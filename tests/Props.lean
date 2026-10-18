import LeanJson

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved. Not a substitute for the theorems; the check that
runs in under a second so a mistake surfaces while the change is still in
your head.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

open LeanJson

def Rng.pick {α : Type} [Inhabited α] (r : Rng) (xs : List α) : α × Rng :=
  let (i, r) := r.nat xs.length
  (xs[i]!, r)

/-- A random character: ASCII, controls, quotes, BMP, astral. -/
def genChar (r : Rng) : Char × Rng :=
  let (k, r) := r.nat 6
  match k with
  | 0 => let (n, r) := r.nat 32; (Char.ofNat n, r)
  | 1 => r.pick ['"', '\\', '/', ' ', '\n', '\t', Char.ofNat 127]
  | 2 => let (n, r) := r.nat 0xD000; (Char.ofNat (0x80 + n), r)
  | 3 => let (n, r) := r.nat 0x100000; (Char.ofNat (0x10000 + n), r)
  | _ => let (n, r) := r.nat 95; (Char.ofNat (32 + n), r)

def genString (r : Rng) : String × Rng := Id.run do
  let (len, r0) := r.nat 12
  let mut g := r0
  let mut cs : List Char := []
  for _ in [0:len] do
    let (c, g') := genChar g
    g := g'
    cs := c :: cs
  (String.ofList cs, g)

def genNumber (r : Rng) : Number × Rng :=
  let (k, r) := r.nat 7
  match k with
  | 4 => (.nan, r)
  | 5 => (.inf, r)
  | 6 => (.negInf, r)
  | 0 => let (n, r) := r.nat 1000; (.int ((n : Int) - 500), r)
  | 1 =>
    let (n, r) := r.next
    let (e, r) := r.nat 30
    (.int ((n.toNat : Int) * 10 ^ e * (if e % 2 = 0 then 1 else -1)), r)
  | _ =>
    let (m, r) := r.next
    let (e, r) := r.nat 80
    let (s, r) := r.nat 2
    (.float (Decimal.normalize (s = 1) (m.toNat % 10 ^ ((e % 19) + 1)) ((e : Int) - 40)), r)

def genJson : Nat → Rng → Json × Rng
  | 0, r => let (n, r) := genNumber r; (.num n, r)
  | d + 1, r =>
    let (k, r) := r.nat 8
    match k with
    | 0 => (.null, r)
    | 1 => let (b, r) := r.nat 2; (.bool (b = 1), r)
    | 2 => let (n, r) := genNumber r; (.num n, r)
    | 3 => let (s, r) := genString r; (.str s, r)
    | 4 | 5 => Id.run do
      let (len, r0) := r.nat 4
      let mut g := r0
      let mut xs : List Json := []
      for _ in [0:len] do
        let (x, g') := genJson d g
        g := g'
        xs := x :: xs
      (.arr xs.toArray, g)
    | _ => Id.run do
      let (len, r0) := r.nat 4
      let mut g := r0
      let mut kvs : List (String × Json) := []
      for _ in [0:len] do
        let (kk, g1) := g.nat 3
        let (s, g2) := genString g1
        let (x, g3) := genJson d g2
        g := g3
        kvs := ((if kk = 0 then "k" else s), x) :: kvs
      (.obj kvs.toArray, g)

mutual
/-- Every object's repeated keys collapsed, `dict`-style, all the way down. -/
def deepDedup : Json → Json
  | .arr ⟨xs⟩ => .arr ⟨deepList xs⟩
  | .obj ⟨kvs⟩ => .obj (Json.dedupKeys ⟨deepFields kvs⟩)
  | j => j
def deepList : List Json → List Json
  | [] => []
  | x :: xs => deepDedup x :: deepList xs
def deepFields : List (String × Json) → List (String × Json)
  | [] => []
  | (k, v) :: kvs => (k, deepDedup v) :: deepFields kvs
end

/-- The default parser returns `v` with repeated keys collapsed; the parser
that keeps them returns `v` itself. -/
def checkRoundTrip (o : PrintOpts) (r : Rng) : Option String × Rng :=
  let (v, r) := genJson 4 r
  let b := (print v o).val
  match parse b, parseWith { dedupKeys := false } b with
  | .ok w, .ok u =>
    (if w.val == deepDedup v && u.val == v then none else some s!"{v} reparsed as {w.val} / {u.val}", r)
  | .error e, _ | _, .error e => (some s!"{v}: {e.description}", r)

def finiteFloat (r : Rng) : Float × Rng :=
  let (bits, r) := r.next
  let x := Float.ofBits bits
  if x.isNaN || x.isInf then (1.5, r) else (x, r)

def checkModes (r : Rng) : Option String × Rng :=
  let (v, r) := genJson 4 r
  let (m, r) := r.pick [InfNanMode.null, .strings]
  let b := (print v { infNan := m }).val
  match parseWith .strict b with
  | .ok w =>
    (if v.allFinite && !(w.val == deepDedup v) then some s!"{v} reparsed as {w.val}" else none, r)
  | .error e => (some s!"{v}: {e.description}", r)

def properties : List Property := [
  ⟨"null and strings modes print strict RFC 8259 JSON (and round-trip finite values)", checkModes⟩,
  ⟨"strict parse of constants output: accepted iff the value is finite", fun r =>
    let (v, r) := genJson 4 r
    match parseWith .strict (print v).val with
    | .ok w => (if v.allFinite && w.val == deepDedup v then none else some s!"{v}", r)
    | .error _ => (if v.allFinite then some s!"{v} rejected" else none, r)⟩,
  ⟨"parse (print v) = v, compact", checkRoundTrip {}⟩,
  ⟨"parse (print v) = v, indent 2", checkRoundTrip { indent := some 2 }⟩,
  ⟨"parse (print v) = v, ensure_ascii", checkRoundTrip { ensureAscii := true }⟩,
  ⟨"parse (print v) = v, json.dumps separators", checkRoundTrip { spaced := true }⟩,
  ⟨"indexing: v[k]? is the last member named k, v[i]? the i-th element", fun r =>
    let (v, r) := genJson 3 r
    let (i, r) := r.nat 5
    let ok := match v with
      | .obj kvs => kvs.all fun kv => v[kv.1]? == Json.lookupLast kv.1 kvs.toList
      | .arr xs => v[i]? == xs[i]? && v[xs.size]? == none
      | _ => v["k"]? == none && v[0]? == none
    (if ok then none else some s!"{v}", r)⟩,
  ⟨"ensure_ascii output is ASCII", fun r =>
    let (v, r) := genJson 4 r
    let b := (print v { ensureAscii := true }).val
    (if b.data.all (· < 128) then none else some s!"{v}", r)⟩,
  ⟨"printBA agrees with printWith", fun r =>
    let (v, r) := genJson 4 r
    (if printBA {} v == (printWith {} 0 v).toByteArray then none else some s!"{v}", r)⟩,
  ⟨"parseAt reads a value out of a concatenation", fun r =>
    let (a, r) := genJson 3 r
    let (b, r) := genJson 3 r
    let pa := (print a).val
    let buf := pa ++ " ".toUTF8 ++ (print b).val
    match parseAt buf 0 with
    | .ok x => (if x.val == (deepDedup a, pa.size) then none else some s!"{a} then {b}", r)
    | .error e => (some e.description, r)⟩,
  ⟨"Float -> Number -> Float: identity on bits, NaN to NaN", fun r =>
    let (bits, r) := r.next
    let x := Float.ofBits bits
    let y := (Number.ofFloat x).toFloat
    (if (x.isNaN && y.isNaN) || x.toBits == y.toBits then none else some s!"{x} -> {y}", r)⟩,
  ⟨"Float -> shortest decimal -> Float is the identity on bits", fun r =>
    let (x, r) := finiteFloat r
    match Number.ofFloat? x with
    | some n => (if n.toFloat.toBits == x.toBits then none else some s!"{x} via {Json.num n}", r)
    | none => (some s!"{x}: no decimal", r)⟩,
  ⟨"printed Float re-parses to the same bits", fun r =>
    let (x, r) := finiteFloat r
    match from_json (to_json x).val with
    | .ok v => match v.val with
      | .num n => (if n.toFloat.toBits == x.toBits then none else some s!"{x}", r)
      | _ => (some s!"{x}: not a number", r)
    | .error e => (some s!"{x}: {e.description}", r)⟩,
  ⟨"dedupKeys keeps last values, distinct keys, first positions", fun r =>
    let (v, r) := genJson 3 r
    match v with
    | .obj kvs =>
      let dd := (Json.dedupKeys kvs).toList
      let keys := dd.map (·.1)
      let distinct := keys.eraseDups.length == keys.length
      let same := kvs.all fun kv => Json.lookupLast kv.1 dd == Json.lookupLast kv.1 kvs.toList
      let order := keys == (kvs.toList.map (·.1)).eraseDups
      let list := dd == Json.dedupKeysList kvs.toList
      (if distinct && same && order && list then none else some s!"{v}", r)
    | _ => (none, r)⟩,
  ⟨"random bytes: errors in bounds, results within the depth limit", fun r => Id.run do
    let (len, r0) := r.nat 24
    let mut g := r0
    let mut bs : ByteArray := .empty
    for _ in [0:len] do
      let (b, g') := g.pick [34, 91, 93, 123, 125, 44, 58, 32, 10, 48, 49, 45, 46, 101, 116, 110, 92, 117, 97, 0xc3, 0xa9]
      g := g'
      bs := bs.push (UInt8.ofNat b)
    match parse bs with
    | .ok v => (if v.val.height ≤ 200 then none else some s!"{bs.data}: too deep", g)
    | .error e =>
      (if e.offset ≤ bs.size then none else some s!"{bs.data}: {e.description}", g)⟩,
  ⟨"random nesting: depth ≤ 200 parses, deeper is recursion limit exceeded", fun r =>
    let (n, r) := r.nat 260
    let (scalar, r) := r.nat 2
    let inner := if scalar = 1 then "1" else ""
    let s := String.join (List.replicate n "[") ++ inner ++ String.join (List.replicate n "]")
    let deep := if scalar = 1 then n ≥ 201 else n ≥ 202
    match from_json s with
    | .ok v => (if !deep && v.val.height ≤ 200 then none else some s!"depth {n} accepted", r)
    | .error e =>
      (if deep && e.kind == .recursionLimitExceeded then none else some s!"depth {n}: {e.description}", r)⟩,
  ⟨"Lean.Json bridge: ofLean (toLean v) = v on its common fragment", fun r =>
    let (n, r) := r.nat 1000
    let (s, r) := genString r
    let v : Json := json% {"a": [(n : Nat), true, null], "b": s, "c": {"d": -3}}
    (if Json.ofLean v.toLean == v then none else some s!"{v}", r)⟩
]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
