import LeanJson.RepoImpl.Parse
import LeanJson.RepoImpl.Builder
import Lean.Data.Json.Basic
import Lean.Data.Json.Printer

/-!
# RepoImpl: accessors, dict semantics, `Lean.Json` and `Float` bridges

What a consumer (lean-pydantic, lean-httpx) needs beyond parse and print:
typed getters, last-wins key lookup and Python-`dict` deduplication (jiter
keeps duplicate keys; a `dict` built from them keeps the first position and
the last value), conversions to and from core `Lean.Json`, and the
`Float` bridge (`Number.toFloat`, `Number.ofFloat?`).
-/

namespace LeanJson

namespace Json

instance : Coe String Json := ⟨Json.str⟩
instance : Coe Bool Json := ⟨Json.bool⟩
instance : Coe Int Json := ⟨fun i => Json.num (.int i)⟩
instance : Coe Nat Json := ⟨fun n => Json.num (.int n)⟩
instance : OfNat Json n := ⟨Json.num (.int n)⟩

/-- An integer value. -/
def ofInt (i : Int) : Json := .num (.int i)

/-- An object from its members, in order. -/
def mkObj (kvs : List (String × Json)) : Json := .obj kvs

def isNull : Json → Bool
  | .null => true
  | _ => false

def getBool? : Json → Option Bool
  | .bool b => some b
  | _ => none

def getStr? : Json → Option String
  | .str s => some s
  | _ => none

def getNum? : Json → Option Number
  | .num n => some n
  | _ => none

/-- An integer literal's value (a float literal such as `1.0` is not one; see
`Number.toInt?` for the lax reading). -/
def getInt? : Json → Option Int
  | .num (.int i) => some i
  | _ => none

def getArr? : Json → Option (List Json)
  | .arr xs => some xs
  | _ => none

def getObj? : Json → Option (List (String × Json))
  | .obj kvs => some kvs
  | _ => none

/-- The value of the last member named `k`: what `dict(pairs)[k]` gives in
Python, and what jiter's `LazyIndexMap::get` returns. -/
def lookupLast (k : String) : List (String × Json) → Option Json
  | [] => none
  | (k', v) :: kvs =>
    match lookupLast k kvs with
    | some w => some w
    | none => if k' = k then some v else none

/-- Member `k` of an object, last occurrence winning. -/
def getObjVal? (v : Json) (k : String) : Option Json :=
  match v with
  | .obj kvs => lookupLast k kvs
  | _ => none

/-- Element `i` of an array. -/
def getArrVal? (v : Json) (i : Nat) : Option Json :=
  match v with
  | .arr xs => xs[i]?
  | _ => none

/-- Insert into an association list with `dict` semantics: an existing key
keeps its position and takes the new value. -/
def insertLast (k : String) (v : Json) : List (String × Json) → List (String × Json)
  | [] => [(k, v)]
  | (k', v') :: kvs => if k' = k then (k, v) :: kvs else (k', v') :: insertLast k v kvs

/-- The members as a Python `dict` would hold them: one entry per key, at the
key's first position, with its last value. -/
def dedupKeys (kvs : List (String × Json)) : List (String × Json) :=
  kvs.foldl (fun acc kv => insertLast kv.1 kv.2 acc) []

mutual
/-- How many containers deep the deepest value inside `j` sits: `0` for a
scalar or an empty container, one more than the deepest child otherwise.
jiter (and `from_json`) accepts exactly the documents with `height ≤ 200`. -/
def height : Json → Nat
  | .arr (x :: xs) => 1 + max x.height (heightList xs)
  | .obj ((_, v) :: kvs) => 1 + max v.height (heightFields kvs)
  | _ => 0
def heightList : List Json → Nat
  | [] => 0
  | x :: xs => max x.height (heightList xs)
def heightFields : List (String × Json) → Nat
  | [] => 0
  | (_, v) :: kvs => max v.height (heightFields kvs)
end

end Json

namespace Number

/-- The integer an integer-valued number denotes (`123` and `123.0` both give
`123`, as pydantic's lax int validator accepts; `123.4` gives `none`). -/
def toInt? : Number → Option Int
  | .int i => some i
  | .float d => d.toInt?

/-- The nearest `Float` (huge magnitudes become `±inf`, tiny ones `±0.0`, as
an IEEE parse of the literal would). -/
def toFloat : Number → Float
  | .int i => Float.ofInt i
  | .float d =>
    -- a lower bound on the digit count, from the bit length (log10 2 > 0.30103)
    let L : Int := (d.mant.log2 * 30103 / 100000 : Nat)
    let mag : Float :=
      if d.mant = 0 then 0.0
      else if d.exp + L > 400 then 1.0 / 0.0
      else if d.exp + L < -400 then 0.0
      else if d.exp < 0 then Float.ofScientific d.mant true d.exp.natAbs
      else Float.ofScientific d.mant false d.exp.toNat
    if d.neg then -mag else mag

/-- `x = m * 2^e` exactly, for a finite `x`: (negative, m, e). -/
def decodeFloat (x : Float) : Option (Bool × Nat × Int) :=
  let bits := x.toBits
  let neg := bits >>> 63 == 1
  let be := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if be = 0x7FF then none
  else if be = 0 then some (neg, frac, -1074)
  else some (neg, frac + 2 ^ 52, (be : Int) - 1075)

/-- Round `num / den` to the nearest integer, ties to even. -/
def roundDiv (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r < den then q
  else if q % 2 = 0 then q else q + 1

/-- The decimal exponent of the leading digit of `num / den > 0`. -/
def log10Floor (num den : Nat) : Int :=
  if num ≥ den then ((natDigits (num / den)).length : Int) - 1
  else
    -- smallest k ≥ 1 with num * 10^k ≥ den, at most 330 for a double
    let rec go : Nat → Nat → Int
      | 0, k => -(k : Int)
      | f + 1, k => if num * 10 ^ k ≥ den then -(k : Int) else go f (k + 1)
    go 400 1

/-- The shortest decimal that reads back as `x` (via `Float.ofScientific`),
trying 1 to 17 significant digits; `none` for NaN and infinities. Tested,
not proved (`tests/Props.lean`). -/
def ofFloat? (x : Float) : Option Number :=
  match decodeFloat x with
  | none => none
  | some (neg, m, e) =>
    if m = 0 then some (.float (Decimal.normalize neg 0 0))
    else
      let (num, den) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ e.natAbs)
      let lead := log10Floor num den
      let candidate (p : Nat) : Nat × Int :=
        let q : Int := lead - (p - 1 : Nat)
        let dgt := if q ≥ 0 then roundDiv num (den * 10 ^ q.toNat) else roundDiv (num * 10 ^ q.natAbs) den
        (dgt, q)
      let back (c : Nat × Int) : Float :=
        if c.2 < 0 then Float.ofScientific c.1 true c.2.natAbs else Float.ofScientific c.1 false c.2.toNat
      let target := if neg then -x else x
      let rec search : Nat → Nat → Nat × Int
        | 0, p => candidate p
        | f + 1, p =>
          let c := candidate p
          if (back c).toBits == target.toBits then c else search f (p + 1)
      let c := search 16 1
      some (.float (Decimal.normalize neg c.1 c.2))

end Number

/-! ## `Lean.Json` bridge -/

mutual
/-- Into core `Lean.Json`. Objects become a sorted map, so key order is lost
and the last of duplicate keys wins; floats become `JsonNumber`s exactly
(a float with an integral value becomes indistinguishable from an int).
`JsonNumber` has a `Nat` exponent, so a float above `1e4300` would need its
digits written out; it becomes `null` instead (upstream: `inf`, which
`Lean.Json` cannot hold either). -/
def Json.toLean : Json → Lean.Json
  | .null => .null
  | .bool b => .bool b
  | .num (.int i) => .num ⟨i, 0⟩
  | .num (.float d) =>
    let m : Int := if d.neg then -(d.mant : Int) else d.mant
    if d.exp > 4300 then .null
    else if d.exp ≥ 0 then .num ⟨m * (10 ^ d.exp.toNat : Nat), 0⟩ else .num ⟨m, d.exp.natAbs⟩
  | .str s => .str s
  | .arr xs => .arr (Json.toLeanList xs).toArray
  | .obj kvs => Lean.Json.mkObj (Json.toLeanFields kvs)
def Json.toLeanList : List Json → List Lean.Json
  | [] => []
  | x :: xs => x.toLean :: Json.toLeanList xs
def Json.toLeanFields : List (String × Json) → List (String × Lean.Json)
  | [] => []
  | (k, v) :: kvs => (k, v.toLean) :: Json.toLeanFields kvs
end

/-- From core `Lean.Json`, through its printer and this parser (core's
`Lean.Json` is nested through `Std.TreeMap.Raw`, which admits no structural
recursion). A `JsonNumber` with exponent 0 becomes an int, others a float. -/
def Json.ofLean (j : Lean.Json) : Json :=
  match parseDocument j.compress.toUTF8 with
  | .ok v => v
  | .error _ => .null

/-- The compact printing as a `String`. -/
def Json.compress (v : Json) : String :=
  (String.fromUTF8? (printBA {} v)).getD ""


instance : ToString Json := ⟨Json.compress⟩

/-- Displays as the `json%` term that builds the value. Written by hand: the
derived printer for a nested inductive is a `partial def`. -/
instance : Repr Json := ⟨fun j _ => .text ("json% " ++ j.compress)⟩

end LeanJson
