import LeanJson
open LeanJson

/-!
# Native memory and time benchmark

`lake exe bench [flat|keys|strings|wide|dups|collide|collide-naive|e2e] [mb] [max-ms]` builds an input of about `mb` MB,
parses it with `parse` (the `from_json` defaults) and reports the time and the
process's peak resident memory (`VmHWM`). It fails when the memory the parse
adds exceeds `8 × input + 32 MB` (`10 ×` for `wide`, whose every key is a
string kept twice, in the object and in its key index; `12 ×` for `flat` and
`e2e`, see below), or the parse takes longer than `max-ms` when given.

`flat` is ten million one-byte elements, so its result is almost entirely
the element array: 8 bytes of pointer per 2 bytes of input, 80 MB. An array
built by `push` grows by doubling, and at the last growth the old buffer and
the new one, twice as large, are live together: up to 3 × the final array.
How much of the new buffer the kernel counts as resident varies by machine:
`grow` (ten million pushes, no parsing) adds 220 MB on one machine where
`grow-exact` (the same array allocated at its final size) adds 80 MB, and
the parse of `flat` adds 147 MB on some CI runners and 226 MB on others. So
the bound for `flat` and `e2e` is `12 × input + 32 MB`: the input, plus three
times the 4-bytes-per-input-byte pointer array, plus slack. pydantic-core
2.50.1 adds 150 MB on the same input. Run one kind per process: the peak is
process-wide.

* `flat`: `[1,1,...]`, 10 M small integers in 20 MB (pydantic-core 2.50.1:
  211 MB peak).
* `keys`: one object repeating `"key":12345`, collapsed to one member as a
  `dict` (pydantic-core: 136 MB at 60 MB).
* `strings`: an array of 30-byte strings.
* `wide`: one object of distinct keys `"k0":0,"k1":1,…` (pydantic-core 2.50.1:
  2 MB, 152k keys in 44-52 ms; 20 MB, 1.4 M keys in 1.4 s). Before key
  collapsing ran in constant time per key this was quadratic (2 MB: 39 s).
* `dups`: the same with keys cycling through 1000 names, so almost every
  member repeats an earlier key (pydantic-core: 20 MB in 174 ms).
* `collide`: one object of the 10000 keys in `tests/fixtures/collide-keys.txt`
  (from `lake exe collidegen`), which all share one bucket of every
  `Std.HashMap` up to 65536 buckets under Lean's fixed-seed `String.hash`,
  written `mb` times over (so later passes repeat earlier keys). The key
  index must stay fast on them (`KeyIndex`). `collide-naive` inserts the same
  keys into a plain `Std.HashMap String Nat`, to show the attack is real.
* `e2e`: the `flat` input as a server handles a request body: text in,
  `from_json`, `to_json` out (bound: 12 × input + 32 MB).
* `grow`, `grow-exact`: the array-growth diagnostic above (no bound).
-/

def peakKB : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  for l in s.splitOn "\n" do
    if l.startsWith "VmHWM:" then
      return ((l.drop 6).trimAscii.toString.takeWhile Char.isDigit).toNat!
  return 0

def flatArray (mb : Nat) : ByteArray := Id.run do
  let n := mb * 1000000 / 2
  let mut b := ByteArray.emptyWithCapacity (2 * n + 2)
  b := b.push 91
  for i in [0:n] do
    if i > 0 then b := b.push 44
    b := b.push 49
  b.push 93

def repeatedKeys (mb : Nat) : ByteArray := Id.run do
  let item := "\"key\":12345".toUTF8
  let n := mb * 1000000 / (item.size + 1)
  let mut b := ByteArray.emptyWithCapacity (n * (item.size + 1) + 2)
  b := b.push 123
  for i in [0:n] do
    if i > 0 then b := b.push 44
    b := b ++ item
  b.push 125

/-- An object of distinct keys `"k0":0,"k1":1,…` (`period = 0`), or of keys
cycling through `period` names, each repeated (`"k0".."k999"` again and
again): the wide request bodies a server must not choke on. -/
def wideKeys (mb : Nat) (period : Nat := 0) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (mb * 1000000 + 64)
  b := b.push 123
  let mut i := 0
  while b.size < mb * 1000000 do
    if i > 0 then b := b.push 44
    let k := if period = 0 then i else i % period
    b := b ++ s!"\"k{k}\":{i % 1000}".toUTF8
    i := i + 1
  b.push 125

/-- 20000 keys of 1000 characters each (`"k0xxx…":0,…`). -/
def longKeys (_ : Unit) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 20300000
  b := b.push 123
  for i in [0:20000] do
    if i > 0 then b := b.push 44
    let k := s!"k{i}"
    b := b ++ s!"\"{k}{String.ofList (List.replicate (1000 - k.length) 'x')}\":{i}".toUTF8
  b.push 125

/-- One string of `mb` MB of a repeated escape `esc` (`\\n`, or a surrogate
pair `\\ud83d\\ude00`). -/
def escapeString (mb : Nat) (esc : String) : ByteArray := Id.run do
  let e := esc.toUTF8
  let reps := mb * 1000000 / e.size
  let mut b := ByteArray.emptyWithCapacity (reps * e.size + 2)
  b := b.push 34
  for _ in [0:reps] do
    b := b ++ e
  b.push 34

/-- 5000 integers of 4000 digits. -/
def bigInts (_ : Unit) : ByteArray := Id.run do
  let d := (String.join (List.replicate 400 "1234567890")).toUTF8
  let mut b := ByteArray.emptyWithCapacity (5000 * 4001 + 2)
  b := b.push 91
  for i in [0:5000] do
    if i > 0 then b := b.push 44
    b := b ++ d
  b.push 93

def strings (mb : Nat) : ByteArray := Id.run do
  let item := "\"hello world, a medium string\"".toUTF8
  let n := mb * 1000000 / (item.size + 1)
  let mut b := ByteArray.emptyWithCapacity (n * (item.size + 1) + 2)
  b := b.push 91
  for i in [0:n] do
    if i > 0 then b := b.push 44
    b := b ++ item
  b.push 93

/-- A request/response round trip as a server does it: the body as text,
`from_json`, then `to_json` of the result. The peak covers both. -/
def endToEnd (mb : Nat) : IO UInt32 := do
  let body := String.fromUTF8! (flatArray mb)
  let base ← peakKB
  let t ← IO.monoMsNow
  match from_json body with
  | .ok v =>
    let out := (to_json v.val).val
    let t2 ← IO.monoMsNow
    let peak ← peakKB
    let added := (peak - base) * 1024
    let bound := 12 * body.utf8ByteSize + 32 * 1000000
    IO.println s!"e2e {body.utf8ByteSize / 1000000} MB: from_json + to_json {t2 - t} ms, peak {peak / 1024} MB (before {base / 1024} MB), {out.size} bytes out"
    if added > bound then
      IO.println s!"FAIL: the round trip added {added / 1000000} MB, over the bound {bound / 1000000} MB"
      return 1
    return 0
  | .error e => IO.println e.description; return 1

def collideKeys : IO (Array String) := do
  let s ← IO.FS.readFile "tests/fixtures/collide-keys.txt"
  return (s.splitOn "\n").filter (· ≠ "") |>.toArray

/-- The colliding keys as one object, written `passes` times over. -/
def collideObject (keys : Array String) (passes : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (passes * keys.size * 16 + 2)
  b := b.push 123
  let mut first := true
  for p in [0:passes] do
    for k in keys do
      if !first then b := b.push 44
      first := false
      b := b ++ s!"\"{k}\":{p}".toUTF8
  b.push 125

/-- The same keys into a plain `Std.HashMap String Nat`: the index this
library would have without `KeyIndex`. -/
def collideNaive (passes : Nat) : IO UInt32 := do
  let keys ← collideKeys
  let t ← IO.monoMsNow
  let mut m : Std.HashMap String Nat := {}
  for p in [0:passes] do
    for k in keys do
      m := m.insert k p
  let t2 ← IO.monoMsNow
  IO.println s!"collide-naive: {keys.size} keys x {passes} into Std.HashMap String Nat: {t2 - t} ms ({m.size} entries)"
  return 0

/-- Array growth alone, no parsing: `mb`·500000 elements pushed one by one
(`grow`) or into an array allocated at its final size (`grow-exact`). A
diagnostic for how the machine accounts the doubling of a growing array. -/
def grow (exact : Bool) (mb : Nat) : IO UInt32 := do
  let n := mb * 500000
  let base ← peakKB
  let mut a : Array Json := if exact then Array.emptyWithCapacity n else #[]
  for _ in [0:n] do
    a := a.push .null
  let peak ← peakKB
  IO.println s!"grow{if exact then "-exact" else ""} {n} elements: peak {peak / 1024} MB (before {base / 1024} MB), added {(peak - base) / 1024} MB, size {a.size}"
  return 0

def main (args : List String) : IO UInt32 := do
  let kind := args.head?.getD "flat"
  if kind == "grow" || kind == "grow-exact" then
    return ← grow (kind == "grow-exact") ((args.drop 1).head?.bind String.toNat? |>.getD 20)
  let mb := (args.drop 1).head?.bind String.toNat? |>.getD 20
  let maxMs := (args.drop 2).head?.bind String.toNat?
  if kind == "e2e" then return ← endToEnd mb
  if kind == "collide-naive" then return ← collideNaive mb
  let keys ← if kind == "collide" then collideKeys else pure #[]
  let input := match kind with
    | "keys" => repeatedKeys mb
    | "strings" => strings mb
    | "wide" => wideKeys mb
    | "dups" => wideKeys mb 1000
    | "collide" => collideObject keys mb
    | "longkeys" => longKeys ()
    | "escapes" => escapeString mb "\\n"
    | "surrogates" => escapeString mb "\\ud83d\\ude00"
    | "bigints" => bigInts ()
    | _ => flatArray mb
  let base ← peakKB
  let t ← IO.monoMsNow
  match parse input with
  | .ok v =>
    let t2 ← IO.monoMsNow
    let peak ← peakKB
    let out := (print v.val).val.size
    let added := (peak - base) * 1024
    let bound := (if kind == "flat" then 12 else if kind == "wide" then 10 else 8) * input.size + 32 * 1000000
    if kind == "collide" then
      match v.val with
      | .obj kvs =>
        if kvs.size != keys.size then
          IO.println s!"FAIL: {kvs.size} members, expected {keys.size} distinct keys"
          return 1
      | _ => IO.println "FAIL: not an object"; return 1
    IO.println s!"{kind} {input.size / 1000000} MB: parse {t2 - t} ms, peak {peak / 1024} MB (before {base / 1024} MB), reprint {out} bytes"
    if added > bound then
      IO.println s!"FAIL: the parse added {added / 1000000} MB, over the bound {bound / 1000000} MB"
      return 1
    if let some m := maxMs then
      if t2 - t > m then
        IO.println s!"FAIL: the parse took {t2 - t} ms, over the bound {m} ms"
        return 1
    return 0
  | .error e => IO.println e.description; return 1
