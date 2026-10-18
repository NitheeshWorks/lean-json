/-!
# Generator of keys that collide in a hash table

`lake exe collidegen <count> <bits> > tests/fixtures/collide-keys.txt` prints
`count` keys `"c<i>"` whose Lean `String.hash` values all land in hash-table
bucket 0 of every `Std.HashMap` with at most `2^bits` buckets (the bucket is
the low bits of `scrambleHash (String.hash k)`). With a plain
`Std.HashMap String Nat` as the key index, an object of these keys takes time
quadratic in the keys; `KeyIndex` (`LeanJson/RepoImpl/KeyIndex.lean`) must not.
The fixture is generated once and committed; `lake exe bench collide` reads it.
-/

/-- Std's bucket scrambler (`Std.DHashMap.Internal.scrambleHash`). -/
def scramble (h : UInt64) : UInt64 :=
  let f := h ^^^ (h >>> 32)
  f ^^^ (f >>> 16)

def main (args : List String) : IO UInt32 := do
  let count := (args[0]?.bind String.toNat?).getD 10000
  let bits := (args[1]?.bind String.toNat?).getD 16
  let mask : UInt64 := (1 <<< bits.toUInt64) - 1
  let out ← IO.getStdout
  let mut found := 0
  let mut i := 0
  while found < count do
    let k := "c" ++ toString i
    if scramble k.hash &&& mask == 0 then
      out.putStrLn k
      found := found + 1
    i := i + 1
  return 0
