import LeanJson
open LeanJson

/-!
# Native memory and time benchmark

`lake exe bench [flat|keys|strings] [mb]` builds an input of about `mb` MB,
parses it with `parse` (the `from_json` defaults) and reports the time and the
process's peak resident memory (`VmHWM`). It fails when the memory the parse
adds exceeds `8 × input + 32 MB`. Run one kind per process: the peak is
process-wide.

* `flat`: `[1,1,...]`, 10 M small integers in 20 MB (pydantic-core 2.50.1:
  211 MB peak).
* `keys`: one object repeating `"key":12345`, collapsed to one member as a
  `dict` (pydantic-core: 136 MB at 60 MB).
* `strings`: an array of 30-byte strings.
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

def strings (mb : Nat) : ByteArray := Id.run do
  let item := "\"hello world, a medium string\"".toUTF8
  let n := mb * 1000000 / (item.size + 1)
  let mut b := ByteArray.emptyWithCapacity (n * (item.size + 1) + 2)
  b := b.push 91
  for i in [0:n] do
    if i > 0 then b := b.push 44
    b := b ++ item
  b.push 93

def main (args : List String) : IO UInt32 := do
  let kind := args.head?.getD "flat"
  let mb := (args.drop 1).head?.bind String.toNat? |>.getD 20
  let input := match kind with
    | "keys" => repeatedKeys mb
    | "strings" => strings mb
    | _ => flatArray mb
  let base ← peakKB
  let t ← IO.monoMsNow
  match parse input with
  | .ok v =>
    let t2 ← IO.monoMsNow
    let peak ← peakKB
    let out := (print v.val).val.size
    let added := (peak - base) * 1024
    let bound := 8 * input.size + 32 * 1000000
    IO.println s!"{kind} {input.size / 1000000} MB: parse {t2 - t} ms, peak {peak / 1024} MB (before {base / 1024} MB), reprint {out} bytes"
    if added > bound then
      IO.println s!"FAIL: the parse added {added / 1000000} MB, over the bound {bound / 1000000} MB"
      return 1
    return 0
  | .error e => IO.println e.description; return 1
