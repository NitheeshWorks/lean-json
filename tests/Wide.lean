import LeanJson
open LeanJson
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 10000000
  let mut b : ByteArray := ByteArray.emptyWithCapacity (2*n+2)
  b := b.push 91
  for i in [0:n] do
    if i > 0 then b := b.push 44
    b := b.push 49
  b := b.push 93
  match parse b with
  | .ok v => IO.println s!"ok {(v.val.getArr?.map (·.length))}"
  | .error e => IO.println e.description
  let mut o : ByteArray := ByteArray.emptyWithCapacity (8*n+2)
  o := o.push 123
  for i in [0:n] do
    if i > 0 then o := o.push 44
    o := o ++ "\"a\":1".toUTF8
  o := o.push 125
  match parse o with
  | .ok v => IO.println s!"ok obj {(v.val.getObj?.map (·.length))}"
  | .error e => IO.println e.description
  -- 10^7 open and close brackets: rejected at depth 202, no stack overflow
  let mut d : ByteArray := ByteArray.emptyWithCapacity (2*n)
  for _ in [0:n] do d := d.push 91
  for _ in [0:n] do d := d.push 93
  match parse d with
  | .ok _ => IO.println "deep accepted?!"
  | .error e => IO.println s!"deep: {e.description}"
  -- a wide array printed back
  match parse b with
  | .ok v => IO.println s!"reprint {(print v.val).val.size} bytes"
  | .error e => IO.println e.description
