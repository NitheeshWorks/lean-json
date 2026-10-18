import LeanJson
open LeanJson
def deep : Nat → Json | 0 => .null | n+1 => .arr [deep n]
def main : IO Unit := do
  for n in [20000, 200000] do
    let t ← IO.monoMsNow
    let b := (print (deep n)).val
    IO.println s!"print depth {n}: {b.size} bytes {(← IO.monoMsNow) - t} ms"
    let t ← IO.monoMsNow
    match parse b with
    | .ok _ => IO.println s!"parse depth {n}: {(← IO.monoMsNow) - t} ms"
    | .error e => IO.println e.description
  for k in [100000, 1000000] do
    let s := "0." ++ String.ofList (List.replicate k '7')
    let t ← IO.monoMsNow
    match from_json s with
    | .ok v => do
      let t2 ← IO.monoMsNow
      let out := (print v.val).val
      IO.println s!"frac {k}: parse {t2 - t} ms, print {(← IO.monoMsNow) - t2} ms, {out.size} bytes"
    | .error e => IO.println e.description
  let s := "1" ++ String.ofList (List.replicate 100000 '0') ++ ".0"
  let t ← IO.monoMsNow
  match from_json s with
  | .ok v => IO.println s!"trailing zeros: {(← IO.monoMsNow) - t} ms {(print v.val).val.size}"
  | .error e => IO.println e.description
  let big : Json := .arr ((List.range 300000).map fun i => json% {"id": i, "name": "x", "tags": [1.5, true, null]})
  let t ← IO.monoMsNow
  let b := (print big).val
  let t2 ← IO.monoMsNow
  match parse b with
  | .ok _ => IO.println s!"wide: {b.size} bytes, print {t2 - t} ms, parse {(← IO.monoMsNow) - t2} ms"
  | .error e => IO.println e.description
