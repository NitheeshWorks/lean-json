import LeanJson
open LeanJson

/-! The README quickstart, compiled so it cannot rot (`lake exe quickstart`). -/

def main : IO Unit := do
  -- from_json: text or bytes in, a `Json` value (or a jiter-style error) out
  let data ← IO.ofExcept ((·.val) <$> from_json "{\"name\": \"Alice\", \"tags\": [\"a\", \"b\"]}"
    |>.mapError (·.description))
  IO.println data                                   -- {"name":"Alice","tags":["a","b"]}
  IO.println data["name"]?                          -- (some "Alice")
  IO.println data["tags"]?[1]?                      -- (some "b")
  -- to_json: compact by default, like Starlette's JSONResponse
  let b := (to_json data).val
  IO.println (String.fromUTF8! b)                   -- {"name":"Alice","tags":["a","b"]}
  IO.println (String.fromUTF8! (to_json data (indent := some 2)).val)
  -- json% builds values from literals and Lean terms
  let item_id : Int := 42
  let q : Option String := none
  IO.println (json% {"item_id": item_id, "q": q})   -- {"item_id":42,"q":null}
  -- errors read like pydantic's json_invalid
  match from_json "[1,\n2,\n3,]" with
  | .ok _ => pure ()
  | .error e => IO.println s!"Invalid JSON: {e.description}"  -- trailing comma at line 3 column 3
