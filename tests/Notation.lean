import Lean
import LeanJson

/-!
# `json%` next to Lean core's `json%`

Lean core declares its own `json%` (`Lean.Data.Json.Elab`, for `Lean.Json`),
which every module importing `Lean` sees. LeanJson's `json%` is declared at a
higher priority, so with both in scope a literal is LeanJson's, with no type
ascription (the FastAPI-style handler body `json% {"message": "Hello World"}`).
This file imports both; it is a compile-time test, built by default.
-/

open LeanJson

/-- No expected type: the literal is LeanJson's. -/
def hello := json% {"message": "Hello World"}

example : hello = Json.obj #[("message", .str "Hello World")] := rfl

def itemId : Nat := 5
def q : Option String := none

/-- Splices, nesting, numbers, `null` and literals, unascribed. -/
def item := json% {"item_id": itemId, "q": q, "tags": ["a", "b"], "n": -3, "ok": true, "x": null}

example : item = Json.obj #[("item_id", .num (.int 5)), ("q", .null),
    ("tags", .arr #[.str "a", .str "b"]), ("n", .num (.int (-3))), ("ok", .bool true), ("x", .null)] := rfl

/-- With an expected type it is the same value. -/
example : (json% {"message": "Hello World"} : Json) = hello := rfl

def main : IO UInt32 := do
  IO.println s!"json% with Lean imported: {(print hello).val.size} bytes, {(print item).val.size} bytes"
  return 0
