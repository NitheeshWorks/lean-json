import LeanJson.Specifications.Json

/-!
# APIs: the public surface

What lean-pydantic, lean-httpx and lean-starlette call. Each function takes
no precondition and returns a refinement whose predicate is named in
`Specifications/Json.lean` (`Spec.Parsed`, `Spec.ParsedAt`, `Spec.Printed`);
those predicates are proved, by construction here and by the theorems of
`Proofs/`, and they only ever gain fields, so code that takes `.val` keeps
compiling as the guarantees grow.

| Upstream (pydantic-core)          | Here                                   |
|-----------------------------------|----------------------------------------|
| `from_json(data)`                 | `LeanJson.parse` / `LeanJson.parseStr` |
| `to_json(v)`                      | `LeanJson.print v`                     |
| `to_json(v, indent=k)`            | `LeanJson.print v { indent := some k }` |
| `to_json(v, ensure_ascii=True)`   | `LeanJson.print v { ensureAscii := true }` |
| `json_invalid` error context      | `JsonError.description`                |
-/

namespace LeanJson

/-- Parse a whole JSON document (`from_json`): optional whitespace, one value,
optional whitespace, end of input. On failure, the error carries jiter's
kind, byte offset, line and column. -/
def parse (bs : ByteArray) : Except JsonError {v : Json // Spec.Parsed bs v} :=
  match h : parseDocument bs with
  | .ok v => .ok ⟨v, ⟨h⟩⟩
  | .error e => .error (e.toJsonError bs)

/-- `parse` on the UTF-8 bytes of a string. -/
def parseStr (s : String) : Except JsonError {v : Json // Spec.Parsed s.toUTF8 v} :=
  parse s.toUTF8

/-- Parse one value starting at byte `pos` (after optional whitespace),
returning it with the position just past it; trailing bytes are left alone.
For streaming and embedded use. -/
def parseAt (bs : ByteArray) (pos : Nat) : Except JsonError {r : Json × Nat // Spec.ParsedAt bs pos r} :=
  match h : parseValue bs pos (fuelFor bs pos) with
  | .ok r => .ok ⟨r, ⟨h⟩⟩
  | .error e => .error (e.toJsonError bs)

/-- Print a value (`to_json`). The default options give the compact form;
`indent` and `ensureAscii` mirror pydantic-core's keyword arguments. -/
def print (v : Json) (o : PrintOpts := {}) : {b : ByteArray // Spec.Printed o v b} :=
  ⟨(printWith o 0 v).toByteArray, ⟨by simp⟩⟩

/-- The printed form as a `String` (the bytes are always valid UTF-8). -/
def printStr (v : Json) (o : PrintOpts := {}) : String :=
  (String.fromUTF8? (print v o).val).getD ""

end LeanJson
