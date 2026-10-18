import LeanJson.Proofs.Compact
import LeanJson.RepoImpl.Notation

/-!
# APIs: the public surface

pydantic-core's JSON functions, under their own names (and Lean-cased
aliases), each returning its value together with the proved guarantees:

| pydantic-core                         | here                                          |
|---------------------------------------|-----------------------------------------------|
| `from_json(data)`                     | `from_json data` (`String` or `ByteArray`)    |
| `to_json(value)`                      | `to_json value` (any `IntoJson` value)        |
| `to_json(value, indent=2)`            | `to_json value (indent := some 2)`            |
| `to_json(value, ensure_ascii=True)`   | `to_json value (ensure_ascii := true)`        |
| `ValueError` / `json_invalid` context | `JsonError`, `JsonError.description`          |

The refinements (`Spec.Parsed`, `Spec.Printed`, `Spec.ParsedAt`) are proved
here from the theorems of `Proofs/`; code that wants only the value takes
`.val`.
-/

namespace LeanJson

open Spec

/-- What `from_json` accepts: text or bytes, as in Python. -/
class JsonInput (α : Type) where
  toBytes : α → ByteArray

instance : JsonInput ByteArray := ⟨id⟩
instance : JsonInput String := ⟨String.toUTF8⟩

theorem parsed_of_ref {bs : ByteArray} {v : Json} (h : parseDocument bs = .ok v) : Parsed bs v where
  ref := h
  reprint o := parseLossless_print v o
  canonical _ _ hw := parse_canonical h hw

/-- Parse a whole JSON document (`from_json`): optional whitespace, one
value, optional whitespace, end of input. Errors carry jiter's kind, byte
offset, line and column. -/
def parse (bs : ByteArray) : Except JsonError {v : Json // Parsed bs v} :=
  match h : parseDocument bs with
  | .ok v => .ok ⟨v, parsed_of_ref h⟩
  | .error e => .error (e.toJsonError bs)

/-- `from_json(data)`: parse JSON text or bytes. -/
def from_json {α : Type} [JsonInput α] (data : α) :
    Except JsonError {v : Json // Parsed (JsonInput.toBytes data) v} :=
  parse (JsonInput.toBytes data)

/-- `from_json`, Lean-cased. -/
abbrev fromJson {α : Type} [JsonInput α] (data : α) := from_json data

/-- `parse` on the UTF-8 bytes of a string. -/
def parseStr (s : String) : Except JsonError {v : Json // Parsed s.toUTF8 v} :=
  parse s.toUTF8

theorem parsedAt_of_ref {bs : ByteArray} {pos : Nat} {r : Json × Nat}
    (h : parseValue bs pos (fuelFor bs pos) = .ok r) : ParsedAt bs pos r where
  ref := h
  bounds := step_progress {} bs pos _ r.1 r.2 h
  canonical o d w rest hw hr := by
    have e1 := parse_print_ext o d w bs pos rest (fuelFor bs pos) hw hr
      (by have := length_le_of_at hw; unfold fuelFor; omega)
    rw [parseValue_relax {} bs _ pos r h] at e1
    cases e1; rfl

/-- Parse one value starting at byte `pos` (after optional whitespace),
returning it with the position just past it; trailing bytes are left alone.
For streaming and embedded use. -/
def parseAt (bs : ByteArray) (pos : Nat) :
    Except JsonError {r : Json × Nat // ParsedAt bs pos r} :=
  match h : parseValue bs pos (fuelFor bs pos) with
  | .ok r => .ok ⟨r, parsedAt_of_ref h⟩
  | .error e => .error (e.toJsonError bs)

theorem printed (o : PrintOpts) (v : Json) : Printed o v (printWith o 0 v).toByteArray where
  bytes := by simp
  roundTrip := parseLossless_print v o
  roundTripDefault h := parse_print v o h
  compact ho := by simpa using print_compact o ho v

/-- Print a value. The default options give the compact form. -/
def print (v : Json) (o : PrintOpts := {}) : {b : ByteArray // Printed o v b} :=
  ⟨(printWith o 0 v).toByteArray, printed o v⟩

/-- `to_json(value, indent=None, ensure_ascii=False)`: serialise any value
that converts to JSON. -/
def to_json {α : Type} [IntoJson α] (value : α) (indent : Option Nat := none)
    (ensure_ascii : Bool := false) :
    {b : ByteArray // Printed { indent, ensureAscii := ensure_ascii } (intoJson value) b} :=
  print (intoJson value) { indent, ensureAscii := ensure_ascii }

/-- `to_json`, Lean-cased. -/
abbrev toJson {α : Type} [IntoJson α] (value : α) (indent : Option Nat := none)
    (ensure_ascii : Bool := false) := to_json value indent ensure_ascii

/-- The printed form as a `String` (the bytes are always valid UTF-8). -/
def printStr (v : Json) (o : PrintOpts := {}) : String :=
  (String.fromUTF8? (print v o).val).getD ""

end LeanJson
