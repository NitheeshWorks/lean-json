import LeanJson.Proofs.Compact
import LeanJson.Proofs.Builder
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
| `data["name"]`, `data[0]`             | `data["name"]?`, `data[0]?` (`Option Json`)   |
| `json.dumps(value)`                   | `dumps value` (`", "`, `": "`, ASCII)         |

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

theorem parsed_of_ref {cfg : ParseCfg} {bs : ByteArray} {v : Json} (h : parseDocumentWith cfg bs = .ok v) :
    ParsedWith cfg bs v where
  ref := h
  reprint o hrb := parseLossless_print v o hrb
  canonical _ _ hrb hk hw := parse_canonical h hrb hk hw
  height _ hL := parse_height hL h
  finite hs := parse_finite hs h

/-- Parse a whole JSON document under a configuration. Errors carry jiter's
kind, byte offset, line and column. -/
def parseWith (cfg : ParseCfg) (bs : ByteArray) : Except JsonError {v : Json // ParsedWith cfg bs v} :=
  match h : parseDocumentWith cfg bs with
  | .ok v => .ok ⟨v, parsed_of_ref h⟩
  | .error e => .error (e.toJsonError bs)

/-- Parse a whole JSON document as `from_json` does by default: optional
whitespace, one value, optional whitespace, end of input; `NaN`, `Infinity`
and `-Infinity` accepted. -/
def parse (bs : ByteArray) : Except JsonError {v : Json // Parsed bs v} := parseWith {} bs

/-- `from_json(data, allow_inf_nan=True)`: parse JSON text or bytes. With
`allow_inf_nan := false`, `NaN` and the infinities are rejected, as strict
RFC 8259 JSON. -/
def from_json {α : Type} [JsonInput α] (data : α) (allow_inf_nan : Bool := true) :
    Except JsonError {v : Json // ParsedWith { allowInfNan := allow_inf_nan } (JsonInput.toBytes data) v} :=
  parseWith { allowInfNan := allow_inf_nan } (JsonInput.toBytes data)

/-- `from_json`, Lean-cased. -/
abbrev fromJson {α : Type} [JsonInput α] (data : α) (allow_inf_nan : Bool := true) :=
  from_json data allow_inf_nan

/-- `parse` on the UTF-8 bytes of a string. -/
def parseStr (s : String) : Except JsonError {v : Json // Parsed s.toUTF8 v} :=
  parse s.toUTF8

theorem parsedAt_of_ref {bs : ByteArray} {pos : Nat} {r : Json × Nat}
    (h : parseValue bs pos = .ok r) : ParsedAt bs pos r where
  ref := h
  bounds := parseValueAt_progress h
  canonical o d w rest hrb hk hw hr := by
    have e1 := (valueCodec (ParseCfg.relax {}) o d).law w _ _ rest ⟨fits_relax fun _ => hk, hrb⟩ hw hr
    simp only [valueCodec] at e1
    rw [parseValue_relax {} bs pos r h] at e1
    cases e1; rfl

/-- Parse one value starting at byte `pos` (after optional whitespace),
returning it with the position just past it; trailing bytes are left alone.
For streaming and embedded use. -/
def parseAt (bs : ByteArray) (pos : Nat) :
    Except JsonError {r : Json × Nat // ParsedAt bs pos r} :=
  match h : parseValue bs pos with
  | .ok r => .ok ⟨r, parsedAt_of_ref h⟩
  | .error e => .error (e.toJsonError bs)

theorem printed (o : PrintOpts) (v : Json) : Printed o v (printWith o 0 v).toByteArray where
  bytes := by simp
  roundTrip hrb := parseLossless_print v o hrb
  roundTripDefault hrb hi hk hd := parse_print v o (fits_default hi hk hd) hrb
  roundTripStrict hi hk hd hf := parseDocumentWith_print .strict o v (fits_strict hi hk hd hf) (Or.inr hf)
  compact ho hs := by simpa using print_compact o ho hs v

/-- Print a value. The default options give the compact form. Built byte
by byte (`printBA`, linear in the output), proved equal to the specification
`printWith`. It recurses once per level of nesting (`Json.height`), so a value
built in Lean hundreds of thousands of levels deep can exhaust the stack;
values from `from_json` are at most 200 deep. -/
def print (v : Json) (o : PrintOpts := {}) : {b : ByteArray // Printed o v b} :=
  ⟨printBA o v, printBA_eq o v ▸ printed o v⟩

/-- `to_json(value, indent=None, ensure_ascii=False, inf_nan_mode='constants')`:
serialise any value that converts to JSON. NaN and the infinities print per
`inf_nan_mode`, as pydantic-core does (`constants` writes `NaN`, which is not
RFC 8259 JSON; a caller that must emit strict JSON, like Starlette's
`JSONResponse`, checks `Json.allFinite` first, as `allow_nan=False` does). -/
def to_json {α : Type} [IntoJson α] (value : α) (indent : Option Nat := none)
    (ensure_ascii : Bool := false) (inf_nan_mode : InfNanMode := .constants) :
    {b : ByteArray // Printed { indent, ensureAscii := ensure_ascii, infNan := inf_nan_mode }
      (intoJson value) b} :=
  print (intoJson value) { indent, ensureAscii := ensure_ascii, infNan := inf_nan_mode }

theorem parse_val {cfg : ParseCfg} {bs : ByteArray} {v : Json} (h : parseDocumentWith cfg bs = .ok v) :
    (parseWith cfg bs).map (·.val) = .ok v := by
  unfold parseWith
  split
  · rename_i w hw; rw [h] at hw; cases hw; rfl
  · rename_i e he; rw [h] at he; cases he

/-- **`from_json (to_json j) = j`** at both functions' defaults, under every
`indent` and `ensure_ascii`, for every value whose integers fit jiter's
4300-byte limit, whose objects repeat no key, and whose height is at most 200
(jiter's nesting limit). Each condition is necessary: upstream rejects longer
integer literals and deeper nesting, and `from_json` returns a `dict`, which
keeps one value per key. NaN and the infinities round-trip (`to_json` writes `NaN`,
`from_json` reads it). -/
theorem from_json_to_json (j : Json) (indent : Option Nat := none) (ensure_ascii : Bool := false)
    (hint : IntsFit j) (hkeys : KeysUnique j) (hdepth : j.height ≤ 200) :
    (from_json (to_json j indent ensure_ascii).val).map (·.val) = .ok j :=
  parse_val ((to_json j indent ensure_ascii).property.roundTripDefault (Or.inl rfl) hint hkeys hdepth)

/-- **The strict round trip**: `from_json (to_json j) (allow_inf_nan := false) = j`
under every `inf_nan_mode`, when `j` has no NaN or infinity (then the output is
RFC 8259 JSON). -/
theorem from_json_to_json_strict (j : Json) (indent : Option Nat := none) (ensure_ascii : Bool := false)
    (inf_nan_mode : InfNanMode := .constants)
    (hint : IntsFit j) (hkeys : KeysUnique j) (hdepth : j.height ≤ 200) (hfin : j.allFinite = true) :
    (from_json (to_json j indent ensure_ascii inf_nan_mode).val (allow_inf_nan := false)).map (·.val)
      = .ok j :=
  parse_val ((to_json j indent ensure_ascii inf_nan_mode).property.roundTripStrict hint hkeys hdepth hfin)

/-- **`to_json` is injective**, under every `indent` and `ensure_ascii` (and the
default `inf_nan_mode`; `null` and `strings` modes print `NaN` as `null` or
`"NaN"`). -/
theorem to_json_injective (indent : Option Nat := none) (ensure_ascii : Bool := false) :
    Function.Injective (fun j : Json => (to_json j indent ensure_ascii).val) := by
  intro a b hab
  have ha := (to_json a indent ensure_ascii).property.bytes
  have hb := (to_json b indent ensure_ascii).property.bytes
  simp only at hab
  rw [hab] at ha
  exact print_injective _ rfl (ha.symm.trans hb)

/-- **`to_json` is injective on finite values** under every `indent`,
`ensure_ascii` and `inf_nan_mode`. -/
theorem to_json_injective_finite (indent : Option Nat := none) (ensure_ascii : Bool := false)
    (inf_nan_mode : InfNanMode := .constants) {a b : Json} (ha : a.allFinite = true)
    (hb : b.allFinite = true)
    (hab : (to_json a indent ensure_ascii inf_nan_mode).val = (to_json b indent ensure_ascii inf_nan_mode).val) :
    a = b := by
  have ea := (to_json a indent ensure_ascii inf_nan_mode).property.bytes
  have eb := (to_json b indent ensure_ascii inf_nan_mode).property.bytes
  rw [hab] at ea
  exact print_injective_finite _ ha hb (ea.symm.trans eb)

/-- `to_json`, Lean-cased. -/
abbrev toJson {α : Type} [IntoJson α] (value : α) (indent : Option Nat := none)
    (ensure_ascii : Bool := false) (inf_nan_mode : InfNanMode := .constants) :=
  to_json value indent ensure_ascii inf_nan_mode

/-- The printed form as a `String` (the bytes are always valid UTF-8). -/
def printStr (v : Json) (o : PrintOpts := {}) : String :=
  (String.fromUTF8? (print v o).val).getD ""

/-- Python's `json.dumps(obj, indent=None, ensure_ascii=True)`: `", "` and
`": "` separators on one line, `","` and `": "` with `indent`, non-ASCII
escaped by default. (`to_json` is the compact pydantic-core form.) -/
def dumps {α : Type} [IntoJson α] (obj : α) (indent : Option Nat := none) (ensure_ascii : Bool := true) :
    String :=
  printStr (intoJson obj) { indent, ensureAscii := ensure_ascii, spaced := true }

end LeanJson
