import LeanJson.Proofs.Compact

/-!
# The harness: one `Verified<Layer>` structure per layer

`VerifiedJson` bundles the codec's implementation with a proof term for every
property `Specifications/Json.lean` states. A specification with no proof is
a compile error the moment it needs a field here, so this file is an honest
map of what is verified.
-/

namespace LeanJson

open Spec

/-- The JSON layer: the reference parser and printer, and a proof of every
headline specification. -/
structure VerifiedJson where
  parse : ParseCfg → ValueParser := parseValueAt
  print : Printer := printWith
  /-- Round trip on any continuation, any options, any depth (lossless parser). -/
  parsePrintExt : ParsePrintExt (parse .lossless) print
  /-- Strings, both escape modes, `\uXXXX` and surrogate pairs. -/
  stringExt : StringExt parseString printString
  /-- Numbers: integers of any size, floats with mantissa, exponent and sign of zero. -/
  numberExt : NumberExt (parseNumber .lossless) printNumber
  /-- The printer is injective under every option set. -/
  printInjective : PrintInjective print
  /-- …and on finite values under every option, every NaN/infinity mode included. -/
  printInjectiveFinite : PrintInjectiveFinite print
  /-- Every production consumes a byte and stays in bounds. -/
  stepProgress : ∀ cfg, StepProgress (parse cfg)
  /-- Compact output has no layout whitespace. -/
  compact : Compact printBytes
  /-- `parse (print j) = .ok j`, for every value within the default limits:
  integers within 4300 bytes, no repeated key, height at most 200. -/
  parsePrint : ∀ (j : Json) (o : PrintOpts), ReadsBack o j → IntsFit j → KeysUnique j → j.height ≤ 200 →
    parseDocument (print o 0 j).toByteArray = .ok j
  /-- Strict mode reads back every finite value. -/
  parsePrintStrict : ∀ (j : Json) (o : PrintOpts), IntsFit j → KeysUnique j → j.height ≤ 200 →
    j.allFinite = true →
    parseDocumentWith .strict (print o 0 j).toByteArray = .ok j
  /-- Strict mode never returns a NaN or infinity. -/
  strictFinite : ∀ (bs : ByteArray) (v : Json), parseDocumentWith .strict bs = .ok v → v.allFinite = true
  /-- The default parser never returns a value deeper than its limit. -/
  depthBound : ∀ (bs : ByteArray) (v : Json), parseDocument bs = .ok v → v.height ≤ 200

/-- The JSON layer, verified. -/
def theVerifiedJson : VerifiedJson where
  parsePrintExt := parse_print_ext
  stringExt := string_ext
  numberExt := number_ext
  printInjective := print_injective_spec
  printInjectiveFinite o _ _ hv hw h := print_injective_finite o hv hw h
  stepProgress := step_progress
  compact := print_compact_spec
  parsePrint j o hrb hi hk hd := parse_print j o (fits_default hi hk hd) hrb
  parsePrintStrict j o hi hk hd hf :=
    parseDocumentWith_print .strict o j (fits_strict hi hk hd hf) (Or.inr hf)
  strictFinite _ _ h := parse_finite rfl h
  depthBound _ _ h := parseDocument_height h

end LeanJson
