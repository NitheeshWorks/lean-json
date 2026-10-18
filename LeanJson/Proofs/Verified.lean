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
  parse : ParseCfg → ValueParser := parseValueWith
  print : Printer := printWith
  /-- Round trip on any continuation, any options, any depth (lossless parser). -/
  parsePrintExt : ParsePrintExt (parse .lossless) print
  /-- Strings, both escape modes, `\uXXXX` and surrogate pairs. -/
  stringExt : StringExt parseString printString
  /-- Numbers: integers of any size, floats with mantissa, exponent and sign of zero. -/
  numberExt : NumberExt (parseNumber .lossless) printNumber
  /-- The printer is injective under every option set. -/
  printInjective : PrintInjective print
  /-- More fuel never changes a non-fuel answer, under every configuration. -/
  fuelMono : ∀ cfg, FuelMono (parse cfg)
  /-- The entry points' fuel budget never runs out. -/
  fuelEnough : ∀ cfg, FuelEnough (parse cfg)
  /-- Every production consumes a byte and stays in bounds. -/
  stepProgress : ∀ cfg, StepProgress (parse cfg)
  /-- Compact output has no layout whitespace. -/
  compact : Compact printBytes
  /-- `parse (print j) = .ok j`, for every value within the default limits. -/
  parsePrint : ∀ (j : Json) (o : PrintOpts), Fits {} j →
    parseDocument (print o 0 j).toByteArray = .ok j

/-- The JSON layer, verified. -/
def theVerifiedJson : VerifiedJson where
  parsePrintExt := parse_print_ext
  stringExt := string_ext
  numberExt := number_ext
  printInjective := print_injective_spec
  fuelMono := parse_fuel_mono
  fuelEnough := parse_fuel_enough
  stepProgress := step_progress
  compact := print_compact_spec
  parsePrint j o h := parse_print j o h

end LeanJson
