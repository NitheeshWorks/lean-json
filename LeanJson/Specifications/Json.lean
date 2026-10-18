import LeanJson.RepoImpl.Access

/-!
# Specifications: what the codec must satisfy

Stated in `Prop`, over the implementation's signatures, with no proof
attached. `Proofs/` proves each one of the reference implementation and
`Proofs/Verified.lean` bundles them.

Every decoder property is an `_ext` property: it holds on *any* buffer whose
bytes from the cursor on are the printed form followed by an arbitrary
continuation, and it reports the final cursor, so the lemmas compose one
field after another.
-/

namespace LeanJson.Spec

/-- From `pos` on, `bs` holds `l` and then `rest`. -/
def At (bs : ByteArray) (pos : Nat) (l rest : List UInt8) : Prop :=
  bs.data.toList.drop pos = l ++ rest

/-- `rest` cannot continue a number literal: it is empty or starts with a byte
that is not a digit, `.`, `e` or `E`. (After a value inside a container the
next byte is `,` `]` `}` or whitespace, which qualify.) -/
def NumStop (rest : List UInt8) : Prop :=
  ∀ b, rest.head? = some b → isDigit b = false ∧ b ≠ 46 ∧ b ≠ 101 ∧ b ≠ 69

mutual
/-- Every number in `v` is within `cfg`'s limits (always true for
`ParseCfg.lossless`). -/
def Fits (cfg : ParseCfg) : Json → Prop
  | .num n => cfg.intLenOk n.intLen = true
  | .arr xs => FitsList cfg xs
  | .obj kvs => FitsFields cfg kvs
  | _ => True
def FitsList (cfg : ParseCfg) : List Json → Prop
  | [] => True
  | x :: xs => Fits cfg x ∧ FitsList cfg xs
def FitsFields (cfg : ParseCfg) : List (String × Json) → Prop
  | [] => True
  | (_, v) :: kvs => Fits cfg v ∧ FitsFields cfg kvs
end

/-- The signature of a value parser: buffer, cursor, fuel. -/
abbrev ValueParser := ByteArray → Nat → Nat → Except ParseErr (Json × Nat)

/-- The signature of a printer: options, depth, value. -/
abbrev Printer := PrintOpts → Nat → Json → List UInt8

/-- **Round trip on any continuation.** Whatever the options and depth, the
printed form of `v`, followed by anything that cannot extend a number,
parses back to `v` with the cursor just past it, given more fuel than
printed bytes. -/
def ParsePrintExt (parse : ValueParser) (print : Printer) : Prop :=
  ∀ (o : PrintOpts) (d : Nat) (v : Json) (bs : ByteArray) (pos : Nat) (rest : List UInt8)
    (fuel : Nat),
    At bs pos (print o d v) rest → NumStop rest → (print o d v).length < fuel →
    parse bs pos fuel = .ok (v, pos + (print o d v).length)

/-- String literals round-trip on any continuation, in both escape modes
(raw UTF-8 and `ensure_ascii`, including `\uXXXX` surrogate pairs). -/
def StringExt (parse : ByteArray → Nat → Except ParseErr (String × Nat))
    (print : Bool → String → List UInt8) : Prop :=
  ∀ (ascii : Bool) (s : String) (bs : ByteArray) (pos : Nat) (rest : List UInt8),
    At bs pos (print ascii s) rest → parse bs pos = .ok (s, pos + (print ascii s).length)

/-- Numbers round-trip on any continuation that cannot extend them: integers
of any size, and floats (mantissa and exponent, sign of zero included). -/
def NumberExt (parse : ByteArray → Nat → Except ParseErr (Number × Nat))
    (print : Number → List UInt8) : Prop :=
  ∀ (n : Number) (bs : ByteArray) (pos : Nat) (rest : List UInt8),
    At bs pos (print n) rest → NumStop rest → parse bs pos = .ok (n, pos + (print n).length)

/-- The printer is injective, for every choice of options. -/
def PrintInjective (print : Printer) : Prop :=
  ∀ (o : PrintOpts) (v w : Json), print o 0 v = print o 0 w → v = w

/-- More fuel never changes a result that was not a fuel failure. -/
def FuelMono (parse : ValueParser) : Prop :=
  ∀ (bs : ByteArray) (pos n m : Nat), n ≤ m →
    (∀ e, parse bs pos n = .error e → e.kind ≠ .recursionLimitExceeded) →
    parse bs pos m = parse bs pos n

/-- `2 * (size - pos) + 1` fuel is always enough: the parser never fails for
lack of fuel at that budget. -/
def FuelEnough (parse : ValueParser) : Prop :=
  ∀ (bs : ByteArray) (pos : Nat) (e : ParseErr),
    parse bs pos (2 * (bs.size - pos) + 1) = .error e → e.kind ≠ .recursionLimitExceeded

/-- Every successful parse consumes at least one byte and stays in bounds. -/
def StepProgress (parse : ValueParser) : Prop :=
  ∀ (bs : ByteArray) (pos fuel : Nat) (v : Json) (p : Nat),
    parse bs pos fuel = .ok (v, p) → pos < p ∧ p ≤ bs.size

mutual
/-- Whether a string occurring in `v` (a value or a key) contains a space. -/
def HasSpaceInString : Json → Prop
  | .str s => ' ' ∈ s.toList
  | .arr xs => HasSpaceInList xs
  | .obj kvs => HasSpaceInFields kvs
  | _ => False
def HasSpaceInList : List Json → Prop
  | [] => False
  | x :: xs => HasSpaceInString x ∨ HasSpaceInList xs
def HasSpaceInFields : List (String × Json) → Prop
  | [] => False
  | (k, v) :: kvs => ' ' ∈ k.toList ∨ HasSpaceInString v ∨ HasSpaceInFields kvs
end

/-- **Compact output.** The default printing contains no tab, line feed or
carriage return byte at all (inside strings they are escaped), and a space
byte only when some string in the value contains a space. Separators are
therefore exactly `,` and `:`. -/
def Compact (print : Json → List UInt8) : Prop :=
  ∀ v : Json, (9 : UInt8) ∉ print v ∧ (10 : UInt8) ∉ print v ∧ (13 : UInt8) ∉ print v ∧
    ((32 : UInt8) ∈ print v → HasSpaceInString v)

/-- What a successful document parse of `bs` guarantees about its result `v`.
It is the postcondition `LeanJson.from_json` returns. -/
structure Parsed (bs : ByteArray) (v : Json) : Prop where
  /-- `v` is the reference parser's answer. -/
  ref : parseDocument bs = .ok v
  /-- Printed again, under any options, `v` reads back as itself. -/
  reprint : ∀ o : PrintOpts, parseDocumentWith .lossless (printWith o 0 v).toByteArray = .ok v
  /-- If the input is the printing of some value `w` (any options), then `w`
  is what was read: canonical input re-prints to exactly the input. -/
  canonical : ∀ (o : PrintOpts) (w : Json), printWith o 0 w = bs.data.toList → w = v

/-- What a successful prefix parse of `bs` from `pos` guarantees about its
result `r = (value, end position)`. -/
structure ParsedAt (bs : ByteArray) (pos : Nat) (r : Json × Nat) : Prop where
  /-- `r` is the reference parser's answer at the API's fuel budget. -/
  ref : parseValue bs pos (fuelFor bs pos) = .ok r
  /-- At least one byte was consumed, and no byte past the end. -/
  bounds : pos < r.2 ∧ r.2 ≤ bs.size
  /-- If the bytes from `pos` are the printing of some `w` (any options and
  depth) followed by a continuation that cannot extend a number, the result
  is `w` and the end position is just past its printing. -/
  canonical : ∀ (o : PrintOpts) (d : Nat) (w : Json) (rest : List UInt8),
    At bs pos (printWith o d w) rest → NumStop rest → r = (w, pos + (printWith o d w).length)

/-- What `LeanJson.to_json` guarantees about its output `b` for `v` under `o`. -/
structure Printed (o : PrintOpts) (v : Json) (b : ByteArray) : Prop where
  /-- `b` is exactly the printed bytes. -/
  bytes : b.data.toList = printWith o 0 v
  /-- The lossless parser reads `b` back as `v`. -/
  roundTrip : parseDocumentWith .lossless b = .ok v
  /-- So does the default (`from_json`) parser, when every integer in `v` is
  within its 4300-byte limit. -/
  roundTripDefault : Fits {} v → parseDocument b = .ok v
  /-- Compact options give no layout whitespace: no tab, LF or CR byte, and a
  space only inside a string that has one. -/
  compact : o.indent = none → (9 : UInt8) ∉ b.data.toList ∧ (10 : UInt8) ∉ b.data.toList ∧
    (13 : UInt8) ∉ b.data.toList ∧ ((32 : UInt8) ∈ b.data.toList → HasSpaceInString v)

end LeanJson.Spec
