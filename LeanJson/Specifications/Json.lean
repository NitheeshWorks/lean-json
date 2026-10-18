import LeanJson.RepoImpl.Access
import LeanJson.RepoImpl.Partial

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
/-- `v`, sitting inside `d` containers, is within `cfg`'s limits: every
number's integer part fits `maxIntLen`, every value (scalar or container)
sits inside fewer than `maxDepth` containers, and, when `cfg` collapses
repeated keys, no object repeats a key. Always true for `ParseCfg.lossless`. -/
def FitsAt (cfg : ParseCfg) (d : Nat) : Json → Prop
  | .num n => cfg.depthOk d = true ∧ cfg.intLenOk n.intLen = true ∧
      (cfg.allowInfNan = true ∨ n.isFinite = true)
  | .arr ⟨xs⟩ => cfg.depthOk d = true ∧ FitsList cfg (d + 1) xs
  | .obj ⟨kvs⟩ => cfg.depthOk d = true ∧ (cfg.dedupKeys = true → (kvs.map Prod.fst).Nodup) ∧
      FitsFields cfg (d + 1) kvs
  | _ => cfg.depthOk d = true
def FitsList (cfg : ParseCfg) (d : Nat) : List Json → Prop
  | [] => True
  | x :: xs => FitsAt cfg d x ∧ FitsList cfg d xs
def FitsFields (cfg : ParseCfg) (d : Nat) : List (String × Json) → Prop
  | [] => True
  | (_, v) :: kvs => FitsAt cfg d v ∧ FitsFields cfg d kvs
end

/-- A top-level value within `cfg`'s limits. -/
def Fits (cfg : ParseCfg) (v : Json) : Prop := FitsAt cfg 0 v

/-- Every integer in `j` is within jiter's 4300-byte limit (depth aside). -/
def IntsFit (j : Json) : Prop := Fits { maxDepth := none, dedupKeys := false } j

/-- No object in `j` repeats a key, so collapsing repeated keys (as
`from_json` does) leaves `j` unchanged. -/
def KeysUnique (j : Json) : Prop := Fits { ParseCfg.lossless with dedupKeys := true } j

/-- The printing of `v` under `o` can be read back as `v`: either NaN and the
infinities print as constants (`o.infNan = .constants`, the default), or `v`
has none. Under `null` or `strings` mode a non-finite number prints as
`null` or a string, which reads back as that instead. -/
def ReadsBack (o : PrintOpts) (v : Json) : Prop := o.infNan = .constants ∨ v.allFinite = true

/-- The signature of a value parser: buffer and cursor in; value and end
position out. -/
abbrev ValueParser := ByteArray → Nat → Except ParseErr (Json × Nat)

/-- The signature of a printer: options, depth, value. -/
abbrev Printer := PrintOpts → Nat → Json → List UInt8

/-- **Round trip on any continuation.** Whatever the options and depth, the
printed form of `v`, followed by anything that cannot extend a number,
parses back to `v` with the cursor just past it. -/
def ParsePrintExt (parse : ValueParser) (print : Printer) : Prop :=
  ∀ (o : PrintOpts) (d : Nat) (v : Json) (bs : ByteArray) (pos : Nat) (rest : List UInt8),
    ReadsBack o v → At bs pos (print o d v) rest → NumStop rest →
    parse bs pos = .ok (v, pos + (print o d v).length)

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
  ∀ (n : Number) (bs : ByteArray) (pos : Nat) (rest : List UInt8), n ≠ .nan → n ≠ .inf →
    At bs pos (print n) rest → NumStop rest → parse bs pos = .ok (n, pos + (print n).length)

/-- The printer is injective, for every choice of options. -/
def PrintInjective (print : Printer) : Prop :=
  ∀ (o : PrintOpts) (v w : Json), o.infNan = .constants → print o 0 v = print o 0 w → v = w

/-- The printer is injective on finite values, for every choice of options
(every NaN/infinity mode). -/
def PrintInjectiveFinite (print : Printer) : Prop :=
  ∀ (o : PrintOpts) (v w : Json), v.allFinite = true → w.allFinite = true →
    print o 0 v = print o 0 w → v = w

/-- Every successful parse consumes at least one byte and stays in bounds. -/
def StepProgress (parse : ValueParser) : Prop :=
  ∀ (bs : ByteArray) (pos : Nat) (v : Json) (p : Nat),
    parse bs pos = .ok (v, p) → pos < p ∧ p ≤ bs.size

mutual
/-- Whether a string occurring in `v` (a value or a key) contains a space. -/
def HasSpaceInString : Json → Prop
  | .str s => ' ' ∈ s.toList
  | .arr ⟨xs⟩ => HasSpaceInList xs
  | .obj ⟨kvs⟩ => HasSpaceInFields kvs
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

/-- What a successful document parse of `bs` under `cfg` guarantees about its
result `v`. It is the postcondition `LeanJson.from_json` returns. -/
structure ParsedWith (cfg : ParseCfg) (bs : ByteArray) (v : Json) : Prop where
  /-- `v` is the reference parser's answer. -/
  ref : parseDocumentWith cfg bs = .ok v
  /-- Printed again, under any options that read back, `v` reads back as itself. -/
  reprint : ∀ o : PrintOpts, ReadsBack o v →
    parseDocumentWith .lossless (printWith o 0 v).toByteArray = .ok v
  /-- If the input is the printing of some value `w` (under options that read
  back, and with no repeated key if `cfg` collapses them), then `w` is what
  was read: canonical input re-prints to exactly the input. -/
  canonical : ∀ (o : PrintOpts) (w : Json), ReadsBack o w → (cfg.dedupKeys = true → KeysUnique w) →
    printWith o 0 w = bs.data.toList → w = v
  /-- Nothing nested deeper than the configured limit is returned. -/
  height : ∀ L, cfg.maxDepth = some L → v.height < L
  /-- In strict mode, no `NaN` or infinity is returned. -/
  finite : cfg.allowInfNan = false → v.allFinite = true

/-- What a successful parse of partial input guarantees about its result
`v` (`from_json(data, allow_partial=...)`). -/
structure ParsedPartial (cfg : ParseCfg) (mode : PartialMode) (bs : ByteArray) (v : Json) : Prop where
  /-- `v` is the partial parser's answer. -/
  ref : parsePartialWith cfg mode bs = .ok v
  /-- On a complete document, partial mode changes nothing. -/
  complete : ∀ w, parseDocumentWith cfg bs = .ok w → v = w

/-- The postcondition of `from_json` under `allow_partial := mode`. -/
abbrev FromJson (cfg : ParseCfg) (mode : PartialMode) (bs : ByteArray) (v : Json) : Prop :=
  match mode with
  | .off => ParsedWith cfg bs v
  | m => ParsedPartial cfg m bs v

/-- `ParsedWith` at `from_json`'s defaults. -/
abbrev Parsed (bs : ByteArray) (v : Json) : Prop := ParsedWith {} bs v

/-- What a successful prefix parse of `bs` from `pos` guarantees about its
result `r = (value, end position)`. -/
structure ParsedAt (bs : ByteArray) (pos : Nat) (r : Json × Nat) : Prop where
  /-- `r` is the reference parser's answer. -/
  ref : parseValue bs pos = .ok r
  /-- At least one byte was consumed, and no byte past the end. -/
  bounds : pos < r.2 ∧ r.2 ≤ bs.size
  /-- If the bytes from `pos` are the printing of some `w` with no repeated key
  (any options and depth) followed by a continuation that cannot extend a
  number, the result is `w` and the end position is just past its printing. -/
  canonical : ∀ (o : PrintOpts) (d : Nat) (w : Json) (rest : List UInt8), ReadsBack o w → KeysUnique w →
    At bs pos (printWith o d w) rest → NumStop rest → r = (w, pos + (printWith o d w).length)

/-- What `LeanJson.to_json` guarantees about its output `b` for `v` under `o`. -/
structure Printed (o : PrintOpts) (v : Json) (b : ByteArray) : Prop where
  /-- `b` is exactly the printed bytes. -/
  bytes : b.data.toList = printWith o 0 v
  /-- The lossless parser reads `b` back as `v`. -/
  roundTrip : ReadsBack o v → parseDocumentWith .lossless b = .ok v
  /-- So does the default (`from_json`) parser, when every integer in `v` is
  within its 4300-byte limit, no object repeats a key (`from_json` collapses
  them), and `v` is nested no deeper than its 201-level limit allows. -/
  roundTripDefault : ReadsBack o v → IntsFit v → KeysUnique v → v.height ≤ 200 →
    parseDocument b = .ok v
  /-- And the strict (`allow_inf_nan=False`) parser, when moreover `v` has no
  `NaN` or infinity: `b` is then RFC 8259 JSON. -/
  roundTripStrict : IntsFit v → KeysUnique v → v.height ≤ 200 → v.allFinite = true →
    parseDocumentWith .strict b = .ok v
  /-- Compact options give no layout whitespace: no tab, LF or CR byte, and a
  space only inside a string that has one. -/
  compact : o.indent = none → o.spaced = false → (9 : UInt8) ∉ b.data.toList ∧ (10 : UInt8) ∉ b.data.toList ∧
    (13 : UInt8) ∉ b.data.toList ∧ ((32 : UInt8) ∈ b.data.toList → HasSpaceInString v)

end LeanJson.Spec
