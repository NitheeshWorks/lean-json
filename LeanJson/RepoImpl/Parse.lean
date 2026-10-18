import LeanJson.RepoImpl.Print

/-!
# RepoImpl: the parser

A total RFC 8259 parser over a `ByteArray` with a `Nat` cursor. Every
function recurses structurally on a fuel argument. The scanners (whitespace,
digits, string bodies) take fuel `bs.size`, which is always enough because
each step consumes a byte; the value parser takes the caller's fuel, and
the public entry points pass `bs.size + 1`, which is enough for every input
(`step_progress`, `parse_fuel_enough` in `Proofs/`).

Behaviour follows jiter, pydantic-core's parser: whitespace is space, tab,
LF, CR; numbers follow the RFC grammar (no leading zeros, no `+`, no bare
`.`); a literal with a fraction or exponent is a float; strings reject raw
control characters and decode `\uXXXX` with surrogate pairs; duplicate keys
are kept in order. Error kinds and offsets follow jiter's `JsonErrorType`.
`NaN` and `Infinity` are rejected (see `CONTRIBUTING.md`, deviations).
-/

namespace LeanJson

/-- JSON whitespace: space, tab, line feed, carriage return. -/
def isWs (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-- The first position at or after `pos` that is not whitespace. -/
def skipWs (bs : ByteArray) : (pos fuel : Nat) → Nat
  | pos, 0 => pos
  | pos, f + 1 =>
    match bs[pos]? with
    | some b => if isWs b then skipWs bs (pos + 1) f else pos
    | none => pos

/-- Match a fixed literal (`rue`, `ull`, ...) at `pos`; the position after
it. A mismatching byte is `expected ident` (jiter), end of input is `EOF
while parsing a value`. -/
def expectLit (bs : ByteArray) : (pos : Nat) → List UInt8 → Except ParseErr Nat
  | pos, [] => .ok pos
  | pos, c :: cs =>
    match bs[pos]? with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some b => if b == c then expectLit bs (pos + 1) cs else .error ⟨.expectedSomeIdent, pos⟩

/-- Scan a run of decimal digits, accumulating their value and count. -/
def scanDigits (bs : ByteArray) : (pos fuel acc cnt : Nat) → Nat × Nat × Nat
  | pos, 0, acc, cnt => (acc, cnt, pos)
  | pos, f + 1, acc, cnt =>
    match bs[pos]? with
    | some b =>
      if isDigit b then scanDigits bs (pos + 1) f (acc * 10 + (b.toNat - 48)) (cnt + 1)
      else (acc, cnt, pos)
    | none => (acc, cnt, pos)

/-- At least one digit at `pos`, else an error (end of input: `EOF while
parsing a value`; anything else: `invalid number`). -/
def digits1 (bs : ByteArray) (pos : Nat) : Except ParseErr (Nat × Nat × Nat) :=
  let r := scanDigits bs pos bs.size 0 0
  if r.2.1 = 0 then
    match bs[pos]? with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some _ => .error ⟨.invalidNumber, pos⟩
  else .ok r

/-- The integer part: `0`, or a nonzero digit followed by digits. A leading
zero followed by a digit is `invalid number`. Returns (value, position). -/
def parseIntPart (bs : ByteArray) (pos : Nat) : Except ParseErr (Nat × Nat) :=
  match bs[pos]? with
  | none => .error ⟨.eofWhileParsingValue, pos⟩
  | some b =>
    if b == 48 then
      match bs[pos + 1]? with
      | some c => if isDigit c then .error ⟨.invalidNumber, pos + 1⟩ else .ok (0, pos + 1)
      | none => .ok (0, pos + 1)
    else if isDigit b then
      let r := scanDigits bs pos bs.size 0 0
      .ok (r.1, r.2.2)
    else .error ⟨.invalidNumber, pos⟩

/-- An optional fraction `.digits`: (value, digit count, position), count 0
when absent. -/
def parseFrac (bs : ByteArray) (pos : Nat) : Except ParseErr (Nat × Nat × Nat) :=
  match bs[pos]? with
  | some 46 => digits1 bs (pos + 1)
  | _ => .ok (0, 0, pos)

/-- An optional exponent `e[+-]digits`: (present, value, position). -/
def parseExp (bs : ByteArray) (pos : Nat) : Except ParseErr (Bool × Int × Nat) :=
  match bs[pos]? with
  | some b =>
    if b == 101 || b == 69 then
      match bs[pos + 1]? with
      | some 45 => do
        let (v, _, p) ← digits1 bs (pos + 2)
        .ok (true, -(v : Int), p)
      | some 43 => do
        let (v, _, p) ← digits1 bs (pos + 2)
        .ok (true, (v : Int), p)
      | _ => do
        let (v, _, p) ← digits1 bs (pos + 1)
        .ok (true, (v : Int), p)
    else .ok (false, 0, pos)
  | none => .ok (false, 0, pos)

/-- Assemble a number from its parts: an integer when there is neither a
fraction nor an exponent, otherwise a normalised decimal. -/
def mkNumber (neg : Bool) (iv fv fc : Nat) (hasExp : Bool) (ev : Int) : Number :=
  if fc = 0 ∧ hasExp = false then .int (if neg then -(iv : Int) else iv)
  else .float (Decimal.normalize neg (iv * 10 ^ fc + fv) (ev - fc))

/-- A number at `pos` (which holds `-` or a digit). -/
def parseNumber (bs : ByteArray) (pos : Nat) : Except ParseErr (Number × Nat) := do
  let neg := bs[pos]? == some 45
  let p0 := if neg then pos + 1 else pos
  let (iv, p1) ← parseIntPart bs p0
  let (fv, fc, p2) ← parseFrac bs p1
  let (he, ev, p3) ← parseExp bs p2
  .ok (mkNumber neg iv fv fc he ev, p3)

/-- One hex digit at `i`. -/
def hexAt (bs : ByteArray) (i : Nat) : Except ParseErr Nat :=
  match bs[i]? with
  | none => .error ⟨.eofWhileParsingString, i⟩
  | some b =>
    match hexVal b with
    | some v => .ok v
    | none => .error ⟨.invalidEscape, i⟩

/-- Four hex digits at `pos`. -/
def parseHex4 (bs : ByteArray) (pos : Nat) : Except ParseErr Nat :=
  match hexAt bs pos, hexAt bs (pos + 1), hexAt bs (pos + 2), hexAt bs (pos + 3) with
  | .ok a, .ok b, .ok c, .ok d => .ok (a * 4096 + b * 256 + c * 16 + d)
  | .error e, _, _, _ => .error e
  | .ok _, .error e, _, _ => .error e
  | .ok _, .ok _, .error e, _ => .error e
  | .ok _, .ok _, .ok _, .error e => .error e

/-- The escape sequence after a backslash at `pos - 1`: the character and the
position after the escape. -/
def parseEscape (bs : ByteArray) (pos : Nat) : Except ParseErr (Char × Nat) :=
  match bs[pos]? with
  | none => .error ⟨.eofWhileParsingString, pos⟩
  | some b =>
    if b == 34 then .ok ('"', pos + 1)
    else if b == 92 then .ok ('\\', pos + 1)
    else if b == 47 then .ok ('/', pos + 1)
    else if b == 98 then .ok (Char.ofNat 8, pos + 1)
    else if b == 102 then .ok (Char.ofNat 12, pos + 1)
    else if b == 110 then .ok ('\n', pos + 1)
    else if b == 114 then .ok ('\r', pos + 1)
    else if b == 116 then .ok ('\t', pos + 1)
    else if b == 117 then do
      let u ← parseHex4 bs (pos + 1)
      if 0xDC00 ≤ u ∧ u < 0xE000 then .error ⟨.loneLeadingSurrogateInHexEscape, pos + 1⟩
      else if 0xD800 ≤ u ∧ u < 0xDC00 then
        if bs[pos + 5]? == some 92 && bs[pos + 6]? == some 117 then do
          let l ← parseHex4 bs (pos + 7)
          if 0xDC00 ≤ l ∧ l < 0xE000 then
            .ok (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)), pos + 11)
          else .error ⟨.loneLeadingSurrogateInHexEscape, pos + 7⟩
        else .error ⟨.unexpectedEndOfHexEscape, pos + 5⟩
      else .ok (Char.ofNat u, pos + 5)
    else .error ⟨.invalidEscape, pos⟩

/-- The body of a string literal from `pos` (just after the opening quote)
to the closing quote; the characters (reversed onto `acc`) and the position
after the closing quote. -/
def parseStrBody (bs : ByteArray) : (pos fuel : Nat) → List Char → Except ParseErr (List Char × Nat)
  | pos, 0, _ => .error ⟨.eofWhileParsingString, pos⟩
  | pos, f + 1, acc =>
    match bs[pos]? with
    | none => .error ⟨.eofWhileParsingString, pos⟩
    | some b =>
      if b == 34 then .ok (acc.reverse, pos + 1)
      else if b == 92 then
        match parseEscape bs (pos + 1) with
        | .ok (c, p) => parseStrBody bs p f (c :: acc)
        | .error e => .error e
      else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
      else if b < 128 then parseStrBody bs (pos + 1) f (Char.ofNat b.toNat :: acc)
      else
        match bs.utf8DecodeChar? pos with
        | some c => parseStrBody bs (pos + c.utf8Size) f (c :: acc)
        | none => .error ⟨.invalidUnicodeCodePoint, pos⟩

/-- A string literal whose opening quote is at `pos`. -/
def parseString (bs : ByteArray) (pos : Nat) : Except ParseErr (String × Nat) :=
  match parseStrBody bs (pos + 1) bs.size [] with
  | .ok (cs, p) => .ok (String.ofList cs, p)
  | .error e => .error e

mutual
/-- A value at `pos` after optional whitespace: the value and the position
just after it. -/
def parseValue (bs : ByteArray) : (pos fuel : Nat) → Except ParseErr (Json × Nat)
  | pos, 0 => .error ⟨.recursionLimitExceeded, pos⟩
  | pos0, n + 1 =>
    let pos := skipWs bs pos0 bs.size
    match bs[pos]? with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some b =>
      if b == 34 then
        match parseString bs pos with
        | .ok (s, p) => .ok (.str s, p)
        | .error e => .error e
      else if b == 91 then
        let p := skipWs bs (pos + 1) bs.size
        match bs[p]? with
        | none => .error ⟨.eofWhileParsingList, p⟩
        | some 93 => .ok (.arr [], p + 1)
        | some _ => parseElems bs p n []
      else if b == 123 then
        let p := skipWs bs (pos + 1) bs.size
        match bs[p]? with
        | none => .error ⟨.eofWhileParsingObject, p⟩
        | some 125 => .ok (.obj [], p + 1)
        | some 34 => parseMembers bs p n []
        | some _ => .error ⟨.keyMustBeAString, p⟩
      else if b == 116 then
        match expectLit bs (pos + 1) [114, 117, 101] with
        | .ok p => .ok (.bool true, p)
        | .error e => .error e
      else if b == 102 then
        match expectLit bs (pos + 1) [97, 108, 115, 101] with
        | .ok p => .ok (.bool false, p)
        | .error e => .error e
      else if b == 110 then
        match expectLit bs (pos + 1) [117, 108, 108] with
        | .ok p => .ok (.null, p)
        | .error e => .error e
      else if b == 45 || isDigit b then
        match parseNumber bs pos with
        | .ok (x, p) => .ok (.num x, p)
        | .error e => .error e
      else .error ⟨.expectedSomeValue, pos⟩
/-- Array elements from `pos` (an element is due); `acc` holds the elements
so far, reversed. -/
def parseElems (bs : ByteArray) : (pos fuel : Nat) → List Json → Except ParseErr (Json × Nat)
  | pos, 0, _ => .error ⟨.recursionLimitExceeded, pos⟩
  | pos, n + 1, acc =>
    match parseValue bs pos n with
    | .error e => .error e
    | .ok (v, p1) =>
      let p := skipWs bs p1 bs.size
      match bs[p]? with
      | none => .error ⟨.eofWhileParsingList, p⟩
      | some 44 =>
        let q := skipWs bs (p + 1) bs.size
        if bs[q]? == some 93 then .error ⟨.trailingComma, q⟩
        else parseElems bs q n (v :: acc)
      | some 93 => .ok (.arr (v :: acc).reverse, p + 1)
      | some _ => .error ⟨.expectedListCommaOrEnd, p⟩
/-- Object members from `pos` (which holds the opening quote of a key);
`acc` holds the members so far, reversed. -/
def parseMembers (bs : ByteArray) : (pos fuel : Nat) → List (String × Json) → Except ParseErr (Json × Nat)
  | pos, 0, _ => .error ⟨.recursionLimitExceeded, pos⟩
  | pos, n + 1, acc =>
    match parseString bs pos with
    | .error e => .error e
    | .ok (k, p1) =>
      let p := skipWs bs p1 bs.size
      match bs[p]? with
      | none => .error ⟨.eofWhileParsingObject, p⟩
      | some 58 =>
        match parseValue bs (p + 1) n with
        | .error e => .error e
        | .ok (v, p2) =>
          let p3 := skipWs bs p2 bs.size
          match bs[p3]? with
          | none => .error ⟨.eofWhileParsingObject, p3⟩
          | some 44 =>
            let q := skipWs bs (p3 + 1) bs.size
            match bs[q]? with
            | none => .error ⟨.eofWhileParsingValue, q⟩
            | some 34 => parseMembers bs q n ((k, v) :: acc)
            | some 125 => .error ⟨.trailingComma, q⟩
            | some _ => .error ⟨.keyMustBeAString, q⟩
          | some 125 => .ok (.obj ((k, v) :: acc).reverse, p3 + 1)
          | some _ => .error ⟨.expectedObjectCommaOrEnd, p3⟩
      | some _ => .error ⟨.expectedColon, p⟩
end

/-- A whole document: optional whitespace, one value, optional whitespace,
end of input (else `trailing characters`). -/
def parseDocument (bs : ByteArray) : Except ParseErr Json :=
  match parseValue bs 0 (bs.size + 1) with
  | .error e => .error e
  | .ok (v, p) =>
    let q := skipWs bs p bs.size
    if q < bs.size then .error ⟨.trailingCharacters, q⟩ else .ok v

/-- jiter's line/column for a byte offset: 1-based line; column is the
1-based column of the byte at `offset`, or for an offset at or past the end,
the length of the last line. -/
def lineCol (bs : ByteArray) (offset : Nat) : Nat × Nat :=
  let rec go : (i fuel line start : Nat) → Nat × Nat
    | i, 0, line, start => (line, i - start)
    | i, f + 1, line, start =>
      match bs[i]? with
      | none => (line, i - start)
      | some b =>
        let (line, start) := if b == 10 then (line + 1, i + 1) else (line, start)
        if i = offset then (line, i + 1 - start) else go (i + 1) f line start
  go 0 (bs.size + 1) 1 0

/-- A low-level error with jiter's line and column attached. -/
def ParseErr.toJsonError (bs : ByteArray) (e : ParseErr) : JsonError :=
  let lc := lineCol bs e.offset
  { kind := e.kind, offset := e.offset, line := lc.1, column := lc.2 }

end LeanJson
