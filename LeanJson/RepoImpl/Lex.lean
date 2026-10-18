import LeanJson.RepoImpl.Print

/-!
# RepoImpl: the lexical productions

Whitespace, literals, numbers and escapes, over a `ByteArray` with a `Nat`
cursor. The scanners recurse on the remaining input (`termination_by
bs.size - pos`); nothing takes fuel.

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
def skipWs (bs : ByteArray) (pos : Nat) : Nat :=
  if h : pos < bs.size then
    if isWs bs[pos] then skipWs bs (pos + 1) else pos
  else pos
termination_by bs.size - pos

/-- Match a fixed literal (`rue`, `ull`, ...) at `pos`; the position after
it. A mismatching byte is `expected ident` (jiter), end of input is `EOF
while parsing a value`. -/
def expectLit (bs : ByteArray) : (pos : Nat) → List UInt8 → Except ParseErr Nat
  | pos, [] => .ok pos
  | pos, c :: cs =>
    match bs[pos]? with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some b => if b == c then expectLit bs (pos + 1) cs else .error ⟨.expectedSomeIdent, pos⟩

/-- Count a run of decimal digits from `pos`: (count, position after). -/
def scanDigits (bs : ByteArray) (pos cnt : Nat) : Nat × Nat :=
  if h : pos < bs.size then
    if isDigit bs[pos] then scanDigits bs (pos + 1) (cnt + 1) else (cnt, pos)
  else (cnt, pos)
termination_by bs.size - pos

/-- The digit at byte `i` (`0` past the end). -/
def digitAt (bs : ByteArray) (i : Nat) : Nat := (bs[i]?.getD 48).toNat - 48

/-- The value of `len` digits from `start`, left to right. -/
def smallValue (bs : ByteArray) : (start len acc : Nat) → Nat
  | _, 0, acc => acc
  | start, k + 1, acc => smallValue bs (start + 1) k (acc * 10 + digitAt bs start)

/-- The value of the `len` digits from `start`, by divide and conquer, so a
long digit run costs a few big multiplications rather than one per digit. -/
def digitsValue (bs : ByteArray) (start len : Nat) : Nat :=
  if len ≤ 16 then smallValue bs start len 0
  else
    let h := len / 2
    digitsValue bs start h * 10 ^ (len - h) + digitsValue bs (start + h) (len - h)
termination_by len

/-- At least one digit at `pos`: (value, count, position after), else an error
(end of input: `EOF while parsing a value`; anything else: `invalid number`). -/
def digits1 (bs : ByteArray) (pos : Nat) : Except ParseErr (Nat × Nat × Nat) :=
  let r := scanDigits bs pos 0
  if r.1 = 0 then
    match bs[pos]? with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some _ => .error ⟨.invalidNumber, pos⟩
  else .ok (digitsValue bs pos r.1, r.1, r.2)

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
      let r := scanDigits bs pos 0
      .ok (digitsValue bs pos r.1, r.2)
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

/-- Parser configuration. `maxIntLen` is jiter's limit on the length of a
number's sign and integer digits (4300, Python's `int` digit limit); a longer
literal is `number out of range`. `none` lifts the limit (the lossless
parser the round-trip theorems are stated for). -/
structure ParseCfg where
  maxIntLen : Option Nat := some 4300
  /-- jiter's nesting limit: a value may sit inside at most `maxDepth - 1`
  containers (201 means 201 nested containers parse, provided the innermost
  is empty; a value inside 201 containers is `recursion limit exceeded`).
  `none` lifts it: then the parser's stack use grows with the input's
  nesting, so it is not for untrusted input. -/
  maxDepth : Option Nat := some 201
  /-- Read `NaN`, `Infinity` and `-Infinity` (pydantic-core's
  `allow_inf_nan`, `true` in `from_json`); `false` is strict RFC 8259. -/
  allowInfNan : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- The configuration with no limits. Not for untrusted input: without a depth
limit, deeply nested input can exhaust the stack. -/
def ParseCfg.lossless : ParseCfg := { maxIntLen := none, maxDepth := none, allowInfNan := true }

/-- Strict RFC 8259 numbers: no `NaN` or infinities, default limits. -/
def ParseCfg.strict : ParseCfg := { allowInfNan := false }

/-- Whether a value may be parsed inside `d` containers. -/
def ParseCfg.depthOk (cfg : ParseCfg) (d : Nat) : Bool :=
  match cfg.maxDepth with
  | none => true
  | some L => d < L

/-- Whether an integer part spanning `n` bytes (sign included) is allowed. -/
def ParseCfg.intLenOk (cfg : ParseCfg) (n : Nat) : Bool :=
  match cfg.maxIntLen with
  | none => true
  | some L => n ≤ L

/-- The digits of a number from `p0` (just past its sign, if any), the number
having started at `pos`. -/
def parseNumberBody (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) (neg : Bool) (p0 : Nat) :
    Except ParseErr (Number × Nat) := do
  let (iv, p1) ← parseIntPart bs p0
  if cfg.intLenOk (p1 - pos) = false then
    .error ⟨.numberOutOfRange, pos + cfg.maxIntLen.getD 0 + 1⟩
  else
    let (fv, fc, p2) ← parseFrac bs p1
    let (he, ev, p3) ← parseExp bs p2
    .ok (mkNumber neg iv fv fc he ev, p3)

/-- A number at `pos` (which holds `-` or a digit). With `allowInfNan`,
`-Infinity` too. -/
def parseNumber (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Except ParseErr (Number × Nat) :=
  if bs[pos]? == some 45 then
    if cfg.allowInfNan && bs[pos + 1]? == some 73 then
      (expectLit bs (pos + 2) [110, 102, 105, 110, 105, 116, 121]).map (fun p => (.negInf, p))
    else parseNumberBody cfg bs pos true (pos + 1)
  else parseNumberBody cfg bs pos false pos

/-- One hex digit at `i`. -/
def hexAt (bs : ByteArray) (i : Nat) : Except ParseErr Nat :=
  match bs[i]? with
  | none => .error ⟨.eofWhileParsingString, i⟩
  | some b =>
    match hexVal b with
    | some v => .ok v
    | none => .error ⟨.invalidEscape, i⟩

/-- Four hex digits at `pos`. Fewer than four bytes left is `EOF while
parsing a string` at the end of input, as jiter reports it. -/
def parseHex4 (bs : ByteArray) (pos : Nat) : Except ParseErr Nat :=
  if bs.size < pos + 4 then .error ⟨.eofWhileParsingString, bs.size⟩ else
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
      if 0xDC00 ≤ u ∧ u < 0xE000 then .error ⟨.loneLeadingSurrogateInHexEscape, pos + 4⟩
      else if 0xD800 ≤ u ∧ u < 0xDC00 then
        match bs[pos + 5]? with
        | none => .error ⟨.eofWhileParsingString, pos + 5⟩
        | some 92 =>
          match bs[pos + 6]? with
          | none => .error ⟨.eofWhileParsingString, pos + 6⟩
          | some 117 => do
            let l ← parseHex4 bs (pos + 7)
            if 0xDC00 ≤ l ∧ l < 0xE000 then
              .ok (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)), pos + 11)
            else .error ⟨.loneLeadingSurrogateInHexEscape, pos + 10⟩
          | some _ => .error ⟨.unexpectedEndOfHexEscape, pos + 6⟩
        | some _ => .error ⟨.unexpectedEndOfHexEscape, pos + 5⟩
      else .ok (Char.ofNat u, pos + 5)
    else .error ⟨.invalidEscape, pos⟩

/-- An escape always ends after the byte it starts at. -/
theorem parseEscape_next {bs : ByteArray} {q : Nat} {r : Char × Nat} (h : parseEscape bs q = .ok r) :
    q < r.2 := by
  unfold parseEscape at h
  split at h
  · cases h
  · rename_i b _
    by_cases c34 : (b == 34) = true
    · rw [ite_eq_left c34] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c34] at h
    by_cases c92 : (b == 92) = true
    · rw [ite_eq_left c92] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c92] at h
    by_cases c47 : (b == 47) = true
    · rw [ite_eq_left c47] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c47] at h
    by_cases c98 : (b == 98) = true
    · rw [ite_eq_left c98] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c98] at h
    by_cases c102 : (b == 102) = true
    · rw [ite_eq_left c102] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c102] at h
    by_cases c110 : (b == 110) = true
    · rw [ite_eq_left c110] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c110] at h
    by_cases c114 : (b == 114) = true
    · rw [ite_eq_left c114] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c114] at h
    by_cases c116 : (b == 116) = true
    · rw [ite_eq_left c116] at h; cases h; exact Nat.lt_succ_self _
    rw [ite_eq_right c116] at h
    by_cases c117 : (b == 117) = true
    · rw [ite_eq_left c117] at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i u _
        by_cases d1 : 56320 ≤ u ∧ u < 57344
        · rw [ite_eq_left d1] at h; cases h
        rw [ite_eq_right d1] at h
        by_cases d2 : 55296 ≤ u ∧ u < 56320
        · rw [ite_eq_left d2] at h
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · have hr := (Except.ok.inj h).symm
                  rw [hr]; simp
                · cases h
            · cases h
          · cases h
        · rw [ite_eq_right d2] at h; cases h; simp
    · rw [ite_eq_right c117] at h; cases h

end LeanJson
