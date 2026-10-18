import LeanJson.RepoImpl.Print
import LeanJson.RepoImpl.KeyIndex

/-!
# RepoImpl: the lexical productions

Whitespace, literals, numbers and escapes, over a *view* of the input: a
byte accessor `get : Nat → Option UInt8` and its length `n`, with a `Nat`
cursor. A view is what lets one definition serve both the fast parser (the
bytes of a `ByteArray` from some offset on, `@[specialize]`d into direct
array reads) and the Keel parser the laws are stated for (a `List UInt8`).
The scanners recurse on the remaining input (`termination_by n - pos`);
nothing takes fuel.

Behaviour follows jiter, pydantic-core's parser: whitespace is space, tab,
LF, CR; numbers follow the RFC grammar (no leading zeros, no `+`, no bare
`.`); a literal with a fraction or exponent is a float; strings reject raw
control characters and decode `\uXXXX` with surrogate pairs. Error kinds and
offsets follow jiter's `JsonErrorType`. `NaN`, `Infinity` and `-Infinity` are
read when `ParseCfg.allowInfNan` holds (the default). Also here: `ParseCfg`,
and `Fields`, an object under construction with `dict` key collapsing.
-/

namespace LeanJson

/-- JSON whitespace: space, tab, line feed, carriage return. -/
@[inline] def isWs (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-- The first position at or after `pos` that is not whitespace. -/
@[specialize] def skipWs (get : Nat → Option UInt8) (n pos : Nat) : Nat :=
  if pos < n then
    match get pos with
    | some b => if isWs b then skipWs get n (pos + 1) else pos
    | none => pos
  else pos
termination_by n - pos

/-- Match a fixed literal (`rue`, `ull`, ...) at `pos`; the position after
it. A mismatching byte is `expected ident` (jiter), end of input is `EOF
while parsing a value`. -/
@[specialize] def expectLit (get : Nat → Option UInt8) : (pos : Nat) → List UInt8 → Except ParseErr Nat
  | pos, [] => .ok pos
  | pos, c :: cs =>
    match get pos with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some b => if b == c then expectLit get (pos + 1) cs else .error ⟨.expectedSomeIdent, pos⟩

/-- Count a run of decimal digits from `pos`: (count, position after). -/
@[specialize] def scanDigits (get : Nat → Option UInt8) (n pos cnt : Nat) : Nat × Nat :=
  if pos < n then
    match get pos with
    | some b => if isDigit b then scanDigits get n (pos + 1) (cnt + 1) else (cnt, pos)
    | none => (cnt, pos)
  else (cnt, pos)
termination_by n - pos

/-- The digit at byte `i` (`0` past the end). -/
@[inline] def digitAt (get : Nat → Option UInt8) (i : Nat) : Nat := ((get i).getD 48).toNat - 48

/-- The value of `len` digits from `start`, left to right. -/
@[specialize] def smallValue (get : Nat → Option UInt8) : (start len acc : Nat) → Nat
  | _, 0, acc => acc
  | start, k + 1, acc => smallValue get (start + 1) k (acc * 10 + digitAt get start)

/-- The value of the `len` digits from `start`, by divide and conquer, so a
long digit run costs a few big multiplications rather than one per digit. -/
@[specialize] def digitsValue (get : Nat → Option UInt8) (start len : Nat) : Nat :=
  if len ≤ 16 then smallValue get start len 0
  else
    let h := len / 2
    digitsValue get start h * 10 ^ (len - h) + digitsValue get (start + h) (len - h)
termination_by len

/-- At least one digit at `pos`: (value, count, position after), else an error
(end of input: `EOF while parsing a value`; anything else: `invalid number`). -/
@[inline] def digits1 (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (Nat × Nat × Nat) :=
  let r := scanDigits get n pos 0
  if r.1 = 0 then
    match get pos with
    | none => .error ⟨.eofWhileParsingValue, pos⟩
    | some _ => .error ⟨.invalidNumber, pos⟩
  else .ok (digitsValue get pos r.1, r.1, r.2)

/-- The integer part: `0`, or a nonzero digit followed by digits. A leading
zero followed by a digit is `invalid number`. Returns (value, position). -/
@[inline] def parseIntPart (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (Nat × Nat) :=
  match get pos with
  | none => .error ⟨.eofWhileParsingValue, pos⟩
  | some b =>
    if b == 48 then
      match get (pos + 1) with
      | some c => if isDigit c then .error ⟨.invalidNumber, pos + 1⟩ else .ok (0, pos + 1)
      | none => .ok (0, pos + 1)
    else if isDigit b then
      let r := scanDigits get n pos 0
      .ok (digitsValue get pos r.1, r.2)
    else .error ⟨.invalidNumber, pos⟩

/-- An optional fraction `.digits`: (value, digit count, position), count 0
when absent. -/
@[inline] def parseFrac (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (Nat × Nat × Nat) :=
  match get pos with
  | some 46 => digits1 get n (pos + 1)
  | _ => .ok (0, 0, pos)

/-- An optional exponent `e[+-]digits`: (present, value, position). -/
@[inline] def parseExp (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (Bool × Int × Nat) :=
  match get pos with
  | some b =>
    if b == 101 || b == 69 then
      match get (pos + 1) with
      | some 45 => do
        let (v, _, p) ← digits1 get n (pos + 2)
        .ok (true, -(v : Int), p)
      | some 43 => do
        let (v, _, p) ← digits1 get n (pos + 2)
        .ok (true, (v : Int), p)
      | _ => do
        let (v, _, p) ← digits1 get n (pos + 1)
        .ok (true, (v : Int), p)
    else .ok (false, 0, pos)
  | none => .ok (false, 0, pos)

/-- Assemble a number from its parts: an integer when there is neither a
fraction nor an exponent, otherwise a normalised decimal. -/
@[inline] def mkNumber (neg : Bool) (iv fv fc : Nat) (hasExp : Bool) (ev : Int) : Number :=
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
  /-- Collapse repeated object keys as a Python `dict` does (what `from_json`
  returns): the last value wins and the key keeps its first position.
  `false` keeps every member, in input order. -/
  dedupKeys : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- Whether the member at position `j` has key `a`. -/
@[inline] def Fields.isAt (acc : Array (String × Json)) (j : Nat) (a : String) : Bool :=
  if h : j < acc.size then acc[j].1 == a else false

/-- Add member `(k, v)` to an object under construction with Python `dict`
semantics: a new key is appended (and its position recorded in `idx`), an
existing key keeps its position and takes the new value. Constant time
(amortised), and `O(log n)` at worst on hostile keys (`KeyIndex`). The new
position is read before the push, so `acc` is not shared when it grows and
is extended in place. -/
@[inline] def dictInsert (acc : Array (String × Json)) (idx : KeyIndex) (k : String) (v : Json) :
    Array (String × Json) × KeyIndex :=
  match idx.find (Fields.isAt acc) k with
  | some i => (acc.setIfInBounds i (k, v), idx)
  | none =>
    let i := acc.size
    (acc.push (k, v), idx.add k i)

/-- The integers `0` to `1023` as values, built once: the parser returns these
shared objects instead of allocating a fresh value per small integer. -/
def smallInts : Array Json := Array.ofFn (n := 1024) fun k => .num (.int k)

/-- `.num n`, shared when `n` is a small non-negative integer
(`Json.ofNumber_eq`). -/
def Json.ofNumber (n : Number) : Json :=
  match n with
  | .int (.ofNat k) =>
    match smallInts[k]? with
    | some j => j
    | none => .num n
  | _ => .num n

theorem Json.ofNumber_eq (n : Number) : Json.ofNumber n = .num n := by
  unfold Json.ofNumber
  split
  · rename_i k
    split
    · rename_i j h
      simp only [smallInts, Array.getElem?_ofFn] at h
      split at h
      · cases h; rfl
      · cases h
    · rfl
  · rfl

/-- An object under construction: its members so far, and (when keys are
collapsed) where each key sits. -/
abbrev Fields := Array (String × Json) × KeyIndex

/-- The empty object under construction. -/
def Fields.empty : Fields := (#[], .empty)

/-- Add a member, collapsing a repeated key when `dedup` holds. -/
@[inline] def Fields.add (dedup : Bool) (st : Fields) (k : String) (v : Json) : Fields :=
  if dedup then dictInsert st.1 st.2 k v else (st.1.push (k, v), st.2)

/-- The configuration with no limits. Not for untrusted input: without a depth
limit, deeply nested input can exhaust the stack. -/
def ParseCfg.lossless : ParseCfg :=
  { maxIntLen := none, maxDepth := none, allowInfNan := true, dedupKeys := false }

/-- `cfg` with its limits lifted, keys collapsed as in `cfg`: a parse under
`cfg` that succeeds gives the same answer under `cfg.relax`. -/
def ParseCfg.relax (cfg : ParseCfg) : ParseCfg := { ParseCfg.lossless with dedupKeys := cfg.dedupKeys }

/-- Strict RFC 8259 numbers: no `NaN` or infinities, default limits. -/
def ParseCfg.strict : ParseCfg := { allowInfNan := false }

/-- Whether a value may be parsed inside `d` containers. -/
def ParseCfg.depthOk (cfg : ParseCfg) (d : Nat) : Bool :=
  match cfg.maxDepth with
  | none => true
  | some L => d < L

/-- Whether an integer part spanning `n` bytes (sign included) is allowed. -/
@[inline] def ParseCfg.intLenOk (cfg : ParseCfg) (n : Nat) : Bool :=
  match cfg.maxIntLen with
  | none => true
  | some L => n ≤ L

/-- The digits of a number from `p0` (just past its sign, if any), the number
having started at `pos`. -/
@[inline] def parseNumberBody (cfg : ParseCfg) (get : Nat → Option UInt8) (n pos : Nat) (neg : Bool) (p0 : Nat) :
    Except ParseErr (Number × Nat) := do
  let (iv, p1) ← parseIntPart get n p0
  if cfg.intLenOk (p1 - pos) = false then
    .error ⟨.numberOutOfRange, pos + cfg.maxIntLen.getD 0 + 1⟩
  else
    let (fv, fc, p2) ← parseFrac get n p1
    let (he, ev, p3) ← parseExp get n p2
    .ok (mkNumber neg iv fv fc he ev, p3)

/-- A number at `pos` (which holds `-` or a digit). With `allowInfNan`,
`-Infinity` too. -/
@[inline] def parseNumber (cfg : ParseCfg) (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (Number × Nat) :=
  if get pos == some 45 then
    if cfg.allowInfNan && get (pos + 1) == some 73 then
      (expectLit get (pos + 2) [110, 102, 105, 110, 105, 116, 121]).map (fun p => (.negInf, p))
    else parseNumberBody cfg get n pos true (pos + 1)
  else parseNumberBody cfg get n pos false pos

/-- One hex digit at `i`. -/
@[inline] def hexAt (get : Nat → Option UInt8) (i : Nat) : Except ParseErr Nat :=
  match get i with
  | none => .error ⟨.eofWhileParsingString, i⟩
  | some b =>
    match hexVal b with
    | some v => .ok v
    | none => .error ⟨.invalidEscape, i⟩

/-- Four hex digits at `pos`. Fewer than four bytes left is `EOF while
parsing a string` at the end of input, as jiter reports it. -/
@[specialize] def parseHex4 (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr Nat :=
  if n < pos + 4 then .error ⟨.eofWhileParsingString, n⟩ else
  match hexAt get pos, hexAt get (pos + 1), hexAt get (pos + 2), hexAt get (pos + 3) with
  | .ok a, .ok b, .ok c, .ok d => .ok (a * 4096 + b * 256 + c * 16 + d)
  | .error e, _, _, _ => .error e
  | .ok _, .error e, _, _ => .error e
  | .ok _, .ok _, .error e, _ => .error e
  | .ok _, .ok _, .ok _, .error e => .error e

/-- The escape sequence after a backslash at `pos - 1`: the character and the
position after the escape. -/
@[specialize] def parseEscape (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (Char × Nat) :=
  match get pos with
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
      let u ← parseHex4 get n (pos + 1)
      if 0xDC00 ≤ u ∧ u < 0xE000 then .error ⟨.loneLeadingSurrogateInHexEscape, pos + 4⟩
      else if 0xD800 ≤ u ∧ u < 0xDC00 then
        match get (pos + 5) with
        | none => .error ⟨.eofWhileParsingString, pos + 5⟩
        | some 92 =>
          match get (pos + 6) with
          | none => .error ⟨.eofWhileParsingString, pos + 6⟩
          | some 117 => do
            let l ← parseHex4 get n (pos + 7)
            if 0xDC00 ≤ l ∧ l < 0xE000 then
              .ok (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)), pos + 11)
            else .error ⟨.loneLeadingSurrogateInHexEscape, pos + 10⟩
          | some _ => .error ⟨.unexpectedEndOfHexEscape, pos + 6⟩
        | some _ => .error ⟨.unexpectedEndOfHexEscape, pos + 5⟩
      else .ok (Char.ofNat u, pos + 5)
    else .error ⟨.invalidEscape, pos⟩

/-- An escape always ends after the byte it starts at. -/
theorem parseEscape_next {get : Nat → Option UInt8} {n q : Nat} {r : Char × Nat} (h : parseEscape get n q = .ok r) :
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
