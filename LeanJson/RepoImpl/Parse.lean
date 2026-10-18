import LeanJson.RepoImpl.Str
import LeanJson.RepoImpl.Scan

/-!
# RepoImpl: the value parser

One value's grammar is `valueStep`: given the bytes of a view whose position
`0` holds the value's first byte, and a `child` parser for the values nested
in it, it reads the value and returns it with its end position. Nesting is
`valueGo`, which feeds `valueStep` itself as the child, each nested value
read through a view rebased at its own first byte, with a budget of nesting
levels that falls by one per level (jiter's limit, `ParseCfg.maxDepth`).

The same `valueStep` is the body of the Keel parser (`Grammar.lean`), where
nesting is `Keel.Parser.fixDepth`; `valueL_ok_iff` (in `Proofs/`) says the two
succeed alike. Positions inside a view are relative to it.

Behaviour follows jiter: whitespace is space, tab, LF, CR; numbers follow the
RFC grammar (no leading zeros, no `+`, no bare `.`); a literal with a fraction
or exponent is a float; strings reject raw control characters and decode
`\uXXXX` with surrogate pairs. Error kinds and offsets follow jiter's
`JsonErrorType`.
-/

namespace LeanJson

/-- The view of a list: its bytes by position. -/
@[inline] def lv (L : List UInt8) : Nat → Option UInt8 := fun k => L[k]?

/-- The view of a buffer. Inlined, so a read and the match on it compile to a
bounds check and a byte load, with no `Option` allocated. -/
@[inline] def bv (bs : ByteArray) : Nat → Option UInt8 := fun k => bs[k]?

/-- The values `some b` for the bytes below `m`. -/
def someBytesUpTo (m : Nat) : Array (Option UInt8) := Array.ofFn (n := m) fun i => some (UInt8.ofNat i.val)

/-- `some b` for every byte, built once and shared. -/
def someBytes : Array (Option UInt8) := someBytesUpTo 256

/-- `some b`, taken from the shared table: no allocation. -/
@[inline] def someByteIn (tbl : Array (Option UInt8)) (b : UInt8) : Option UInt8 :=
  match tbl[b.toNat]? with
  | some o => o
  | none => some b

/-- Stated for every table size, so the kernel never builds the table. -/
theorem someByteIn_eq (m : Nat) (b : UInt8) : someByteIn (someBytesUpTo m) b = some b := by
  unfold someByteIn
  split
  · rename_i o h
    simp only [someBytesUpTo, Array.getElem?_ofFn] at h
    split at h
    · cases h; simp
    · cases h
  · rfl

/-- `bv` reading through the shared `some b` table: where a read is not
inlined (a byte read through a view that the compiler lifted into a
function), it returns a shared object instead of allocating one per byte.
Equal to `bv` (`bv_eq_fast`), and what the compiler runs (`@[csimp]`). -/
@[inline] def bvFast (bs : ByteArray) : Nat → Option UInt8 := fun k =>
  if h : k < bs.size then someByteIn someBytes bs[k] else none

@[csimp] theorem bv_eq_fast : @bv = @bvFast := by
  funext bs k
  unfold bv bvFast
  split
  · rename_i h
    rw [show someBytes = someBytesUpTo 256 from rfl, someByteIn_eq]
    simp [h]
  · rename_i h
    simp [h]

/-- Move a result's positions (its end position, or its error offset) on by
`k`: a result read in a view rebased at `k`, seen from the enclosing view. -/
@[inline] def shiftRes {α : Type} (k : Nat) : Except ParseErr (α × Nat) → Except ParseErr (α × Nat)
  | .ok (a, p) => .ok (a, p + k)
  | .error e => .error ⟨e.kind, e.offset + k⟩

/-- Array elements from `pos`, where an element is due (a byte that is not
whitespace); `acc` holds the elements so far. A tail-recursive loop, so a
wide array uses constant stack. -/
@[specialize] def parseElems (child : Nat → Except ParseErr (Json × Nat)) (get : Nat → Option UInt8)
    (n pos : Nat) (acc : Array Json) : Except ParseErr (Json × Nat) :=
  match child pos with
  | .error e => .error e
  | .ok (v, j) =>
    let p := skipWs get n j
    match get p with
    | some 44 =>
      let q := skipWs get n (p + 1)
      match get q with
      | some 93 => .error ⟨.trailingComma, q⟩
      | some _ =>
        -- A child always consumes input, so `q` is past `pos`; checked to keep
        -- the loop total whatever `child` does.
        if _h : pos < q ∧ q < n then parseElems child get n q (acc.push v)
        else .error ⟨.expectedSomeValue, q⟩
      | none => .error ⟨.eofWhileParsingValue, q⟩
    | some 93 => .ok (.arr (acc.push v), p + 1)
    | some _ => .error ⟨.expectedListCommaOrEnd, p⟩
    | none => .error ⟨.eofWhileParsingList, p⟩
termination_by n - pos
decreasing_by all_goals (simp only [q, p] at *; omega)

/-- Object members from `pos`, which holds the opening quote of a key; `acc`
is the object so far; `dedup` collapses repeated keys. Tail-recursive. -/
@[specialize] def parseMembers (dedup : Bool) (child : Nat → Except ParseErr (Json × Nat))
    (get : Nat → Option UInt8) (n pos : Nat) (acc : Fields) : Except ParseErr (Json × Nat) :=
  match parseString get n pos with
  | .error e => .error e
  | .ok (k, kn) =>
    let p := skipWs get n kn
    match get p with
    | some 58 =>
      let q := skipWs get n (p + 1)
      match get q with
      | none => .error ⟨.eofWhileParsingValue, q⟩
      | some _ =>
        match child q with
        | .error e => .error e
        | .ok (v, j) =>
          let p3 := skipWs get n j
          match get p3 with
          | some 44 =>
            let q2 := skipWs get n (p3 + 1)
            match get q2 with
            | some 34 =>
              if _h : pos < q2 ∧ q2 < n then parseMembers dedup child get n q2 (acc.add dedup k v)
              else .error ⟨.keyMustBeAString, q2⟩
            | some 125 => .error ⟨.trailingComma, q2⟩
            | some _ => .error ⟨.keyMustBeAString, q2⟩
            | none => .error ⟨.eofWhileParsingValue, q2⟩
          | some 125 => .ok (.obj (acc.add dedup k v).1, p3 + 1)
          | some _ => .error ⟨.expectedObjectCommaOrEnd, p3⟩
          | none => .error ⟨.eofWhileParsingObject, p3⟩
    | some _ => .error ⟨.expectedColon, p⟩
    | none => .error ⟨.eofWhileParsingObject, p⟩
termination_by n - pos
decreasing_by all_goals (simp only [q2, p3] at *; omega)

/-- One value, whose first byte is at position `0` of the view; `child`
reads a value nested in it, at a position of the view where a non-whitespace
byte is. -/
@[specialize] def valueStep (cfg : ParseCfg) (child : Nat → Except ParseErr (Json × Nat))
    (get : Nat → Option UInt8) (n : Nat) : Except ParseErr (Json × Nat) :=
  match get 0 with
  | none => .error ⟨.eofWhileParsingValue, 0⟩
  | some b =>
    if b == 34 then (parseString get n 0).map fun r => (.str r.1, r.2)
    else if b == 91 then
      let p := skipWs get n 1
      match get p with
      | some 93 => .ok (.arr #[], p + 1)
      | some _ => parseElems child get n p #[]
      | none => .error ⟨.eofWhileParsingList, p⟩
    else if b == 123 then
      let p := skipWs get n 1
      match get p with
      | some 125 => .ok (.obj #[], p + 1)
      | some 34 => parseMembers cfg.dedupKeys child get n p .empty
      | some _ => .error ⟨.keyMustBeAString, p⟩
      | none => .error ⟨.eofWhileParsingObject, p⟩
    else if b == 116 then (expectLit get 1 [114, 117, 101]).map fun p => (.bool true, p)
    else if b == 102 then (expectLit get 1 [97, 108, 115, 101]).map fun p => (.bool false, p)
    else if b == 110 then (expectLit get 1 [117, 108, 108]).map fun p => (.null, p)
    else if b == 45 || isDigit b then (parseNumber cfg get n 0).map fun r => (Json.ofNumber r.1, r.2)
    else if b == 78 && cfg.allowInfNan then (expectLit get 1 [97, 78]).map fun p => (.num .nan, p)
    else if b == 73 && cfg.allowInfNan then
      (expectLit get 1 [110, 102, 105, 110, 105, 116, 121]).map fun p => (.num .inf, p)
    else .error ⟨.expectedSomeValue, 0⟩

/-- The value at `base` of the root view `get`/`n`, with `d` more levels of
nesting allowed (none left: `recursion limit exceeded`, at the value).
Positions are relative to `base`. -/
@[specialize] def valueGo (cfg : ParseCfg) (get : Nat → Option UInt8) (n : Nat) :
    (d base : Nat) → Except ParseErr (Json × Nat)
  | 0, _ => .error ⟨.recursionLimitExceeded, 0⟩
  | d + 1, base =>
    valueStep cfg (fun j => shiftRes j (valueGo cfg get n d (base + j))) (fun k => get (base + k)) (n - base)

/-- The view `get` rebased at `base`. A named inline function rather than a
lambda: passed to the specialised `valueStep`, it inlines into each byte
read, which then compiles to a bounds check and a load, where a lambda would
be lifted into a function returning an allocated `Option` per byte. -/
@[inline] def rebase (get : Nat → Option UInt8) (base k : Nat) : Option UInt8 := get (base + k)

/-- `valueGo` with its views written through `rebase`; equal to it
(`valueGo_eq_fast`), and what the compiler runs (`@[csimp]`). -/
@[specialize] def valueGoFast (cfg : ParseCfg) (get : Nat → Option UInt8) (n : Nat) :
    (d base : Nat) → Except ParseErr (Json × Nat)
  | 0, _ => .error ⟨.recursionLimitExceeded, 0⟩
  | d + 1, base =>
    valueStep cfg (fun j => shiftRes j (valueGoFast cfg get n d (base + j))) (rebase get base) (n - base)

theorem valueGo_eq_fast_at (cfg : ParseCfg) (get : Nat → Option UInt8) (n : Nat) :
    ∀ d base, valueGo cfg get n d base = valueGoFast cfg get n d base
  | 0, _ => rfl
  | d + 1, base => by
    rw [valueGo, valueGoFast]
    simp only [valueGo_eq_fast_at cfg get n d]
    rfl

@[csimp] theorem valueGo_eq_fast : @valueGo = @valueGoFast := by
  funext cfg get n d base; exact valueGo_eq_fast_at cfg get n d base

/-- The nesting budget for a view of `n` bytes: jiter's limit, or, with no
limit, more levels than the bytes can open. -/
def ParseCfg.budget (cfg : ParseCfg) (n : Nat) : Nat := cfg.maxDepth.getD (n + 1)

/-- A value at `pos` after optional whitespace; its end position. -/
@[specialize] def parseValueIn (cfg : ParseCfg) (get : Nat → Option UInt8) (n pos : Nat) :
    Except ParseErr (Json × Nat) :=
  let q := skipWs get n pos
  match get q with
  | none => .error ⟨.eofWhileParsingValue, q⟩
  | some _ => shiftRes q (valueGo cfg get n (cfg.budget n) q)

/-- The value parser on a buffer: the value at `pos` (after optional
whitespace) and the position after it. -/
def parseValueAt (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Except ParseErr (Json × Nat) :=
  parseValueIn cfg (bv bs) bs.size pos

/-- A string literal on a buffer, its opening quote at `pos`. -/
def parseStringAt (bs : ByteArray) (pos : Nat) : Except ParseErr (String × Nat) :=
  parseString (bv bs) bs.size pos

/-- A number literal on a buffer, its first byte at `pos`. -/
def parseNumberAt (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Except ParseErr (Number × Nat) :=
  parseNumber cfg (bv bs) bs.size pos

/-- The value parser with jiter's default limits. -/
def parseValue (bs : ByteArray) (pos : Nat) : Except ParseErr (Json × Nat) := parseValueAt {} bs pos

/-- A whole document: optional whitespace, one value, optional whitespace,
end of input (else `trailing characters`). -/
@[specialize] def parseDocumentIn (cfg : ParseCfg) (get : Nat → Option UInt8) (n : Nat) :
    Except ParseErr Json :=
  match parseValueIn cfg get n 0 with
  | .error e => .error e
  | .ok (v, p) =>
    let q := skipWs get n p
    if q < n then .error ⟨.trailingCharacters, q⟩ else .ok v

/-- `parseDocumentIn` on a buffer. -/
def parseDocumentWith (cfg : ParseCfg) (bs : ByteArray) : Except ParseErr Json :=
  parseDocumentIn cfg (bv bs) bs.size

/-- `parseDocumentWith` with jiter's default limits: what `from_json` does. -/
def parseDocument (bs : ByteArray) : Except ParseErr Json := parseDocumentWith {} bs

/-- jiter's line/column for a byte offset: 1-based line; column is the
1-based column of the byte at `offset`, or for an offset at or past the end,
the length of the last line. -/
def lineCol (bs : ByteArray) (offset : Nat) : Nat × Nat :=
  go 0 1 0
where
  go (i line start : Nat) : Nat × Nat :=
    if h : i < bs.size then
      let (line, start) := if bs[i] == 10 then (line + 1, i + 1) else (line, start)
      if i = offset then (line, i + 1 - start) else go (i + 1) line start
    else (line, i - start)
  termination_by bs.size - i

/-- A low-level error with jiter's line and column attached. -/
def ParseErr.toJsonError (bs : ByteArray) (e : ParseErr) : JsonError :=
  let lc := lineCol bs e.offset
  { kind := e.kind, offset := e.offset, line := lc.1, column := lc.2 }


/-! ## The parser on a buffer, strings taken in runs

A string literal's bytes up to the next quote, backslash, control character
or non-ASCII byte are taken whole, as one slice of the buffer
(`asciiSlice`), rather than pushed one character at a time. That needs the
buffer itself, which a view hides, so the parser on a buffer
(`parseValueAt`, `parseDocumentWith`) is run as `valueGoBA`: `valueGo` with
its key and string reader replaced by `strBodyBA`. Each is proved equal to
what it replaces, and the compiler runs them through `@[csimp]`. -/

/-- Whether a byte ends a run of string-literal bytes taken whole: a quote,
a backslash, a control character or a non-ASCII byte. -/
@[inline] def strStop (x : UInt8) : Bool := x < 32 || x == 34 || x == 92 || 128 ≤ x

theorem toNat_ofNat_ascii {n : Nat} (h : n < 128) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, Char.ofNatAux, Nat.isValidChar, show n < 55296 by omega, Char.toNat]

theorem utf8EncodeChar_ascii {n : Nat} (h : n < 128) : String.utf8EncodeChar (Char.ofNat n) = [UInt8.ofNat n] := by
  unfold String.utf8EncodeChar
  dsimp only
  rw [Char.toNat_val, toNat_ofNat_ascii h, ite_eq_left (by omega)]

theorem ascii_chars_encode :
    ∀ (l : List UInt8), (∀ x ∈ l, x < 128) → (l.map fun x => Char.ofNat x.toNat).flatMap String.utf8EncodeChar = l
  | [], _ => rfl
  | x :: l, h => by
    have hx : x.toNat < 128 := by have := h x (by simp); rw [UInt8.lt_iff_toNat_lt] at this; simpa using this
    simp only [List.map_cons, List.flatMap_cons, utf8EncodeChar_ascii hx, UInt8.ofNat_toNat,
      ascii_chars_encode l (fun y hy => h y (by simp [hy])), List.singleton_append]

/-- Bytes `i` to `j` of `bs`, all ASCII, as a string: one copy. -/
@[inline] def asciiSlice (bs : ByteArray) (i j : Nat) (h : ∀ x ∈ (bs.extract i j).data.toList, x < 128) : String :=
  String.ofByteArray (bs.extract i j)
    ⟨_, by
      apply ByteArray.ext
      simp only [List.utf8Encode, List.data_toByteArray]
      rw [ascii_chars_encode _ h]⟩


theorem mem_extract {bs : ByteArray} {i j : Nat} {x : UInt8} (hx : x ∈ (bs.extract i j).data.toList) :
    ∃ k, ∃ hk : k < bs.size, i ≤ k ∧ k < j ∧ bs[k] = x := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  simp at hm
  refine ⟨i + m, by omega, by omega, by omega, ?_⟩
  simp only [ByteArray.data_extract, Array.getElem_toList, Array.getElem_extract]
  rfl

/-- The bytes of a run that `strStop` passes over are ASCII. -/
theorem ascii_of_run {bs : ByteArray} {i j : Nat}
    (hrun : ∀ k (hk : k < bs.size), i ≤ k → k < j → strStop bs[k] = false) :
    ∀ x ∈ (bs.extract i j).data.toList, x < 128 := by
  intro x hx
  obtain ⟨k, hk, h1, h2, rfl⟩ := mem_extract hx
  have := hrun k hk h1 h2
  simp only [strStop, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at this
  exact UInt8.not_le.mp this.2

theorem extract_cons (bs : ByteArray) {i j : Nat} (h : i < j) (hj : j ≤ bs.size) :
    (bs.extract i j).data.toList = bs[i] :: (bs.extract (i + 1) j).data.toList := by
  simp only [ByteArray.data_extract, Array.toList_extract]
  rw [List.extract_eq_take_drop, List.extract_eq_take_drop, List.drop_eq_getElem_cons (by simp; omega),
    show j - i = (j - (i + 1)) + 1 by omega, List.take_succ_cons]
  rfl

/-- A string literal takes a run of plain ASCII bytes whole: reading it
character by character appends exactly that slice of the buffer. -/
theorem parseStrBody_run (bs : ByteArray) (base : Nat) (pos j : Nat) (acc : String) (h1 : base + pos ≤ j)
    (h2 : j ≤ bs.size) (hrun : ∀ k (hk : k < bs.size), base + pos ≤ k → k < j → strStop bs[k] = false) :
    parseStrBody (rebase (bv bs) base) (bs.size - base) pos acc =
      parseStrBody (rebase (bv bs) base) (bs.size - base) (j - base)
        (acc ++ asciiSlice bs (base + pos) j (ascii_of_run hrun)) := by
  by_cases e : base + pos = j
  · subst e
    have : asciiSlice bs (base + pos) (base + pos) (ascii_of_run hrun) = "" := by
      apply String.toByteArray_inj.mp
      simp [asciiSlice]
    rw [this, String.append_empty, show base + pos - base = pos by omega]
  · have hi : base + pos < bs.size := by omega
    have hs := hrun (base + pos) hi (Nat.le_refl _) (by omega)
    simp only [strStop, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hs
    obtain ⟨⟨⟨h32, h34⟩, h92⟩, h128⟩ := hs
    rw [parseStrBody, ite_eq_left (by omega)]
    have hg : rebase (bv bs) base pos = some bs[base + pos] := by
      simp [rebase, bv, hi]
    rw [hg]
    dsimp only
    rw [ite_eq_right (by simpa using h34), ite_eq_right (by simpa using h92), ite_eq_right h32,
      ite_eq_left (UInt8.not_le.mp h128)]
    rw [parseStrBody_run bs base (pos + 1) j _ (by omega) h2
      (fun k hk h1 h2 => hrun k hk (by omega) h2)]
    congr 1
    apply String.toByteArray_inj.mp
    have hb : (bs[base + pos]).toNat < 128 := by
      have := UInt8.not_le.mp h128; rw [UInt8.lt_iff_toNat_lt] at this; simpa using this
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [String.toByteArray_append, String.toByteArray_push, ByteArray.toList_data_append,
      asciiSlice, List.utf8Encode_singleton, utf8EncodeChar_ascii hb, UInt8.ofNat_toNat,
      show base + (pos + 1) = base + pos + 1 by omega, extract_cons bs (by omega : base + pos < j) h2]
    simp
termination_by j - (base + pos)


theorem run_of_find {bs : ByteArray} {i : Nat} (hi : i < bs.size) (hs : strStop bs[i] = false) :
    ∀ k (hk : k < bs.size), i ≤ k → k < findFrom strStop bs (i + 1) → strStop bs[k] = false := by
  intro k hk h1 h2
  by_cases e : k = i
  · subst e; exact hs
  · exact findFrom_run k hk (by omega) h2

/-- `acc ++ s`, without copying `s` when `acc` is empty. -/
@[inline] def appendRun (acc s : String) : String := if acc.isEmpty then s else acc ++ s

theorem appendRun_eq (acc s : String) : appendRun acc s = acc ++ s := by
  unfold appendRun
  split
  · rename_i h
    have : acc = "" := by simpa [String.isEmpty_iff] using h
    subst this; simp
  · rfl

/-- `escCode` on the buffer, the letter at absolute position `a`. -/
@[inline] def escCodeBA (bs : ByteArray) (a : Nat) : UInt32 :=
  if h : a < bs.size then
    match simpleEscape bs[a] with
    | some c => c.val
    | none => 0x110000
  else 0x110000

theorem escCodeBA_eq (bs : ByteArray) (base q : Nat) :
    escCodeBA bs (base + q) = escCode (rebase (bv bs) base) q := by
  unfold escCodeBA escCode
  by_cases h : base + q < bs.size
  · rw [dite_eq_left h]
    simp [rebase, bv, h]
    rfl
  · rw [dite_eq_right h]
    simp [rebase, bv, h]

theorem simpleEscape_small {b : UInt8} {c : Char} (h : simpleEscape b = some c) : c.toNat < 128 := by
  unfold simpleEscape at h
  repeat' split at h
  all_goals first | (cases h; decide) | cases h

/-- The character of a one-letter escape, from its code: no `Nat` on the way. -/
theorem escCodeBA_char {bs : ByteArray} {a : Nat} (h : escCodeBA bs a < 0x110000) :
    Char.ofNat (escCodeBA bs a).toNat = Char.ofUInt8 (escCodeBA bs a).toUInt8 := by
  unfold escCodeBA at h ⊢
  split at h
  · rename_i ha
    rw [dite_eq_left ha]
    split at h
    · rename_i c hc
      have hs := simpleEscape_small hc
      rw [Char.toNat_val, Char.ofNat_toNat]
      apply Char.ext
      show c.val = c.val.toUInt8.toUInt32
      apply UInt32.toNat_inj.mp
      rw [UInt8.toNat_toUInt32, UInt32.toNat_toUInt8]
      rw [← Char.toNat_val] at hs
      omega
    · simp at h
  · rename_i ha
    simp at h

/-- `hexD` on the buffer, at absolute position `a`. -/
@[inline] def hexDBA (bs : ByteArray) (a : Nat) : Nat :=
  if h : a < bs.size then
    match hexVal bs[a] with
    | some v => v
    | none => 16
  else 16

theorem hexDBA_eq (bs : ByteArray) (base q : Nat) :
    hexDBA bs (base + q) = hexD (rebase (bv bs) base) q := by
  unfold hexDBA hexD
  by_cases h : base + q < bs.size
  · rw [dite_eq_left h]
    simp [rebase, bv, h]
    rfl
  · rw [dite_eq_right h]
    simp [rebase, bv, h]

/-- `hex4v` on the buffer, the first digit at absolute position `a`. -/
@[inline] def hex4vBA (bs : ByteArray) (a : Nat) : Nat :=
  let a0 := hexDBA bs a
  let b := hexDBA bs (a + 1)
  let c := hexDBA bs (a + 2)
  let d := hexDBA bs (a + 3)
  if a0 < 16 ∧ b < 16 ∧ c < 16 ∧ d < 16 then a0 * 4096 + b * 256 + c * 16 + d else 65536

theorem hex4vBA_eq (bs : ByteArray) (base q : Nat) :
    hex4vBA bs (base + q) = hex4v (rebase (bv bs) base) q := by
  unfold hex4vBA hex4v
  simp only [Nat.add_assoc, hexDBA_eq]

/-- Byte `a` of `bs`, or `0` past the end. -/
@[inline] def byteAt (bs : ByteArray) (a : Nat) : UInt8 := if h : a < bs.size then bs[a] else 0

theorem byteAt_eq {bs : ByteArray} {base q : Nat} {b : UInt8} (hb : b ≠ 0) :
    (byteAt bs (base + q) == b) = true ↔ rebase (bv bs) base q = some b := by
  unfold byteAt
  by_cases h : base + q < bs.size
  · rw [dite_eq_left h]; simp [rebase, bv, h]
  · rw [dite_eq_right h]; simp [rebase, bv, h]; exact Ne.symm hb

/-- `uEsc` on the buffer, the `u` at absolute position `a`; `n` is the
length of the view from `base`, as in `uEsc`. -/
@[inline] def uEscBA (bs : ByteArray) (base n a : Nat) : Nat :=
  if byteAt bs a == 117 then
    if n + base < a + 5 then 0 else
    let u := hex4vBA bs (a + 1)
    if u < 0xD800 ∨ (0xE000 ≤ u ∧ u < 65536) then u * 16 + 5
    else if u < 0xDC00 then
      if byteAt bs (a + 5) == 92 && byteAt bs (a + 6) == 117 then
        if n + base < a + 11 then 0 else
        let l := hex4vBA bs (a + 7)
        if 0xDC00 ≤ l ∧ l < 0xE000 then (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)) * 16 + 11
        else 0
      else 0
    else 0
  else 0

theorem uEscBA_eq (bs : ByteArray) (base n q : Nat) :
    uEscBA bs base n (base + q) = uEsc (rebase (bv bs) base) n q := by
  unfold uEscBA uEsc
  simp only [Nat.add_assoc, hex4vBA_eq]
  by_cases h117 : (byteAt bs (base + q) == 117) = true
  · rw [ite_eq_left h117, (byteAt_eq (by decide)).mp h117]
    simp only []
    by_cases h5 : n < q + 5
    · rw [ite_eq_left (by omega : n + base < base + (q + 5)), ite_eq_left h5]
    rw [ite_eq_right (by omega : ¬ n + base < base + (q + 5)), ite_eq_right h5]
    split
    · rfl
    split
    · by_cases hb : (byteAt bs (base + (q + 5)) == 92 && byteAt bs (base + (q + 6)) == 117) = true
      · rw [ite_eq_left hb]
        simp only [Bool.and_eq_true] at hb
        rw [(byteAt_eq (by decide)).mp hb.1, (byteAt_eq (by decide)).mp hb.2]
        simp only []
        by_cases h11 : n < q + 11
        · rw [ite_eq_left (by omega : n + base < base + (q + 11)), ite_eq_left h11]
        rw [ite_eq_right (by omega : ¬ n + base < base + (q + 11)), ite_eq_right h11]
      · rw [ite_eq_right hb]
        split
        · rename_i h1 h2
          exact absurd (by simp only [Bool.and_eq_true]; exact ⟨(byteAt_eq (by decide)).mpr h1, (byteAt_eq (by decide)).mpr h2⟩) hb
        · rfl
    · rfl
  · rw [ite_eq_right h117]
    split
    · rename_i h; exact absurd ((byteAt_eq (by decide)).mpr h) h117
    · rfl

/-- `parseStrBodyFast` on the buffer `bs` seen from `base` (the view
`rebase (bv bs) base`), taking each run of plain ASCII bytes whole as one
slice of the buffer; equal to it (`strBodyBA_eq`). -/
def strBodyBA (bs : ByteArray) (base pos : Nat) (acc : String) : Except ParseErr (String × Nat) :=
  if hi : base + pos < bs.size then
    if hs : strStop bs[base + pos] = false then
      let j := findFrom strStop bs (base + pos + 1)
      strBodyBA bs base (j - base) (appendRun acc (asciiSlice bs (base + pos) j (ascii_of_run (run_of_find hi hs))))
    else
      let get := rebase (bv bs) base
      let n := bs.size - base
      let b := bs[base + pos]
      if b == 34 then .ok (acc, pos + 1)
      else if b == 92 then
        let c := escCodeBA bs (base + (pos + 1))
        if c < 0x110000 then strBodyBA bs base (pos + 2) (acc.push (Char.ofUInt8 c.toUInt8))
        else
          let u := uEscBA bs base n (base + (pos + 1))
          if hu : u ≠ 0 then strBodyBA bs base (pos + 1 + u % 16) (acc.push (Char.ofNat (u / 16)))
          else
          match _he : parseEscape get n (pos + 1) with
          | .ok (c, p) => strBodyBA bs base p (acc.push c)
          | .error e => .error e
      else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
      else if b < 128 then strBodyBA bs base (pos + 1) (acc.push (Char.ofNat b.toNat))
      else
        match decodeChar? get pos with
        | some c => strBodyBA bs base (pos + c.utf8Size) (acc.push c)
        | none => .error ⟨.invalidUnicodeCodePoint, pos + 1⟩
  else .error ⟨.eofWhileParsingString, pos⟩
termination_by bs.size - (base + pos)
decreasing_by
  all_goals first
    | (have := le_findFrom strStop bs (base + pos + 1)
       have := findFrom_le strStop bs (base + pos + 1) (by omega)
       omega)
    | omega
    | (have := parseEscape_next _he; simp at this; omega)
    | (have := Char.utf8Size_pos c; omega)
    | (rw [uEscBA_eq] at hu; have := parseEscape_next (uEsc_spec hu); simp at this; omega)

theorem strBodyBA_eq (bs : ByteArray) (base pos : Nat) (acc : String) :
    strBodyBA bs base pos acc = parseStrBodyFast (rebase (bv bs) base) (bs.size - base) pos acc := by
  rw [strBodyBA]
  split
  · rename_i hi
    split
    · rename_i hs
      have hle := le_findFrom strStop bs (base + pos + 1)
      have hfl := findFrom_le strStop bs (base + pos + 1) (by omega)
      dsimp only
      rw [appendRun_eq, ← parseStrBody_eq_fast_at, parseStrBody_run bs base pos _ acc (by omega) hfl
        (run_of_find hi hs), parseStrBody_eq_fast_at]
      exact strBodyBA_eq bs base _ _
    · rename_i hs
      rw [parseStrBodyFast, ite_eq_left (show pos < bs.size - base by omega)]
      have hg : rebase (bv bs) base pos = some bs[base + pos] := by
        simp [rebase, bv, hi]
      rw [hg]
      dsimp only
      rw [escCodeBA_eq, uEscBA_eq]
      by_cases c34 : (bs[base + pos] == 34) = true
      · rw [ite_eq_left c34, ite_eq_left c34]
      rw [ite_eq_right c34, ite_eq_right c34]
      by_cases c92 : (bs[base + pos] == 92) = true
      · rw [ite_eq_left c92, ite_eq_left c92]
        by_cases hc : escCode (rebase (bv bs) base) (pos + 1) < 0x110000
        · rw [ite_eq_left hc, ite_eq_left hc, ← escCodeBA_eq, ← escCodeBA_char (by rw [escCodeBA_eq]; exact hc)]
          exact strBodyBA_eq bs base _ _
        rw [ite_eq_right hc, ite_eq_right hc]
        by_cases hu : uEsc (rebase (bv bs) base) (bs.size - base) (pos + 1) ≠ 0
        · rw [dite_eq_left hu, dite_eq_left hu]
          exact strBodyBA_eq bs base _ _
        rw [dite_eq_right hu, dite_eq_right hu]
        split
        · rename_i c p h
          have := parseEscape_next h
          simp at this
          split
          · rename_i c' p' h'
            rw [h] at h'; cases h'
            exact strBodyBA_eq bs base p _
          · rename_i e h'; rw [h] at h'; cases h'
        · rename_i e h
          split
          · rename_i c' p' h'; rw [h] at h'; cases h'
          · rename_i e' h'; rw [h] at h'; cases h'; rfl
      rw [ite_eq_right c92, ite_eq_right c92]
      by_cases c32 : bs[base + pos] < 32
      · rw [ite_eq_left c32, ite_eq_left c32]
      rw [ite_eq_right c32, ite_eq_right c32]
      by_cases c128 : bs[base + pos] < 128
      · rw [ite_eq_left c128, ite_eq_left c128]
        exact strBodyBA_eq bs base _ _
      rw [ite_eq_right c128, ite_eq_right c128]
      cases hd : decodeChar? (rebase (bv bs) base) pos with
      | none => rfl
      | some c =>
        have := Char.utf8Size_pos c
        exact strBodyBA_eq bs base _ _
  · rename_i hi
    rw [parseStrBodyFast, ite_eq_right (show ¬ pos < bs.size - base by omega)]
termination_by bs.size - (base + pos)


/-- `parseMembers` with the key reader `str` given (`str pos` reads the key
whose opening quote is at `pos`). -/
@[specialize] def parseMembersS (str : Nat → Except ParseErr (String × Nat)) (dedup : Bool)
    (child : Nat → Except ParseErr (Json × Nat))
    (get : Nat → Option UInt8) (n pos : Nat) (acc : Fields) : Except ParseErr (Json × Nat) :=
  match str pos with
  | .error e => .error e
  | .ok (k, kn) =>
    let p := skipWs get n kn
    match get p with
    | some 58 =>
      let q := skipWs get n (p + 1)
      match get q with
      | none => .error ⟨.eofWhileParsingValue, q⟩
      | some _ =>
        match child q with
        | .error e => .error e
        | .ok (v, j) =>
          let p3 := skipWs get n j
          match get p3 with
          | some 44 =>
            let q2 := skipWs get n (p3 + 1)
            match get q2 with
            | some 34 =>
              if _h : pos < q2 ∧ q2 < n then parseMembersS str dedup child get n q2 (acc.add dedup k v)
              else .error ⟨.keyMustBeAString, q2⟩
            | some 125 => .error ⟨.trailingComma, q2⟩
            | some _ => .error ⟨.keyMustBeAString, q2⟩
            | none => .error ⟨.eofWhileParsingValue, q2⟩
          | some 125 => .ok (.obj (acc.add dedup k v).1, p3 + 1)
          | some _ => .error ⟨.expectedObjectCommaOrEnd, p3⟩
          | none => .error ⟨.eofWhileParsingObject, p3⟩
    | some _ => .error ⟨.expectedColon, p⟩
    | none => .error ⟨.eofWhileParsingObject, p⟩
termination_by n - pos
decreasing_by all_goals (simp only [q2, p3] at *; omega)


theorem parseMembers_eq_S (dedup : Bool) (child : Nat → Except ParseErr (Json × Nat))
    (get : Nat → Option UInt8) (n : Nat) : ∀ pos acc,
    parseMembers dedup child get n pos acc = parseMembersS (parseString get n) dedup child get n pos acc := by
  intro pos acc
  rw [parseMembers, parseMembersS]
  repeat' (first | rfl | split | dsimp only)
  all_goals first
    | rfl
    | exact parseMembers_eq_S dedup child get n _ _
termination_by pos => n - pos

/-- `valueStep` with the string and key reader `str` given. -/
@[specialize] def valueStepS (str : Nat → Except ParseErr (String × Nat)) (cfg : ParseCfg)
    (child : Nat → Except ParseErr (Json × Nat))
    (get : Nat → Option UInt8) (n : Nat) : Except ParseErr (Json × Nat) :=
  match get 0 with
  | none => .error ⟨.eofWhileParsingValue, 0⟩
  | some b =>
    if b == 34 then (str 0).map fun r => (.str r.1, r.2)
    else if b == 91 then
      let p := skipWs get n 1
      match get p with
      | some 93 => .ok (.arr #[], p + 1)
      | some _ => parseElems child get n p #[]
      | none => .error ⟨.eofWhileParsingList, p⟩
    else if b == 123 then
      let p := skipWs get n 1
      match get p with
      | some 125 => .ok (.obj #[], p + 1)
      | some 34 => parseMembersS str cfg.dedupKeys child get n p .empty
      | some _ => .error ⟨.keyMustBeAString, p⟩
      | none => .error ⟨.eofWhileParsingObject, p⟩
    else if b == 116 then (expectLit get 1 [114, 117, 101]).map fun p => (.bool true, p)
    else if b == 102 then (expectLit get 1 [97, 108, 115, 101]).map fun p => (.bool false, p)
    else if b == 110 then (expectLit get 1 [117, 108, 108]).map fun p => (.null, p)
    else if b == 45 || isDigit b then (parseNumber cfg get n 0).map fun r => (Json.ofNumber r.1, r.2)
    else if b == 78 && cfg.allowInfNan then (expectLit get 1 [97, 78]).map fun p => (.num .nan, p)
    else if b == 73 && cfg.allowInfNan then
      (expectLit get 1 [110, 102, 105, 110, 105, 116, 121]).map fun p => (.num .inf, p)
    else .error ⟨.expectedSomeValue, 0⟩


theorem valueStep_eq_S (cfg : ParseCfg) (child : Nat → Except ParseErr (Json × Nat))
    (get : Nat → Option UInt8) (n : Nat) :
    valueStep cfg child get n = valueStepS (parseString get n) cfg child get n := by
  unfold valueStep valueStepS
  simp only [parseMembers_eq_S]

/-- A string literal of the buffer `bs` seen from `base`, its opening quote
at `pos`, read by `strBodyBA`. -/
@[inline] def strBA (bs : ByteArray) (base pos : Nat) : Except ParseErr (String × Nat) :=
  strBodyBA bs base (pos + 1) ""

theorem strBA_eq (bs : ByteArray) (base : Nat) :
    strBA bs base = parseString (rebase (bv bs) base) (bs.size - base) := by
  funext pos
  unfold strBA parseString
  rw [strBodyBA_eq, parseStrBody_eq_fast_at]

/-- `valueGo` on the buffer `bs`, reading strings and keys with `strBA`;
equal to it (`valueGoBA_eq`). -/
def valueGoBA (cfg : ParseCfg) (bs : ByteArray) : (d base : Nat) → Except ParseErr (Json × Nat)
  | 0, _ => .error ⟨.recursionLimitExceeded, 0⟩
  | d + 1, base =>
    valueStepS (strBA bs base) cfg (fun j => shiftRes j (valueGoBA cfg bs d (base + j))) (rebase (bv bs) base)
      (bs.size - base)

theorem valueGoBA_eq (cfg : ParseCfg) (bs : ByteArray) :
    ∀ d base, valueGoBA cfg bs d base = valueGo cfg (bv bs) bs.size d base
  | 0, _ => rfl
  | d + 1, base => by
    rw [valueGoBA, valueGo, valueStep_eq_S, strBA_eq]
    simp only [valueGoBA_eq cfg bs d]
    rfl

/-- `parseValueAt` through `valueGoBA`: what the compiler runs. -/
def parseValueAtBA (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Except ParseErr (Json × Nat) :=
  let q := skipWs (bv bs) bs.size pos
  match bv bs q with
  | none => .error ⟨.eofWhileParsingValue, q⟩
  | some _ => shiftRes q (valueGoBA cfg bs (cfg.budget bs.size) q)

@[csimp] theorem parseValueAt_eq_BA : @parseValueAt = @parseValueAtBA := by
  funext cfg bs pos
  unfold parseValueAt parseValueIn parseValueAtBA
  simp only [valueGoBA_eq]

/-- `parseDocumentWith` through `valueGoBA`: what the compiler runs. -/
def parseDocumentWithBA (cfg : ParseCfg) (bs : ByteArray) : Except ParseErr Json :=
  match parseValueAtBA cfg bs 0 with
  | .error e => .error e
  | .ok (v, p) =>
    let q := skipWs (bv bs) bs.size p
    if q < bs.size then .error ⟨.trailingCharacters, q⟩ else .ok v

@[csimp] theorem parseDocumentWith_eq_BA : @parseDocumentWith = @parseDocumentWithBA := by
  funext cfg bs
  unfold parseDocumentWith parseDocumentIn parseDocumentWithBA
  rw [← parseValueAt_eq_BA]
  rfl

end LeanJson
