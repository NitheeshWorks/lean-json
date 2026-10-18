import LeanJson.RepoImpl.Str

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

end LeanJson
