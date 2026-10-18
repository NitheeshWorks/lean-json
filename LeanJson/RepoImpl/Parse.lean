import LeanJson.RepoImpl.Step

/-!
# RepoImpl: the value parser

A total RFC 8259 parser over a `ByteArray` with a `Nat` cursor, with no fuel:
every production returns a `Step`, whose type records that the cursor moved
forward and stayed in the buffer, and the mutual recursion is well founded on
the remaining input (`termination_by bs.size - pos`, with element and member
lists ranked above the values they contain).

Behaviour follows jiter, pydantic-core's parser: whitespace is space, tab,
LF, CR; numbers follow the RFC grammar (no leading zeros, no `+`, no bare
`.`); a literal with a fraction or exponent is a float; strings reject raw
control characters and decode `\uXXXX` with surrogate pairs; duplicate keys
are kept in order. Error kinds and offsets follow jiter's `JsonErrorType`.
`NaN` and `Infinity` are rejected (see `CONTRIBUTING.md`, deviations).
-/

namespace LeanJson

/-- A successful parse from `pos`: the value and the cursor after it, which is
strictly further on and within the buffer. Progress is in the type. -/
structure Step (bs : ByteArray) (pos : Nat) (α : Type) where
  val : α
  next : Nat
  lt : pos < next
  le : next ≤ bs.size

/-- Forget the progress proof. -/
def Step.out {bs : ByteArray} {pos : Nat} {α : Type} (s : Step bs pos α) : α × Nat := (s.val, s.next)

/-- A step from a later position is a step from an earlier one. -/
def Step.from {bs : ByteArray} {p q : Nat} {α : Type} (s : Step bs q α) (h : p ≤ q) : Step bs p α :=
  ⟨s.val, s.next, Nat.lt_of_le_of_lt h s.lt, s.le⟩

/-- A lexical production's result as a step from where it started: the
progress fact comes from the production's own lemma. -/
def Step.lift {bs : ByteArray} {q : Nat} {α : Type} :
    (r : Except ParseErr (α × Nat)) → (∀ x, r = .ok x → Adv bs q x.2 ∧ q < x.2) →
      Except ParseErr (Step bs q α)
  | .ok x, h => .ok ⟨x.1, x.2, (h x rfl).2, (h x rfl).1.2 (h x rfl).2⟩
  | .error e, _ => .error e

/-- Relabel a step's value and restart it from an earlier position. -/
def Step.cast {bs : ByteArray} {p q : Nat} {α β : Type} (s : Step bs q α) (f : α → β) (h : p ≤ q) :
    Step bs p β :=
  ⟨f s.val, s.next, Nat.lt_of_le_of_lt h s.lt, s.le⟩

theorem skipWs_ge (bs : ByteArray) (pos : Nat) : pos ≤ skipWs bs pos := (skipWs_adv bs pos).1

theorem numStep {cfg : ParseCfg} {bs : ByteArray} {q : Nat} :
    ∀ x, (parseNumber cfg bs q).map (fun y => (Json.num y.1, y.2)) = .ok x → Adv bs q x.2 ∧ q < x.2 := by
  intro x h
  cases hn : parseNumber cfg bs q with
  | error e => rw [hn] at h; cases h
  | ok y => rw [hn] at h; cases h; exact parseNumber_adv hn

theorem litStep {bs : ByteArray} {q : Nat} {lit : List UInt8} (v : Json) (hq : q < bs.size) :
    ∀ x, (expectLit bs (q + 1) lit).map (fun p => (v, p)) = .ok x → Adv bs q x.2 ∧ q < x.2 := by
  intro x h
  cases hl : expectLit bs (q + 1) lit with
  | error e => rw [hl] at h; cases h
  | ok p =>
    rw [hl] at h; cases h
    have a := expectLit_adv bs _ _ _ hl
    exact ⟨(Adv.of_lt (Nat.le_succ q) hq).trans a, by have := a.1; simp; omega⟩

mutual
/-- A value at `pos` after optional whitespace. -/
def parseValueWith (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Except ParseErr (Step bs pos Json) :=
  let q := skipWs bs pos
  have hq : pos ≤ q := skipWs_ge bs pos
  if hqs : q < bs.size then
    let b := bs[q]
    if b == 34 then
      (Step.lift (parseString bs q) (fun _ h => parseString_adv h)).map (·.cast .str hq)
    else if b == 91 then
      let p := skipWs bs (q + 1)
      have hp : q + 1 ≤ p := skipWs_ge bs (q + 1)
      if hps : p < bs.size then
        if bs[p] == 93 then .ok ⟨.arr [], p + 1, by omega, by omega⟩
        else (parseElems cfg bs p []).map (·.cast id (by omega))
      else .error ⟨.eofWhileParsingList, p⟩
    else if b == 123 then
      let p := skipWs bs (q + 1)
      have hp : q + 1 ≤ p := skipWs_ge bs (q + 1)
      if hps : p < bs.size then
        if bs[p] == 125 then .ok ⟨.obj [], p + 1, by omega, by omega⟩
        else if bs[p] == 34 then (parseMembers cfg bs p []).map (·.cast id (by omega))
        else .error ⟨.keyMustBeAString, p⟩
      else .error ⟨.eofWhileParsingObject, p⟩
    else if b == 116 then
      (Step.lift _ (litStep (lit := [114, 117, 101]) (.bool true) hqs)).map (·.cast id hq)
    else if b == 102 then
      (Step.lift _ (litStep (lit := [97, 108, 115, 101]) (.bool false) hqs)).map (·.cast id hq)
    else if b == 110 then
      (Step.lift _ (litStep (lit := [117, 108, 108]) .null hqs)).map (·.cast id hq)
    else if b == 45 || isDigit b then
      (Step.lift _ (numStep (cfg := cfg))).map (·.cast id hq)
    else .error ⟨.expectedSomeValue, q⟩
  else .error ⟨.eofWhileParsingValue, q⟩
termination_by (bs.size - pos, 0)
decreasing_by
  all_goals
    simp only [Prod.lex_def]
    simp only [q, p] at hq hqs hp hps ⊢
    omega
/-- Array elements from `pos` (an element is due); `acc` holds the elements
so far, reversed. -/
def parseElems (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) (acc : List Json) :
    Except ParseErr (Step bs pos Json) :=
  match parseValueWith cfg bs pos with
  | .error e => .error e
  | .ok s =>
    have hs : pos < s.next := s.lt
    let p := skipWs bs s.next
    have hp : s.next ≤ p := skipWs_ge bs s.next
    if hps : p < bs.size then
      if bs[p] == 44 then
        let q := skipWs bs (p + 1)
        have hq : p + 1 ≤ q := skipWs_ge bs (p + 1)
        if bs[q]? == some 93 then .error ⟨.trailingComma, q⟩
        else (parseElems cfg bs q (s.val :: acc)).map (·.cast id (by omega))
      else if bs[p] == 93 then .ok ⟨.arr (s.val :: acc).reverse, p + 1, by omega, by omega⟩
      else .error ⟨.expectedListCommaOrEnd, p⟩
    else .error ⟨.eofWhileParsingList, p⟩
termination_by (bs.size - pos, 1)
decreasing_by
  all_goals simp only [Prod.lex_def]
  · simp
  · simp only [p, q] at hp hq hs hps ⊢
    omega
/-- Object members from `pos` (which holds the opening quote of a key);
`acc` holds the members so far, reversed. -/
def parseMembers (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) (acc : List (String × Json)) :
    Except ParseErr (Step bs pos Json) :=
  match Step.lift (parseString bs pos) (fun _ h => parseString_adv h) with
  | .error e => .error e
  | .ok k =>
    have hk : pos < k.next := k.lt
    let p := skipWs bs k.next
    have hp : k.next ≤ p := skipWs_ge bs k.next
    if hps : p < bs.size then
      if bs[p] == 58 then
        match parseValueWith cfg bs (p + 1) with
        | .error e => .error e
        | .ok s =>
          have hs : p + 1 < s.next := s.lt
          let p3 := skipWs bs s.next
          have h3 : s.next ≤ p3 := skipWs_ge bs s.next
          if hp3 : p3 < bs.size then
            if bs[p3] == 44 then
              let q := skipWs bs (p3 + 1)
              have hq : p3 + 1 ≤ q := skipWs_ge bs (p3 + 1)
              if hqs : q < bs.size then
                if bs[q] == 34 then
                  (parseMembers cfg bs q ((k.val, s.val) :: acc)).map (·.cast id (by omega))
                else if bs[q] == 125 then .error ⟨.trailingComma, q⟩
                else .error ⟨.keyMustBeAString, q⟩
              else .error ⟨.eofWhileParsingValue, q⟩
            else if bs[p3] == 125 then
              .ok ⟨.obj ((k.val, s.val) :: acc).reverse, p3 + 1, by omega, by omega⟩
            else .error ⟨.expectedObjectCommaOrEnd, p3⟩
          else .error ⟨.eofWhileParsingObject, p3⟩
      else .error ⟨.expectedColon, p⟩
    else .error ⟨.eofWhileParsingObject, p⟩
termination_by (bs.size - pos, 1)
decreasing_by
  all_goals simp only [Prod.lex_def]
  · simp only [p] at hp hps ⊢
    omega
  · simp only [p, p3, q] at hp h3 hq hs hqs ⊢
    omega
end

/-- The value parser with its progress forgotten: value and end position. -/
def parseValueAt (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Except ParseErr (Json × Nat) :=
  (parseValueWith cfg bs pos).map Step.out

/-- The value parser with jiter's default limits. -/
def parseValue (bs : ByteArray) (pos : Nat) : Except ParseErr (Json × Nat) := parseValueAt {} bs pos

/-- A whole document: optional whitespace, one value, optional whitespace,
end of input (else `trailing characters`). -/
def parseDocumentWith (cfg : ParseCfg) (bs : ByteArray) : Except ParseErr Json :=
  match parseValueAt cfg bs 0 with
  | .error e => .error e
  | .ok (v, p) =>
    let q := skipWs bs p
    if q < bs.size then .error ⟨.trailingCharacters, q⟩ else .ok v

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
