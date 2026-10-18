import LeanJson.RepoImpl.Partial

/-!
# Proofs: partial mode on complete input

`parsePartial_complete`: wherever the document parser succeeds, the partial
parser (in either partial mode) returns the same value. Partial mode only
adds answers, for input that the document parser rejects.

Each loop of the partial parser is matched with the loop it shadows: a
success of `parseStrBody`, `parseElems`, `parseMembers`, `valueStep` and
`valueGo` is a `done` of `partialStrBody`, `pElems`, `pMembers`, `pStep` and
`pGo`, with the same value and end.
-/

namespace LeanJson

variable {get : Nat → Option UInt8} {n : Nat}

theorem partialStrBody_of_ok {pos : Nat} {acc s : String} {p : Nat}
    (h : parseStrBody get n pos acc = .ok (s, p)) : partialStrBody get n pos acc = .ok (s, some p) := by
  rw [parseStrBody] at h
  rw [partialStrBody]
  by_cases hp : pos < n
  · rw [ite_eq_left hp] at h ⊢
    cases hg : get pos with
    | none => rw [hg] at h; cases h
    | some b =>
      simp only [hg] at h ⊢
      by_cases c34 : (b == 34) = true
      · rw [ite_eq_left c34] at h ⊢; cases h; rfl
      rw [ite_eq_right c34] at h ⊢
      by_cases c92 : (b == 92) = true
      · rw [ite_eq_left c92] at h ⊢
        split at h
        · rename_i c q he
          have := parseEscape_next he
          split
          · rename_i c' q' he'
            rw [he] at he'; cases he'
            exact partialStrBody_of_ok h
          · rename_i e he'; rw [he] at he'; cases he'
        · cases h
      rw [ite_eq_right c92] at h ⊢
      by_cases c32 : b < 32
      · rw [ite_eq_left c32] at h; cases h
      rw [ite_eq_right c32] at h ⊢
      by_cases c128 : b < 128
      · rw [ite_eq_left c128] at h ⊢; exact partialStrBody_of_ok h
      rw [ite_eq_right c128] at h ⊢
      split at h
      · rename_i c hc
        have := Char.utf8Size_pos c
        rw [hc]; exact partialStrBody_of_ok h
      · cases h
  · rw [ite_eq_right hp] at h; cases h
termination_by n - pos
decreasing_by all_goals (simp at *; omega)

/-- `c₂` answers `done` wherever `c₁` succeeds, with the same value and end. -/
def DoneOn (c₁ : Nat → Except ParseErr (Json × Nat)) (c₂ : Nat → Except ParseErr PRes) : Prop :=
  ∀ j v q, c₁ j = .ok (v, q) → c₂ j = .ok (.done v q)

theorem pElems_of_ok {c₁ : Nat → Except ParseErr (Json × Nat)} {c₂ : Nat → Except ParseErr PRes}
    (hc : DoneOn c₁ c₂) {pos : Nat} {acc : Array Json} {v : Json} {p : Nat}
    (h : parseElems c₁ get n pos acc = .ok (v, p)) : pElems c₂ get n pos acc = .ok (.done v p) := by
  rw [parseElems] at h
  rw [pElems]
  split at h
  · cases h
  rename_i w j hw
  rw [hc _ _ _ hw]
  dsimp only at h ⊢
  generalize get (skipWs get n j) = g1 at h ⊢
  generalize get (skipWs get n (skipWs get n j + 1)) = g2 at h ⊢
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i hb
        simp only [dite_eq_left hb]
        exact pElems_of_ok hc h
      · cases h
    · cases h
  · cases h; rfl
  · cases h
  · cases h
termination_by n - pos
decreasing_by all_goals omega

theorem pMembers_of_ok {c₁ : Nat → Except ParseErr (Json × Nat)} {c₂ : Nat → Except ParseErr PRes}
    (hc : DoneOn c₁ c₂) {dedup : Bool} {pos : Nat} {acc : Fields} {v : Json} {p : Nat}
    (h : parseMembers dedup c₁ get n pos acc = .ok (v, p)) :
    pMembers dedup c₂ get n pos acc = .ok (.done v p) := by
  rw [parseMembers] at h
  rw [pMembers]
  split at h
  · cases h
  rename_i k kn hk
  rw [hk]
  dsimp only at h ⊢
  generalize get (skipWs get n kn) = g1 at h ⊢
  split at h
  · generalize get (skipWs get n (skipWs get n kn + 1)) = g2 at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i w j hw
        rw [hc _ _ _ hw]
        dsimp only at h ⊢
        generalize get (skipWs get n j) = g3 at h ⊢
        generalize get (skipWs get n (skipWs get n j + 1)) = g4 at h ⊢
        split at h
        · split at h
          · split at h
            · rename_i hb
              simp only [dite_eq_left hb]
              exact pMembers_of_ok hc h
            · cases h
          all_goals cases h
        · cases h; rfl
        all_goals cases h
  all_goals cases h
termination_by n - pos
decreasing_by all_goals omega

/-- A step whose first byte opens no container never calls its child. -/
theorem valueStep_scalar (cfg : ParseCfg) (c c' : Nat → Except ParseErr (Json × Nat))
    (h1 : get 0 ≠ some 91) (h2 : get 0 ≠ some 123) :
    valueStep cfg c get n = valueStep cfg c' get n := by
  unfold valueStep
  split
  · rfl
  rename_i b hb
  have e1 : (b == 91) = false := by
    cases e : b == 91
    · rfl
    · exact absurd (by rw [hb, beq_iff_eq.mp e]) h1
  have e2 : (b == 123) = false := by
    cases e : b == 123
    · rfl
    · exact absurd (by rw [hb, beq_iff_eq.mp e]) h2
  simp only [e1, e2, Bool.false_eq_true, ↓reduceIte]

theorem pStep_of_ok (cfg : ParseCfg) (ts : Bool) {c₁ : Nat → Except ParseErr (Json × Nat)}
    {c₂ : Nat → Except ParseErr PRes} (hc : DoneOn c₁ c₂) {v : Json} {p : Nat}
    (h : valueStep cfg c₁ get n = .ok (v, p)) : pStep cfg ts c₂ get n = .ok (.done v p) := by
  have scalar : get 0 ≠ some 91 → get 0 ≠ some 123 →
      scalarP (valueStep cfg (fun _ => .error ⟨.recursionLimitExceeded, 0⟩) get n) = .ok (.done v p) := by
    intro h1 h2
    rw [valueStep_scalar cfg _ c₁ h1 h2, h]; rfl
  unfold pStep
  split
  · rename_i hg
    unfold valueStep at h
    rw [hg] at h
    simp only [show ((91 : UInt8) == 34) = false from rfl, show ((91 : UInt8) == 91) = true from rfl,
      Bool.false_eq_true, ↓reduceIte] at h
    dsimp only at h ⊢
    generalize get (skipWs get n 1) = g at h ⊢
    split at h
    · cases h; rfl
    · split
      · rename_i heq; cases heq; simp_all
      · exact pElems_of_ok hc h
      · contradiction
    · cases h
  · rename_i hg
    unfold valueStep at h
    rw [hg] at h
    simp only [show ((123 : UInt8) == 34) = false from rfl, show ((123 : UInt8) == 91) = false from rfl,
      show ((123 : UInt8) == 123) = true from rfl, Bool.false_eq_true, ↓reduceIte] at h
    dsimp only at h ⊢
    generalize get (skipWs get n 1) = g at h ⊢
    split at h
    · cases h; rfl
    · exact pMembers_of_ok hc h
    · cases h
    · cases h
  · rename_i hg
    split
    · unfold valueStep at h
      rw [hg] at h
      simp only [show ((34 : UInt8) == 34) = true from rfl, ↓reduceIte, parseString] at h
      cases hs : parseStrBody get n (0 + 1) "" with
      | error e => rw [hs] at h; cases h
      | ok r =>
        rw [hs] at h; cases h
        rw [Nat.zero_add] at hs
        rw [partialStrBody_of_ok hs]
    · exact scalar (by rw [hg]; simp) (by rw [hg]; simp)
  · rename_i h91 h123 _
    exact scalar h91 h123

theorem pGo_of_ok (cfg : ParseCfg) (ts : Bool) : ∀ (d base : Nat) {v : Json} {p : Nat},
    valueGo cfg get n d base = .ok (v, p) → pGo cfg ts get n d base = .ok (.done v p)
  | 0, _, _, _, h => by simp [valueGo] at h
  | d + 1, base, _, _, h => by
    rw [valueGo] at h
    rw [pGo]
    refine pStep_of_ok cfg ts (fun j w q hj => ?_) h
    cases hr : valueGo cfg get n d (base + j) with
    | error e => rw [hr] at hj; cases hj
    | ok r =>
      obtain ⟨w', q'⟩ := r
      rw [hr] at hj; cases hj
      rw [pGo_of_ok cfg ts d (base + j) hr]; rfl

/-- **Partial mode changes nothing on a complete document**: wherever the
document parser succeeds, the partial parser returns the same value. -/
theorem parsePartialIn_complete (cfg : ParseCfg) (mode : PartialMode) {w : Json}
    (h : parseDocumentIn cfg get n = .ok w) : parsePartialIn cfg mode get n = .ok w := by
  unfold parseDocumentIn at h
  cases hv : parseValueIn cfg get n 0 with
  | error e => rw [hv] at h; cases h
  | ok r =>
    obtain ⟨v, p⟩ := r
    rw [hv] at h
    have hw : v = w := by
      dsimp only at h
      by_cases hq : skipWs get n p < n
      · rw [ite_eq_left hq] at h; cases h
      · rw [ite_eq_right hq] at h; cases h; rfl
    subst hw
    unfold parseValueIn at hv
    unfold parsePartialIn
    dsimp only at hv ⊢
    split at hv
    · cases hv
    · rename_i hq
      rw [hq]
      dsimp only
      cases hr : valueGo cfg get n (cfg.budget n) (skipWs get n 0) with
      | error e => rw [hr] at hv; cases hv
      | ok r =>
        obtain ⟨v', p'⟩ := r
        rw [hr] at hv
        simp only [shiftRes, Except.ok.injEq, Prod.mk.injEq] at hv
        rw [pGo_of_ok cfg _ _ _ hr, ← hv.1]
        rfl

theorem parsePartialWith_complete (cfg : ParseCfg) (mode : PartialMode) {bs : ByteArray} {w : Json}
    (h : parseDocumentWith cfg bs = .ok w) : parsePartialWith cfg mode bs = .ok w :=
  parsePartialIn_complete cfg mode h

end LeanJson
