import LeanJson.Proofs.Value

/-!
# Proofs: progress and bounds

Every successful production consumes at least one byte and never moves the
cursor past the end of the input (`step_progress`). `Adv bs p q` says the
cursor moved from `p` to `q` only over bytes that exist.
-/

namespace LeanJson

/-- The cursor moved forward from `p` to `q`, and if it moved at all it stayed
within the buffer. -/
def Adv (bs : ByteArray) (p q : Nat) : Prop := p ≤ q ∧ (p < q → q ≤ bs.size)

theorem Adv.refl (bs : ByteArray) (p : Nat) : Adv bs p p := ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem Adv.trans {bs : ByteArray} {p q r : Nat} (h1 : Adv bs p q) (h2 : Adv bs q r) : Adv bs p r := by
  obtain ⟨a1, b1⟩ := h1; obtain ⟨a2, b2⟩ := h2
  refine ⟨Nat.le_trans a1 a2, fun h => ?_⟩
  by_cases hqr : q < r
  · exact b2 hqr
  · have : q = r := by omega
    subst this; exact b1 h

theorem lt_size_of_get {bs : ByteArray} {i : Nat} {b : UInt8} (h : bs[i]? = some b) : i < bs.size := by
  by_cases hi : i < bs.size
  · exact hi
  · rw [getElem?_neg bs i hi] at h; cases h

theorem Adv.step {bs : ByteArray} {p : Nat} {b : UInt8} (h : bs[p]? = some b) : Adv bs p (p + 1) :=
  ⟨by omega, fun _ => lt_size_of_get h⟩

theorem Adv.of_lt {bs : ByteArray} {p q : Nat} (h1 : p ≤ q) (h2 : q ≤ bs.size) : Adv bs p q :=
  ⟨h1, fun _ => h2⟩

theorem skipWs_adv (bs : ByteArray) : ∀ (pos f : Nat), Adv bs pos (skipWs bs pos f)
  | pos, 0 => Adv.refl _ _
  | pos, f + 1 => by
    unfold skipWs
    split
    · rename_i b hb
      split
      · exact (Adv.step hb).trans (skipWs_adv bs (pos + 1) f)
      · exact Adv.refl _ _
    · exact Adv.refl _ _

theorem expectLit_adv (bs : ByteArray) : ∀ (p : Nat) (lit : List UInt8) (q : Nat),
    expectLit bs p lit = .ok q → Adv bs p q
  | p, [], q, h => by simp [expectLit] at h; subst h; exact Adv.refl _ _
  | p, c :: cs, q, h => by
    unfold expectLit at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · exact (Adv.step hb).trans (expectLit_adv bs (p + 1) cs q h)
      · cases h

theorem scanDigits_adv (bs : ByteArray) : ∀ (pos f acc cnt : Nat), Adv bs pos (scanDigits bs pos f acc cnt).2.2
  | pos, 0, _, _ => Adv.refl _ _
  | pos, f + 1, acc, cnt => by
    unfold scanDigits
    split
    · rename_i b hb
      split
      · exact (Adv.step hb).trans (scanDigits_adv bs (pos + 1) f _ _)
      · exact Adv.refl _ _
    · exact Adv.refl _ _

theorem scanDigits_move {bs : ByteArray} {pos f acc cnt : Nat} {b : UInt8} (hb : bs[pos]? = some b)
    (hd : isDigit b = true) (hf : 0 < f) : pos < (scanDigits bs pos f acc cnt).2.2 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  simp only [scanDigits, hb, hd, ↓reduceIte]
  have := (scanDigits_adv bs (pos + 1) g (acc * 10 + (b.toNat - 48)) (cnt + 1)).1
  omega

theorem digits1_adv {bs : ByteArray} {pos : Nat} {r : Nat × Nat × Nat} (h : digits1 bs pos = .ok r) :
    Adv bs pos r.2.2 := by
  unfold digits1 at h
  simp only at h
  by_cases hc : (scanDigits bs pos bs.size 0 0).2.1 = 0
  · rw [ite_eq_left hc] at h; split at h <;> cases h
  · rw [ite_eq_right hc] at h; cases h; exact scanDigits_adv bs pos _ _ _

theorem parseIntPart_adv {bs : ByteArray} {pos : Nat} {r : Nat × Nat} (h : parseIntPart bs pos = .ok r) :
    Adv bs pos r.2 ∧ pos < r.2 := by
  unfold parseIntPart at h
  split at h
  · cases h
  · rename_i b hb
    split at h
    · split at h
      · split at h
        · cases h
        · cases h; exact ⟨Adv.step hb, by simp⟩
      · cases h; exact ⟨Adv.step hb, by simp⟩
    · split at h
      · cases h
        rename_i hd
        exact ⟨scanDigits_adv bs pos _ _ _, scanDigits_move hb hd (by have := lt_size_of_get hb; omega)⟩
      · cases h

theorem parseFrac_adv {bs : ByteArray} {pos : Nat} {r : Nat × Nat × Nat} (h : parseFrac bs pos = .ok r) :
    Adv bs pos r.2.2 := by
  unfold parseFrac at h
  split at h
  · rename_i hb; exact (Adv.step hb).trans (digits1_adv h)
  · cases h; exact Adv.refl _ _

theorem parseExp_adv {bs : ByteArray} {pos : Nat} {r : Bool × Int × Nat} (h : parseExp bs pos = .ok r) :
    Adv bs pos r.2.2 := by
  unfold parseExp at h
  split at h
  · rename_i b hb
    split at h
    · split at h
      · rename_i hb1
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i x hx; cases h
          exact ((Adv.step hb).trans (Adv.step hb1)).trans (digits1_adv hx)
      · rename_i hb1
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i x hx; cases h
          exact ((Adv.step hb).trans (Adv.step hb1)).trans (digits1_adv hx)
      · simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i x hx; cases h
          exact (Adv.step hb).trans (digits1_adv hx)
    · cases h; exact Adv.refl _ _
  · cases h; exact Adv.refl _ _

theorem parseNumber_adv {bs : ByteArray} {pos : Nat} {r : Number × Nat} (h : parseNumber bs pos = .ok r) :
    Adv bs pos r.2 ∧ pos < r.2 := by
  unfold parseNumber at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i x1 h1
    split at h
    · cases h
    · rename_i x2 h2
      split at h
      · cases h
      · rename_i x3 h3
        cases h
        have a1 := parseIntPart_adv h1
        have a2 := parseFrac_adv h2
        have a3 := parseExp_adv h3
        have a0 : Adv bs pos (if (bs[pos]? == some 45) = true then pos + 1 else pos) := by
          split
          · rename_i hh
            have : bs[pos]? = some 45 := by simpa using hh
            exact Adv.step this
          · exact Adv.refl _ _
        refine ⟨((a0.trans a1.1).trans a2).trans a3, ?_⟩
        have b0 := a0.1; have b1 := a1.2; have b2 := a2.1; have b3 := a3.1
        exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt b0 b1) (Nat.le_trans b2 b3)

theorem hexAt_ok {bs : ByteArray} {i n : Nat} (h : hexAt bs i = .ok n) : i < bs.size := by
  unfold hexAt at h
  split at h
  · cases h
  · rename_i b hb; exact lt_size_of_get hb

theorem parseHex4_adv {bs : ByteArray} {p n : Nat} (h : parseHex4 bs p = .ok n) : Adv bs p (p + 4) := by
  unfold parseHex4 at h
  split at h
  · rename_i h3; exact Adv.of_lt (by omega) (by have := hexAt_ok h3; omega)
  all_goals cases h

theorem parseEscape_adv {bs : ByteArray} {q : Nat} {r : Char × Nat} (h : parseEscape bs q = .ok r) :
    Adv bs q r.2 ∧ q < r.2 := by
  unfold parseEscape at h
  split at h
  · cases h
  · rename_i b hb
    have s1 := Adv.step hb
    by_cases c34 : (b == 34) = true
    · rw [ite_eq_left c34] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c34] at h
    by_cases c92 : (b == 92) = true
    · rw [ite_eq_left c92] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c92] at h
    by_cases c47 : (b == 47) = true
    · rw [ite_eq_left c47] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c47] at h
    by_cases c98 : (b == 98) = true
    · rw [ite_eq_left c98] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c98] at h
    by_cases c102 : (b == 102) = true
    · rw [ite_eq_left c102] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c102] at h
    by_cases c110 : (b == 110) = true
    · rw [ite_eq_left c110] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c110] at h
    by_cases c114 : (b == 114) = true
    · rw [ite_eq_left c114] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c114] at h
    by_cases c116 : (b == 116) = true
    · rw [ite_eq_left c116] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c116] at h
    by_cases c117 : (b == 117) = true
    · rw [ite_eq_left c117] at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i u hu
        have a1 := s1.trans (parseHex4_adv hu)
        split at h
        · cases h
        split at h
        · split at h
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            obtain ⟨h5, h6⟩ := hc
            try simp only [bind, Except.bind] at h
            split at h
            · cases h
            · rename_i l hl
              split at h
              · have hr := (Except.ok.inj h).symm
                rw [hr]
                have a2 := ((a1.trans (Adv.step (by simpa [Nat.add_assoc] using h5))).trans
                  (Adv.step (by simpa [Nat.add_assoc] using h6))).trans (parseHex4_adv hl)
                exact ⟨by simpa [Nat.add_assoc] using a2, by simp⟩
              · cases h
          · cases h
        · cases h
          exact ⟨by simpa [Nat.add_assoc] using a1, by simp⟩
    · rw [ite_eq_right c117] at h; cases h

theorem parseStrBody_adv (bs : ByteArray) : ∀ (f pos : Nat) (acc : List Char) (r : List Char × Nat),
    parseStrBody bs pos f acc = .ok r → Adv bs pos r.2 ∧ pos < r.2
  | 0, pos, acc, r, h => by simp [parseStrBody] at h
  | f + 1, pos, acc, r, h => by
    unfold parseStrBody at h
    split at h
    · cases h
    · rename_i b hb
      have s1 := Adv.step hb
      by_cases c1 : (b == 34) = true
      · rw [ite_eq_left c1] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
      rw [ite_eq_right c1] at h
      by_cases c2 : (b == 92) = true
      · rw [ite_eq_left c2] at h
        split at h
        · rename_i c p he
          have a1 := parseEscape_adv he
          have a2 := parseStrBody_adv bs f p _ r h
          exact ⟨(s1.trans a1.1).trans a2.1, by have := a1.2; have := a2.2; simp at *; omega⟩
        · cases h
      rw [ite_eq_right c2] at h
      by_cases c3 : b < 32
      · rw [ite_eq_left c3] at h; cases h
      rw [ite_eq_right c3] at h
      by_cases c4 : b < 128
      · rw [ite_eq_left c4] at h
        have a2 := parseStrBody_adv bs f (pos + 1) _ r h
        exact ⟨s1.trans a2.1, by have := a2.2; omega⟩
      rw [ite_eq_right c4] at h
      split at h
      · rename_i c hc
        have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some hc
        have hpos := c.utf8Size_pos
        have a2 := parseStrBody_adv bs f (pos + c.utf8Size) _ r h
        exact ⟨(Adv.of_lt (by omega) hle).trans a2.1, by have := a2.2; omega⟩
      · cases h

theorem parseString_adv {bs : ByteArray} {pos : Nat} {r : String × Nat} (h : parseString bs pos = .ok r) :
    Adv bs pos r.2 ∧ pos < r.2 := by
  unfold parseString at h
  split at h
  · rename_i cs p he
    cases h
    have a := parseStrBody_adv bs _ _ _ _ he
    -- the opening quote exists because the body parse read a byte at pos + 1 or beyond
    refine ⟨⟨by have := a.2; simp at *; omega, fun _ => a.1.2 a.2⟩, by have := a.2; simp at *; omega⟩
  · cases h

mutual
theorem parseValue_adv (bs : ByteArray) : ∀ (n pos : Nat) (r : Json × Nat),
    parseValue bs pos n = .ok r → Adv bs pos r.2 ∧ pos < r.2
  | 0, pos, r, h => by simp [parseValue] at h
  | n + 1, pos, r, h => by
    unfold parseValue at h
    simp only at h
    have a0 := skipWs_adv bs pos bs.size
    generalize skipWs bs pos bs.size = q at h a0
    split at h
    · cases h
    · rename_i b hb
      have s1 := a0.trans (Adv.step hb)
      have lt1 : pos < q + 1 := by have := a0.1; omega
      by_cases c34 : (b == 34) = true
      · rw [ite_eq_left c34] at h
        split at h
        · rename_i s p hs
          cases h
          have a := parseString_adv hs
          exact ⟨a0.trans a.1, by have := a0.1; have := a.2; simp at *; omega⟩
        · cases h
      rw [ite_eq_right c34] at h
      by_cases c91 : (b == 91) = true
      · rw [ite_eq_left c91] at h
        have a1 := s1.trans (skipWs_adv bs (q + 1) bs.size)
        generalize skipWs bs (q + 1) bs.size = p at h a1
        split at h
        · cases h
        · rename_i hp; cases h
          exact ⟨a1.trans (Adv.step hp), by have := a1.1; simp; omega⟩
        · have a := parseElems_adv bs n p [] r h
          exact ⟨a1.trans a.1, by have := a1.1; have := a.2; omega⟩
      rw [ite_eq_right c91] at h
      by_cases c123 : (b == 123) = true
      · rw [ite_eq_left c123] at h
        have a1 := s1.trans (skipWs_adv bs (q + 1) bs.size)
        generalize skipWs bs (q + 1) bs.size = p at h a1
        split at h
        · cases h
        · rename_i hp; cases h
          exact ⟨a1.trans (Adv.step hp), by have := a1.1; simp; omega⟩
        · have a := parseMembers_adv bs n p [] r h
          exact ⟨a1.trans a.1, by have := a1.1; have := a.2; omega⟩
        · cases h
      rw [ite_eq_right c123] at h
      by_cases c116 : (b == 116) = true
      · rw [ite_eq_left c116] at h
        split at h
        · rename_i p hp; cases h
          have a := expectLit_adv bs _ _ _ hp
          exact ⟨s1.trans a, by have := a.1; simp; omega⟩
        · cases h
      rw [ite_eq_right c116] at h
      by_cases c102 : (b == 102) = true
      · rw [ite_eq_left c102] at h
        split at h
        · rename_i p hp; cases h
          have a := expectLit_adv bs _ _ _ hp
          exact ⟨s1.trans a, by have := a.1; simp; omega⟩
        · cases h
      rw [ite_eq_right c102] at h
      by_cases c110 : (b == 110) = true
      · rw [ite_eq_left c110] at h
        split at h
        · rename_i p hp; cases h
          have a := expectLit_adv bs _ _ _ hp
          exact ⟨s1.trans a, by have := a.1; simp; omega⟩
        · cases h
      rw [ite_eq_right c110] at h
      by_cases cn : (b == 45 || isDigit b) = true
      · rw [ite_eq_left cn] at h
        split at h
        · rename_i x p hp; cases h
          have a := parseNumber_adv hp
          exact ⟨a0.trans a.1, by have := a0.1; have := a.2; simp at *; omega⟩
        · cases h
      rw [ite_eq_right cn] at h
      cases h
theorem parseElems_adv (bs : ByteArray) : ∀ (n pos : Nat) (acc : List Json) (r : Json × Nat),
    parseElems bs pos n acc = .ok r → Adv bs pos r.2 ∧ pos < r.2
  | 0, pos, acc, r, h => by simp [parseElems] at h
  | n + 1, pos, acc, r, h => by
    unfold parseElems at h
    split at h
    · cases h
    · rename_i v p1 hv
      have a1 := parseValue_adv bs n pos _ hv
      simp only at a1 h
      have a2 := a1.1.trans (skipWs_adv bs p1 bs.size)
      generalize skipWs bs p1 bs.size = p at h a2
      split at h
      · cases h
      · rename_i hp
        have a3 := (a2.trans (Adv.step hp)).trans (skipWs_adv bs (p + 1) bs.size)
        generalize skipWs bs (p + 1) bs.size = q at h a3
        split at h
        · cases h
        · have a := parseElems_adv bs n q _ r h
          exact ⟨a3.trans a.1, by have := a1.2; have := a2.1; have := a3.1; have := a.2; omega⟩
      · rename_i hp; cases h
        exact ⟨a2.trans (Adv.step hp), by have := a1.2; have := a2.1; simp; omega⟩
      · cases h
theorem parseMembers_adv (bs : ByteArray) : ∀ (n pos : Nat) (acc : List (String × Json)) (r : Json × Nat),
    parseMembers bs pos n acc = .ok r → Adv bs pos r.2 ∧ pos < r.2
  | 0, pos, acc, r, h => by simp [parseMembers] at h
  | n + 1, pos, acc, r, h => by
    unfold parseMembers at h
    split at h
    · cases h
    · rename_i k p1 hk
      have a1 := parseString_adv hk
      simp only at a1 h
      have a2 := a1.1.trans (skipWs_adv bs p1 bs.size)
      generalize skipWs bs p1 bs.size = p at h a2
      split at h
      · cases h
      · rename_i hp
        split at h
        · cases h
        · rename_i v p2 hv
          have a3 := (a2.trans (Adv.step hp)).trans (parseValue_adv bs n (p + 1) _ hv).1
          have a4 := a3.trans (skipWs_adv bs p2 bs.size)
          generalize skipWs bs p2 bs.size = p3 at h a4
          split at h
          · cases h
          · rename_i hp3
            have a5 := (a4.trans (Adv.step hp3)).trans (skipWs_adv bs (p3 + 1) bs.size)
            generalize skipWs bs (p3 + 1) bs.size = q at h a5
            split at h
            · cases h
            · have a := parseMembers_adv bs n q _ r h
              exact ⟨a5.trans a.1, by have := a1.2; have := a2.1; have := a5.1; have := a.2; omega⟩
            · cases h
            · cases h
          · rename_i hp3; cases h
            exact ⟨a4.trans (Adv.step hp3), by have := a1.2; have := a4.1; simp; omega⟩
          · cases h
      · cases h
end

/-- **Step progress**: a successful value parse consumes at least one byte and
ends within the buffer. -/
theorem step_progress : Spec.StepProgress parseValue := by
  intro bs pos fuel v p h
  have a := parseValue_adv bs fuel pos (v, p) h
  exact ⟨a.2, a.1.2 a.2⟩

end LeanJson
