import LeanJson.RepoImpl.Str

/-!
# RepoImpl: progress of the lexical productions

`Adv bs p q`: the cursor moved forward from `p` to `q`, only over bytes that
exist. Every lexical production advances this way, and every one that
succeeds consumes at least one byte. These facts are what make the value
parser's recursion well founded (`RepoImpl/Parse.lean`), so they live with the
definitions rather than in `Proofs/`.
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

theorem skipWs_adv (bs : ByteArray) (pos : Nat) : Adv bs pos (skipWs bs pos) := by
  unfold skipWs
  split
  · rename_i h
    split
    · exact (Adv.of_lt (Nat.le_succ pos) h).trans (skipWs_adv bs (pos + 1))
    · exact Adv.refl _ _
  · exact Adv.refl _ _
termination_by bs.size - pos

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

theorem scanDigits_adv (bs : ByteArray) (pos cnt : Nat) : Adv bs pos (scanDigits bs pos cnt).2 := by
  unfold scanDigits
  split
  · rename_i h
    split
    · exact (Adv.of_lt (Nat.le_succ pos) h).trans (scanDigits_adv bs (pos + 1) (cnt + 1))
    · exact Adv.refl _ _
  · exact Adv.refl _ _
termination_by bs.size - pos

theorem getElem_of_get {bs : ByteArray} {i : Nat} {b : UInt8} (h : bs[i]? = some b) (hi : i < bs.size) :
    bs[i] = b := by
  rw [getElem?_pos bs i hi] at h; exact Option.some.inj h

theorem scanDigits_move {bs : ByteArray} {pos cnt : Nat} {b : UInt8} (hb : bs[pos]? = some b)
    (hd : isDigit b = true) : pos < (scanDigits bs pos cnt).2 := by
  have hlt := lt_size_of_get hb
  unfold scanDigits
  rw [dite_eq_left hlt, getElem_of_get hb hlt, ite_eq_left hd]
  have := (scanDigits_adv bs (pos + 1) (cnt + 1)).1
  omega

theorem digits1_adv {bs : ByteArray} {pos : Nat} {r : Nat × Nat × Nat} (h : digits1 bs pos = .ok r) :
    Adv bs pos r.2.2 := by
  unfold digits1 at h
  simp only at h
  by_cases hc : (scanDigits bs pos 0).1 = 0
  · rw [ite_eq_left hc] at h; split at h <;> cases h
  · rw [ite_eq_right hc] at h; cases h; exact scanDigits_adv bs pos _

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
        exact ⟨scanDigits_adv bs pos _, scanDigits_move hb hd⟩
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

theorem parseNumber_adv {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {r : Number × Nat}
    (h : parseNumber cfg bs pos = .ok r) : Adv bs pos r.2 ∧ pos < r.2 := by
  unfold parseNumber at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i x1 h1
    split at h
    · cases h
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
  · cases h
  · rename_i hs; exact Adv.of_lt (by omega) (by omega)

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
          · cases h
          · rename_i h5
            split at h
            · cases h
            · rename_i h6
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
        · cases h
          exact ⟨by simpa [Nat.add_assoc] using a1, by simp⟩
    · rw [ite_eq_right c117] at h; cases h

theorem parseStrBody_adv (bs : ByteArray) (pos : Nat) (acc : List Char) (r : List Char × Nat)
    (h : parseStrBody bs pos acc = .ok r) : Adv bs pos r.2 ∧ pos < r.2 := by
  unfold parseStrBody at h
  split at h
  · rename_i hlt
    have s1 : Adv bs pos (pos + 1) := Adv.of_lt (Nat.le_succ pos) hlt
    simp only at h
    by_cases c1 : (bs[pos] == 34) = true
    · rw [ite_eq_left c1] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c1] at h
    by_cases c2 : (bs[pos] == 92) = true
    · rw [ite_eq_left c2] at h
      split at h
      · rename_i c p he
        have a1 := parseEscape_adv he
        have a2 := parseStrBody_adv bs p _ r h
        exact ⟨(s1.trans a1.1).trans a2.1, by have := a1.2; have := a2.2; simp at *; omega⟩
      · cases h
    rw [ite_eq_right c2] at h
    by_cases c3 : bs[pos] < 32
    · rw [ite_eq_left c3] at h; cases h
    rw [ite_eq_right c3] at h
    by_cases c4 : bs[pos] < 128
    · rw [ite_eq_left c4] at h
      have a2 := parseStrBody_adv bs (pos + 1) _ r h
      exact ⟨s1.trans a2.1, by have := a2.2; omega⟩
    rw [ite_eq_right c4] at h
    split at h
    · rename_i c hc
      have hle := ByteArray.le_size_of_utf8DecodeChar?_eq_some hc
      have hpos := c.utf8Size_pos
      have a2 := parseStrBody_adv bs (pos + c.utf8Size) _ r h
      exact ⟨(Adv.of_lt (by omega) hle).trans a2.1, by have := a2.2; omega⟩
    · cases h
  · cases h
termination_by bs.size - pos
decreasing_by
  all_goals first
    | omega
    | (have := parseEscape_next he; simp at this; omega)

theorem parseString_adv {bs : ByteArray} {pos : Nat} {r : String × Nat} (h : parseString bs pos = .ok r) :
    Adv bs pos r.2 ∧ pos < r.2 := by
  unfold parseString at h
  split at h
  · rename_i cs p he
    cases h
    have a := parseStrBody_adv bs _ _ _ he
    -- the opening quote exists because the body parse read a byte at pos + 1 or beyond
    refine ⟨⟨by have := a.2; simp at *; omega, fun _ => a.1.2 a.2⟩, by have := a.2; simp at *; omega⟩
  · cases h

/-- A literal: its first byte at `q`, the rest matched from `q + 1`. -/
theorem litAdv {bs : ByteArray} {q p : Nat} {b : UInt8} {lit : List UInt8} (hb : bs[q]? = some b)
    (hl : expectLit bs (q + 1) lit = .ok p) (_ : lit ≠ []) : Adv bs q p ∧ q < p :=
  ⟨(Adv.step hb).trans (expectLit_adv bs _ _ _ hl), by have := (expectLit_adv bs _ _ _ hl).1; omega⟩

end LeanJson
