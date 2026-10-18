import LeanJson.Proofs.View

/-!
# Proofs: progress of the lexical productions

`Adv n p q`: the cursor moved forward from `p` to `q`, only over bytes the
view (of length `n`) holds. Every lexical production advances this way, and
every one that succeeds consumes at least one byte. Stated for any view that
reads nothing past its length (`ViewOk`).
-/

namespace LeanJson

variable {get : Nat → Option UInt8} {n : Nat}

theorem skipWs_adv (hv : ViewOk get n) (pos : Nat) : Adv n pos (skipWs get n pos) := by
  unfold skipWs
  split
  · rename_i h
    split
    · split
      · exact (Adv.of_lt (Nat.le_succ pos) h).trans (skipWs_adv hv (pos + 1))
      · exact Adv.refl _ _
    · exact Adv.refl _ _
  · exact Adv.refl _ _
termination_by n - pos

theorem skipWs_ge (get : Nat → Option UInt8) (n pos : Nat) : pos ≤ skipWs get n pos := by
  unfold skipWs
  split
  · split
    · split
      · have := skipWs_ge get n (pos + 1); omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  · exact Nat.le_refl _
termination_by n - pos

theorem expectLit_adv (hv : ViewOk get n) : ∀ (p : Nat) (lit : List UInt8) (q : Nat),
    expectLit get p lit = .ok q → Adv n p q
  | p, [], q, h => by simp [expectLit] at h; subst h; exact Adv.refl _ _
  | p, c :: cs, q, h => by
    unfold expectLit at h
    split at h
    · cases h
    · rename_i b hb
      split at h
      · exact (Adv.step hv hb).trans (expectLit_adv hv (p + 1) cs q h)
      · cases h

theorem scanDigits_adv (hv : ViewOk get n) (pos cnt : Nat) : Adv n pos (scanDigits get n pos cnt).2 := by
  unfold scanDigits
  split
  · rename_i h
    split
    · split
      · exact (Adv.of_lt (Nat.le_succ pos) h).trans (scanDigits_adv hv (pos + 1) (cnt + 1))
      · exact Adv.refl _ _
    · exact Adv.refl _ _
  · exact Adv.refl _ _
termination_by n - pos

theorem scanDigits_move (hv : ViewOk get n) {pos cnt : Nat} {b : UInt8} (hb : get pos = some b)
    (hd : isDigit b = true) : pos < (scanDigits get n pos cnt).2 := by
  have hlt := hv _ _ hb
  unfold scanDigits
  simp only [hlt, ↓reduceIte]
  simp only [hb, hd, ↓reduceIte]
  have := (scanDigits_adv hv (pos + 1) (cnt + 1)).1
  omega

theorem digits1_adv (hv : ViewOk get n) {pos : Nat} {r : Nat × Nat × Nat} (h : digits1 get n pos = .ok r) :
    Adv n pos r.2.2 := by
  unfold digits1 at h
  simp only at h
  by_cases hc : (scanDigits get n pos 0).1 = 0
  · rw [ite_eq_left hc] at h; split at h <;> cases h
  · rw [ite_eq_right hc] at h; cases h; exact scanDigits_adv hv pos _

theorem parseIntPart_adv (hv : ViewOk get n) {pos : Nat} {r : Nat × Nat} (h : parseIntPart get n pos = .ok r) :
    Adv n pos r.2 ∧ pos < r.2 := by
  unfold parseIntPart at h
  split at h
  · cases h
  · rename_i b hb
    split at h
    · split at h
      · split at h
        · cases h
        · cases h; exact ⟨Adv.step hv hb, by simp⟩
      · cases h; exact ⟨Adv.step hv hb, by simp⟩
    · split at h
      · cases h
        rename_i hd
        exact ⟨scanDigits_adv hv pos _, scanDigits_move hv hb hd⟩
      · cases h

theorem parseFrac_adv (hv : ViewOk get n) {pos : Nat} {r : Nat × Nat × Nat} (h : parseFrac get n pos = .ok r) :
    Adv n pos r.2.2 := by
  unfold parseFrac at h
  split at h
  · rename_i hb; exact (Adv.step hv hb).trans (digits1_adv hv h)
  · cases h; exact Adv.refl _ _

theorem parseExp_adv (hv : ViewOk get n) {pos : Nat} {r : Bool × Int × Nat} (h : parseExp get n pos = .ok r) :
    Adv n pos r.2.2 := by
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
          exact ((Adv.step hv hb).trans (Adv.step hv hb1)).trans (digits1_adv hv hx)
      · rename_i hb1
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i x hx; cases h
          exact ((Adv.step hv hb).trans (Adv.step hv hb1)).trans (digits1_adv hv hx)
      · simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i x hx; cases h
          exact (Adv.step hv hb).trans (digits1_adv hv hx)
    · cases h; exact Adv.refl _ _
  · cases h; exact Adv.refl _ _

theorem parseNumberBody_adv (hv : ViewOk get n) {cfg : ParseCfg} {pos p0 : Nat} {neg : Bool}
    {r : Number × Nat} (hp0 : Adv n pos p0) (h : parseNumberBody cfg get n pos neg p0 = .ok r) :
    Adv n pos r.2 ∧ pos < r.2 := by
  unfold parseNumberBody at h
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
        have a1 := parseIntPart_adv hv h1
        have a2 := parseFrac_adv hv h2
        have a3 := parseExp_adv hv h3
        refine ⟨((hp0.trans a1.1).trans a2).trans a3, ?_⟩
        have b0 := hp0.1; have b1 := a1.2; have b2 := a2.1; have b3 := a3.1
        exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt b0 b1) (Nat.le_trans b2 b3)

theorem parseNumber_adv (hv : ViewOk get n) {cfg : ParseCfg} {pos : Nat} {r : Number × Nat}
    (h : parseNumber cfg get n pos = .ok r) : Adv n pos r.2 ∧ pos < r.2 := by
  unfold parseNumber at h
  by_cases c45 : (get pos == some 45) = true
  · rw [ite_eq_left c45] at h
    have h45 : get pos = some 45 := by simpa using c45
    by_cases ci : (cfg.allowInfNan && get (pos + 1) == some 73) = true
    · rw [ite_eq_left ci] at h
      have h73 : get (pos + 1) = some 73 := by simp at ci; exact ci.2
      cases hl : expectLit get (pos + 2) [110, 102, 105, 110, 105, 116, 121] with
      | error e => rw [hl] at h; cases h
      | ok p =>
        rw [hl] at h; cases h
        have a := expectLit_adv hv _ _ _ hl
        exact ⟨((Adv.step hv h45).trans (Adv.step hv h73)).trans a, by have := a.1; simp; omega⟩
    · rw [ite_eq_right ci] at h
      exact parseNumberBody_adv hv (Adv.step hv h45) h
  · rw [ite_eq_right c45] at h
    exact parseNumberBody_adv hv (Adv.refl _ _) h

theorem parseHex4_adv {p m : Nat} (h : parseHex4 get n p = .ok m) : Adv n p (p + 4) := by
  unfold parseHex4 at h
  split at h
  · cases h
  · rename_i hs; exact Adv.of_lt (by omega) (by omega)

theorem parseEscape_adv (hv : ViewOk get n) {q : Nat} {r : Char × Nat} (h : parseEscape get n q = .ok r) :
    Adv n q r.2 ∧ q < r.2 := by
  unfold parseEscape at h
  split at h
  · cases h
  · rename_i b hb
    have s1 := Adv.step hv hb
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
                  have a2 := ((a1.trans (Adv.step hv (by simpa [Nat.add_assoc] using h5))).trans
                    (Adv.step hv (by simpa [Nat.add_assoc] using h6))).trans (parseHex4_adv hl)
                  exact ⟨by simpa [Nat.add_assoc] using a2, by simp⟩
                · cases h
            · cases h
          · cases h
        · cases h
          exact ⟨by simpa [Nat.add_assoc] using a1, by simp⟩
    · rw [ite_eq_right c117] at h; cases h

theorem window_size_le (hv : ViewOk get n) (pos : Nat) : pos + (window get pos).size ≤ n ∨
    (window get pos).size = 0 := by
  unfold window
  split
  · right; rfl
  · rename_i b0 h0
    have := hv _ _ h0
    split
    · left; simp; omega
    · rename_i b1 h1
      have := hv _ _ h1
      split
      · left; simp; omega
      · rename_i b2 h2
        have := hv _ _ h2
        split
        · left; simp; omega
        · rename_i b3 h3
          have := hv _ _ h3
          left; simp; omega

theorem decodeChar_le (hv : ViewOk get n) {pos : Nat} {c : Char} (h : decodeChar? get pos = some c) :
    pos + c.utf8Size ≤ n := by
  unfold decodeChar? at h
  have h1 := ByteArray.le_size_of_utf8DecodeChar?_eq_some h
  have hp := c.utf8Size_pos
  rcases window_size_le hv pos with h2 | h2 <;> omega

theorem parseStrBody_adv (hv : ViewOk get n) (pos : Nat) (acc : String) (r : String × Nat)
    (h : parseStrBody get n pos acc = .ok r) : Adv n pos r.2 ∧ pos < r.2 := by
  unfold parseStrBody at h
  split at h
  · rename_i hlt
    have s1 : Adv n pos (pos + 1) := Adv.of_lt (Nat.le_succ pos) hlt
    split at h
    · cases h
    rename_i b hb
    by_cases c1 : (b == 34) = true
    · rw [ite_eq_left c1] at h; cases h; exact ⟨s1, Nat.lt_succ_self _⟩
    rw [ite_eq_right c1] at h
    by_cases c2 : (b == 92) = true
    · rw [ite_eq_left c2] at h
      split at h
      · rename_i c p he
        have a1 := parseEscape_adv hv he
        have a2 := parseStrBody_adv hv p _ r h
        exact ⟨(s1.trans a1.1).trans a2.1, by have := a1.2; have := a2.2; simp at *; omega⟩
      · cases h
    rw [ite_eq_right c2] at h
    by_cases c3 : b < 32
    · rw [ite_eq_left c3] at h; cases h
    rw [ite_eq_right c3] at h
    by_cases c4 : b < 128
    · rw [ite_eq_left c4] at h
      have a2 := parseStrBody_adv hv (pos + 1) _ r h
      exact ⟨s1.trans a2.1, by have := a2.2; omega⟩
    rw [ite_eq_right c4] at h
    split at h
    · rename_i c hc
      have hle := decodeChar_le hv hc
      have hpos := c.utf8Size_pos
      have a2 := parseStrBody_adv hv (pos + c.utf8Size) _ r h
      exact ⟨(Adv.of_lt (by omega) hle).trans a2.1, by have := a2.2; omega⟩
    · cases h
  · cases h
termination_by n - pos
decreasing_by
  all_goals first
    | omega
    | (have := parseEscape_next he; simp at this; omega)

theorem parseString_adv (hv : ViewOk get n) {pos : Nat} {r : String × Nat}
    (h : parseString get n pos = .ok r) : Adv n pos r.2 ∧ pos < r.2 := by
  unfold parseString at h
  have a := parseStrBody_adv hv _ _ _ h
  exact ⟨⟨by have := a.2; have := a.1.1; omega, fun _ => a.1.2 a.2⟩, by have := a.2; omega⟩

/-- A literal: its first byte at `q`, the rest matched from `q + 1`. -/
theorem litAdv (hv : ViewOk get n) {q p : Nat} {b : UInt8} {lit : List UInt8} (hb : get q = some b)
    (hl : expectLit get (q + 1) lit = .ok p) : Adv n q p ∧ q < p :=
  ⟨(Adv.step hv hb).trans (expectLit_adv hv _ _ _ hl), by have := (expectLit_adv hv _ _ _ hl).1; omega⟩

end LeanJson
