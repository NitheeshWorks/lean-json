import LeanJson.Proofs.Progress

/-!
# Proofs: fuel

The value parser recurses on fuel. `parse_fuel_enough`: a budget of
`2 * (size - pos) + 1` never runs out, so the public entry points never
report `recursionLimitExceeded`. `parse_fuel_mono`: more fuel never changes
an answer that was not a fuel failure.
-/

namespace LeanJson

/-- The result is not a fuel failure. -/
def NotFuel {α : Type} (r : Except ParseErr α) : Prop :=
  ∀ e, r = .error e → e.kind ≠ .recursionLimitExceeded

theorem expectLit_nofuel (bs : ByteArray) : ∀ (p : Nat) (lit : List UInt8), NotFuel (expectLit bs p lit)
  | p, [] => by intro e he; simp [expectLit] at he
  | p, c :: cs => by
    intro e he
    unfold expectLit at he
    split at he
    · cases he; simp
    · split at he
      · exact expectLit_nofuel bs (p + 1) cs e he
      · cases he; simp

theorem digits1_nofuel (bs : ByteArray) (p : Nat) : NotFuel (digits1 bs p) := by
  intro e he
  unfold digits1 at he
  simp only at he
  split at he
  · split at he <;> (cases he; simp)
  · cases he

theorem parseIntPart_nofuel (bs : ByteArray) (p : Nat) : NotFuel (parseIntPart bs p) := by
  intro e h1
  unfold parseIntPart at h1
  repeat' split at h1
  all_goals first | (cases h1; simp) | cases h1

theorem parseFrac_nofuel (bs : ByteArray) (p : Nat) : NotFuel (parseFrac bs p) := by
  intro e h2
  unfold parseFrac at h2
  split at h2
  · exact digits1_nofuel bs _ e h2
  · cases h2

theorem parseExp_nofuel (bs : ByteArray) (p : Nat) : NotFuel (parseExp bs p) := by
  intro e h3
  unfold parseExp at h3
  repeat' split at h3
  all_goals first | (cases h3; simp) | cases h3 | skip
  all_goals
    simp only [bind, Except.bind] at h3
    split at h3
    · rename_i e' hd; cases h3; exact digits1_nofuel bs _ _ hd
    · cases h3

theorem parseNumber_nofuel (cfg : ParseCfg) (bs : ByteArray) (p : Nat) : NotFuel (parseNumber cfg bs p) := by
  intro e he
  unfold parseNumber at he
  simp only [bind, Except.bind] at he
  split at he
  · rename_i e' h1; cases he; exact parseIntPart_nofuel bs _ _ h1
  · split at he
    · cases he; simp
    · split at he
      · rename_i e' h2; cases he; exact parseFrac_nofuel bs _ _ h2
      · split at he
        · rename_i e' h3; cases he; exact parseExp_nofuel bs _ _ h3
        · cases he

theorem hexAt_nofuel (bs : ByteArray) (i : Nat) : NotFuel (hexAt bs i) := by
  intro e he; unfold hexAt at he
  repeat' split at he
  all_goals first | (cases he; simp) | cases he

theorem parseHex4_nofuel (bs : ByteArray) (p : Nat) : NotFuel (parseHex4 bs p) := by
  intro e he; unfold parseHex4 at he
  split at he
  · cases he; simp
  · split at he
    · cases he
    · rename_i e' h; cases he; exact hexAt_nofuel bs _ _ h
    · rename_i e' _ h; cases he; exact hexAt_nofuel bs _ _ h
    · rename_i e' _ _ h; cases he; exact hexAt_nofuel bs _ _ h
    · rename_i e' _ _ _ h; cases he; exact hexAt_nofuel bs _ _ h

theorem parseEscape_nofuel (bs : ByteArray) (p : Nat) : NotFuel (parseEscape bs p) := by
  intro e he; unfold parseEscape at he
  split at he
  · cases he; simp
  · rename_i b hb
    by_cases c34 : (b == 34) = true
    · rw [ite_eq_left c34] at he; cases he
    rw [ite_eq_right c34] at he
    by_cases c92 : (b == 92) = true
    · rw [ite_eq_left c92] at he; cases he
    rw [ite_eq_right c92] at he
    by_cases c47 : (b == 47) = true
    · rw [ite_eq_left c47] at he; cases he
    rw [ite_eq_right c47] at he
    by_cases c98 : (b == 98) = true
    · rw [ite_eq_left c98] at he; cases he
    rw [ite_eq_right c98] at he
    by_cases c102 : (b == 102) = true
    · rw [ite_eq_left c102] at he; cases he
    rw [ite_eq_right c102] at he
    by_cases c110 : (b == 110) = true
    · rw [ite_eq_left c110] at he; cases he
    rw [ite_eq_right c110] at he
    by_cases c114 : (b == 114) = true
    · rw [ite_eq_left c114] at he; cases he
    rw [ite_eq_right c114] at he
    by_cases c116 : (b == 116) = true
    · rw [ite_eq_left c116] at he; cases he
    rw [ite_eq_right c116] at he
    by_cases c117 : (b == 117) = true
    · rw [ite_eq_left c117] at he
      simp only [bind, Except.bind] at he
      split at he
      · rename_i e' hh; cases he; exact parseHex4_nofuel bs _ _ hh
      · rename_i u _
        by_cases d1 : 56320 ≤ u ∧ u < 57344
        · rw [ite_eq_left d1] at he; cases he; simp
        rw [ite_eq_right d1] at he
        by_cases d2 : 55296 ≤ u ∧ u < 56320
        · rw [ite_eq_left d2] at he
          split at he
          · cases he; simp
          · split at he
            · cases he; simp
            · split at he
              · rename_i e' hh; cases he; exact parseHex4_nofuel bs _ _ hh
              · split at he
                · cases he
                · cases he; simp
            · cases he; simp
          · cases he; simp
        · rw [ite_eq_right d2] at he; cases he
    · rw [ite_eq_right c117] at he; cases he; simp

theorem parseStrBody_nofuel (bs : ByteArray) : ∀ (f p : Nat) (acc : List Char), NotFuel (parseStrBody bs p f acc)
  | 0, p, acc => by intro e he; simp [parseStrBody] at he; cases he; simp
  | f + 1, p, acc => by
    intro e he; unfold parseStrBody at he
    split at he
    · cases he; simp
    · split at he
      · cases he
      · split at he
        · split at he
          · exact parseStrBody_nofuel bs f _ _ e he
          · rename_i e' hh; cases he; exact parseEscape_nofuel bs _ _ hh
        · split at he
          · cases he; simp
          · split at he
            · exact parseStrBody_nofuel bs f _ _ e he
            · split at he
              · exact parseStrBody_nofuel bs f _ _ e he
              · cases he; simp

theorem parseString_nofuel (bs : ByteArray) (p : Nat) : NotFuel (parseString bs p) := by
  intro e he; unfold parseString at he
  split at he
  · cases he
  · rename_i e' hh; cases he; exact parseStrBody_nofuel bs _ _ _ _ hh

mutual
theorem parseValue_enough (cfg : ParseCfg) (bs : ByteArray) : ∀ (n pos : Nat), 2 * (bs.size - pos) < n →
    NotFuel (parseValueWith cfg bs pos n)
  | 0, pos, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, pos, hn => by
    intro e he
    unfold parseValueWith at he
    simp only at he
    have a0 := skipWs_adv bs pos bs.size
    generalize skipWs bs pos bs.size = q at he a0
    split at he
    · cases he; simp
    rename_i b hb
    have hq := lt_size_of_get hb
    have hq0 := a0.1
    by_cases c34 : (b == 34) = true
    · rw [ite_eq_left c34] at he
      split at he
      · cases he
      · rename_i e' hh; cases he; exact parseString_nofuel bs _ _ hh
    rw [ite_eq_right c34] at he
    by_cases c91 : (b == 91) = true
    · rw [ite_eq_left c91] at he
      have a1 := (skipWs_adv bs (q + 1) bs.size).1
      generalize skipWs bs (q + 1) bs.size = p at he a1
      split at he
      · cases he; simp
      · cases he
      · exact parseElems_enough cfg bs n p [] (by omega) e he
    rw [ite_eq_right c91] at he
    by_cases c123 : (b == 123) = true
    · rw [ite_eq_left c123] at he
      have a1 := (skipWs_adv bs (q + 1) bs.size).1
      generalize skipWs bs (q + 1) bs.size = p at he a1
      split at he
      · cases he; simp
      · cases he
      · exact parseMembers_enough cfg bs n p [] (by omega) e he
      · cases he; simp
    rw [ite_eq_right c123] at he
    by_cases c116 : (b == 116) = true
    · rw [ite_eq_left c116] at he
      split at he
      · cases he
      · rename_i e' hh; cases he; exact expectLit_nofuel bs _ _ _ hh
    rw [ite_eq_right c116] at he
    by_cases c102 : (b == 102) = true
    · rw [ite_eq_left c102] at he
      split at he
      · cases he
      · rename_i e' hh; cases he; exact expectLit_nofuel bs _ _ _ hh
    rw [ite_eq_right c102] at he
    by_cases c110 : (b == 110) = true
    · rw [ite_eq_left c110] at he
      split at he
      · cases he
      · rename_i e' hh; cases he; exact expectLit_nofuel bs _ _ _ hh
    rw [ite_eq_right c110] at he
    by_cases cn : (b == 45 || isDigit b) = true
    · rw [ite_eq_left cn] at he
      split at he
      · cases he
      · rename_i e' hh; cases he; exact parseNumber_nofuel cfg bs _ _ hh
    rw [ite_eq_right cn] at he
    cases he; simp
theorem parseElems_enough (cfg : ParseCfg) (bs : ByteArray) : ∀ (n pos : Nat) (acc : List Json),
    2 * (bs.size - pos) + 1 < n → NotFuel (parseElems cfg bs pos n acc)
  | 0, pos, acc, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, pos, acc, hn => by
    intro e he
    unfold parseElems at he
    split at he
    · rename_i e' hh; cases he; exact parseValue_enough cfg bs n pos (by omega) _ hh
    · rename_i v p1 hv
      have a1 := parseValue_adv cfg bs n pos _ hv
      have h1 := a1.2; have h1' := a1.1.2 a1.2
      simp only at h1 h1' he
      have a2 := (skipWs_adv bs p1 bs.size).1
      generalize skipWs bs p1 bs.size = p at he a2
      split at he
      · cases he; simp
      · rename_i hp
        have hps := lt_size_of_get hp
        have a3 := (skipWs_adv bs (p + 1) bs.size).1
        generalize skipWs bs (p + 1) bs.size = q at he a3
        split at he
        · cases he; simp
        · exact parseElems_enough cfg bs n q _ (by omega) e he
      · cases he
      · cases he; simp
theorem parseMembers_enough (cfg : ParseCfg) (bs : ByteArray) : ∀ (n pos : Nat) (acc : List (String × Json)),
    2 * (bs.size - pos) + 1 < n → NotFuel (parseMembers cfg bs pos n acc)
  | 0, pos, acc, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, pos, acc, hn => by
    intro e he
    unfold parseMembers at he
    split at he
    · rename_i e' hh; cases he; exact parseString_nofuel bs _ _ hh
    · rename_i k p1 hk
      have a1 := parseString_adv hk
      have h1 := a1.2
      simp only at h1 he
      have a2 := (skipWs_adv bs p1 bs.size).1
      generalize skipWs bs p1 bs.size = p at he a2
      split at he
      · cases he; simp
      · rename_i hp
        have hps := lt_size_of_get hp
        split at he
        · rename_i e' hh; cases he; exact parseValue_enough cfg bs n (p + 1) (by omega) _ hh
        · rename_i v p2 hv
          have b1 := (parseValue_adv cfg bs n (p + 1) _ hv).2
          simp only at b1
          have a4 := (skipWs_adv bs p2 bs.size).1
          generalize skipWs bs p2 bs.size = p3 at he a4
          split at he
          · cases he; simp
          · rename_i hp3
            have hp3s := lt_size_of_get hp3
            have a5 := (skipWs_adv bs (p3 + 1) bs.size).1
            generalize skipWs bs (p3 + 1) bs.size = q at he a5
            split at he
            · cases he; simp
            · exact parseMembers_enough cfg bs n q _ (by omega) e he
            · cases he; simp
            · cases he; simp
          · cases he
          · cases he; simp
      · cases he; simp
end

/-- **Fuel is enough**: at the API's budget the parser never runs out. -/
theorem parse_fuel_enough (cfg : ParseCfg) : Spec.FuelEnough (parseValueWith cfg) := by
  intro bs pos e he
  exact parseValue_enough cfg bs _ pos (by omega) e he

mutual
theorem parseValue_mono (cfg : ParseCfg) (bs : ByteArray) : ∀ (n m pos : Nat) (r : Except ParseErr (Json × Nat)),
    n ≤ m → parseValueWith cfg bs pos n = r → NotFuel r → parseValueWith cfg bs pos m = r
  | 0, m, pos, r, _, h, hnf => by
    subst h; exact absurd rfl (hnf _ rfl)
  | n + 1, m, pos, r, hle, h, hnf => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold parseValueWith at h ⊢
    try simp only at h ⊢
    generalize skipWs bs pos bs.size = q at h ⊢
    split at h
    · rename_i hb; (try rw [hb]); exact h
    rename_i b hb
    (try rw [hb]); try simp only
    by_cases c34 : (b == 34) = true
    · rw [ite_eq_left c34] at h ⊢; exact h
    rw [ite_eq_right c34] at h ⊢
    by_cases c91 : (b == 91) = true
    · rw [ite_eq_left c91] at h ⊢
      generalize skipWs bs (q + 1) bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); exact h
      · exact parseElems_mono cfg bs n m' p [] r (by omega) h hnf
    rw [ite_eq_right c91] at h ⊢
    by_cases c123 : (b == 123) = true
    · rw [ite_eq_left c123] at h ⊢
      generalize skipWs bs (q + 1) bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); exact parseMembers_mono cfg bs n m' p [] r (by omega) h hnf
      · exact h
    rw [ite_eq_right c123] at h ⊢
    exact h
theorem parseElems_mono (cfg : ParseCfg) (bs : ByteArray) : ∀ (n m pos : Nat) (acc : List Json) (r : Except ParseErr (Json × Nat)),
    n ≤ m → parseElems cfg bs pos n acc = r → NotFuel r → parseElems cfg bs pos m acc = r
  | 0, m, pos, acc, r, _, h, hnf => by
    subst h; exact absurd rfl (hnf _ rfl)
  | n + 1, m, pos, acc, r, hle, h, hnf => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold parseElems at h ⊢
    split at h
    · rename_i e hv
      subst h
      rw [parseValue_mono cfg bs n m' pos _ (by omega) hv hnf]
    · rename_i v p1 hv
      rw [parseValue_mono cfg bs n m' pos _ (by omega) hv (by intro e he; cases he)]
      try simp only at h ⊢
      generalize skipWs bs p1 bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); try simp only at h ⊢
        generalize skipWs bs (p + 1) bs.size = q at h ⊢
        split at h
        · rename_i c; rw [ite_eq_left c]; exact h
        · rename_i c; rw [ite_eq_right c]; exact parseElems_mono cfg bs n m' q _ r (by omega) h hnf
      · rename_i hp; (try rw [hp]); exact h
      · exact h
theorem parseMembers_mono (cfg : ParseCfg) (bs : ByteArray) : ∀ (n m pos : Nat) (acc : List (String × Json))
    (r : Except ParseErr (Json × Nat)),
    n ≤ m → parseMembers cfg bs pos n acc = r → NotFuel r → parseMembers cfg bs pos m acc = r
  | 0, m, pos, acc, r, _, h, hnf => by
    subst h; exact absurd rfl (hnf _ rfl)
  | n + 1, m, pos, acc, r, hle, h, hnf => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold parseMembers at h ⊢
    split at h
    · rename_i e hk; (try rw [hk]); exact h
    · rename_i k p1 hk
      (try rw [hk]); try simp only at h ⊢
      generalize skipWs bs p1 bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); try simp only
        split at h
        · rename_i e hv
          subst h
          rw [parseValue_mono cfg bs n m' (p + 1) _ (by omega) hv hnf]
        · rename_i v p2 hv
          rw [parseValue_mono cfg bs n m' (p + 1) _ (by omega) hv (by intro e he; cases he)]
          try simp only at h ⊢
          generalize skipWs bs p2 bs.size = p3 at h ⊢
          split at h
          · rename_i hp3; (try rw [hp3]); exact h
          · rename_i hp3; (try rw [hp3]); try simp only at h ⊢
            generalize skipWs bs (p3 + 1) bs.size = q at h ⊢
            split at h
            · rename_i hq; (try rw [hq]); exact h
            · rename_i hq; (try rw [hq]); exact parseMembers_mono cfg bs n m' q _ r (by omega) h hnf
            · rename_i hq; (try rw [hq]); exact h
            · exact h
          · rename_i hp3; (try rw [hp3]); exact h
          · exact h
      · exact h
end

/-- **Fuel monotonicity**: more fuel never changes an answer that was not a
fuel failure. -/
theorem parse_fuel_mono (cfg : ParseCfg) : Spec.FuelMono (parseValueWith cfg) := by
  intro bs pos n m hle hnf
  exact parseValue_mono cfg bs n m pos _ hle rfl hnf

end LeanJson
