import LeanJson.Proofs.Step
import LeanJson.RepoImpl.Grammar

/-!
# Proofs: the fast parser is the Keel parser

`valueL_ok_iff`: on every list, the nesting loop with `d` levels succeeds
exactly when Keel's `fixDepth d (valueNode cfg)` does, with the same value
and end. Both run the same `valueStep`, so the proof is one induction on `d`
with `valueStep_sim` at each level.

`valueNode_monotone`: the body passes on every failure that consumed input,
so Keel's `fixDepth_ok` applies: a bounded success is the unbounded one.
Together with `fixDepth_eq_fix` that gives `valueL_deepen`: a success with
`d` levels is a success with any number of levels beyond the input's length,
which is what the depth limit is (`Proofs/Codec.lean`).
-/

namespace LeanJson

open Keel Parser

variable {ε : Type} [ParseError ε]

omit [ParseError ε] in
theorem ofResult_shift {α : Type} (r : Result ε α) (j : Nat) : ofResult (r.shift j) = shiftRes j (ofResult r) := by
  cases r <;> rfl

theorem valueNode_run (cfg : ParseCfg) (h : Parser UInt8 ε Json) (L : List UInt8) :
    (valueNode cfg h).run L 0 =
      toResult L.length (valueStep cfg (fun j => ofResult (h.run L j)) (lv L) L.length) := by
  simp [valueNode, Input.rest]

theorem fixDepth_succ_run (d : Nat) (F : Parser UInt8 ε Json → Parser UInt8 ε Json) (L : List UInt8) :
    (fixDepth (d + 1) F).run L 0 = (F (guarded L.length fun _ _ => fixDepth d F)).run L 0 := by
  show (F (guarded (L.length - 0) fun _ _ => fixDepth d F)).run L 0 = _
  rw [Nat.sub_zero]

/-- Inside the input, past its start, the handle of `fixDepth (d + 1)` is
`fixDepth d` on the tokens left. -/
theorem guarded_run (d : Nat) (F : Parser UInt8 ε Json → Parser UInt8 ε Json) (L : List UInt8) {j : Nat}
    (hj : 0 < j) (hjn : j < L.length) :
    (guarded L.length fun _ _ => fixDepth d F).run L j = ((fixDepth d F).run (L.drop j) 0).shift j := by
  show (if h : L.length - j < L.length then _ else _) = _
  rw [dite_eq_left (by omega)]
  exact (fixDepth d F).run_eq L j

/-- The child the Keel body hands the grammar, for `fixDepth (d + 1)`. -/
theorem keelChild (cfg : ParseCfg) (d : Nat) (L : List UInt8) {j : Nat} (hj : 0 < j) (hjn : j < L.length) :
    ofResult ((guarded L.length fun _ _ => fixDepth d (valueNode cfg (ε := ε))).run L j) =
      shiftRes j (ofResult ((fixDepth d (valueNode cfg (ε := ε))).run (L.drop j) 0)) := by
  rw [guarded_run d _ L hj hjn, ofResult_shift]

theorem toResult_ok {α : Type} {n : Nat} {r : Except ParseErr (α × Nat)} {v : α} {p : Nat}
    (h : toResult (ε := ε) n r = .ok v p) : ∃ p', r = .ok (v, p') ∧ p = min p' n := by
  rcases r with e | ⟨w, q⟩
  · cases h
  · cases h; exact ⟨q, rfl, rfl⟩

/-- **The fast parser is the Keel parser**: with `d` levels, on any list, the
nesting loop succeeds exactly when `fixDepth d (valueNode cfg)` does, with
the same value and end. -/
theorem valueL_ok_iff (cfg : ParseCfg) :
    ∀ (d : Nat) (L : List UInt8) (v : Json) (p : Nat),
      valueL cfg d L = .ok (v, p) ↔ (fixDepth d (valueNode cfg (ε := ε))).run L 0 = .ok v p
  | 0, L, v, p => by
    constructor
    · intro h; simp [valueL, valueGo] at h
    · intro h
      exfalso
      revert h
      show (if L.length - 0 = 0 then _ else _) ≠ _
      split
      · rename_i hL
        have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        rw [show (valueNode cfg _).run ([] : List UInt8) 0 = _ from valueNode_run cfg _ []]
        simp [valueStep, lv, toResult]
      · cases L <;> simp_all [failAhead]
  | d + 1, L, v, p => by
    rw [valueL_succ, fixDepth_succ_run, valueNode_run]
    have hv := viewOk_lv L
    -- The two children agree wherever the fast one succeeds, and wherever the Keel one does.
    have sim₁ : ∀ j, 0 < j → j < L.length →
        Sim (fun _ _ => True) L.length (shiftRes j (valueL cfg d (L.drop j)))
          (ofResult ((guarded L.length fun _ _ => fixDepth d (valueNode cfg (ε := ε))).run L j)) := by
      intro j hj hjn
      rw [keelChild cfg d L hj hjn]
      cases hc : valueL cfg d (L.drop j) with
      | error e => exact Or.inr ⟨j, _, hj, hjn, trivial, rfl⟩
      | ok r =>
        obtain ⟨w, q⟩ := r
        rw [(valueL_ok_iff cfg d (L.drop j) w q).mp hc]
        exact Or.inl rfl
    have sim₂ : ∀ j, 0 < j → j < L.length →
        Sim (fun _ _ => True) L.length
          (ofResult ((guarded L.length fun _ _ => fixDepth d (valueNode cfg (ε := ε))).run L j))
          (shiftRes j (valueL cfg d (L.drop j))) := by
      intro j hj hjn
      rw [keelChild cfg d L hj hjn]
      cases hc : (fixDepth d (valueNode cfg (ε := ε))).run (L.drop j) 0 with
      | error e => exact Or.inr ⟨j, _, hj, hjn, trivial, rfl⟩
      | ok w q =>
        rw [(valueL_ok_iff cfg d (L.drop j) w q).mpr hc]
        exact Or.inl rfl
    constructor
    · intro h
      have hp := (valueL_progress cfg (d + 1) L (by rw [valueL_succ]; exact h)).2
      rcases valueStep_sim cfg hv sim₁ with e | ⟨_, _, _, _, _, e⟩
      · rw [← e, h]; simp [toResult, Nat.min_eq_left hp]
      · rw [h] at e; cases e
    · intro h
      obtain ⟨p', hs, rfl⟩ := toResult_ok h
      rcases valueStep_sim cfg hv sim₂ with e | ⟨_, _, _, _, _, e⟩
      · rw [← e, hs]
        have hp := (valueL_progress cfg (d + 1) L (by rw [valueL_succ, ← e]; exact hs)).2
        rw [Nat.min_eq_left hp]
      · rw [hs] at e; cases e

/-- **The body passes on every failure that consumed input**: a nested
failure past the cursor fails the value past the cursor. So Keel's laws for
`fixDepth` apply to it. -/
theorem valueNode_monotone (cfg : ParseCfg) : Monotone (valueNode cfg (ε := ε)) := by
  intro p q hpq L
  have sim : ∀ j, 0 < j → j < L.length →
      Sim (fun j e => j < e.offset) L.length (ofResult (p.run L j)) (ofResult (q.run L j)) := by
    intro j hj hjn
    rcases hpq (L.drop j) with e | ⟨e, r, he, hr⟩
    · left; rw [p.run_eq L j, q.run_eq L j]; exact congrArg (fun r => ofResult (Result.shift j r)) (run_zero_of_parse e)
    · right
      have := run_eq_error_of_parse p (s := L) (i := j) he (by simp; omega)
      refine ⟨j, _, hj, hjn, ?_, by rw [this]; rfl⟩
      simp at hr ⊢; omega
  unfold Parser.parse
  rw [valueNode_run, valueNode_run]
  rcases valueStep_sim cfg (viewOk_lv L) sim with e | ⟨j, e', hj, hjn, hq, he⟩
  · exact Or.inl (by rw [e])
  · refine Or.inr ⟨_, _, by rw [he]; rfl, ?_⟩
    simp; omega

omit [ParseError ε] in
theorem run_of_parse_ok {P : Parser UInt8 ε Json} {L : List UInt8} {v : Json} {p : Nat}
    (hp : p ≤ L.length) (h : P.parse L = .ok v (L.drop p)) : P.run L 0 = .ok v p := by
  have := run_eq_of_parse P (s := L) (i := 0) h (Nat.zero_le _)
  simpa [Nat.sub_sub_self hp] using this

/-- **More levels change nothing that succeeded**: a success with `d` levels
is a success with any number of levels beyond the input's length. By
`fixDepth_ok` (the bounded fixpoint agrees with `fix` where it succeeds) and
`fixDepth_eq_fix` (beyond the input's length the bound is never reached). -/
theorem valueL_deepen (cfg : ParseCfg) {d d' : Nat} {L : List UInt8} {v : Json} {p : Nat}
    (h : valueL cfg d L = .ok (v, p)) (hd : L.length < d') : valueL cfg d' L = .ok (v, p) := by
  have hp := (valueL_progress cfg d L h).2
  have h1 := (valueL_ok_iff (ε := Keel.Parse.Error) cfg d L v p).mp h
  have h2 : (fixDepth d (valueNode cfg (ε := Keel.Parse.Error))).parse L = .ok v (L.drop p) := by
    unfold Parser.parse; rw [h1]; rfl
  have h3 := fixDepth_ok (valueNode_monotone cfg) h2
  rw [← fixDepth_eq_fix _ d' L hd] at h3
  exact (valueL_ok_iff cfg d' L v p).mpr (run_of_parse_ok hp h3)

end LeanJson
