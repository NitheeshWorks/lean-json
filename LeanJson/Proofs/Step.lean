import LeanJson.Proofs.String
import LeanJson.Proofs.Fields
import LeanJson.RepoImpl.Parse

/-!
# Proofs: the laws of one step

`valueStep` reads one value and calls its `child` for the values nested in
it. Three facts about it carry every value-level theorem, each proved once by
induction on the element and member loops:

* `valueStep_sim`: the step sees its child only through the child's answers,
  and passes each child failure on unchanged. It gives the agreement of the
  fast parser with the Keel parser, and that the Keel body is `Monotone`.
* `valueStep_shape`: what a step returns is a node over what its child
  returned, and it ends past its first byte, within the view.
* `valueStep_relax`: lifting the integer-length and NaN limits keeps every
  success.

`valueGo_rebase` says the nesting loop reads a value through the view rebased
at its first byte, so a nested value is read just as a top-level one is.
-/

namespace LeanJson

/-- A child parser: a value at a position of the view, and its end. -/
abbrev Child := Nat → Except ParseErr (Json × Nat)

/-- The outcome of a step under child `c₁`, against `c₂`: the same, or an
error of `c₁`'s that `Q` allows, at a position inside the view. -/
def Sim (Q : Nat → ParseErr → Prop) (n : Nat) (r₁ r₂ : Except ParseErr (Json × Nat)) : Prop :=
  r₁ = r₂ ∨ ∃ j e, 0 < j ∧ j < n ∧ Q j e ∧ r₁ = .error e

theorem Sim.refl {Q n} (r) : Sim Q n r r := Or.inl rfl

variable {get : Nat → Option UInt8} {n : Nat} {Q : Nat → ParseErr → Prop} {c₁ c₂ : Child}

theorem parseElems_sim (hv : ViewOk get n)
    (h : ∀ j, 0 < j → j < n → Sim Q n (c₁ j) (c₂ j)) (pos : Nat) (acc : Array Json)
    (h0 : 0 < pos) (hn : pos < n) : Sim Q n (parseElems c₁ get n pos acc) (parseElems c₂ get n pos acc) := by
  rcases h pos h0 hn with e | ⟨j, e, hj0, hjn, hq, he⟩
  · rw [parseElems, parseElems, e]
    split
    · exact .refl _
    · dsimp only
      generalize get (skipWs get n _) = g1
      generalize get (skipWs get n (skipWs get n _ + 1)) = g2
      split
      · split
        · exact .refl _
        · split
          · exact parseElems_sim hv h _ _ (by omega) (by omega)
          · exact .refl _
        · exact .refl _
      all_goals exact .refl _
  · exact Or.inr ⟨j, e, hj0, hjn, hq, by rw [parseElems, he]⟩
termination_by n - pos
decreasing_by all_goals omega

theorem parseMembers_sim (hv : ViewOk get n) (dedup : Bool)
    (h : ∀ j, 0 < j → j < n → Sim Q n (c₁ j) (c₂ j)) (pos : Nat) (acc : Fields) :
    Sim Q n (parseMembers dedup c₁ get n pos acc) (parseMembers dedup c₂ get n pos acc) := by
  rw [parseMembers, parseMembers]
  split
  · exact .refl _
  rename_i k kn _
  dsimp only
  split
  · split
    · exact .refl _
    rename_i hq
    have := hv _ _ hq
    have := skipWs_ge get n (skipWs get n kn + 1)
    rcases h (skipWs get n (skipWs get n kn + 1)) (by omega) (by omega) with e | ⟨j, e, hj0, hjn, hq', he⟩
    · rw [e]
      split
      · exact .refl _
      · rename_i v j' _
        generalize get (skipWs get n j') = g1
        generalize get (skipWs get n (skipWs get n j' + 1)) = g2
        split
        · split
          · split
            · exact parseMembers_sim hv dedup h _ _
            · exact .refl _
          all_goals exact .refl _
        all_goals exact .refl _
    · exact Or.inr ⟨j, e, hj0, hjn, hq', by rw [he]⟩
  all_goals exact .refl _
termination_by n - pos
decreasing_by omega

/-- **The step depends on its child only through the child's answers**, and
passes every child failure on unchanged: wherever `c₁` agrees with `c₂` or
fails as `Q` allows, so does the step. -/
theorem valueStep_sim (cfg : ParseCfg) (hv : ViewOk get n)
    (h : ∀ j, 0 < j → j < n → Sim Q n (c₁ j) (c₂ j)) :
    Sim Q n (valueStep cfg c₁ get n) (valueStep cfg c₂ get n) := by
  unfold valueStep
  split
  · exact .refl _
  have := skipWs_ge get n 1
  split
  · exact .refl _
  split
  · dsimp only
    split
    · exact .refl _
    · rename_i hp; exact parseElems_sim hv h _ _ (by omega) (hv _ _ hp)
    · exact .refl _
  split
  · dsimp only
    split
    · exact .refl _
    · exact parseMembers_sim hv _ h _ _
    all_goals exact .refl _
  exact .refl _

/-- What a step returns, given what its child returns (`P`): an array or
object of `P` values, a number the configuration admits, or another scalar. -/
def Node (cfg : ParseCfg) (P : Json → Prop) : Json → Prop
  | .arr ⟨xs⟩ => ∀ x ∈ xs, P x
  | .obj ⟨kvs⟩ => ∀ kv ∈ kvs, P kv.2
  | .num x => cfg.allowInfNan = true ∨ x.isFinite = true
  | _ => True

variable {P : Json → Prop} {c : Child}

/-- The child's successes satisfy `P` and move forward within the view. -/
def ChildOk (P : Json → Prop) (n : Nat) (c : Child) : Prop :=
  ∀ j w q, 0 < j → j < n → c j = .ok (w, q) → P w ∧ j < q ∧ q ≤ n

theorem parseElems_shape (hv : ViewOk get n) (hc : ChildOk P n c) (pos : Nat) (acc : Array Json)
    (h0 : 0 < pos) (hn : pos < n) (hacc : ∀ x ∈ acc.toList, P x) {v : Json} {p : Nat}
    (h : parseElems c get n pos acc = .ok (v, p)) :
    (∃ xs, v = .arr ⟨xs⟩ ∧ ∀ x ∈ xs, P x) ∧ pos < p ∧ p ≤ n := by
  rw [parseElems] at h
  split at h
  · cases h
  rename_i w j hw
  obtain ⟨hpw, hj1, hj2⟩ := hc pos w j (by omega) hn hw
  have hacc' : ∀ x ∈ (acc.push w).toList, P x := by
    intro x hx; simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hacc x hx
    · exact hpw
  have g1 := skipWs_ge get n j
  dsimp only at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i hlt
        have := parseElems_shape hv hc _ _ (by omega) hlt.2 hacc' h
        exact ⟨this.1, by omega, this.2.2⟩
      · cases h
    · cases h
  · rename_i hb; cases h; exact ⟨⟨_, rfl, hacc'⟩, by omega, hv _ _ hb⟩
  all_goals cases h
termination_by n - pos
decreasing_by omega

theorem parseMembers_shape (hv : ViewOk get n) (hc : ChildOk P n c) (dedup : Bool) (pos : Nat)
    (acc : Fields) (hacc : ∀ kv ∈ acc.1.toList, P kv.2) {v : Json} {p : Nat}
    (h : parseMembers dedup c get n pos acc = .ok (v, p)) :
    (∃ kvs, v = .obj ⟨kvs⟩ ∧ ∀ kv ∈ kvs, P kv.2) ∧ pos < p ∧ p ≤ n := by
  rw [parseMembers] at h
  split at h
  · cases h
  rename_i k kn hk
  have hkn := (parseString_adv hv hk).2
  have g1 := skipWs_ge get n kn
  dsimp only at h
  split at h
  · have g2 := skipWs_ge get n (skipWs get n kn + 1)
    split at h
    · cases h
    rename_i hq
    split at h
    · cases h
    rename_i w j hw
    obtain ⟨hpw, hj1, hj2⟩ := hc _ w j (by omega) (hv _ _ hq) hw
    have hacc' : ∀ kv ∈ (acc.add dedup k w).1.toList, P kv.2 := by
      intro kv hkv
      rcases Fields.mem_add hkv with hkv | rfl
      · exact hacc kv hkv
      · exact hpw
    have g3 := skipWs_ge get n j
    split at h
    · split at h
      · split at h
        · rename_i hlt
          have := parseMembers_shape hv hc dedup _ _ hacc' h
          exact ⟨this.1, by omega, this.2.2⟩
        · cases h
      all_goals cases h
    · rename_i hb; cases h; exact ⟨⟨_, rfl, hacc'⟩, by omega, hv _ _ hb⟩
    all_goals cases h
  all_goals cases h
termination_by n - pos
decreasing_by omega

theorem parseNumber_admitted {cfg : ParseCfg} {pos : Nat} {x : Number} {p : Nat}
    (h : parseNumber cfg get n pos = .ok (x, p)) : cfg.allowInfNan = true ∨ x.isFinite = true := by
  have body : ∀ {neg p0}, parseNumberBody cfg get n pos neg p0 = .ok (x, p) → x.isFinite = true := by
    intro neg p0 hb
    unfold parseNumberBody at hb
    simp only [bind, Except.bind] at hb
    split at hb
    · cases hb
    · split at hb
      · cases hb
      · split at hb
        · cases hb
        · split at hb
          · cases hb
          · cases hb; unfold mkNumber; split <;> rfl
  unfold parseNumber at h
  split at h
  · split at h
    · rename_i c; simp at c; exact Or.inl c.1
    · exact Or.inr (body h)
  · exact Or.inr (body h)

/-- **What one step returns**, given what its child returns: a node over the
child's values, ending past its first byte and within the view. -/
theorem valueStep_shape (cfg : ParseCfg) (hv : ViewOk get n) (hc : ChildOk P n c) {v : Json} {p : Nat}
    (h : valueStep cfg c get n = .ok (v, p)) : Node cfg P v ∧ 0 < p ∧ p ≤ n := by
  unfold valueStep at h
  split at h
  · cases h
  rename_i b hb
  have h0 := hv _ _ hb
  have g := skipWs_ge get n 1
  have lit : ∀ {w : Json} {l : List UInt8}, (expectLit get 1 l).map (fun q => (w, q)) = .ok (v, p) →
      Node cfg P w → Node cfg P v ∧ 0 < p ∧ p ≤ n := by
    intro w l hl hw
    cases he : expectLit get 1 l with
    | error => rw [he] at hl; cases hl
    | ok q =>
      rw [he] at hl; cases hl
      have := litAdv hv hb he
      exact ⟨hw, by omega, this.1.2 this.2⟩
  split at h
  · cases hs : parseString get n 0 with
    | error => rw [hs] at h; cases h
    | ok r =>
      rw [hs] at h; cases h
      have := parseString_adv hv hs
      exact ⟨trivial, by omega, this.1.2 this.2⟩
  split at h
  · dsimp only at h
    split at h
    · rename_i hp; cases h; exact ⟨by simp [Node], by omega, hv _ _ hp⟩
    · rename_i hp
      obtain ⟨⟨xs, rfl, hxs⟩, h1, h2⟩ := parseElems_shape hv hc _ _ (by omega) (hv _ _ hp) (by simp) h
      exact ⟨hxs, by omega, h2⟩
    · cases h
  split at h
  · dsimp only at h
    split at h
    · rename_i hp; cases h; exact ⟨by simp [Node], by omega, hv _ _ hp⟩
    · obtain ⟨⟨kvs, rfl, hkvs⟩, h1, h2⟩ := parseMembers_shape hv hc _ _ _ (by simp [Fields.empty]) h
      exact ⟨hkvs, by omega, h2⟩
    all_goals cases h
  split at h
  · exact lit h trivial
  split at h
  · exact lit h trivial
  split at h
  · exact lit h trivial
  split at h
  · cases hs : parseNumber cfg get n 0 with
    | error => rw [hs] at h; cases h
    | ok r =>
      rw [hs] at h; cases h
      have := parseNumber_adv hv hs
      rw [Json.ofNumber_eq]
      exact ⟨parseNumber_admitted hs, by omega, this.1.2 this.2⟩
  split at h
  · rename_i ha; exact lit h (Or.inl (by simp at ha; exact ha.2))
  split at h
  · rename_i ha; exact lit h (Or.inl (by simp at ha; exact ha.2))
  cases h

/-! ## Lifting the limits -/

theorem parseNumberBody_relax {cfg : ParseCfg} {pos : Nat} {neg : Bool} {p0 : Nat}
    {r : Number × Nat} (h : parseNumberBody cfg get n pos neg p0 = .ok r) :
    parseNumberBody cfg.relax get n pos neg p0 = .ok r := by
  unfold parseNumberBody at h ⊢
  simp only [bind, Except.bind] at h ⊢
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [ParseCfg.intLenOk, ParseCfg.relax, ParseCfg.lossless, Bool.true_eq_false, ↓reduceIte]
      exact h

theorem parseNumberBody_I {cfg : ParseCfg} {pos : Nat} {neg : Bool} {p0 : Nat}
    (hI : get p0 = some 73) (r : Number × Nat) : parseNumberBody cfg get n pos neg p0 ≠ .ok r := by
  intro h
  unfold parseNumberBody at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i h1
    unfold parseIntPart at h1
    rw [hI] at h1
    simp (config := { decide := true }) [] at h1

theorem parseNumber_relax {cfg : ParseCfg} {pos : Nat} {r : Number × Nat}
    (h : parseNumber cfg get n pos = .ok r) : parseNumber cfg.relax get n pos = .ok r := by
  unfold parseNumber at h ⊢
  by_cases c45 : (get pos == some 45) = true
  · rw [ite_eq_left c45] at h ⊢
    by_cases ci : (cfg.allowInfNan && get (pos + 1) == some 73) = true
    · rw [ite_eq_left ci] at h
      have h73 : (get (pos + 1) == some 73) = true := by simp at ci; simp [ci.2]
      rw [ite_eq_left (by simp [ParseCfg.relax, ParseCfg.lossless, h73])]
      exact h
    · rw [ite_eq_right ci] at h
      by_cases h73 : (get (pos + 1) == some 73) = true
      · exact absurd h (parseNumberBody_I (by simpa using h73) r)
      · rw [ite_eq_right (by simp [ParseCfg.relax, ParseCfg.lossless, h73])]
        exact parseNumberBody_relax h
  · rw [ite_eq_right c45] at h ⊢
    exact parseNumberBody_relax h

/-- **Limits only add errors**, for one step: what a step reads under `cfg`
it reads under `cfg.relax`. -/
theorem valueStep_relax (cfg : ParseCfg) {x : Json × Nat} (h : valueStep cfg c get n = .ok x) :
    valueStep cfg.relax c get n = .ok x := by
  unfold valueStep at h ⊢
  have hd : cfg.relax.dedupKeys = cfg.dedupKeys := rfl
  have ha : cfg.relax.allowInfNan = true := rfl
  rw [hd, ha]
  split at h
  · cases h
  rename_i b hb
  by_cases c34 : (b == 34) = true
  · rw [ite_eq_left c34] at h ⊢; exact h
  rw [ite_eq_right c34] at h ⊢
  by_cases c91 : (b == 91) = true
  · rw [ite_eq_left c91] at h ⊢; exact h
  rw [ite_eq_right c91] at h ⊢
  by_cases c123 : (b == 123) = true
  · rw [ite_eq_left c123] at h ⊢; exact h
  rw [ite_eq_right c123] at h ⊢
  by_cases c116 : (b == 116) = true
  · rw [ite_eq_left c116] at h ⊢; exact h
  rw [ite_eq_right c116] at h ⊢
  by_cases c102 : (b == 102) = true
  · rw [ite_eq_left c102] at h ⊢; exact h
  rw [ite_eq_right c102] at h ⊢
  by_cases c110 : (b == 110) = true
  · rw [ite_eq_left c110] at h ⊢; exact h
  rw [ite_eq_right c110] at h ⊢
  by_cases cn : (b == 45 || isDigit b) = true
  · rw [ite_eq_left cn] at h ⊢
    cases hx : parseNumber cfg get n 0 with
    | error e => rw [hx] at h; cases h
    | ok x => rw [hx] at h; rw [parseNumber_relax hx]; exact h
  rw [ite_eq_right cn] at h ⊢
  cases hA : cfg.allowInfNan
  · simp [hA] at h
  · rw [hA] at h; exact h

/-! ## The nesting loop -/

/-- The nesting loop at `base` is the loop at `0` of the view rebased at
`base`. -/
theorem valueGo_rebase (cfg : ParseCfg) (get : Nat → Option UInt8) (n : Nat) :
    ∀ d base, valueGo cfg get n d base = valueGo cfg (fun k => get (base + k)) (n - base) d 0
  | 0, _ => rfl
  | d + 1, base => by
    simp only [valueGo, Nat.zero_add, Nat.sub_zero]
    congr 1
    funext j
    rw [valueGo_rebase cfg get n d (base + j), valueGo_rebase cfg _ (n - base) d j]
    simp only [Nat.add_assoc, Nat.sub_sub]

/-- The view of a list, rebased, is the view of its suffix. -/
theorem lv_rebase (L : List UInt8) (j : Nat) : (fun k => lv L (j + k)) = lv (L.drop j) := by
  funext k; simp [lv]

/-- The nesting loop on a list: the value at its start. -/
abbrev valueL (cfg : ParseCfg) (d : Nat) (L : List UInt8) : Except ParseErr (Json × Nat) :=
  valueGo cfg (lv L) L.length d 0

theorem valueL_succ (cfg : ParseCfg) (d : Nat) (L : List UInt8) :
    valueL cfg (d + 1) L = valueStep cfg (fun j => shiftRes j (valueL cfg d (L.drop j))) (lv L) L.length := by
  simp only [valueL, valueGo, Nat.zero_add, Nat.sub_zero]
  congr 1
  funext j
  rw [valueGo_rebase, lv_rebase, List.length_drop]

/-- **Progress**: a success of the nesting loop ends past its first byte and
within the view. -/
theorem valueL_progress (cfg : ParseCfg) :
    ∀ (d : Nat) (L : List UInt8) {v : Json} {p : Nat}, valueL cfg d L = .ok (v, p) → 0 < p ∧ p ≤ L.length
  | 0, _, _, _, h => by simp [valueL, valueGo] at h
  | d + 1, L, v, p, h => by
    rw [valueL_succ] at h
    refine (valueStep_shape (P := fun _ => True) cfg (viewOk_lv L) ?_ h).2
    intro j w q hj hjn hw
    dsimp only at hw
    cases hc : valueL cfg d (L.drop j) with
    | error e => rw [hc] at hw; cases hw
    | ok r =>
      obtain ⟨w', q'⟩ := r
      rw [hc] at hw; cases hw
      have := valueL_progress cfg d (L.drop j) hc
      simp at this; exact ⟨trivial, by omega, by omega⟩

end LeanJson
