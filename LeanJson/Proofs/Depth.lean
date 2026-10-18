import LeanJson.Proofs.Grammar
import LeanJson.Proofs.Value

/-!
# Proofs: the depth limit and strict finiteness

`valueL_height`: a value read with `d` levels left has height below `d`, so
under `maxDepth = some L` nothing nested deeper than jiter allows is returned.
`valueL_finite`: in strict mode no `NaN` or infinity is returned. Both are one
induction on the levels, with `valueStep_shape` at each.

`fits_height`: a value within a configuration's limits is lower than its depth
limit; `fits_default`: a value whose integers fit, whose keys are unique and
whose height is at most 200 is within the default limits.
-/

namespace LeanJson

open Spec

theorem depthOk_some {cfg : ParseCfg} {L k : Nat} (hL : cfg.maxDepth = some L) :
    cfg.depthOk k = true ↔ k < L := by
  simp [ParseCfg.depthOk, hL]

theorem heightList_lt {xs : List Json} {m : Nat} (h : ∀ y ∈ xs, y.height < m) (hm : 0 < m) :
    Json.heightList xs < m := by
  induction xs with
  | nil => simpa [Json.heightList]
  | cons y ys ih =>
    simp only [Json.heightList]
    exact Nat.max_lt.mpr ⟨h y (by simp), ih (fun z hz => h z (by simp [hz]))⟩

theorem heightFields_lt {kvs : List (String × Json)} {m : Nat} (h : ∀ kv ∈ kvs, kv.2.height < m)
    (hm : 0 < m) : Json.heightFields kvs < m := by
  induction kvs with
  | nil => simpa [Json.heightFields]
  | cons y ys ih =>
    obtain ⟨k, v⟩ := y
    simp only [Json.heightFields]
    exact Nat.max_lt.mpr ⟨h (k, v) (by simp), ih (fun z hz => h z (by simp [hz]))⟩

theorem height_arr {ys : List Json} {k L : Nat} (hk : k < L) (h : ∀ y ∈ ys, k + 1 + y.height < L) :
    k + (Json.arr ⟨ys⟩).height < L := by
  cases ys with
  | nil => simpa [Json.height]
  | cons y ys =>
    have := heightList_lt (xs := y :: ys) (m := L - k - 1) (fun z hz => by have := h z hz; omega)
      (by have := h y (by simp); omega)
    simp only [Json.heightList] at this
    simp only [Json.height]; omega

theorem height_obj {kvs : List (String × Json)} {k L : Nat} (hk : k < L)
    (h : ∀ kv ∈ kvs, k + 1 + kv.2.height < L) : k + (Json.obj ⟨kvs⟩).height < L := by
  cases kvs with
  | nil => simpa [Json.height]
  | cons kv kvs =>
    obtain ⟨key, v⟩ := kv
    have := heightFields_lt (kvs := (key, v) :: kvs) (m := L - k - 1)
      (fun z hz => by have := h z hz; omega) (by have := h (key, v) (by simp); simp at this; omega)
    simp only [Json.heightFields] at this
    simp only [Json.height]; omega

/-- **The depth bound**: a value read with `d` levels left has height below
`d`. -/
theorem valueL_height (cfg : ParseCfg) :
    ∀ (d : Nat) (L : List UInt8) {v : Json} {p : Nat}, valueL cfg d L = .ok (v, p) → v.height < d
  | 0, _, _, _, h => by simp [valueL, valueGo] at h
  | d + 1, L, v, p, h => by
    rw [valueL_succ] at h
    have hn := (valueStep_shape (P := fun w => w.height < d) cfg (viewOk_lv L) ?_ h).1
    · match v, hn with
      | .arr ⟨[]⟩, _ | .obj ⟨[]⟩, _ => simp [Json.height]
      | .arr ⟨x :: xs⟩, hn =>
        have := heightList_lt (xs := x :: xs) hn (by have := hn x (by simp); omega)
        simp only [Json.heightList] at this; simp only [Json.height]; omega
      | .obj ⟨(k, w) :: kvs⟩, hn =>
        have := heightFields_lt (kvs := (k, w) :: kvs) hn (by have := hn (k, w) (by simp); simp at this; omega)
        simp only [Json.heightFields] at this; simp only [Json.height]; omega
      | .null, _ | .bool _, _ | .num _, _ | .str _, _ => simp [Json.height]
    · intro j w q _ _ hw
      dsimp only at hw
      cases hc : valueL cfg d (L.drop j) with
      | error e => rw [hc] at hw; cases hw
      | ok r =>
        obtain ⟨w', q'⟩ := r
        rw [hc] at hw; cases hw
        have := (valueL_progress cfg d _ hc)
        simp at this
        exact ⟨valueL_height cfg d _ hc, by omega, by omega⟩

theorem allFiniteList_of {xs : List Json} (h : ∀ y ∈ xs, y.allFinite = true) :
    Json.allFiniteList xs = true := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [Json.allFiniteList, Bool.and_eq_true]
    exact ⟨h y (by simp), ih (fun z hz => h z (by simp [hz]))⟩

theorem allFiniteFields_of {kvs : List (String × Json)} (h : ∀ kv ∈ kvs, kv.2.allFinite = true) :
    Json.allFiniteFields kvs = true := by
  induction kvs with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨k, v⟩ := y
    simp only [Json.allFiniteFields, Bool.and_eq_true]
    exact ⟨h (k, v) (by simp), ih (fun z hz => h z (by simp [hz]))⟩

/-- **Strict mode returns RFC 8259 JSON**: under `allowInfNan = false`, no
value read has a `NaN` or infinity. -/
theorem valueL_finite (cfg : ParseCfg) (hs : cfg.allowInfNan = false) :
    ∀ (d : Nat) (L : List UInt8) {v : Json} {p : Nat}, valueL cfg d L = .ok (v, p) → v.allFinite = true
  | 0, _, _, _, h => by simp [valueL, valueGo] at h
  | d + 1, L, v, p, h => by
    rw [valueL_succ] at h
    have hn := (valueStep_shape (P := fun w => w.allFinite = true) cfg (viewOk_lv L) ?_ h).1
    · match v, hn with
      | .arr ⟨xs⟩, hn => simpa [Json.allFinite] using allFiniteList_of hn
      | .obj ⟨kvs⟩, hn => simpa [Json.allFinite] using allFiniteFields_of hn
      | .num x, hn => simpa [Node, Json.allFinite, hs] using hn
      | .null, _ | .bool _, _ | .str _, _ => rfl
    · intro j w q _ _ hw
      dsimp only at hw
      cases hc : valueL cfg d (L.drop j) with
      | error e => rw [hc] at hw; cases hw
      | ok r =>
        obtain ⟨w', q'⟩ := r
        rw [hc] at hw; cases hw
        have := (valueL_progress cfg d _ hc)
        simp at this
        exact ⟨valueL_finite cfg hs d _ hc, by omega, by omega⟩

mutual
/-- A value within `cfg`'s limits, inside `k` containers, is lower than its
depth limit. -/
theorem fitsAt_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) :
    ∀ (k : Nat) (v : Json), FitsAt cfg k v → k + v.height < L
  | k, .arr ⟨xs⟩, h => height_arr ((depthOk_some hL).mp h.1) (fitsList_height hL (k + 1) xs h.2)
  | k, .obj ⟨kvs⟩, h => height_obj ((depthOk_some hL).mp h.1) (fitsFields_height hL (k + 1) kvs h.2.2)
  | k, .num _, h => by simpa [Json.height] using (depthOk_some hL).mp h.1
  | k, .null, h | k, .bool _, h | k, .str _, h => by simpa [Json.height] using (depthOk_some hL).mp h
theorem fitsList_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) :
    ∀ (k : Nat) (xs : List Json), FitsList cfg k xs → ∀ x ∈ xs, k + x.height < L
  | _, [], _, _, hx => nomatch hx
  | k, x :: xs, h, y, hy =>
    (List.mem_cons.mp hy).elim (fun e => e ▸ fitsAt_height hL k x h.1) (fitsList_height hL k xs h.2 y)
theorem fitsFields_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) :
    ∀ (k : Nat) (kvs : List (String × Json)), FitsFields cfg k kvs → ∀ kv ∈ kvs, k + kv.2.height < L
  | _, [], _, _, hx => nomatch hx
  | k, (_, v) :: kvs, h, y, hy =>
    (List.mem_cons.mp hy).elim (fun e => e ▸ fitsAt_height hL k v h.1) (fitsFields_height hL k kvs h.2 y)
end

theorem fits_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) {v : Json} (h : Fits cfg v) :
    v.height < L := by
  simpa using fitsAt_height hL 0 v h

/-! ## Values within the limits -/

theorem or_list {A : Prop} {x : Json} {xs : List Json}
    (h : A ∨ Json.allFiniteList (x :: xs) = true) : (A ∨ x.allFinite = true) ∧ (A ∨ Json.allFiniteList xs = true) := by
  simp only [Json.allFiniteList, Bool.and_eq_true] at h
  exact ⟨h.imp id And.left, h.imp id And.right⟩

theorem or_fields {A : Prop} {k : String} {v : Json} {kvs : List (String × Json)}
    (h : A ∨ Json.allFiniteFields ((k, v) :: kvs) = true) :
    (A ∨ v.allFinite = true) ∧ (A ∨ Json.allFiniteFields kvs = true) := by
  simp only [Json.allFiniteFields, Bool.and_eq_true] at h
  exact ⟨h.imp id And.left, h.imp id And.right⟩

/-- The configuration `IntsFit` is stated for: jiter's integer limit only. -/
abbrev intsCfg : ParseCfg := { maxDepth := none, dedupKeys := false }
/-- The configuration `KeysUnique` is stated for: distinct keys only. -/
abbrev keysCfg : ParseCfg := { ParseCfg.lossless with dedupKeys := true }

mutual
theorem fitsAt_of : ∀ (a : Bool) (k : Nat) (v : Json), FitsAt intsCfg k v → FitsAt keysCfg k v →
    k + v.height < 201 → (a = true ∨ v.allFinite = true) → FitsAt { allowInfNan := a } k v
  | a, k, .null, _, _, hh, _ | a, k, .bool _, _, _, hh, _ | a, k, .str _, _, _, hh, _ => by
    simp [FitsAt, ParseCfg.depthOk, Json.height] at hh ⊢; omega
  | a, k, .num _, h, _, hh, hf => by
    refine ⟨?_, h.2.1, by simpa [Json.allFinite] using hf⟩
    simp [ParseCfg.depthOk, Json.height] at hh ⊢; omega
  | a, k, .arr ⟨xs⟩, h, u, hh, hf => by
    refine ⟨?_, fitsList_of a (k + 1) xs h.2 u.2 ?_ (by simpa [Json.allFinite] using hf)⟩
    · cases xs <;> simp [ParseCfg.depthOk, Json.height] at hh ⊢ <;> omega
    · intro x hx
      cases xs with
      | nil => cases hx
      | cons y ys =>
        have := height_le_list hx
        simp only [Json.height, Json.heightList] at hh this; omega
  | a, k, .obj ⟨kvs⟩, h, u, hh, hf => by
    refine ⟨?_, u.2.1, fitsFields_of a (k + 1) kvs h.2.2 u.2.2 ?_ (by simpa [Json.allFinite] using hf)⟩
    · cases kvs with
      | nil => simp [ParseCfg.depthOk, Json.height] at hh ⊢; omega
      | cons kv kvs => obtain ⟨_, _⟩ := kv; simp [ParseCfg.depthOk, Json.height] at hh ⊢; omega
    · intro kv hkv
      cases kvs with
      | nil => cases hkv
      | cons y ys =>
        obtain ⟨_, _⟩ := y
        have := height_le_fields hkv
        simp only [Json.height, Json.heightFields] at hh this; omega
theorem fitsList_of : ∀ (a : Bool) (k : Nat) (xs : List Json), FitsList intsCfg k xs →
    FitsList keysCfg k xs → (∀ x ∈ xs, k + x.height < 201) → (a = true ∨ Json.allFiniteList xs = true) →
    FitsList { allowInfNan := a } k xs
  | _, _, [], _, _, _, _ => trivial
  | a, k, x :: xs, h, u, hh, hf =>
    ⟨fitsAt_of a k x h.1 u.1 (hh x (by simp)) (or_list hf).1,
      fitsList_of a k xs h.2 u.2 (fun y hy => hh y (by simp [hy])) (or_list hf).2⟩
theorem fitsFields_of : ∀ (a : Bool) (k : Nat) (kvs : List (String × Json)),
    FitsFields intsCfg k kvs → FitsFields keysCfg k kvs → (∀ kv ∈ kvs, k + kv.2.height < 201) →
    (a = true ∨ Json.allFiniteFields kvs = true) → FitsFields { allowInfNan := a } k kvs
  | _, _, [], _, _, _, _ => trivial
  | a, k, (key, v) :: kvs, h, u, hh, hf =>
    ⟨fitsAt_of a k v h.1 u.1 (hh (key, v) (by simp)) (or_fields hf).1,
      fitsFields_of a k kvs h.2 u.2 (fun y hy => hh y (by simp [hy])) (or_fields hf).2⟩
end

/-- A value whose integers fit, whose keys are unique and whose height is at
most 200 is within the default limits. -/
theorem fits_default {j : Json} (hint : IntsFit j) (hkeys : KeysUnique j) (hdepth : j.height ≤ 200) :
    Fits {} j :=
  fitsAt_of true 0 j hint hkeys (by omega) (Or.inl rfl)

/-- …and within the strict limits, when it has no NaN or infinity. -/
theorem fits_strict {j : Json} (hint : IntsFit j) (hkeys : KeysUnique j) (hdepth : j.height ≤ 200)
    (hfin : j.allFinite = true) : Fits .strict j :=
  fitsAt_of false 0 j hint hkeys (by omega) (Or.inr hfin)

end LeanJson
