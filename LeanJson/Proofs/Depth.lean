import LeanJson.Proofs.Codec

/-!
# Proofs: the depth limit

`parse_height`: under a configuration with `maxDepth = some L`, every value the
parser returns has `height < L`: input nested deeper is never accepted. With
jiter's default (201) that is `height ≤ 200`, matching `from_json`.

`fits_default`: a value whose integers fit and whose height is at most 200
is within the default limits, so `parse_print` applies to it.
-/

namespace LeanJson

open Spec

theorem depthOk_some {cfg : ParseCfg} {L k : Nat} (hL : cfg.maxDepth = some L) :
    cfg.depthOk k = true ↔ k < L := by
  simp [ParseCfg.depthOk, hL]

theorem height_le_list {x : Json} {xs : List Json} (h : x ∈ xs) : x.height ≤ Json.heightList xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [Json.heightList]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem height_le_fields {kv : String × Json} {kvs : List (String × Json)} (h : kv ∈ kvs) :
    kv.2.height ≤ Json.heightFields kvs := by
  induction kvs with
  | nil => cases h
  | cons y ys ih =>
    obtain ⟨k, v⟩ := y
    simp only [Json.heightFields]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

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
    k + (Json.arr ys).height < L := by
  cases ys with
  | nil => simpa [Json.height]
  | cons y ys =>
    have := heightList_lt (xs := y :: ys) (m := L - k - 1) (fun z hz => by have := h z hz; omega)
      (by have := h y (by simp); omega)
    simp only [Json.heightList] at this
    simp only [Json.height]; omega

theorem height_obj {kvs : List (String × Json)} {k L : Nat} (hk : k < L)
    (h : ∀ kv ∈ kvs, k + 1 + kv.2.height < L) : k + (Json.obj kvs).height < L := by
  cases kvs with
  | nil => simpa [Json.height]
  | cons kv kvs =>
    obtain ⟨key, v⟩ := kv
    have := heightFields_lt (kvs := (key, v) :: kvs) (m := L - k - 1)
      (fun z hz => by have := h z hz; omega) (by have := h (key, v) (by simp); simp at this; omega)
    simp only [Json.heightFields] at this
    simp only [Json.height]; omega

/-! ## Parsed values respect the limit -/

section
variable (cfg : ParseCfg) (L : Nat) (bs : ByteArray)

def HV (pos : Nat) : Prop :=
  ∀ k r, parseValueAtD cfg bs k pos = .ok r → k + r.1.height < L
def HE (pos : Nat) : Prop :=
  ∀ k start acc r, start ≤ pos → parseElemsAt cfg bs k start pos acc = .ok r →
    (∀ x ∈ acc, k + x.height < L) → ∃ ys, r.1 = .arr ys ∧ ∀ y ∈ ys, k + y.height < L
def HM (pos : Nat) : Prop :=
  ∀ k start acc r, start ≤ pos → parseMembersAt cfg bs k start pos acc = .ok r →
    (∀ kv ∈ acc, k + kv.2.height < L) → ∃ kvs, r.1 = .obj kvs ∧ ∀ kv ∈ kvs, k + kv.2.height < L
end

theorem map_ok_fst {α : Type} {f : α → Json} {r : Except ParseErr (α × Nat)} {x : Json × Nat}
    (h : r.map (fun y => (f y.1, y.2)) = .ok x) : ∃ a, x.1 = f a := by
  cases r with
  | error e => cases h
  | ok y => cases h; exact ⟨y.1, rfl⟩

theorem map_ok_const {α : Type} {c : Json} {r : Except ParseErr α} {x : Json × α}
    (h : r.map (fun p => (c, p)) = .ok x) : x.1 = c := by
  cases r with
  | error e => cases h
  | ok y => cases h; rfl

theorem hv_step (cfg : ParseCfg) (L : Nat) (hL : cfg.maxDepth = some L) (bs : ByteArray) (pos : Nat)
    (IHe : ∀ p, bs.size - p < bs.size - pos → HE cfg L bs p)
    (IHm : ∀ p, bs.size - p < bs.size - pos → HM cfg L bs p) : HV cfg L bs pos := by
  intro k r h
  rw [parseValueAtD_eq] at h
  have g0 := skipWs_ge bs pos
  have g1 := skipWs_ge bs (skipWs bs pos + 1)
  split at h
  · cases h
  rename_i b hb
  by_cases hd : cfg.depthOk k = false
  · rw [ite_eq_left hd] at h; cases h
  rw [ite_eq_right hd] at h
  have hk : k < L := (depthOk_some hL).mp (by simpa using hd)
  have scalar : ∀ (a : Json), a.height = 0 → r.1 = a → k + r.1.height < L := by
    intro a ha e; rw [e, ha]; omega
  by_cases c34 : (b == 34) = true
  · rw [ite_eq_left c34] at h
    obtain ⟨a, e⟩ := map_ok_fst (f := Json.str) h; exact scalar (.str a) rfl e
  rw [ite_eq_right c34] at h
  by_cases c91 : (b == 91) = true
  · rw [ite_eq_left c91] at h
    split at h
    · cases h
    · rename_i c hp
      have := lt_size_of_get hp
      split at h
      · cases h; exact scalar _ rfl rfl
      · obtain ⟨ys, e, hys⟩ := IHe _ (by omega) _ _ [] r (by omega) h (by simp)
        rw [e]; exact height_arr hk (fun y hy => by have := hys y hy; omega)
  rw [ite_eq_right c91] at h
  by_cases c123 : (b == 123) = true
  · rw [ite_eq_left c123] at h
    split at h
    · cases h
    · rename_i c hp
      have := lt_size_of_get hp
      split at h
      · cases h; exact scalar _ rfl rfl
      · split at h
        · obtain ⟨kvs, e, hkvs⟩ := IHm _ (by omega) _ _ [] r (by omega) h (by simp)
          rw [e]; exact height_obj hk (fun kv hkv => by have := hkvs kv hkv; omega)
        · cases h
  rw [ite_eq_right c123] at h
  by_cases c116 : (b == 116) = true
  · rw [ite_eq_left c116] at h; exact scalar (.bool true) rfl (map_ok_const h)
  rw [ite_eq_right c116] at h
  by_cases c102 : (b == 102) = true
  · rw [ite_eq_left c102] at h; exact scalar (.bool false) rfl (map_ok_const h)
  rw [ite_eq_right c102] at h
  by_cases c110 : (b == 110) = true
  · rw [ite_eq_left c110] at h; exact scalar .null rfl (map_ok_const h)
  rw [ite_eq_right c110] at h
  by_cases cn : (b == 45 || isDigit b) = true
  · rw [ite_eq_left cn] at h
    obtain ⟨a, e⟩ := map_ok_fst (f := fun n : Number => Json.num n) h; exact scalar (.num a) rfl e
  rw [ite_eq_right cn] at h
  cases h

theorem he_step (cfg : ParseCfg) (L : Nat) (bs : ByteArray) (pos : Nat) (hV : HV cfg L bs pos)
    (IHe : ∀ p, bs.size - p < bs.size - pos → HE cfg L bs p) : HE cfg L bs pos := by
  intro k start acc r hsp h hacc
  rw [parseElemsAt_eq _ _ _ _ _ _ hsp] at h
  split at h
  · cases h
  · rename_i v p1 hv
    have pr := parseValueAtD_progress hv
    have hvh := hV _ _ hv
    have g1 := skipWs_ge bs p1
    have g2 := skipWs_ge bs (skipWs bs p1 + 1)
    have hacc' : ∀ x ∈ v :: acc, k + x.height < L := by
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx
      · exact hvh
      · exact hacc x hx
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · exact IHe _ (by simp at pr; omega) _ _ _ r (by simp at pr; omega) h hacc'
      · split at h
        · cases h; exact ⟨_, rfl, fun y hy => hacc' y (List.mem_reverse.mp hy)⟩
        · cases h

theorem hm_step (cfg : ParseCfg) (L : Nat) (bs : ByteArray) (pos : Nat)
    (IHv : ∀ p, bs.size - p < bs.size - pos → HV cfg L bs p)
    (IHm : ∀ p, bs.size - p < bs.size - pos → HM cfg L bs p) : HM cfg L bs pos := by
  intro k start acc r hsp h hacc
  rw [parseMembersAt_eq _ _ _ _ _ _ hsp] at h
  split at h
  · cases h
  · rename_i key p1 hk
    have pk := (parseString_adv hk).2
    have g1 := skipWs_ge bs p1
    split at h
    · cases h
    · rename_i c hp
      have hps := lt_size_of_get hp
      split at h
      · split at h
        · cases h
        · rename_i v p2 hv
          have pr := parseValueAtD_progress hv
          have hvh := IHv _ (by omega) _ _ hv
          have g2 := skipWs_ge bs p2
          have g3 := skipWs_ge bs (skipWs bs p2 + 1)
          have hacc' : ∀ kv ∈ (key, v) :: acc, k + kv.2.height < L := by
            intro kv hx; rcases List.mem_cons.mp hx with rfl | hx
            · exact hvh
            · exact hacc kv hx
          split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · rename_i f he
                have hqs := lt_size_of_get he
                split at h
                · exact IHm _ (by simp at pr; omega) _ _ _ r (by simp at pr; omega) h hacc'
                · split at h <;> cases h
            · split at h
              · cases h; exact ⟨_, rfl, fun kv hkv => hacc' kv (List.mem_reverse.mp hkv)⟩
              · cases h
      · cases h

theorem height_all (cfg : ParseCfg) (L : Nat) (hL : cfg.maxDepth = some L) (bs : ByteArray) :
    ∀ n pos, bs.size - pos ≤ n → HV cfg L bs pos ∧ HE cfg L bs pos ∧ HM cfg L bs pos := by
  intro n
  induction n with
  | zero =>
    intro pos hp
    have IH0 : ∀ p, bs.size - p < bs.size - pos → False := fun p h => by omega
    have hv := hv_step cfg L hL bs pos (fun p h => (IH0 p h).elim) (fun p h => (IH0 p h).elim)
    exact ⟨hv, he_step cfg L bs pos hv (fun p h => (IH0 p h).elim),
      hm_step cfg L bs pos (fun p h => (IH0 p h).elim) (fun p h => (IH0 p h).elim)⟩
  | succ n ih =>
    intro pos hp
    have IH : ∀ p, bs.size - p < bs.size - pos → HV cfg L bs p ∧ HE cfg L bs p ∧ HM cfg L bs p :=
      fun p h => ih p (by omega)
    have hv := hv_step cfg L hL bs pos (fun p h => (IH p h).2.1) (fun p h => (IH p h).2.2)
    exact ⟨hv, he_step cfg L bs pos hv (fun p h => (IH p h).2.1),
      hm_step cfg L bs pos (fun p h => (IH p h).1) (fun p h => (IH p h).2.2)⟩

/-- **The depth bound.** Under `maxDepth = some L`, a successful document
parse returns a value of height below `L`. -/
theorem parse_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : v.height < L := by
  unfold parseDocumentWith at h
  split at h
  · cases h
  · rename_i w p hw
    simp only at h
    split at h
    · cases h
    · cases h
      have := (height_all cfg L hL bs _ 0 (Nat.le_refl _)).1 0 _ hw
      simpa using this

/-- `from_json` never returns a value nested deeper than jiter allows. -/
theorem parseDocument_height {bs : ByteArray} {v : Json} (h : parseDocument bs = .ok v) :
    v.height ≤ 200 := by
  have := parse_height (cfg := {}) (L := 201) rfl h
  omega

/-! ## Values within the limits -/

mutual
theorem fitsAt_default : ∀ (k : Nat) (v : Json), FitsAt { maxDepth := none } k v →
    k + v.height < 201 → FitsAt {} k v
  | k, .null, _, hh | k, .bool _, _, hh | k, .str _, _, hh => by
    simp [FitsAt, ParseCfg.depthOk, Json.height] at hh ⊢; omega
  | k, .num _, h, hh => by
    refine ⟨?_, h.2⟩; simp [ParseCfg.depthOk, Json.height] at hh ⊢; omega
  | k, .arr xs, h, hh => by
    refine ⟨?_, fitsList_default (k + 1) xs h.2 ?_⟩
    · cases xs <;> simp [ParseCfg.depthOk, Json.height] at hh ⊢ <;> omega
    · intro x hx
      cases xs with
      | nil => cases hx
      | cons y ys =>
        have := height_le_list hx
        simp only [Json.height, Json.heightList] at hh this; omega
  | k, .obj kvs, h, hh => by
    refine ⟨?_, fitsFields_default (k + 1) kvs h.2 ?_⟩
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
theorem fitsList_default : ∀ (k : Nat) (xs : List Json), FitsList { maxDepth := none } k xs →
    (∀ x ∈ xs, k + x.height < 201) → FitsList {} k xs
  | _, [], _, _ => trivial
  | k, x :: xs, h, hh =>
    ⟨fitsAt_default k x h.1 (hh x (by simp)),
      fitsList_default k xs h.2 (fun y hy => hh y (by simp [hy]))⟩
theorem fitsFields_default : ∀ (k : Nat) (kvs : List (String × Json)),
    FitsFields { maxDepth := none } k kvs → (∀ kv ∈ kvs, k + kv.2.height < 201) → FitsFields {} k kvs
  | _, [], _, _ => trivial
  | k, (key, v) :: kvs, h, hh =>
    ⟨fitsAt_default k v h.1 (hh (key, v) (by simp)),
      fitsFields_default k kvs h.2 (fun y hy => hh y (by simp [hy]))⟩
end

/-- A value whose integers fit and whose height is at most 200 is within the
default limits. -/
theorem fits_default {j : Json} (hint : IntsFit j) (hdepth : j.height ≤ 200) : Fits {} j :=
  fitsAt_default 0 j hint (by omega)

end LeanJson
