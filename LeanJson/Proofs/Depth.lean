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

/-! ## What every parsed value satisfies

One induction over the parser, for any property `P k v` ("`v`, parsed inside
`k` containers") that holds of each scalar the parser can produce and is
preserved by arrays and objects. The depth bound and strict finiteness are
instances. -/

/-- A property of values, indexed by how many containers they sit in, that the
parser's productions preserve under `cfg`. -/
structure ParseInvariant (cfg : ParseCfg) (P : Nat → Json → Prop) : Prop where
  scalar : ∀ k (a : Json), cfg.depthOk k = true → a.height = 0 → (∀ n, a ≠ .num n) → P k a
  num : ∀ k (bs : ByteArray) pos x p, cfg.depthOk k = true → parseNumber cfg bs pos = .ok (x, p) →
    P k (.num x)
  nonfinite : ∀ k, cfg.depthOk k = true → cfg.allowInfNan = true → P k (.num .nan) ∧ P k (.num .inf)
  arr : ∀ k ys, cfg.depthOk k = true → (∀ y ∈ ys, P (k + 1) y) → P k (.arr ys)
  obj : ∀ k kvs, cfg.depthOk k = true → (∀ kv ∈ kvs, P (k + 1) kv.2) → P k (.obj kvs)

section
variable (cfg : ParseCfg) (P : Nat → Json → Prop) (bs : ByteArray)

def HV (pos : Nat) : Prop :=
  ∀ k r, parseValueAtD cfg bs k pos = .ok r → P k r.1
def HE (pos : Nat) : Prop :=
  ∀ k start acc r, start ≤ pos → parseElemsAt cfg bs k start pos acc = .ok r →
    (∀ x ∈ acc, P k x) → ∃ ys, r.1 = .arr ys ∧ ∀ y ∈ ys, P k y
def HM (pos : Nat) : Prop :=
  ∀ k start acc r, start ≤ pos → parseMembersAt cfg bs k start pos acc = .ok r →
    (∀ kv ∈ acc, P k kv.2) → ∃ kvs, r.1 = .obj kvs ∧ ∀ kv ∈ kvs, P k kv.2
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

theorem hv_step {cfg : ParseCfg} {P : Nat → Json → Prop} (inv : ParseInvariant cfg P) (bs : ByteArray)
    (pos : Nat) (IHe : ∀ p, bs.size - p < bs.size - pos → HE cfg P bs p)
    (IHm : ∀ p, bs.size - p < bs.size - pos → HM cfg P bs p) : HV cfg P bs pos := by
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
  have hk : cfg.depthOk k = true := by simpa using hd
  have scalar : ∀ a : Json, a.height = 0 → (∀ n, a ≠ .num n) → r.1 = a → P k r.1 := by
    intro a ha hn e; rw [e]; exact inv.scalar k a hk ha hn
  by_cases c34 : (b == 34) = true
  · rw [ite_eq_left c34] at h
    obtain ⟨a, e⟩ := map_ok_fst (f := Json.str) h
    exact scalar (.str a) rfl (fun _ h => by cases h) e
  rw [ite_eq_right c34] at h
  by_cases c91 : (b == 91) = true
  · rw [ite_eq_left c91] at h
    split at h
    · cases h
    · rename_i c hp
      have := lt_size_of_get hp
      split at h
      · cases h; exact inv.arr k [] hk (by simp)
      · obtain ⟨ys, e, hys⟩ := IHe _ (by omega) _ _ [] r (by omega) h (by simp)
        rw [e]; exact inv.arr k ys hk hys
  rw [ite_eq_right c91] at h
  by_cases c123 : (b == 123) = true
  · rw [ite_eq_left c123] at h
    split at h
    · cases h
    · rename_i c hp
      have := lt_size_of_get hp
      split at h
      · cases h; exact inv.obj k [] hk (by simp)
      · split at h
        · obtain ⟨kvs, e, hkvs⟩ := IHm _ (by omega) _ _ [] r (by omega) h (by simp)
          rw [e]; exact inv.obj k kvs hk hkvs
        · cases h
  rw [ite_eq_right c123] at h
  by_cases c116 : (b == 116) = true
  · rw [ite_eq_left c116] at h; exact scalar (.bool true) rfl (fun _ h => by cases h) (map_ok_const h)
  rw [ite_eq_right c116] at h
  by_cases c102 : (b == 102) = true
  · rw [ite_eq_left c102] at h; exact scalar (.bool false) rfl (fun _ h => by cases h) (map_ok_const h)
  rw [ite_eq_right c102] at h
  by_cases c110 : (b == 110) = true
  · rw [ite_eq_left c110] at h; exact scalar .null rfl (fun _ h => by cases h) (map_ok_const h)
  rw [ite_eq_right c110] at h
  by_cases cn : (b == 45 || isDigit b) = true
  · rw [ite_eq_left cn] at h
    cases hx : parseNumber cfg bs (skipWs bs pos) with
    | error e => rw [hx] at h; cases h
    | ok x => rw [hx] at h; cases h; exact inv.num k bs _ x.1 x.2 hk hx
  rw [ite_eq_right cn] at h
  by_cases c78 : (b == 78 && cfg.allowInfNan) = true
  · rw [ite_eq_left c78] at h
    rw [map_ok_const h]; exact (inv.nonfinite k hk (by simp at c78; exact c78.2)).1
  rw [ite_eq_right c78] at h
  by_cases c73 : (b == 73 && cfg.allowInfNan) = true
  · rw [ite_eq_left c73] at h
    rw [map_ok_const h]; exact (inv.nonfinite k hk (by simp at c73; exact c73.2)).2
  rw [ite_eq_right c73] at h
  cases h

theorem he_step (cfg : ParseCfg) (P : Nat → Json → Prop) (bs : ByteArray) (pos : Nat)
    (hV : HV cfg P bs pos) (IHe : ∀ p, bs.size - p < bs.size - pos → HE cfg P bs p) :
    HE cfg P bs pos := by
  intro k start acc r hsp h hacc
  rw [parseElemsAt_eq _ _ _ _ _ _ hsp] at h
  split at h
  · cases h
  · rename_i v p1 hv
    have pr := parseValueAtD_progress hv
    have hvh := hV _ _ hv
    have g1 := skipWs_ge bs p1
    have g2 := skipWs_ge bs (skipWs bs p1 + 1)
    have hacc' : ∀ x ∈ v :: acc, P k x := by
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

theorem hm_step (cfg : ParseCfg) (P : Nat → Json → Prop) (bs : ByteArray) (pos : Nat)
    (IHv : ∀ p, bs.size - p < bs.size - pos → HV cfg P bs p)
    (IHm : ∀ p, bs.size - p < bs.size - pos → HM cfg P bs p) : HM cfg P bs pos := by
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
          have hacc' : ∀ kv ∈ (key, v) :: acc, P k kv.2 := by
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

theorem invariant_all {cfg : ParseCfg} {P : Nat → Json → Prop} (inv : ParseInvariant cfg P)
    (bs : ByteArray) : ∀ n pos, bs.size - pos ≤ n → HV cfg P bs pos ∧ HE cfg P bs pos ∧ HM cfg P bs pos := by
  intro n
  induction n with
  | zero =>
    intro pos hp
    have IH0 : ∀ p, bs.size - p < bs.size - pos → False := fun p h => by omega
    have hv := hv_step inv bs pos (fun p h => (IH0 p h).elim) (fun p h => (IH0 p h).elim)
    exact ⟨hv, he_step cfg P bs pos hv (fun p h => (IH0 p h).elim),
      hm_step cfg P bs pos (fun p h => (IH0 p h).elim) (fun p h => (IH0 p h).elim)⟩
  | succ n ih =>
    intro pos hp
    have IH : ∀ p, bs.size - p < bs.size - pos → HV cfg P bs p ∧ HE cfg P bs p ∧ HM cfg P bs p :=
      fun p h => ih p (by omega)
    have hv := hv_step inv bs pos (fun p h => (IH p h).2.1) (fun p h => (IH p h).2.2)
    exact ⟨hv, he_step cfg P bs pos hv (fun p h => (IH p h).2.1),
      hm_step cfg P bs pos (fun p h => (IH p h).1) (fun p h => (IH p h).2.2)⟩

/-- **Every parsed document satisfies an invariant of the parser.** -/
theorem parse_invariant {cfg : ParseCfg} {P : Nat → Json → Prop} (inv : ParseInvariant cfg P)
    {bs : ByteArray} {v : Json} (h : parseDocumentWith cfg bs = .ok v) : P 0 v := by
  unfold parseDocumentWith at h
  split at h
  · cases h
  · rename_i w p hw
    simp only at h
    split at h
    · cases h
    · cases h
      exact (invariant_all inv bs _ 0 (Nat.le_refl _)).1 0 _ hw

/-- The depth bound as a parser invariant. -/
theorem heightInvariant {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) :
    ParseInvariant cfg (fun k v => k + v.height < L) where
  scalar k a hk ha _ := by rw [ha]; simpa using (depthOk_some hL).mp hk
  num k _ _ _ _ hk _ := by simpa [Json.height] using (depthOk_some hL).mp hk
  nonfinite k hk _ := by
    have := (depthOk_some hL).mp hk; exact ⟨by simpa [Json.height], by simpa [Json.height]⟩
  arr k ys hk h := height_arr ((depthOk_some hL).mp hk) (fun y hy => by have := h y hy; omega)
  obj k kvs hk h := height_obj ((depthOk_some hL).mp hk) (fun kv hkv => by have := h kv hkv; omega)

/-- **The depth bound.** Under `maxDepth = some L`, a successful document
parse returns a value of height below `L`. -/
theorem parse_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : v.height < L := by
  simpa using parse_invariant (heightInvariant hL) h

/-- `from_json` never returns a value nested deeper than jiter allows. -/
theorem parseDocument_height {bs : ByteArray} {v : Json} (h : parseDocument bs = .ok v) :
    v.height ≤ 200 := by
  have := parse_height (cfg := {}) (L := 201) rfl h
  omega

theorem parseNumber_strict_finite {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {x : Number} {p : Nat}
    (hs : cfg.allowInfNan = false) (h : parseNumber cfg bs pos = .ok (x, p)) : x.isFinite = true := by
  have body : ∀ {neg p0}, parseNumberBody cfg bs pos neg p0 = .ok (x, p) → x.isFinite = true := by
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
    · rename_i c; simp [hs] at c
    · exact body h
  · exact body h

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

/-- Strict finiteness as a parser invariant. -/
theorem finiteInvariant (cfg : ParseCfg) :
    ParseInvariant cfg (fun _ v => cfg.allowInfNan = false → v.allFinite = true) where
  scalar _ a _ ha hn _ := by
    cases a with
    | num n => exact absurd rfl (hn n)
    | arr xs => cases xs with
      | nil => rfl
      | cons _ _ => simp [Json.height] at ha
    | obj kvs => cases kvs with
      | nil => rfl
      | cons kv _ => obtain ⟨_, _⟩ := kv; simp [Json.height] at ha
    | _ => rfl
  num _ _ _ _ _ _ hx hs := by simpa [Json.allFinite] using parseNumber_strict_finite hs hx
  nonfinite _ _ ha := ⟨fun hs => absurd (ha.symm.trans hs) (by decide),
    fun hs => absurd (ha.symm.trans hs) (by decide)⟩
  arr _ ys _ h hs := by simpa [Json.allFinite] using allFiniteList_of (fun y hy => h y hy hs)
  obj _ kvs _ h hs := by simpa [Json.allFinite] using allFiniteFields_of (fun kv hkv => h kv hkv hs)

/-- **Strict mode returns RFC 8259 JSON**: no `NaN` or infinity. -/
theorem parse_finite {cfg : ParseCfg} (hs : cfg.allowInfNan = false) {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : v.allFinite = true :=
  parse_invariant (finiteInvariant cfg) h hs

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

mutual
theorem fitsAt_of : ∀ (a : Bool) (k : Nat) (v : Json), FitsAt { maxDepth := none } k v →
    k + v.height < 201 → (a = true ∨ v.allFinite = true) → FitsAt { allowInfNan := a } k v
  | a, k, .null, _, hh, _ | a, k, .bool _, _, hh, _ | a, k, .str _, _, hh, _ => by
    simp [FitsAt, ParseCfg.depthOk, Json.height] at hh ⊢; omega
  | a, k, .num _, h, hh, hf => by
    refine ⟨?_, h.2.1, by simpa [Json.allFinite] using hf⟩
    simp [ParseCfg.depthOk, Json.height] at hh ⊢; omega
  | a, k, .arr xs, h, hh, hf => by
    refine ⟨?_, fitsList_of a (k + 1) xs h.2 ?_ (by simpa [Json.allFinite] using hf)⟩
    · cases xs <;> simp [ParseCfg.depthOk, Json.height] at hh ⊢ <;> omega
    · intro x hx
      cases xs with
      | nil => cases hx
      | cons y ys =>
        have := height_le_list hx
        simp only [Json.height, Json.heightList] at hh this; omega
  | a, k, .obj kvs, h, hh, hf => by
    refine ⟨?_, fitsFields_of a (k + 1) kvs h.2 ?_ (by simpa [Json.allFinite] using hf)⟩
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
theorem fitsList_of : ∀ (a : Bool) (k : Nat) (xs : List Json), FitsList { maxDepth := none } k xs →
    (∀ x ∈ xs, k + x.height < 201) → (a = true ∨ Json.allFiniteList xs = true) →
    FitsList { allowInfNan := a } k xs
  | _, _, [], _, _, _ => trivial
  | a, k, x :: xs, h, hh, hf =>
    ⟨fitsAt_of a k x h.1 (hh x (by simp)) (or_list hf).1,
      fitsList_of a k xs h.2 (fun y hy => hh y (by simp [hy])) (or_list hf).2⟩
theorem fitsFields_of : ∀ (a : Bool) (k : Nat) (kvs : List (String × Json)),
    FitsFields { maxDepth := none } k kvs → (∀ kv ∈ kvs, k + kv.2.height < 201) →
    (a = true ∨ Json.allFiniteFields kvs = true) → FitsFields { allowInfNan := a } k kvs
  | _, _, [], _, _, _ => trivial
  | a, k, (key, v) :: kvs, h, hh, hf =>
    ⟨fitsAt_of a k v h.1 (hh (key, v) (by simp)) (or_fields hf).1,
      fitsFields_of a k kvs h.2 (fun y hy => hh y (by simp [hy])) (or_fields hf).2⟩
end

/-- A value whose integers fit and whose height is at most 200 is within the
default limits. -/
theorem fits_default {j : Json} (hint : IntsFit j) (hdepth : j.height ≤ 200) : Fits {} j :=
  fitsAt_of true 0 j hint (by omega) (Or.inl rfl)

/-- …and within the strict limits, when it has no NaN or infinity. -/
theorem fits_strict {j : Json} (hint : IntsFit j) (hdepth : j.height ≤ 200)
    (hfin : j.allFinite = true) : Fits .strict j :=
  fitsAt_of false 0 j hint (by omega) (Or.inr hfin)

end LeanJson
