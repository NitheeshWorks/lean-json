import LeanJson.Proofs.Progress

/-!
# Proofs: digits, digit runs, decimal normal form
-/

namespace LeanJson

open Spec

theorem foldl_digits (l : List Nat) (a : Nat) :
    l.foldl (fun a d => a * 10 + d) a = a * 10 ^ l.length + ofDigits l := by
  induction l generalizing a with
  | nil => simp [ofDigits]
  | cons d l ih =>
    simp only [List.foldl_cons, ofDigits] at *
    rw [ih, ih (0 * 10 + d), List.length_cons, Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ _)]
    omega

theorem ofDigits_append (l₁ l₂ : List Nat) :
    ofDigits (l₁ ++ l₂) = ofDigits l₁ * 10 ^ l₂.length + ofDigits l₂ := by
  unfold ofDigits
  rw [List.foldl_append, foldl_digits]; rfl

@[simp] theorem ofDigits_nil : ofDigits [] = 0 := rfl

theorem ofDigits_cons (d : Nat) (l : List Nat) :
    ofDigits (d :: l) = d * 10 ^ l.length + ofDigits l := by
  have := ofDigits_append [d] l
  simpa [ofDigits] using this

theorem ofDigits_replicate_zero (k : Nat) (l : List Nat) :
    ofDigits (List.replicate k 0 ++ l) = ofDigits l := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, ofDigits_cons, ih]; simp

theorem ofDigits_replicate_zero_right (l : List Nat) (k : Nat) :
    ofDigits (l ++ List.replicate k 0) = ofDigits l * 10 ^ k := by
  rw [ofDigits_append]
  have := ofDigits_replicate_zero k []
  simp only [List.append_nil] at this
  simp [this]

/-! ## `natDigits` -/

theorem natDigitsAux_append : ∀ (f n : Nat) (acc : List Nat), n < f →
    natDigitsAux f n acc = natDigitsAux f n [] ++ acc
  | 0, _, _, h => by omega
  | f + 1, n, acc, h => by
    unfold natDigitsAux
    by_cases hn : n < 10
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      rw [natDigitsAux_append f (n / 10) _ (by omega),
        natDigitsAux_append f (n / 10) [n % 10] (by omega)]
      simp

theorem natDigitsAux_fuel : ∀ (f g n : Nat), n < f → n < g →
    natDigitsAux f n [] = natDigitsAux g n []
  | 0, _, _, h, _ => by omega
  | _, 0, _, _, h => by omega
  | f + 1, g + 1, n, hf, hg => by
    unfold natDigitsAux
    by_cases hn : n < 10
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      rw [natDigitsAux_append f _ _ (by omega), natDigitsAux_append g _ _ (by omega),
        natDigitsAux_fuel f g (n / 10) (by omega) (by omega)]

theorem smallDigits_lt (n : Nat) (h : n < 10) : smallDigits n = [n] := by
  unfold smallDigits; cases n <;> simp [natDigitsAux] <;> omega

theorem smallDigits_ge (n : Nat) (h : 10 ≤ n) :
    smallDigits n = smallDigits (n / 10) ++ [n % 10] := by
  unfold smallDigits
  conv => lhs; unfold natDigitsAux
  simp only [show ¬ n < 10 by omega, ↓reduceIte]
  rw [natDigitsAux_append _ _ _ (by omega), natDigitsAux_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)]

/-- What a digit list for `n` must satisfy. -/
def DigitsOf (n : Nat) (l : List Nat) : Prop :=
  ofDigits l = n ∧ (∀ d ∈ l, d < 10) ∧
    ∃ h t, l = h :: t ∧ (n ≠ 0 → h ≠ 0) ∧ (h = 0 → t = [])

theorem smallDigits_spec (n : Nat) : DigitsOf n (smallDigits n) := by
  by_cases hn : n < 10
  · rw [smallDigits_lt n hn]
    refine ⟨by simp [ofDigits], by simpa using hn, n, [], rfl, id, fun _ => rfl⟩
  · have ih := smallDigits_spec (n / 10)
    rw [smallDigits_ge n (by omega)]
    obtain ⟨h1, h2, h, t, h3, h4, _⟩ := ih
    refine ⟨?_, ?_, h, t ++ [n % 10], by rw [h3]; rfl, fun _ => h4 (by omega), ?_⟩
    · rw [ofDigits_append, h1]; simp [ofDigits]; omega
    · intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | hd
      · exact h2 d hd
      · omega
    · intro h0; exact absurd h0 (h4 (by omega))
termination_by n
decreasing_by omega

theorem smallDigits_length (n k : Nat) (hk : 1 ≤ k) (h : n < 10 ^ k) : (smallDigits n).length ≤ k := by
  by_cases hn : n < 10
  · rw [smallDigits_lt n hn]; simpa using hk
  · rw [smallDigits_ge n (by omega)]
    have h1 : 1 ≤ k - 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this; simp at h; omega
      · omega
    have h2 : n / 10 < 10 ^ (k - 1) := by
      have : 10 ^ k = 10 ^ (k - 1) * 10 := by rw [← Nat.pow_succ]; congr 1; omega
      rw [this] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    have := smallDigits_length (n / 10) (k - 1) h1 h2
    simp; omega
termination_by n
decreasing_by omega

theorem ofDigits_pad (h : Nat) (l : List Nat) : ofDigits (padDigits h l) = ofDigits l := by
  unfold padDigits; exact ofDigits_replicate_zero _ _

theorem pad_length (h : Nat) (l : List Nat) (hl : l.length ≤ h) : (padDigits h l).length = h := by
  unfold padDigits; simp; omega

theorem ten_pow_le (n : Nat) : 10 ^ (n.log2 * 3 / 20) ≤ n ∨ n = 0 := by
  by_cases hn : n = 0
  · exact Or.inr hn
  · left
    have e1 : 10 ^ (n.log2 * 3 / 20) ≤ 16 ^ (n.log2 * 3 / 20) := Nat.pow_le_pow_left (by omega) _
    have e2 : 16 ^ (n.log2 * 3 / 20) = 2 ^ (4 * (n.log2 * 3 / 20)) := by
      rw [Nat.pow_mul]
    have e3 : 2 ^ (4 * (n.log2 * 3 / 20)) ≤ 2 ^ n.log2 := Nat.pow_le_pow_right (by omega) (by omega)
    have e4 : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn
    omega

theorem digitsDC_spec : ∀ (f n : Nat), DigitsOf n (digitsDC f n) ∧
    ∀ k, 1 ≤ k → n < 10 ^ k → (digitsDC f n).length ≤ k
  | 0, n => ⟨smallDigits_spec n, fun k hk h => smallDigits_length n k hk h⟩
  | f + 1, n => by
    unfold digitsDC
    by_cases hs : n < 10 ^ 18
    · rw [ite_eq_left hs]; exact ⟨smallDigits_spec n, fun k hk h => smallDigits_length n k hk h⟩
    rw [ite_eq_right hs]
    simp only
    generalize hh : n.log2 * 3 / 20 = h
    have hpos : 0 < 10 ^ h := Nat.pow_pos (by decide)
    have hle : 10 ^ h ≤ n := by
      rcases ten_pow_le n with e | e
      · rw [hh] at e; exact e
      · omega
    have hq : 1 ≤ n / 10 ^ h := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    have hr : n % 10 ^ h < 10 ^ h := Nat.mod_lt _ hpos
    have h1 : 1 ≤ h := by
      rw [← hh]
      have hl : 7 ≤ n.log2 := by
        rcases Nat.lt_or_ge n.log2 7 with e | e
        · have h2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
          have h3 : 2 ^ (n.log2 + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
          have : (2 : Nat) ^ 7 < 10 ^ 18 := by decide
          omega
        · exact e
      omega
    obtain ⟨qa, qb, qh, qt, qe, qne, _⟩ := (digitsDC_spec f (n / 10 ^ h)).1
    obtain ⟨ra, rb, -⟩ := (digitsDC_spec f (n % 10 ^ h)).1
    have rlen := (digitsDC_spec f (n % 10 ^ h)).2 h h1 hr
    refine ⟨⟨?_, ?_, qh, qt ++ padDigits h (digitsDC f (n % 10 ^ h)), by rw [qe]; rfl,
      fun _ => qne (by omega), fun e => absurd e (qne (by omega))⟩, ?_⟩
    · rw [ofDigits_append, qa, pad_length _ _ rlen, ofDigits_pad, ra]
      rw [Nat.mul_comm]; exact Nat.div_add_mod n (10 ^ h)
    · intro d hd
      simp only [List.mem_append, padDigits, List.mem_replicate] at hd
      rcases hd with hd | ⟨_, hd⟩ | hd
      · exact qb d hd
      · omega
      · exact rb d hd
    · intro k hk hn
      rw [List.length_append, pad_length _ _ rlen]
      have hkh : h < k := by
        rcases Nat.lt_or_ge h k with e | e
        · exact e
        · have : 10 ^ k ≤ 10 ^ h := Nat.pow_le_pow_right (by omega) e
          omega
      have hq' : n / 10 ^ h < 10 ^ (k - h) := by
        apply Nat.div_lt_of_lt_mul
        rw [← Nat.pow_add, show h + (k - h) = k by omega]; exact hn
      have := (digitsDC_spec f (n / 10 ^ h)).2 (k - h) (by omega) hq'
      omega

theorem natDigits_spec (n : Nat) :
    ofDigits (natDigits n) = n ∧ (∀ d ∈ natDigits n, d < 10) ∧
      ∃ h t, natDigits n = h :: t ∧ (n ≠ 0 → h ≠ 0) ∧ (h = 0 → t = []) :=
  (digitsDC_spec 64 n).1

theorem ofDigits_natDigits (n : Nat) : ofDigits (natDigits n) = n := (natDigits_spec n).1

theorem natDigits_lt10 {n d : Nat} (h : d ∈ natDigits n) : d < 10 := (natDigits_spec n).2.1 d h

theorem natDigits_ne_nil (n : Nat) : natDigits n ≠ [] := by
  obtain ⟨_, _, h, t, e, _⟩ := natDigits_spec n
  rw [e]; simp

theorem natDigits_length_pos (n : Nat) : 0 < (natDigits n).length :=
  List.length_pos_iff.mpr (natDigits_ne_nil n)

/-! ## Digit bytes -/

theorem digitByte_isDigit : ∀ d : Fin 10, isDigit (digitByte d) = true := by decide

theorem digitByte_val : ∀ d : Fin 10, (digitByte d).toNat - 48 = d := by decide

theorem digitByte_ne : ∀ d : Fin 10, digitByte d ≠ 46 ∧ digitByte d ≠ 101 ∧ digitByte d ≠ 69 ∧
    digitByte d ≠ 45 ∧ digitByte d ≠ 43 ∧ isWs (digitByte d) = false := by decide

theorem digitByte_zero_iff : ∀ d : Fin 10, digitByte d = 48 ↔ d.val = 0 := by decide

/-- A byte list of digits stops a digit scan when followed by a non-digit. -/
def DigitStop (rest : List UInt8) : Prop := ∀ b, rest.head? = some b → isDigit b = false

theorem NumStop.digitStop {rest : List UInt8} (h : NumStop rest) : DigitStop rest :=
  fun b hb => (h b hb).1

theorem scanDigits_ext (get : Nat → Option UInt8) (n : Nat) (rest : List UInt8) (hr : DigitStop rest) :
    ∀ (ds : List Nat) (pos cnt : Nat), (∀ d ∈ ds, d < 10) →
      AtV get n pos (ds.map digitByte) rest →
      scanDigits get n pos cnt = (cnt + ds.length, pos + ds.length)
  | [], pos, cnt, _, h => by
    unfold scanDigits
    have hg := AtV.nil h
    split
    · cases hh : rest.head? with
      | none => rw [hh] at hg; rw [hg]; rfl
      | some b =>
        rw [hh] at hg
        rw [hg]; simp [hr b hh]
    · rfl
  | d :: ds, pos, cnt, hd, h => by
    have hd10 : d < 10 := hd d (by simp)
    have hg := AtV.get h
    have hlt : pos < n := by have := h.le_size; simp at this; omega
    unfold scanDigits
    simp only [hlt, ↓reduceIte, hg]
    simp only [digitByte_isDigit ⟨d, hd10⟩, ↓reduceIte]
    rw [scanDigits_ext get n rest hr ds (pos + 1) _ (fun x hx => hd x (by simp [hx])) (AtV.next h)]
    simp only [List.length_cons]
    rw [show cnt + 1 + ds.length = cnt + (ds.length + 1) by omega,
      show pos + 1 + ds.length = pos + (ds.length + 1) by omega]

theorem smallValue_ext {get : Nat → Option UInt8} {n : Nat} {R : List UInt8} :
    ∀ (ds : List Nat) (start acc : Nat), (∀ d ∈ ds, d < 10) → AtV get n start (ds.map digitByte) R →
      smallValue get start ds.length acc = ds.foldl (fun a d => a * 10 + d) acc
  | [], _, _, _, _ => rfl
  | d :: ds, start, acc, hd, h => by
    have hd10 : d < 10 := hd d (by simp)
    simp only [List.length_cons, smallValue, List.foldl_cons]
    have hv : digitAt get start = d := by
      unfold digitAt; rw [AtV.get h]
      exact digitByte_val ⟨d, hd10⟩
    rw [hv]
    exact smallValue_ext ds (start + 1) _ (fun x hx => hd x (by simp [hx])) (AtV.next h)

theorem digitsValue_ext {get : Nat → Option UInt8} {n : Nat} {R : List UInt8} (ds : List Nat) (start : Nat)
    (hd : ∀ d ∈ ds, d < 10) (h : AtV get n start (ds.map digitByte) R) :
    digitsValue get start ds.length = ofDigits ds := by
  rw [digitsValue]
  by_cases hs : ds.length ≤ 16
  · rw [ite_eq_left hs, smallValue_ext ds start 0 hd h]; rfl
  · rw [ite_eq_right hs]
    simp only
    have hlen : ds.length / 2 = (ds.take (ds.length / 2)).length := by simp; omega
    have hlen2 : ds.length - ds.length / 2 = (ds.drop (ds.length / 2)).length := by simp
    have hsplit : ds.map digitByte = (ds.take (ds.length / 2)).map digitByte ++
        (ds.drop (ds.length / 2)).map digitByte := by
      rw [← List.map_append, List.take_append_drop]
    rw [hsplit] at h
    have h1 := h.assoc
    have h2 := h.app
    simp only [List.length_map] at h2
    have e1 := digitsValue_ext _ start (fun d hd' => hd d (List.mem_of_mem_take hd')) h1
    have e2 := digitsValue_ext _ _ (fun d hd' => hd d (List.mem_of_mem_drop hd')) h2
    rw [← hlen] at e1 e2
    rw [← hlen2] at e2
    rw [e1, e2, hlen2, ← ofDigits_append, List.take_append_drop]
termination_by ds.length
decreasing_by all_goals simp; omega

/-! ## Normal form -/

theorem mod_pow_zero_of_le {x a b : Nat} (h : x % 10 ^ a = 0) (hb : b ≤ a) : x % 10 ^ b = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.pow_dvd_pow 10 hb) (Nat.dvd_of_mod_eq_zero h))

theorem trailingZeros_mul (m : Nat) (hm : m ≠ 0) (hm10 : m % 10 ≠ 0) (j : Nat) :
    trailingZeros (m * 10 ^ j) = j := by
  have hx : m * 10 ^ j ≠ 0 := Nat.mul_ne_zero hm (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 10)))
  obtain ⟨h1, h2⟩ := trailingZeros_spec _ hx
  have hj : m * 10 ^ j % 10 ^ j = 0 := Nat.mul_mod_left _ _
  have hj1 : m * 10 ^ j % 10 ^ (j + 1) ≠ 0 := by
    intro h
    apply hm10
    have hd := Nat.dvd_of_mod_eq_zero h
    rw [Nat.pow_succ, Nat.mul_comm (10 ^ j) 10] at hd
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mul_dvd_mul_right (Nat.pow_pos (by decide : 0 < 10)) hd)
  rcases Nat.lt_trichotomy (trailingZeros (m * 10 ^ j)) j with hlt | heq | hgt
  · exact absurd (mod_pow_zero_of_le hj (by omega)) h2
  · exact heq
  · exact absurd (mod_pow_zero_of_le h1 (by omega)) hj1

theorem normalize_mul (neg : Bool) (m : Nat) (hm : m ≠ 0) (hm10 : m % 10 ≠ 0) (e : Int) (k : Nat) :
    Decimal.normalize neg (m * 10 ^ k) (e - k) = ⟨neg, m, e, Or.inr hm10⟩ := by
  unfold Decimal.normalize
  have hpos : m * 10 ^ k ≠ 0 := Nat.mul_ne_zero hm (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 10)))
  rw [dite_eq_right hpos]
  simp only [trailingZeros_mul m hm hm10 k, Decimal.mk.injEq, true_and]
  constructor
  · exact Nat.mul_div_cancel _ (Nat.pow_pos (by decide : 0 < 10))
  · omega

theorem normalize_zero (neg : Bool) (e : Int) :
    Decimal.normalize neg 0 e = ⟨neg, 0, 0, Or.inl ⟨rfl, rfl⟩⟩ := by
  simp [Decimal.normalize]

/-- A normalised decimal is its own normal form, scaled by any power of ten. -/
theorem normalize_self (d : Decimal) (k : Nat) :
    Decimal.normalize d.neg (d.mant * 10 ^ k) (d.exp - k) = d := by
  obtain ⟨neg, m, e, h⟩ := d
  rcases h with ⟨rfl, rfl⟩ | h
  · simp [normalize_zero]
  · have hm : m ≠ 0 := by intro h0; subst h0; simp at h
    exact normalize_mul neg m hm h e k

end LeanJson
