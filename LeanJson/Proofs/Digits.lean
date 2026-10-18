import LeanJson.Proofs.Bytes

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

theorem natDigits_lt (n : Nat) (h : n < 10) : natDigits n = [n] := by
  unfold natDigits; cases n <;> simp [natDigitsAux] <;> omega

theorem natDigits_ge (n : Nat) (h : 10 ≤ n) :
    natDigits n = natDigits (n / 10) ++ [n % 10] := by
  unfold natDigits
  conv => lhs; unfold natDigitsAux
  simp only [show ¬ n < 10 by omega, ↓reduceIte]
  rw [natDigitsAux_append _ _ _ (by omega), natDigitsAux_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)]

theorem natDigits_spec (n : Nat) :
    ofDigits (natDigits n) = n ∧ (∀ d ∈ natDigits n, d < 10) ∧
      ∃ h t, natDigits n = h :: t ∧ (n ≠ 0 → h ≠ 0) ∧ (h = 0 → t = []) := by
    by_cases hn : n < 10
    · rw [natDigits_lt n hn]
      refine ⟨by simp [ofDigits], by simpa using hn, n, [], rfl, id, fun _ => rfl⟩
    · have ih := natDigits_spec (n / 10)
      rw [natDigits_ge n (by omega)]
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

theorem scanDigits_ext (bs : ByteArray) (rest : List UInt8) (hr : DigitStop rest) :
    ∀ (ds : List Nat) (pos fuel cnt : Nat), (∀ d ∈ ds, d < 10) →
      At bs pos (ds.map digitByte) rest → ds.length ≤ fuel →
      scanDigits bs pos fuel cnt = (cnt + ds.length, pos + ds.length)
  | [], pos, fuel, cnt, _, h, _ => by
    cases fuel with
    | zero => rfl
    | succ f =>
      unfold scanDigits
      rw [At.nil h]
      cases hh : rest.head? with
      | none => rfl
      | some b => simp [hr b hh]
  | d :: ds, pos, fuel, cnt, hd, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hd10 : d < 10 := hd d (by simp)
    unfold scanDigits
    rw [At.get h]
    simp only [digitByte_isDigit ⟨d, hd10⟩, ↓reduceIte]
    rw [scanDigits_ext bs rest hr ds (pos + 1) f _ (fun x hx => hd x (by simp [hx]))
      (At.next h) (by simp at hf; omega)]
    simp only [List.length_cons]
    rw [show cnt + 1 + ds.length = cnt + (ds.length + 1) by omega,
      show pos + 1 + ds.length = pos + (ds.length + 1) by omega]

theorem smallValue_ext {bs : ByteArray} {R : List UInt8} :
    ∀ (ds : List Nat) (start acc : Nat), (∀ d ∈ ds, d < 10) → At bs start (ds.map digitByte) R →
      smallValue bs start ds.length acc = ds.foldl (fun a d => a * 10 + d) acc
  | [], _, _, _, _ => rfl
  | d :: ds, start, acc, hd, h => by
    have hd10 : d < 10 := hd d (by simp)
    simp only [List.length_cons, smallValue, List.foldl_cons]
    have hv : digitAt bs start = d := by
      unfold digitAt; rw [At.get h]
      exact digitByte_val ⟨d, hd10⟩
    rw [hv]
    exact smallValue_ext ds (start + 1) _ (fun x hx => hd x (by simp [hx])) (At.next h)

theorem digitsValue_ext {bs : ByteArray} {R : List UInt8} :
    ∀ (f : Nat) (ds : List Nat) (start : Nat), (∀ d ∈ ds, d < 10) →
      At bs start (ds.map digitByte) R → ds.length ≤ f →
      digitsValue bs f start ds.length = ofDigits ds
  | 0, ds, start, _, _, hf => by
    have : ds = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | f + 1, ds, start, hd, h, hf => by
    unfold digitsValue
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
      have e1 := digitsValue_ext f _ start (digits_take' hd _) h1 (by simp; omega)
      have e2 := digitsValue_ext f _ _ (digits_drop' hd _) h2 (by simp; omega)
      rw [← hlen] at e1 e2
      rw [← hlen2] at e2
      rw [e1, e2, hlen2, ← ofDigits_append, List.take_append_drop]
where
  digits_take' {ds : List Nat} (h : ∀ d ∈ ds, d < 10) (n : Nat) : ∀ d ∈ ds.take n, d < 10 :=
    fun d hd => h d (List.mem_of_mem_take hd)
  digits_drop' {ds : List Nat} (h : ∀ d ∈ ds, d < 10) (n : Nat) : ∀ d ∈ ds.drop n, d < 10 :=
    fun d hd => h d (List.mem_of_mem_drop hd)

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
