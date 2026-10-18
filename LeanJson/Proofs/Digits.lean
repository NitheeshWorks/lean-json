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
    ∀ (ds : List Nat) (pos fuel acc cnt : Nat), (∀ d ∈ ds, d < 10) →
      At bs pos (ds.map digitByte) rest → ds.length ≤ fuel →
      scanDigits bs pos fuel acc cnt =
        (ds.foldl (fun a d => a * 10 + d) acc, cnt + ds.length, pos + ds.length)
  | [], pos, fuel, acc, cnt, _, h, _ => by
    cases fuel with
    | zero => rfl
    | succ f =>
      unfold scanDigits
      rw [At.nil h]
      cases hh : rest.head? with
      | none => rfl
      | some b => simp [hr b hh]
  | d :: ds, pos, fuel, acc, cnt, hd, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hd10 : d < 10 := hd d (by simp)
    unfold scanDigits
    rw [At.get h]
    simp only [digitByte_isDigit ⟨d, hd10⟩, ↓reduceIte]
    have := digitByte_val ⟨d, hd10⟩
    simp only at this
    rw [this, scanDigits_ext bs rest hr ds (pos + 1) f _ _ (fun x hx => hd x (by simp [hx]))
      (At.next h) (by simp at hf; omega)]
    simp only [List.foldl_cons, List.length_cons]
    rw [show cnt + 1 + ds.length = cnt + (ds.length + 1) by omega,
      show pos + 1 + ds.length = pos + (ds.length + 1) by omega]

/-! ## Normal form -/

theorem stripZeros_mul (m : Nat) (hm : m ≠ 0) (hm10 : m % 10 ≠ 0) (e : Int) :
    ∀ k f, k ≤ f → stripZeros f (m * 10 ^ k) (e - k) = (m, e)
  | 0, 0, _ => by simp [stripZeros]
  | 0, f + 1, _ => by simp [stripZeros, hm10]
  | k + 1, 0, h => by omega
  | k + 1, f + 1, h => by
    unfold stripZeros
    have hpos : m * 10 ^ (k + 1) ≠ 0 := Nat.mul_ne_zero hm (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 10)))
    have hmod : m * 10 ^ (k + 1) % 10 = 0 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; simp
    rw [ite_eq_left ⟨hpos, hmod⟩]
    have hdiv : m * 10 ^ (k + 1) / 10 = m * 10 ^ k := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; simp
    rw [hdiv, show e - ((k + 1 : Nat) : Int) + 1 = e - (k : Int) by omega]
    exact stripZeros_mul m hm hm10 e k f (by omega)

theorem k_le_pow (k : Nat) : k ≤ 10 ^ k := Nat.le_of_lt (Nat.lt_pow_self (by omega))

theorem normalize_mul (neg : Bool) (m : Nat) (hm : m ≠ 0) (hm10 : m % 10 ≠ 0) (e : Int) (k : Nat) :
    Decimal.normalize neg (m * 10 ^ k) (e - k) = ⟨neg, m, e, Or.inr hm10⟩ := by
  unfold Decimal.normalize
  have hpos : m * 10 ^ k ≠ 0 := Nat.mul_ne_zero hm (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 10)))
  rw [dite_eq_right hpos]
  have := stripZeros_mul m hm hm10 e k (m * 10 ^ k)
    (Nat.le_trans (k_le_pow k) (Nat.le_mul_of_pos_left _ (by omega)))
  simp only [this]

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
