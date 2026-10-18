import LeanJson.DataTypes.Json

/-!
# RepoImpl: digits, hex digits, decimal normal form

The arithmetic the number and string codecs share. Everything recurses on
an explicit fuel argument so that it is structural and reduces in the
kernel; the callers pass fuel that is provably enough (`Proofs/Digits.lean`).
-/

namespace LeanJson

/-- The value of a big-endian list of decimal digits. -/
def ofDigits (l : List Nat) : Nat := l.foldl (fun a d => a * 10 + d) 0

/-- Big-endian decimal digits of `n`, accumulating onto `acc`; `fuel` bounds
the number of steps (`n < fuel` suffices). -/
def natDigitsAux : (fuel n : Nat) → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, n, acc => if n < 10 then n :: acc else natDigitsAux f (n / 10) (n % 10 :: acc)

/-- Big-endian decimal digits of a small `n`, one division per digit. -/
def smallDigits (n : Nat) : List Nat := natDigitsAux (n + 1) n []

/-- Left-pad with zeros to length `h`. -/
def padDigits (h : Nat) (l : List Nat) : List Nat := List.replicate (h - l.length) 0 ++ l

/-- Big-endian decimal digits by divide and conquer: split off the low `h`
digits (about half) with one big division, so a long number costs a few big
divisions rather than one per digit. Correct for any `fuel`. -/
def digitsDC : (fuel n : Nat) → List Nat
  | 0, n => smallDigits n
  | f + 1, n =>
    if n < 10 ^ 18 then smallDigits n
    else
      let h := n.log2 * 3 / 20
      digitsDC f (n / 10 ^ h) ++ padDigits h (digitsDC f (n % 10 ^ h))

/-- Big-endian decimal digits of `n`; `[0]` for zero, otherwise no leading
zero. -/
def natDigits (n : Nat) : List Nat := digitsDC 64 n

/-- The ASCII byte of a decimal digit. -/
def digitByte (d : Nat) : UInt8 := UInt8.ofNat (48 + d)

/-- Is this byte an ASCII decimal digit? -/
def isDigit (b : UInt8) : Bool := 48 ≤ b && b ≤ 57

/-- The lowercase ASCII hex digit for `d < 16` (serde_json writes lowercase). -/
def hexByte (d : Nat) : UInt8 := if d < 10 then UInt8.ofNat (48 + d) else UInt8.ofNat (87 + d)

/-- The value of an ASCII hex digit, either case. -/
def hexVal (b : UInt8) : Option Nat :=
  if 48 ≤ b && b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b && b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b && b ≤ 70 then some (b.toNat - 55)
  else none

/-- `n` as decimal ASCII. -/
def printNat (n : Nat) : List UInt8 := (natDigits n).map digitByte

/-- `i` as decimal ASCII with a leading `-` when negative. -/
def printInt (i : Int) : List UInt8 :=
  if i < 0 then 45 :: printNat i.natAbs else printNat i.toNat

/-- Binary search for the number of trailing decimal zeros of `m`: the
invariant is `10^lo ∣ m` and `¬ 10^hi ∣ m`. Logarithmically many big-number
operations, so normalising a long literal stays fast. -/
def tzSearch (m : Nat) : (fuel lo hi : Nat) → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if m % 10 ^ mid = 0 then tzSearch m f mid hi else tzSearch m f lo mid

/-- The number of trailing decimal zeros of a nonzero `m`. -/
def trailingZeros (m : Nat) : Nat := tzSearch m (m.log2 + 2) 0 (m.log2 + 1)

theorem tzSearch_spec (m : Nat) : ∀ (f lo hi : Nat), m % 10 ^ lo = 0 → m % 10 ^ hi ≠ 0 → lo < hi →
    hi - lo ≤ f + 1 → m % 10 ^ tzSearch m f lo hi = 0 ∧ m % 10 ^ (tzSearch m f lo hi + 1) ≠ 0
  | 0, lo, hi, h1, h2, h3, h4 => by
    have : hi = lo + 1 := by omega
    subst this; exact ⟨h1, h2⟩
  | f + 1, lo, hi, h1, h2, h3, h4 => by
    unfold tzSearch
    by_cases hc : hi ≤ lo + 1
    · rw [ite_eq_left hc]
      have : hi = lo + 1 := by omega
      subst this; exact ⟨h1, h2⟩
    · rw [ite_eq_right hc]
      simp only
      by_cases hm : m % 10 ^ ((lo + hi) / 2) = 0
      · rw [ite_eq_left hm]
        exact tzSearch_spec m f _ hi hm h2 (by omega) (by omega)
      · rw [ite_eq_right hm]
        exact tzSearch_spec m f lo _ h1 hm (by omega) (by omega)

theorem pow_ten_not_dvd (m : Nat) (hm : m ≠ 0) : m % 10 ^ (m.log2 + 1) ≠ 0 := by
  have h1 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have h2 : 2 ^ (m.log2 + 1) ≤ 10 ^ (m.log2 + 1) := Nat.pow_le_pow_left (by omega) _
  rw [Nat.mod_eq_of_lt (by omega)]; exact hm

theorem trailingZeros_spec (m : Nat) (hm : m ≠ 0) :
    m % 10 ^ trailingZeros m = 0 ∧ m % 10 ^ (trailingZeros m + 1) ≠ 0 :=
  tzSearch_spec m _ 0 _ (by simp [Nat.mod_one]) (pow_ten_not_dvd m hm) (by omega) (by omega)

theorem div_pow_mod_ne (m k : Nat) (h1 : m % 10 ^ k = 0) (h2 : m % 10 ^ (k + 1) ≠ 0) :
    m / 10 ^ k % 10 ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h1
  have hd : m / 10 ^ k = q := by
    rw [hq, Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide : 0 < 10))]
  rw [hd] at h
  obtain ⟨r, hr⟩ := Nat.dvd_of_mod_eq_zero h
  apply h2
  rw [hq, hr, Nat.pow_succ, ← Nat.mul_assoc]
  exact Nat.mul_mod_right _ _

/-- The normal form of `(-1)^neg * m * 10^e`. -/
def Decimal.normalize (neg : Bool) (m : Nat) (e : Int) : Decimal :=
  if hm : m = 0 then ⟨neg, 0, 0, Or.inl ⟨rfl, rfl⟩⟩
  else ⟨neg, m / 10 ^ trailingZeros m, e + trailingZeros m,
    Or.inr (div_pow_mod_ne m _ (trailingZeros_spec m hm).1 (trailingZeros_spec m hm).2)⟩

/-- The integer value of a decimal, when it has one (exponent `≥ 0`; in normal
form a negative exponent means a fractional part). An exponent above 4300 gives
`none`: upstream reads such a literal as a float `inf`, never as an int. -/
def Decimal.toInt? (d : Decimal) : Option Int :=
  if d.exp < 0 then none
  -- Python's `int` digit limit: anything longer is not an integer pydantic
  -- accepts, and computing it would exhaust memory.
  else if d.exp > 4300 then none
  else
    let v : Int := (d.mant * 10 ^ d.exp.toNat : Nat)
    some (if d.neg then -v else v)

end LeanJson
