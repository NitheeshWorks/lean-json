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

/-- Big-endian decimal digits of `n`; `[0]` for zero, otherwise no leading
zero. -/
def natDigits (n : Nat) : List Nat := natDigitsAux (n + 1) n []

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

/-- Strip trailing decimal zeros from a nonzero mantissa, raising the exponent
to match. `m ≤ fuel` suffices. -/
def stripZeros : (fuel m : Nat) → (e : Int) → Nat × Int
  | 0, m, e => (m, e)
  | f + 1, m, e => if m ≠ 0 ∧ m % 10 = 0 then stripZeros f (m / 10) (e + 1) else (m, e)

theorem stripZeros_spec : ∀ (f m : Nat) (e : Int), m ≠ 0 → m ≤ f →
    (stripZeros f m e).1 % 10 ≠ 0
  | 0, m, _, hm, hf => by omega
  | f + 1, m, e, hm, hf => by
    unfold stripZeros
    by_cases h : m ≠ 0 ∧ m % 10 = 0
    · rw [ite_eq_left h]
      exact stripZeros_spec f (m / 10) (e + 1) (by omega) (by omega)
    · rw [ite_eq_right h]; simp only; omega

/-- The normal form of `(-1)^neg * m * 10^e`. -/
def Decimal.normalize (neg : Bool) (m : Nat) (e : Int) : Decimal :=
  if hm : m = 0 then ⟨neg, 0, 0, Or.inl ⟨rfl, rfl⟩⟩
  else ⟨neg, (stripZeros m m e).1, (stripZeros m m e).2,
    Or.inr (stripZeros_spec m m e hm (Nat.le_refl _))⟩

/-- The integer value of a decimal, when it has one (exponent `≥ 0`; in normal
form a negative exponent means a fractional part). -/
def Decimal.toInt? (d : Decimal) : Option Int :=
  if d.exp < 0 then none
  else
    let v : Int := (d.mant * 10 ^ d.exp.toNat : Nat)
    some (if d.neg then -v else v)

end LeanJson
