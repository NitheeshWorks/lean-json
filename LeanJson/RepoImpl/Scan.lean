/-!
# RepoImpl: scanning a buffer for the next byte of interest

`findFrom p b i` is the first position from `i` on whose byte satisfies
`p`: the end of a run of bytes that a printer can copy whole, or that a
string literal can take whole. It is the specification, one byte at a time.
The compiler runs `findFast` instead (`findFrom_eq_fast`, `@[csimp]`), which
tests eight bytes per step with machine-word indices and one branch.
-/

namespace LeanJson

/-- The first position from `i` on whose byte satisfies `p`, or the end of
`b` (or `i` itself, when it is past the end). -/
def findFrom (p : UInt8 → Bool) (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    if p b[i] then i else findFrom p b (i + 1)
  else i
termination_by b.size - i

theorem findFrom_skip {p : UInt8 → Bool} {b : ByteArray} {i : Nat} (h : i < b.size) (hp : p b[i] = false) :
    findFrom p b i = findFrom p b (i + 1) := by
  rw [findFrom, dite_eq_left h, hp]; rfl

theorem le_findFrom (p : UInt8 → Bool) (b : ByteArray) (i : Nat) : i ≤ findFrom p b i := by
  rw [findFrom]
  split
  · split
    · exact Nat.le_refl _
    · have := le_findFrom p b (i + 1); omega
  · exact Nat.le_refl _
termination_by b.size - i

theorem findFrom_le (p : UInt8 → Bool) (b : ByteArray) (i : Nat) (h : i ≤ b.size) : findFrom p b i ≤ b.size := by
  rw [findFrom]
  split
  · split
    · omega
    · exact findFrom_le p b (i + 1) (by omega)
  · exact h
termination_by b.size - i

/-- Every byte from `i` up to `findFrom p b i` fails `p`. -/
theorem findFrom_run {p : UInt8 → Bool} {b : ByteArray} {i : Nat} :
    ∀ k (hk : k < b.size), i ≤ k → k < findFrom p b i → p b[k] = false := by
  intro k hk hik hkf
  rw [findFrom] at hkf
  split at hkf
  · rename_i h
    split at hkf
    · omega
    · rename_i hp
      by_cases hki : k = i
      · subst hki; simpa using hp
      · exact findFrom_run k hk (by omega) hkf
  · omega
termination_by b.size - i

theorem findFrom_stop_aux {p : UInt8 → Bool} {b : ByteArray} {i : Nat} :
    ∀ j, findFrom p b i = j → (h : j < b.size) → p b[j] = true := by
  intro j hj h
  rw [findFrom] at hj
  split at hj
  · rename_i hi
    split at hj
    · rename_i hp; subst hj; exact hp
    · exact findFrom_stop_aux j hj h
  · omega
termination_by b.size - i

/-- At `findFrom p b i`, if it is not the end, the byte satisfies `p`. -/
theorem findFrom_stop {p : UInt8 → Bool} {b : ByteArray} {i : Nat} (h : findFrom p b i < b.size) :
    p b[findFrom p b i] = true :=
  findFrom_stop_aux _ rfl h

/-- `findFrom` passes over `m` bytes that fail `p`. -/
theorem findFrom_skipN {p : UInt8 → Bool} {b : ByteArray} :
    ∀ (m j : Nat) (h : j + m ≤ b.size), (∀ k (hk : k < m), p (b[j + k]'(by omega)) = false) →
      findFrom p b j = findFrom p b (j + m)
  | 0, _, _, _ => rfl
  | m + 1, j, h, hp => by
    rw [findFrom_skip (by omega) (by simpa using hp 0 (by omega)),
      findFrom_skipN m (j + 1) (by omega) (fun k hk => by
        have := hp (k + 1) (by omega); simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)]
    rw [Nat.add_assoc, Nat.add_comm 1 m]

theorem usize_add_toNat {i : USize} {k : Nat} (hk : k ≤ 8) (h : i.toNat + 8 < USize.size) :
    (i + USize.ofNat k).toNat = i.toNat + k := by
  have hs := USize.size_eq_two_pow
  have h32 : 4294967296 ≤ USize.size := by
    rw [hs]; cases System.Platform.numBits_eq <;> simp_all
  rw [USize.toNat_add, USize.toNat_ofNat_of_lt' (by omega), ← hs]
  exact Nat.mod_eq_of_lt (by omega)

/-- Byte `i + k` of `b`, for `k < 8` inside a block of eight in bounds. -/
@[inline] def at8 (b : ByteArray) (i : USize) (k : Nat) (hk : k < 8) (h : i.toNat + 8 ≤ b.size)
    (hb : b.size < USize.size) : UInt8 :=
  b.uget (i + USize.ofNat k) (by rw [usize_add_toNat (by omega) (by omega)]; omega)

theorem at8_eq {b : ByteArray} {i : USize} {k : Nat} (hk : k < 8) (h : i.toNat + 8 ≤ b.size)
    (hb : b.size < USize.size) : at8 b i k hk h hb = b[i.toNat + k]'(by omega) := by
  have e := usize_add_toNat (i := i) (Nat.le_of_lt hk) (by omega)
  obtain ⟨bs⟩ := b
  simp only [at8, ByteArray.uget]
  have hl : i.toNat + k < bs.size := by simp [ByteArray.size] at h; omega
  show bs[(i + USize.ofNat k).toNat]'(by rw [e]; exact hl) = bs[i.toNat + k]'hl
  simp only [e]

/-- `findFrom` eight bytes at a time from the machine index `i`, then one
at a time from the block where `p` first holds. -/
@[specialize] def findBlocks (p : UInt8 → Bool) (b : ByteArray) (hb : b.size < USize.size) (i : USize) : Nat :=
  if h : i.toNat + 8 ≤ b.size then
    let f := (p (at8 b i 0 (by decide) h hb)).toUInt8 ||| (p (at8 b i 1 (by decide) h hb)).toUInt8 |||
      (p (at8 b i 2 (by decide) h hb)).toUInt8 ||| (p (at8 b i 3 (by decide) h hb)).toUInt8 |||
      (p (at8 b i 4 (by decide) h hb)).toUInt8 ||| (p (at8 b i 5 (by decide) h hb)).toUInt8 |||
      (p (at8 b i 6 (by decide) h hb)).toUInt8 ||| (p (at8 b i 7 (by decide) h hb)).toUInt8
    if f == 0 then findBlocks p b hb (i + 8) else findFrom p b i.toNat
  else findFrom p b i.toNat
termination_by b.size - i.toNat
decreasing_by
  have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat (k := 8) (by decide) (by omega)
  omega

/-- `findFrom` with machine indices and eight bytes per step: equal to it
(`findFrom_eq_fast`), and what the compiler runs. -/
@[inline] def findFast (p : UInt8 → Bool) (b : ByteArray) (i : Nat) : Nat :=
  if hb : b.size < USize.size then
    if i < b.size then findBlocks p b hb (USize.ofNat i) else i
  else findFrom p b i

theorem toUInt8_eq_zero {x : Bool} (h : x.toUInt8 = 0) : x = false := by
  cases x
  · rfl
  · exact absurd h (by decide)

theorem findBlocks_eq (p : UInt8 → Bool) (b : ByteArray) (hb : b.size < USize.size) (i : USize) :
    findBlocks p b hb i = findFrom p b i.toNat := by
  rw [findBlocks]
  split
  · rename_i h
    dsimp only
    split
    · rename_i hf
      simp only [beq_iff_eq, UInt8.or_eq_zero_iff] at hf
      obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hf
      have h8 : (i + USize.ofNat 8).toNat = i.toNat + 8 := usize_add_toNat (by decide) (by omega)
      rw [show i + 8 = i + USize.ofNat 8 from rfl, findBlocks_eq p b hb (i + USize.ofNat 8), h8]
      rw [at8_eq _ h hb] at h0 h1 h2 h3 h4 h5 h6 h7
      symm
      apply findFrom_skipN 8 i.toNat h
      intro k hk
      match k, hk with
      | 0, _ => exact toUInt8_eq_zero h0
      | 1, _ => exact toUInt8_eq_zero h1
      | 2, _ => exact toUInt8_eq_zero h2
      | 3, _ => exact toUInt8_eq_zero h3
      | 4, _ => exact toUInt8_eq_zero h4
      | 5, _ => exact toUInt8_eq_zero h5
      | 6, _ => exact toUInt8_eq_zero h6
      | 7, _ => exact toUInt8_eq_zero h7
    · rfl
  · rfl
termination_by b.size - i.toNat
decreasing_by
  have h8 : (i + 8).toNat = i.toNat + 8 := usize_add_toNat (k := 8) (by decide) (by omega)
  omega

@[csimp] theorem findFrom_eq_fast : @findFrom = @findFast := by
  funext p b i
  unfold findFast
  split
  · rename_i hb
    split
    · rename_i hi
      rw [findBlocks_eq, USize.toNat_ofNat_of_lt' (by omega)]
    · rename_i hi
      rw [findFrom, dite_eq_right hi]
  · rfl

end LeanJson
