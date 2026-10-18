import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.TreeMap

/-!
# RepoImpl: the object-key index

While the parser reads an object it records where each key first appeared, so
that a repeated key is collapsed in constant time (`Fields.add`). The index
must stay fast on hostile input too. A hash with a fixed seed (Lean's
`String.hash`, or `keyHash` below) lets a client precompute many keys that land
in one hash-table bucket, and a plain `Std.HashMap String Nat` then takes time
quadratic in the keys.

`KeyIndex` closes that in two layers:

* The table maps `keySlot k`, the key hash `keyHash k` (FNV-1a over the
  length and the first 64 bytes, so the parser can compute it from the input
  bytes before it builds the key, `keyHashBA_eq`) passed through a permutation
  keyed by `keySeed` (a secret drawn from the operating system once per
  process), to the position of the first key with that slot. Which keys
  share a bucket depends on the secret, so it cannot be arranged in advance.
  The table stores positions only: the key itself is read back from the
  members array, so the index costs what a plain `Std.HashMap String Nat`
  did.
* A key whose slot is already taken by a different key (equal key hashes, a
  full collision that no secret can separate, such as two keys of one length
  that share their first 64 bytes, or a rare slot collision)
  goes to `spill`, a balanced search tree, where it costs a logarithmic
  step, never a linear one.

So the worst case is `O(n log n)` for `n` keys whatever the input, and the
common case is one hash probe and one string comparison per key.

The seed affects only where keys are stored, never what the index answers:
`Fields.add_exact` (`Proofs/Fields.lean`) holds for every value of
`keySeed`, so every theorem about the parser holds for every seed. (In the
logic `keySeed` is an opaque constant; only compiled code draws it.)
-/

namespace LeanJson

/-- The per-process secret behind `keyHash`, drawn from the operating
system's random source when the program starts. -/
initialize keySeed : UInt64 ← do
  let b ← IO.getRandomBytes 8
  pure b.toUInt64LE!

/-- The 64-bit finaliser of MurmurHash3: a bijection that mixes every input
bit into every output bit. -/
@[inline] def fmix64 (h : UInt64) : UInt64 :=
  let h := (h ^^^ (h >>> 33)) * 0xff51afd7ed558ccd
  let h := (h ^^^ (h >>> 33)) * 0xc4ceb9fe1a85ec53
  h ^^^ (h >>> 33)

/-- FNV-1a over bytes `k` to `m` of a string, after `h`. -/
def keyHashGo (s : String) (k m : Nat) (h : UInt64) : UInt64 :=
  if hk : k < m ∧ k < s.utf8ByteSize then
    keyHashGo s (k + 1) m ((h ^^^ (s.getUTF8Byte ⟨k⟩ (by simpa [String.Pos.Raw.lt_iff] using hk.2)).toUInt64) *
      0x100000001b3)
  else h
termination_by m - k

/-- The hash of a key: FNV-1a over its first 64 bytes, seeded with its
length. Defined in Lean over the key's UTF-8 bytes, so that the parser can
compute it from the bytes of the input before it builds the key
(`keyHashBA_eq`); a long key costs no more than 64 bytes. Keys that agree
there share a slot, and all but the first go to the spill tree. -/
def keyHash (s : String) : UInt64 := keyHashGo s 0 64 (0xcbf29ce484222325 ^^^ s.utf8ByteSize.toUInt64)

/-- `keyHashGo` over bytes `i + k` to `i + m` of a buffer. -/
def keyHashBAGo (bs : ByteArray) (i k m : Nat) (h : UInt64) : UInt64 :=
  if hk : k < m ∧ i + k < bs.size then
    keyHashBAGo bs i (k + 1) m ((h ^^^ (bs[i + k]).toUInt64) * 0x100000001b3)
  else h
termination_by m - k

/-- `keyHash` of the key whose bytes are `i` to `j` of `bs`. -/
@[inline] def keyHashBA (bs : ByteArray) (i j : Nat) : UInt64 :=
  keyHashBAGo bs i 0 (min (j - i) 64) (0xcbf29ce484222325 ^^^ (j - i).toUInt64)

theorem keyHashGo_eq (s : String) (bs : ByteArray) (i j : Nat) (hs : s.toByteArray = bs.extract i j)
    (hj : j ≤ bs.size) (k : Nat) (h : UInt64) : keyHashGo s k 64 h = keyHashBAGo bs i k (min (j - i) 64) h := by
  have hsz : s.utf8ByteSize = j - i := by
    rw [← String.size_toByteArray, hs, ByteArray.size_extract]; omega
  rw [keyHashGo, keyHashBAGo]
  by_cases hk : k < 64 ∧ k < s.utf8ByteSize
  · have hk' : k < min (j - i) 64 ∧ i + k < bs.size := ⟨by omega, by omega⟩
    rw [dite_eq_left hk, dite_eq_left hk']
    have hb : s.getUTF8Byte ⟨k⟩ (by simpa [String.Pos.Raw.lt_iff] using hk.2) = bs[i + k] := by
      rw [String.getUTF8Byte_eq_getElem]
      simp only [hs, ByteArray.getElem_extract]
    rw [hb]
    exact keyHashGo_eq s bs i j hs hj (k + 1) _
  · rw [dite_eq_right hk, dite_eq_right (by omega)]
termination_by 64 - k

/-- The hash of a key computed from its bytes in the input is the hash of
the key. -/
theorem keyHashBA_eq (s : String) (bs : ByteArray) (i j : Nat) (hs : s.toByteArray = bs.extract i j)
    (hj : j ≤ bs.size) : keyHash s = keyHashBA bs i j := by
  have hsz : s.utf8ByteSize = j - i := by
    rw [← String.size_toByteArray, hs, ByteArray.size_extract]; omega
  unfold keyHash keyHashBA
  rw [hsz, keyHashGo_eq s bs i j hs hj]

/-- The mixing of a hash into a slot: a permutation keyed by `keySeed` (two
rounds, the secret folded in before each), cut to 63 bits so that a slot is
a scalar `Nat`, stored unboxed. -/
@[inline] def slotOf (h : UInt64) : Nat :=
  (fmix64 (fmix64 (h ^^^ keySeed) ^^^ (keySeed * 0x9e3779b97f4a7c15)) >>> 1).toNat

/-- The table key of `k`. -/
@[inline] def keySlot (k : String) : Nat := slotOf (keyHash k)

/-- A table key. A structure of one `Nat`, so it is a bare `Nat` at run time,
with its own equality and hash, which compile to direct calls (`Nat`'s
`BEq` comes from `DecidableEq` and is passed as a closure). -/
structure SlotKey where
  v : Nat

instance : BEq SlotKey := ⟨fun a b => Nat.beq a.v b.v⟩
instance : Hashable SlotKey := ⟨fun a => UInt64.ofNat a.v⟩
instance : LawfulBEq SlotKey where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq, Nat.beq_eq]
  rfl {a} := by cases a; simp [BEq.beq, Nat.beq_refl]

/-- Where each key of an object under construction first appeared. -/
structure KeyIndex where
  /-- The position of the first key in each slot. -/
  table : Std.HashMap SlotKey Nat
  /-- The keys whose slot was taken by an earlier, different key. -/
  spill : Std.TreeMap String Nat

/-- The empty index. -/
def KeyIndex.empty : KeyIndex := ⟨∅, ∅⟩

/-- The position recorded for `a`, where `isAt j a` tells whether the member
at position `j` has key `a`. -/
@[inline] def KeyIndex.find (x : KeyIndex) (isAt : Nat → String → Bool) (a : String) : Option Nat :=
  (x.table[(⟨keySlot a⟩ : SlotKey)]?).bind fun j => if isAt j a then some j else x.spill[a]?

/-- Record position `i` for `a`, a key not recorded yet. -/
@[inline] def KeyIndex.add (x : KeyIndex) (a : String) (i : Nat) : KeyIndex :=
  let h : SlotKey := ⟨keySlot a⟩
  if x.table.contains h then ⟨x.table, x.spill.insert a i⟩ else ⟨x.table.insert h i, x.spill⟩

end LeanJson
