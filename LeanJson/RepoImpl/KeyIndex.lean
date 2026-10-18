import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.TreeMap

/-!
# RepoImpl: the object-key index

While the parser reads an object it records where each key first appeared, so
that a repeated key is collapsed in constant time (`Fields.add`). The index
must stay fast on hostile input too. Lean's `String.hash` has a fixed seed,
so a client can precompute many keys that land in one hash-table bucket, and
a plain `Std.HashMap String Nat` then takes time quadratic in the keys.

`KeyIndex` closes that in two layers:

* The table maps `keySlot k`, the string hash passed through a permutation
  keyed by `keySeed` (a secret drawn from the operating system once per
  process), to the position of the first key with that slot. Which keys
  share a bucket depends on the secret, so it cannot be arranged in advance.
  The table stores positions only: the key itself is read back from the
  members array, so the index costs what a plain `Std.HashMap String Nat`
  did.
* A key whose slot is already taken by a different key (equal string hashes,
  a full collision that no secret can separate, or a rare slot collision)
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

/-- The table key of `k`: its string hash under a permutation keyed by
`keySeed` (two mixing rounds, the secret folded in before each), cut to 63
bits so that it is a scalar `Nat`, stored unboxed. -/
@[inline] def keySlot (k : String) : Nat :=
  (fmix64 (fmix64 (k.hash ^^^ keySeed) ^^^ (keySeed * 0x9e3779b97f4a7c15)) >>> 1).toNat

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
