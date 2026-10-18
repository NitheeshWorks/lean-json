import LeanJson.Specifications.Json

/-!
# Proofs: reading bytes through `Spec.At`

`At bs pos l rest` says the bytes of `bs` from `pos` on are `l ++ rest`.
These lemmas turn the parser's `bs[pos]?` reads into facts about `l`, so
the codec proofs never index into a `ByteArray` directly.
-/

namespace LeanJson.Spec

theorem getElem?_eq_drop_head (bs : ByteArray) (pos : Nat) :
    bs[pos]? = (bs.data.toList.drop pos).head? := by
  rw [List.head?_drop]
  by_cases h : pos < bs.size
  · rw [getElem?_pos bs pos h, List.getElem?_eq_getElem (by simpa using h)]
    simp [ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg bs pos h, List.getElem?_eq_none (by simp; simpa using h)]

theorem At.get {bs : ByteArray} {pos : Nat} {b : UInt8} {l rest : List UInt8}
    (h : At bs pos (b :: l) rest) : bs[pos]? = some b := by
  rw [getElem?_eq_drop_head, h]; rfl

theorem At.next {bs : ByteArray} {pos : Nat} {b : UInt8} {l rest : List UInt8}
    (h : At bs pos (b :: l) rest) : At bs (pos + 1) l rest := by
  unfold At at *
  rw [← List.drop_drop, h]; rfl

theorem At.app {bs : ByteArray} {pos : Nat} {l₁ l₂ rest : List UInt8}
    (h : At bs pos (l₁ ++ l₂) rest) : At bs (pos + l₁.length) l₂ rest := by
  unfold At at *
  rw [← List.drop_drop, h, List.append_assoc, List.drop_left]

theorem At.app' {bs : ByteArray} {pos : Nat} {l₁ l₂ rest : List UInt8}
    (h : At bs pos l₁ (l₂ ++ rest)) : At bs pos (l₁ ++ l₂) rest := by
  unfold At at *; rw [h, List.append_assoc]

theorem At.assoc {bs : ByteArray} {pos : Nat} {l₁ l₂ rest : List UInt8}
    (h : At bs pos (l₁ ++ l₂) rest) : At bs pos l₁ (l₂ ++ rest) := by
  unfold At at *; rw [h, List.append_assoc]

theorem At.nil {bs : ByteArray} {pos : Nat} {rest : List UInt8}
    (h : At bs pos [] rest) : bs[pos]? = rest.head? := by
  rw [getElem?_eq_drop_head, h]; rfl

theorem At.le_size {bs : ByteArray} {pos : Nat} {l rest : List UInt8}
    (h : At bs pos l rest) (hl : l ≠ []) : pos + l.length ≤ bs.size := by
  unfold At at h
  have h1 := congrArg List.length h
  simp only [List.length_drop, List.length_append, Array.length_toList] at h1
  have : 0 < l.length := List.length_pos_iff.mpr hl
  have : bs.data.size = bs.size := rfl
  omega

theorem At.size_eq {bs : ByteArray} {pos : Nat} {l rest : List UInt8}
    (h : At bs pos l rest) (hl : l ++ rest ≠ []) : pos + l.length + rest.length = bs.size := by
  unfold At at h
  have h1 := congrArg List.length h
  simp only [List.length_drop, List.length_append, Array.length_toList] at h1
  have : 0 < (l ++ rest).length := List.length_pos_iff.mpr hl
  simp only [List.length_append] at this
  have : bs.data.size = bs.size := rfl
  omega

/-- The bytes of a list, placed in a `ByteArray`, are `At` position 0. -/
theorem At.ofList (l rest : List UInt8) : At (l ++ rest).toByteArray 0 l rest := by
  simp [At]

end LeanJson.Spec
