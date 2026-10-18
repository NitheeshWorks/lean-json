import LeanJson.RepoImpl.Lex

/-!
# Proofs: objects under construction

`Fields.add` collapses a repeated key with Python `dict` semantics. Two facts
are all the parser proofs need: a key not seen before is appended (so on
input with distinct keys, collapsing changes nothing), and every member of
the result is an old member or the new one.
-/

namespace LeanJson

/-- The index names only keys that are present. -/
def Fields.Indexed (st : Fields) : Prop := ∀ k, st.2[k]? ≠ none → k ∈ st.1.toList.map Prod.fst

theorem Fields.indexed_empty : Fields.empty.Indexed := by
  intro k h; simp [Fields.empty] at h

/-- A fresh key is appended, and the index stays honest. -/
theorem Fields.add_fresh {d : Bool} {st : Fields} {k : String} {v : Json} (hi : st.Indexed)
    (hk : d = true → k ∉ st.1.toList.map Prod.fst) :
    (st.add d k v).1 = st.1.push (k, v) ∧ (st.add d k v).Indexed := by
  unfold Fields.add
  cases d with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, fun a ha => ?_⟩
    simp only [Array.toList_push, List.map_append, List.mem_append]
    exact Or.inl (hi a ha)
  | true =>
    have hn : st.2[k]? = none := by
      cases h : st.2[k]? with
      | none => rfl
      | some i => exact absurd (hi k (by simp [h])) (hk rfl)
    simp only [↓reduceIte, dictInsert, hn]
    refine ⟨trivial, fun a ha => ?_⟩
    simp only [Std.HashMap.getElem?_insert] at ha
    simp only [Array.toList_push, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_singleton]
    by_cases e : (k == a) = true
    · exact Or.inr (by simpa using (beq_iff_eq.mp e).symm)
    · rw [ite_eq_right e] at ha; exact Or.inl (hi a ha)

/-- Every member after `add` was there before, or is the new one. -/
theorem Fields.mem_add {d : Bool} {st : Fields} {k : String} {v : Json} {kv : String × Json}
    (h : kv ∈ (st.add d k v).1.toList) : kv ∈ st.1.toList ∨ kv = (k, v) := by
  unfold Fields.add at h
  cases d with
  | false => simpa using h
  | true =>
    simp only [ite_true, dictInsert] at h
    split at h
    · rw [Array.toList_setIfInBounds] at h; exact List.mem_or_eq_of_mem_set h
    · simpa using h

end LeanJson
