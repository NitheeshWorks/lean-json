import LeanJson.RepoImpl.Access

/-!
# Proofs: objects under construction

`Fields.add` collapses a repeated key with Python `dict` semantics. Two facts
are all the parser proofs need: a key not seen before is appended (so on
input with distinct keys, collapsing changes nothing), and every member of
the result is an old member or the new one.

`dedupKeys_eq` says the collapsing is exactly the specification
`Json.dedupKeysList` (one entry per key, at its first position, with its last
value), whatever `keySeed` is: the index only speeds up `insertLast`.
-/

namespace LeanJson

/-- The keys of the members so far, in order. -/
abbrev Fields.keys (st : Fields) : List String := st.1.toList.map Prod.fst

/-- The position the index gives for `a`. -/
abbrev Fields.find (st : Fields) (a : String) : Option Nat := st.2.find (Fields.isAt st.1) a

theorem Fields.isAt_iff {acc : Array (String × Json)} {j : Nat} {a : String} :
    Fields.isAt acc j a = true ↔ ∃ h : j < acc.size, acc[j].1 = a := by
  unfold Fields.isAt
  split
  · simp_all
  · simp only [Bool.false_eq_true, false_iff, not_exists]; intro h; omega

/-- Every table entry is a position in bounds, filed under its key's slot. -/
def Fields.Wf (st : Fields) : Prop :=
  ∀ h j, st.2.table[h]? = some j → ∃ hj : j < st.1.size, keySlot st.1[j].1 = h

/-- The index is well formed and names only keys that are present. -/
def Fields.Indexed (st : Fields) : Prop := st.Wf ∧ ∀ a, st.2.spill[a]? ≠ none → a ∈ st.keys

theorem Fields.indexed_empty : Fields.empty.Indexed :=
  ⟨fun h j hj => by simp [Fields.empty, KeyIndex.empty] at hj,
   fun a ha => by simp [Fields.empty, KeyIndex.empty] at ha⟩

theorem Fields.find_mem {st : Fields} {a : String} (hi : st.Indexed) (h : st.find a ≠ none) :
    a ∈ st.keys := by
  simp only [Fields.find, KeyIndex.find] at h
  cases ht : st.2.table[keySlot a]? with
  | none => simp [ht] at h
  | some j =>
    simp only [ht, Option.bind_some] at h
    split at h
    · rename_i hj
      obtain ⟨hl, he⟩ := Fields.isAt_iff.mp hj
      simp only [Fields.keys, List.mem_map]
      exact ⟨st.1[j], by simp, he⟩
    · exact hi.2 a h

/-- Pushing a member keeps the table well formed. -/
theorem Fields.wf_push {acc : Array (String × Json)} {x : KeyIndex} {kv : String × Json}
    (hw : Fields.Wf (acc, x)) : Fields.Wf (acc.push kv, x) := by
  intro h j hj
  obtain ⟨hl, he⟩ := hw h j hj
  dsimp only at hl he
  exact ⟨by simp; omega, by simpa [Array.getElem_push_lt hl] using he⟩

/-- Pushing a fresh key and recording it keeps the table well formed. -/
theorem Fields.wf_add {acc : Array (String × Json)} {x : KeyIndex} {k : String} {v : Json}
    (hw : Fields.Wf (acc, x)) : Fields.Wf (acc.push (k, v), x.add k acc.size) := by
  intro h j hj
  simp only [KeyIndex.add] at hj
  split at hj
  · exact Fields.wf_push hw h j hj
  · simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at hj
    split at hj
    · rename_i e; cases hj; exact ⟨by simp, by simpa using e⟩
    · exact Fields.wf_push hw h j hj

theorem Fields.spill_add {x : KeyIndex} {k a : String} {i : Nat} :
    (x.add k i).spill[a]? = if x.table.contains (keySlot k) ∧ k = a then some i else x.spill[a]? := by
  simp only [KeyIndex.add]
  split
  · rename_i hc
    simp only [Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, hc, true_and]
  · rename_i hc; simp [hc]

/-- A fresh key is appended, and the index stays honest. -/
theorem Fields.add_fresh {d : Bool} {st : Fields} {k : String} {v : Json} (hi : st.Indexed)
    (hk : d = true → k ∉ st.1.toList.map Prod.fst) :
    (st.add d k v).1 = st.1.push (k, v) ∧ (st.add d k v).Indexed := by
  obtain ⟨acc, x⟩ := st
  unfold Fields.add
  cases d with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, Fields.wf_push hi.1, fun a ha => ?_⟩
    simp only [Fields.keys, Array.toList_push, List.map_append, List.mem_append]
    exact Or.inl (hi.2 a ha)
  | true =>
    have hn : x.find (Fields.isAt acc) k = none := by
      cases h : x.find (Fields.isAt acc) k with
      | none => rfl
      | some i => exact absurd (Fields.find_mem (st := (acc, x)) hi (by simp [Fields.find, h])) (hk rfl)
    simp only [↓reduceIte, dictInsert, hn]
    refine ⟨trivial, Fields.wf_add hi.1, fun a ha => ?_⟩
    rw [Fields.spill_add] at ha
    simp only [Fields.keys, Array.toList_push, List.map_append, List.mem_append, List.map_cons,
      List.map_nil, List.mem_singleton]
    split at ha
    · rename_i e; exact Or.inr e.2.symm
    · exact Or.inl (hi.2 a ha)

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

/-- The first position of `a` in a list of keys. -/
def firstPos (a : String) : List String → Option Nat
  | [] => none
  | b :: bs => if b = a then some 0 else (firstPos a bs).map (· + 1)

theorem firstPos_some {a : String} : ∀ {l : List String} {i : Nat}, firstPos a l = some i →
    ∃ h : i < l.length, l[i] = a
  | [], _, h => by cases h
  | b :: bs, i, h => by
    simp only [firstPos] at h
    split at h
    · cases h; exact ⟨by simp, by simpa⟩
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨hl, he⟩ := firstPos_some hj
      exact ⟨by simp; omega, by simpa using he⟩

theorem firstPos_none {a : String} : ∀ {l : List String}, firstPos a l = none → a ∉ l
  | [], _ => by simp
  | b :: bs, h => by
    simp only [firstPos] at h
    split at h
    · cases h
    · rename_i hb
      have := firstPos_none (Option.map_eq_none_iff.mp h)
      simp only [List.mem_cons, not_or]; exact ⟨fun e => hb e.symm, this⟩

theorem firstPos_append {a k : String} : ∀ (l : List String),
    firstPos a (l ++ [k]) = (firstPos a l).or (if k = a then some l.length else none)
  | [] => by by_cases e : k = a <;> simp [firstPos, e]
  | b :: bs => by
    simp only [List.cons_append, firstPos, List.length_cons]
    split
    · rfl
    · rw [firstPos_append bs]
      cases firstPos a bs <;> by_cases e : k = a <;> simp [e]

theorem insertLast_of_some {k : String} {v : Json} : ∀ {l : List (String × Json)} {i : Nat},
    firstPos k (l.map Prod.fst) = some i → Json.insertLast k v l = l.set i (k, v)
  | [], _, h => by cases h
  | (k', v') :: kvs, i, h => by
    simp only [List.map_cons, firstPos] at h
    simp only [Json.insertLast]
    split at h
    · rename_i e; cases h; simp [e]
    · rename_i e
      obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [e, insertLast_of_some hj]

theorem insertLast_of_none {k : String} {v : Json} : ∀ {l : List (String × Json)},
    firstPos k (l.map Prod.fst) = none → Json.insertLast k v l = l ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: kvs, h => by
    simp only [List.map_cons, firstPos] at h
    simp only [Json.insertLast]
    split at h
    · cases h
    · rename_i e; simp [e, insertLast_of_none (Option.map_eq_none_iff.mp h)]

/-- The invariant of a collapsing parse: the index is well formed, a spilled
key's slot is taken, and the index answers exactly the first position of
every key. -/
def Fields.Exact (st : Fields) : Prop :=
  st.Wf ∧ (∀ a, st.2.spill[a]? ≠ none → st.2.table[keySlot a]? ≠ none) ∧
    ∀ a, st.find a = firstPos a st.keys

theorem Fields.exact_empty : Fields.empty.Exact :=
  ⟨Fields.indexed_empty.1, fun a ha => by simp [Fields.empty, KeyIndex.empty] at ha,
   fun a => by simp [Fields.empty, KeyIndex.empty, KeyIndex.find, Fields.keys, firstPos]⟩

/-- **Collapsing a key is `insertLast`**: on an exact index, `add` does to the
members what the specification does, and the index stays exact. -/
theorem Fields.add_exact {st : Fields} {k : String} {v : Json} (hx : st.Exact) :
    (st.add true k v).1.toList = Json.insertLast k v st.1.toList ∧ (st.add true k v).Exact := by
  obtain ⟨acc, x⟩ := st
  obtain ⟨hw, hsp, hf⟩ := hx
  simp only [Fields.add, ↓reduceIte, dictInsert]
  cases hk : x.find (Fields.isAt acc) k with
  | some i =>
    have hk' := hk
    rw [show x.find (Fields.isAt acc) k = Fields.find (acc, x) k from rfl, hf] at hk'
    obtain ⟨hl, he⟩ := firstPos_some hk'
    simp only [Fields.keys, List.length_map, Array.length_toList, List.getElem_map,
      Array.getElem_toList] at hl he
    have hset : (acc.setIfInBounds i (k, v)).toList.map Prod.fst = acc.toList.map Prod.fst := by
      rw [Array.toList_setIfInBounds, List.map_set]
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_set, List.getElem_map, Array.getElem_toList]
      split <;> simp_all
    have hfst : ∀ (j : Nat) (hj : j < (acc.setIfInBounds i (k, v)).size),
        (acc.setIfInBounds i (k, v))[j].1 = (acc[j]'(by simpa using hj)).1 := by
      intro j hj
      rw [Array.getElem_setIfInBounds]
      split
      · rename_i e; subst e; exact he.symm
      · rfl
    have hat : Fields.isAt (acc.setIfInBounds i (k, v)) = Fields.isAt acc := by
      funext j a
      unfold Fields.isAt
      by_cases hj : j < acc.size
      · rw [dite_eq_left (by simpa using hj), dite_eq_left hj, hfst]
      · rw [dite_eq_right (by simpa using hj), dite_eq_right hj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Array.toList_setIfInBounds, insertLast_of_some hk']
    · intro h j hj
      obtain ⟨hl', he'⟩ := hw h j hj
      exact ⟨by simpa using hl', by rw [hfst]; exact he'⟩
    · exact hsp
    · intro a
      show x.find (Fields.isAt (acc.setIfInBounds i (k, v))) a = _
      rw [hat, Fields.keys, hset]; exact hf a
  | none =>
    have hk' := hk
    rw [show x.find (Fields.isAt acc) k = Fields.find (acc, x) k from rfl, hf] at hk'
    have hat : ∀ j a, j < acc.size → Fields.isAt (acc.push (k, v)) j a = Fields.isAt acc j a := by
      intro j a hj
      unfold Fields.isAt
      rw [dite_eq_left (by simp; omega), dite_eq_left hj, Array.getElem_push_lt hj]
    have hatn : ∀ a, Fields.isAt (acc.push (k, v)) acc.size a = (k == a) := by
      intro a; unfold Fields.isAt; rw [dite_eq_left (by simp), Array.getElem_push_eq]
    refine ⟨?_, Fields.wf_add hw, ?_, ?_⟩
    · rw [Array.toList_push, insertLast_of_none hk']
    · intro a ha
      rw [Fields.spill_add] at ha
      simp only [KeyIndex.add]
      split
      · rename_i hc
        split at ha
        · rename_i e; rw [← e.2]; intro hn
          rw [Std.HashMap.contains_eq_isSome_getElem?, hn] at hc; cases hc
        · exact hsp a ha
      · rename_i hc
        rw [ite_eq_right (fun e => hc e.1)] at ha
        simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
        split
        · simp
        · exact hsp a ha
    · intro a
      show (x.add k acc.size).find (Fields.isAt (acc.push (k, v))) a = _
      rw [Fields.keys, Array.toList_push, List.map_append, List.map_singleton, firstPos_append]
      dsimp only
      rw [← show Fields.find (acc, x) a = _ from hf a]
      simp only [Fields.find, KeyIndex.find, KeyIndex.add, List.length_map, Array.length_toList]
      simp only [KeyIndex.find] at hk
      have hb : ∀ j, x.table[keySlot a]? = some j → j < acc.size := fun j hj => (hw _ j hj).1
      by_cases hc : x.table.contains (keySlot k) = true
      · simp only [hc, ↓reduceIte, Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq]
        cases ht : x.table[keySlot a]? with
        | none =>
          have : ¬ k = a := by
            rintro rfl; rw [Std.HashMap.contains_eq_isSome_getElem?, ht] at hc; cases hc
          simp [this]
        | some j =>
          simp only [Option.bind_some, hat j a (hb j ht)]
          by_cases hj : isAt acc j a = true
          · simp [hj]
          · simp only [hj, Bool.false_eq_true, ↓reduceIte]
            by_cases e : k = a
            · subst e
              rw [ht] at hk
              simp only [Option.bind_some, hj, Bool.false_eq_true, ↓reduceIte] at hk
              simp [hk]
            · simp [e]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_insert, beq_iff_eq]
        have hk0 : x.table[keySlot k]? = none := by
          cases h : x.table[keySlot k]? with
          | none => rfl
          | some _ => rw [Std.HashMap.contains_eq_isSome_getElem?, h] at hc; simp at hc
        by_cases he : keySlot k = keySlot a
        · rw [ite_eq_left he, Option.bind_some, hatn, ← he, hk0]
          by_cases e : k = a
          · simp [e]
          · have : x.spill[a]? = none := by
              cases h : x.spill[a]? with
              | none => rfl
              | some _ => exact absurd (he ▸ hk0) (hsp a (by simp [h]))
            simp [e, this]
        · rw [ite_eq_right he]
          have e : ¬ k = a := fun e => he (congrArg keySlot e)
          simp only [e, ↓reduceIte, Option.or_none]
          cases ht : x.table[keySlot a]? with
          | none => rfl
          | some j => simp only [Option.bind_some, hat j a (hb j ht)]

/-- **The parser's key collapsing is the specification**: `dedupKeys`, the
fold of `Fields.add` that the parser performs on an object's members, is
`Json.dedupKeysList`. -/
theorem dedupKeys_eq (kvs : Array (String × Json)) : Json.dedupKeys kvs = (Json.dedupKeysList kvs.toList).toArray := by
  suffices h : ∀ (l : List (String × Json)) (st : Fields), st.Exact →
      (l.foldl (fun st kv => st.add true kv.1 kv.2) st).1.toList =
        l.foldl (fun acc kv => Json.insertLast kv.1 kv.2 acc) st.1.toList by
    rw [Json.dedupKeys, Json.dedupKeysList, ← Array.foldl_toList]
    apply Array.toList_inj.mp
    rw [h _ _ Fields.exact_empty]; rfl
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons kv l ih =>
    intro st hx
    obtain ⟨h1, h2⟩ := Fields.add_exact (k := kv.1) (v := kv.2) hx
    simp only [List.foldl_cons]
    rw [ih _ h2, h1]

end LeanJson
