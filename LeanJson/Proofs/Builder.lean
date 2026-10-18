import LeanJson.RepoImpl.Builder

/-!
# Proofs: the byte builder prints what `printWith` specifies
-/

namespace LeanJson

theorem pushList_data (acc : ByteArray) (l : List UInt8) :
    (pushList acc l).data.toList = acc.data.toList ++ l := by
  induction l generalizing acc with
  | nil => simp [pushList]
  | cons b l ih =>
    simp only [pushList, List.foldl_cons] at *
    rw [ih]; simp [ByteArray.data_push]

theorem push_data (acc : ByteArray) (b : UInt8) : (acc.push b).data.toList = acc.data.toList ++ [b] := by
  simp [ByteArray.data_push]

theorem pushString_data (ascii : Bool) (acc : ByteArray) (s : String) :
    (pushString ascii acc s).data.toList = acc.data.toList ++ printString ascii s := by
  unfold pushString printString
  have key : ∀ (cs : List Char) (a : ByteArray),
      (cs.foldl (fun a c => pushList a (escapeChar ascii c)) a).data.toList =
        a.data.toList ++ cs.flatMap (escapeChar ascii) := by
    intro cs
    induction cs with
    | nil => simp
    | cons c cs ih => intro a; simp only [List.foldl_cons, ih, pushList_data, List.flatMap_cons, List.append_assoc]
  rw [push_data, key, push_data]; simp

theorem snd_lt (kv : String × Json) : sizeOf kv.2 < sizeOf kv := by
  cases kv; simp; omega

mutual
theorem printTo_data (o : PrintOpts) (d : Nat) (acc : ByteArray) (v : Json) :
    (printTo o d acc v).data.toList = acc.data.toList ++ printWith o d v := by
  match v with
  | .null => simp [printTo, printWith, pushList_data]
  | .bool true => simp [printTo, printWith, pushList_data]
  | .bool false => simp [printTo, printWith, pushList_data]
  | .num n => simp [printTo, printWith, pushList_data]
  | .str s => simp [printTo, printWith, pushString_data]
  | .arr a =>
    rw [printTo]
    split
    · rename_i h
      rw [push_data, pushList_data, printElemsFrom_data o, printTo_data o (d + 1) _ a[0], pushList_data, push_data]
      obtain ⟨l⟩ := a
      cases l with
      | nil => simp at h
      | cons x xs => simp [printWith]
    · rename_i h
      obtain ⟨l⟩ := a
      cases l with
      | nil => simp [printWith]
      | cons x xs => simp at h
  | .obj a =>
    rw [printTo]
    split
    · rename_i h
      rw [push_data, pushList_data, printMembersFrom_data o, printTo_data o (d + 1) _ a[0].2, pushList_data,
        pushString_data, pushList_data, push_data]
      obtain ⟨l⟩ := a
      cases l with
      | nil => simp at h
      | cons kv kvs => obtain ⟨k, v⟩ := kv; simp [printWith]
    · rename_i h
      obtain ⟨l⟩ := a
      cases l with
      | nil => simp [printWith]
      | cons x xs => simp at h
termination_by (sizeOf v, 0)
decreasing_by
  all_goals simp_wf
  all_goals apply Prod.Lex.left
  all_goals first
    | omega
    | exact Nat.lt_of_lt_of_le (Array.sizeOf_getElem _ _ _) (Nat.le_add_left _ _)
    | exact Nat.lt_of_lt_of_le (Nat.lt_trans (snd_lt _) (Array.sizeOf_getElem _ _ _)) (Nat.le_add_left _ _)
theorem printElemsFrom_data (o : PrintOpts) (d : Nat) (acc : ByteArray) (a : Array Json) (i : Nat) :
    (printElemsFrom o d acc a i).data.toList = acc.data.toList ++ printElems o d (a.toList.drop i) := by
  rw [printElemsFrom]
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons (i := i) (by simpa using h)]
    rw [printElemsFrom_data o d _ a (i + 1), printTo_data o d _ a[i], pushList_data, push_data]
    simp [printElems]
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simpa using h)]
    simp [printElems]
termination_by (sizeOf a, a.size - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; exact Array.sizeOf_getElem _ _ _)
theorem printMembersFrom_data (o : PrintOpts) (d : Nat) (acc : ByteArray) (a : Array (String × Json))
    (i : Nat) :
    (printMembersFrom o d acc a i).data.toList = acc.data.toList ++ printMembers o d (a.toList.drop i) := by
  rw [printMembersFrom]
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons (i := i) (by simpa using h)]
    rw [printMembersFrom_data o d _ a (i + 1), printTo_data o d _ a[i].2, pushList_data, pushString_data,
      pushList_data, push_data]
    simp [printMembers]
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simpa using h)]
    simp [printMembers]
termination_by (sizeOf a, a.size - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; exact Nat.lt_trans (snd_lt _) (Array.sizeOf_getElem _ _ _))
end

/-- The builder prints exactly the specified bytes. -/
theorem printBA_eq (o : PrintOpts) (v : Json) : printBA o v = (printWith o 0 v).toByteArray := by
  apply ByteArray.ext
  apply Array.ext'
  rw [List.data_toByteArray, List.toList_toArray]
  simpa [printBA] using printTo_data o 0 .empty v

end LeanJson
