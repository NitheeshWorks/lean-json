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

mutual
theorem printTo_data (o : PrintOpts) : ∀ (d : Nat) (acc : ByteArray) (v : Json),
    (printTo o d acc v).data.toList = acc.data.toList ++ printWith o d v
  | d, acc, .null => by simp [printTo, printWith, pushList_data]
  | d, acc, .bool true => by simp [printTo, printWith, pushList_data]
  | d, acc, .bool false => by simp [printTo, printWith, pushList_data]
  | d, acc, .num n => by simp [printTo, printWith, pushList_data]
  | d, acc, .str s => by simp [printTo, printWith, pushString_data]
  | d, acc, .arr ⟨[]⟩ => by simp [printTo, printWith]
  | d, acc, .arr ⟨x :: xs⟩ => by
    simp only [printTo, printWith, push_data, pushList_data, printElemsTo_data o, printTo_data o,
      List.append_assoc, List.cons_append, List.nil_append]
  | d, acc, .obj ⟨[]⟩ => by simp [printTo, printWith]
  | d, acc, .obj ⟨(k, v) :: kvs⟩ => by
    simp only [printTo, printWith, push_data, pushList_data, pushString_data, printMembersTo_data o,
      printTo_data o, List.append_assoc, List.cons_append, List.nil_append]
theorem printElemsTo_data (o : PrintOpts) : ∀ (d : Nat) (acc : ByteArray) (xs : List Json),
    (printElemsTo o d acc xs).data.toList = acc.data.toList ++ printElems o d xs
  | d, acc, [] => by simp [printElemsTo, printElems]
  | d, acc, x :: xs => by
    simp only [printElemsTo, printElems, printElemsTo_data o, printTo_data o, pushList_data, push_data,
      List.append_assoc, List.cons_append, List.nil_append]
theorem printMembersTo_data (o : PrintOpts) : ∀ (d : Nat) (acc : ByteArray) (kvs : List (String × Json)),
    (printMembersTo o d acc kvs).data.toList = acc.data.toList ++ printMembers o d kvs
  | d, acc, [] => by simp [printMembersTo, printMembers]
  | d, acc, (k, v) :: kvs => by
    simp only [printMembersTo, printMembers, printMembersTo_data o, printTo_data o, pushList_data,
      pushString_data, push_data, List.append_assoc, List.cons_append, List.nil_append]
end

/-- The builder prints exactly the specified bytes. -/
theorem printBA_eq (o : PrintOpts) (v : Json) : printBA o v = (printWith o 0 v).toByteArray := by
  apply ByteArray.ext
  apply Array.ext'
  rw [List.data_toByteArray, List.toList_toArray]
  simpa [printBA] using printTo_data o 0 .empty v

end LeanJson
