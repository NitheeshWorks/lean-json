import LeanJson.RepoImpl.Print
import LeanJson.RepoImpl.Scan

/-!
# RepoImpl: the printer as a byte builder

`printTo o d acc v` appends the printing of `v` to the buffer `acc` one
byte at a time, so printing is linear in the output however deep the
nesting (the list-based `printWith` copies a child once per level). It is
proved equal to `printWith` (`Proofs/Builder.lean`), which stays the
specification. A string is copied in runs: the bytes between two characters
that need escaping go across at once (`pushStringFast`, swapped in by
`@[csimp]` through `pushString_eq_fast`).
-/

namespace LeanJson

/-- Append a list of bytes. -/
def pushList (acc : ByteArray) (l : List UInt8) : ByteArray := l.foldl ByteArray.push acc

/-- Append a string literal, escaping as `printString` does. -/
def pushString (ascii : Bool) (acc : ByteArray) (s : String) : ByteArray :=
  (s.toList.foldl (fun a c => pushList a (escapeChar ascii c)) (acc.push 34)).push 34

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


/-- The escaped form of one byte of a string's UTF-8, as `escapeChar false`
writes it: an ASCII quote, backslash or control character escaped, every
other byte (non-ASCII ones included) as itself. -/
def escByte (x : UInt8) : List UInt8 :=
  if x < 32 || x == 34 || x == 92 then escapeChar false (Char.ofNat x.toNat) else [x]

theorem utf8EncodeChar_big {c : Char} (hc : 128 ≤ c.toNat) :
    ∀ x ∈ String.utf8EncodeChar c, 128 ≤ x.toNat := by
  rw [← Char.toNat_val] at hc
  unfold String.utf8EncodeChar
  dsimp only
  intro x hx
  rw [ite_eq_right (by omega)] at hx
  split at hx
  · simp at hx; rcases hx with rfl | rfl <;> simp [UInt8.toNat_ofNat] <;> omega
  split at hx
  · simp at hx; rcases hx with rfl | rfl | rfl <;> simp [UInt8.toNat_ofNat] <;> omega
  · simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp [UInt8.toNat_ofNat] <;> omega

theorem utf8EncodeChar_small {c : Char} (hc : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  unfold String.utf8EncodeChar
  dsimp only
  rw [Char.toNat_val, ite_eq_left (by omega)]

/-- An ASCII character other than a quote, a backslash or a control
character is written as its one byte. -/
theorem escapeChar_plain {c : Char} (hc : c.toNat < 128) (h32 : ¬ c.toNat < 32) (h34 : c.toNat ≠ 34)
    (h92 : c.toNat ≠ 92) (ascii : Bool) : escapeChar ascii c = [UInt8.ofNat c.toNat] := by
  unfold escapeChar
  dsimp only
  rw [ite_eq_right h34, ite_eq_right h92, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h32, ite_eq_right (by omega), utf8EncodeChar_small hc]

theorem escapeChar_bytes (c : Char) :
    (String.utf8EncodeChar c).flatMap escByte = escapeChar false c := by
  by_cases hc : c.toNat < 128
  · rw [utf8EncodeChar_small hc]
    have hx : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp; omega
    have hco : Char.ofNat c.toNat = c := Char.ofNat_toNat c
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, escByte, hx, hco]
    split
    · rfl
    · rename_i h
      simp only [Bool.or_eq_true, beq_iff_eq, not_or, decide_eq_true_eq] at h
      have h32 : ¬ c.toNat < 32 := by
        intro h'; apply h.1.1; rw [UInt8.lt_iff_toNat_lt, hx]; exact h'
      have h34 : c.toNat ≠ 34 := by
        intro h'; apply h.1.2; apply UInt8.toNat_inj.mp; rw [hx, h']; rfl
      have h92 : c.toNat ≠ 92 := by
        intro h'; apply h.2; apply UInt8.toNat_inj.mp; rw [hx, h']; rfl
      rw [escapeChar_plain hc h32 h34 h92]
  · have hall := utf8EncodeChar_big (c := c) (by omega)
    have : (String.utf8EncodeChar c).flatMap escByte = String.utf8EncodeChar c := by
      generalize String.utf8EncodeChar c = l at hall ⊢
      induction l with
      | nil => rfl
      | cons x l ih =>
        have hx := hall x (by simp)
        have : escByte x = [x] := by
          unfold escByte
          rw [ite_eq_right]
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [UInt8.lt_iff_toNat_lt]; simp; omega
          · intro h; subst h; simp at hx
          · intro h; subst h; simp at hx
        simp only [List.flatMap_cons, this, List.singleton_append]
        rw [ih (fun y hy => hall y (by simp [hy]))]
    rw [this]
    unfold escapeChar
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by simp)]

theorem printString_bytes (s : String) :
    s.toList.flatMap (escapeChar false) = s.toByteArray.data.toList.flatMap escByte := by
  rw [← String.utf8Encode_toList]
  simp only [List.utf8Encode, List.data_toByteArray, List.flatMap_assoc, escapeChar_bytes]


/-- Whether a byte of a string's UTF-8 is escaped in a literal (`escByte`):
an ASCII quote, backslash or control character. -/
@[inline] def escNeeded (x : UInt8) : Bool := x < 32 || x == 34 || x == 92

/-- Bytes `st` to `i` of `b`, copied onto the end of `acc` at once. -/
@[inline] def copyRun (b : ByteArray) (st i : Nat) (acc : ByteArray) : ByteArray :=
  b.copySlice st acc acc.size (i - st) false

/-- The escaped form of bytes `i` on of `b`, appended to `acc`: each run of
bytes that need no escape (up to `findFrom escNeeded`) is copied whole. -/
def escapeBytes (b : ByteArray) (i : Nat) (acc : ByteArray) : ByteArray :=
  let j := findFrom escNeeded b i
  let acc := copyRun b i j acc
  if h : j < b.size then
    escapeBytes b (j + 1) (pushList acc (escapeChar false (Char.ofNat b[j].toNat)))
  else acc
termination_by b.size - i
decreasing_by have := le_findFrom escNeeded b i; omega

theorem copyRun_data (b acc : ByteArray) {st i : Nat} (h1 : st ≤ i) :
    (copyRun b st i acc).data.toList = acc.data.toList ++ (b.data.toList.drop st).take (i - st) := by
  unfold copyRun
  rw [ByteArray.copySlice_eq_append]
  have : acc.extract (acc.size + min (i - st) (b.data.size - st)) acc.data.size = ByteArray.empty := by
    ext1; simp; try omega
  rw [this]
  simp [Nat.add_sub_cancel' h1, List.take_drop]

theorem drop_cons_getElem (b : ByteArray) {i : Nat} (h : i < b.size) :
    b.data.toList.drop i = b[i] :: b.data.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]; simp; rfl

/-- A run of bytes that need no escape is written as itself. -/
theorem escByte_run (b : ByteArray) {i j : Nat} (hij : i ≤ j) (hj : j ≤ b.size)
    (hrun : ∀ k (hk : k < b.size), i ≤ k → k < j → escNeeded b[k] = false) :
    (b.data.toList.drop i).flatMap escByte =
      (b.data.toList.drop i).take (j - i) ++ (b.data.toList.drop j).flatMap escByte := by
  by_cases e : i = j
  · subst e; simp
  · have hi : i < b.size := by omega
    have hx : escByte b[i] = [b[i]] := by
      unfold escByte; rw [ite_eq_right (by simpa [escNeeded] using hrun i hi (Nat.le_refl _) (by omega))]
    rw [drop_cons_getElem b hi, List.flatMap_cons, hx,
      escByte_run b (i := i + 1) (by omega) hj (fun k hk h1 h2 => hrun k hk (by omega) h2),
      show j - i = (j - (i + 1)) + 1 by omega, List.take_succ_cons]
    rfl
termination_by j - i

theorem escapeBytes_data (b : ByteArray) (i : Nat) (acc : ByteArray) (h2 : i ≤ b.size) :
    (escapeBytes b i acc).data.toList = acc.data.toList ++ (b.data.toList.drop i).flatMap escByte := by
  have hle := le_findFrom escNeeded b i
  have hfl := findFrom_le escNeeded b i h2
  rw [escapeBytes]
  rw [escByte_run b hle hfl (fun k hk h1 h2 => findFrom_run k hk h1 h2)]
  split
  · rename_i h
    have hstop := findFrom_stop h
    rw [escapeBytes_data b _ _ h, pushList_data, copyRun_data b acc hle, drop_cons_getElem b h]
    have : escByte b[findFrom escNeeded b i] =
        escapeChar false (Char.ofNat b[findFrom escNeeded b i].toNat) := by
      unfold escByte; rw [ite_eq_left (by simpa [escNeeded] using hstop)]
    simp [this]
  · rename_i h
    have e : findFrom escNeeded b i = b.size := by omega
    have : b.data.toList.drop b.size = [] := List.drop_eq_nil_of_le (by simp)
    rw [copyRun_data b acc hle, e, this]
    simp
termination_by b.size - i
decreasing_by omega

/-- Every byte of `b` is ASCII when the first non-ASCII one is at the end. -/
theorem ascii_of_find {b : ByteArray} (h : findFrom (fun x => 128 ≤ x) b 0 = b.size) :
    ∀ x ∈ b.data.toList, x < 128 := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hk' : k < b.size := by simpa using hk
  have := findFrom_run (p := fun x => 128 ≤ x) k hk' (Nat.zero_le _) (by omega)
  simp only [decide_eq_false_iff_not, UInt8.not_le] at this
  exact this

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons, h a (by simp), flatMap_congr_mem (l := l) (fun x hx => h x (by simp [hx]))]

/-- Under `ensureAscii`, a string of ASCII characters is escaped as without. -/
theorem escape_ascii_of {s : String} (h : findFrom (fun x => 128 ≤ x) s.toByteArray 0 = s.toByteArray.size) :
    s.toList.flatMap (escapeChar true) = s.toList.flatMap (escapeChar false) := by
  have hb := ascii_of_find h
  apply flatMap_congr_mem
  intro c hc
  have hc128 : c.toNat < 128 := by
    apply Classical.byContradiction
    intro hn
    have hbig := utf8EncodeChar_big (c := c) (by omega)
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (String.utf8EncodeChar_ne_nil (c := c))
    have hxb : x ∈ s.toByteArray.data.toList := by
      rw [← String.utf8Encode_toList]
      simp only [List.utf8Encode, List.data_toByteArray]
      exact List.mem_flatMap.mpr ⟨c, hc, hx⟩
    have h1 := hb x hxb
    have h2 := hbig x hx
    rw [UInt8.lt_iff_toNat_lt] at h1
    simp at h1; omega
  unfold escapeChar
  simp only [show ¬ (128 ≤ c.toNat) by omega, and_false, ↓reduceIte]

/-- `pushString` copying runs of unescaped bytes whole, rather than one
character's list of bytes at a time (`pushString_eq_fast`). Under
`ensureAscii`, a string with non-ASCII characters goes character by
character as before. -/
def pushStringFast (ascii : Bool) (acc : ByteArray) (s : String) : ByteArray :=
  let b := s.toByteArray
  if !ascii || findFrom (fun x => 128 ≤ x) b 0 == b.size then (escapeBytes b 0 (acc.push 34)).push 34
  else pushString ascii acc s

@[csimp] theorem pushString_eq_fast : @pushString = @pushStringFast := by
  funext ascii acc s
  unfold pushStringFast
  dsimp only
  split
  · rename_i h
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [pushString_data, push_data, escapeBytes_data _ 0 _ (Nat.zero_le _), push_data]
    have : s.toList.flatMap (escapeChar ascii) = s.toList.flatMap (escapeChar false) := by
      cases ascii
      · rfl
      · exact escape_ascii_of (by simpa using h)
    simp [printString, this, printString_bytes]
  · rfl


mutual
/-- Append the printing of `v` at depth `d`. Containers are walked by index,
never converted to a list. -/
def printTo (o : PrintOpts) (d : Nat) (acc : ByteArray) : Json → ByteArray
  | .null => pushList acc litNull
  | .bool true => pushList acc litTrue
  | .bool false => pushList acc litFalse
  | .num n => pushList acc (printNumberIn o n)
  | .str s => pushString o.ensureAscii acc s
  | .arr a =>
    if h : 0 < a.size then
      (pushList (printElemsFrom o (d + 1) (printTo o (d + 1) (pushList (acc.push 91) (o.nl (d + 1))) a[0])
        a 1) (o.nl d)).push 93
    else (acc.push 91).push 93
  | .obj a =>
    if h : 0 < a.size then
      (pushList (printMembersFrom o (d + 1)
        (printTo o (d + 1) (pushList (pushString o.ensureAscii (pushList (acc.push 123) (o.nl (d + 1)))
          a[0].1) o.colon) a[0].2) a 1) (o.nl d)).push 125
    else (acc.push 123).push 125
termination_by v => (sizeOf v, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_getElem a 0 h; omega)
    | (have := Array.sizeOf_getElem a 0 h
       have : sizeOf a[0].2 < sizeOf a[0] := by
         cases a[0]; simp; omega
       omega)
    | (apply Prod.Lex.left; omega)
/-- Append `,` and element `i`, then the rest, from index `i` on. -/
def printElemsFrom (o : PrintOpts) (d : Nat) (acc : ByteArray) (a : Array Json) (i : Nat) : ByteArray :=
  if h : i < a.size then printElemsFrom o d (printTo o d (pushList (acc.push 44) (o.sep d)) a[i]) a (i + 1)
  else acc
termination_by (sizeOf a, a.size - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; have := Array.sizeOf_getElem a i h; omega)
    | (apply Prod.Lex.left
       have := Array.sizeOf_getElem a i h
       have : sizeOf a[i].2 < sizeOf a[i] := by cases a[i]; simp; omega
       omega)
/-- Append `,` and member `i`, then the rest, from index `i` on. -/
def printMembersFrom (o : PrintOpts) (d : Nat) (acc : ByteArray) (a : Array (String × Json)) (i : Nat) :
    ByteArray :=
  if h : i < a.size then
    printMembersFrom o d
      (printTo o d (pushList (pushString o.ensureAscii (pushList (acc.push 44) (o.sep d)) a[i].1) o.colon)
        a[i].2) a (i + 1)
  else acc
termination_by (sizeOf a, a.size - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; have := Array.sizeOf_getElem a i h; omega)
    | (apply Prod.Lex.left
       have := Array.sizeOf_getElem a i h
       have : sizeOf a[i].2 < sizeOf a[i] := by cases a[i]; simp; omega
       omega)
end

/-- The printing of `v` under `o`, as bytes. -/
def printBA (o : PrintOpts) (v : Json) : ByteArray := printTo o 0 .empty v

end LeanJson
