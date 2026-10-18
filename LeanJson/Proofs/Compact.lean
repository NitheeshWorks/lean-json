import LeanJson.Proofs.Depth

/-!
# Proofs: the compact form has no layout whitespace

`print_compact`: with `indent = none` the output contains no tab, line feed
or carriage return byte, and a space byte only where a string in the value
contains a space. So the only separators are `,` and `:`.
-/

namespace LeanJson

open Spec

/-- A byte that is not tab, LF or CR, and is a space only if `P`. -/
def Quiet (P : Prop) (b : UInt8) : Prop := b ≠ 9 ∧ b ≠ 10 ∧ b ≠ 13 ∧ (b = 32 → P)

theorem quiet_mono {P Q : Prop} {b : UInt8} (h : Quiet P b) (hpq : P → Q) : Quiet Q b :=
  ⟨h.1, h.2.1, h.2.2.1, fun e => hpq (h.2.2.2 e)⟩

theorem quiet_of_ge {P : Prop} {b : UInt8} (h : 33 ≤ b.toNat) : Quiet P b := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro e; subst e; simp at h)

/-- Every byte of `l` is quiet. -/
def AllQuiet (P : Prop) (l : List UInt8) : Prop := ∀ b ∈ l, Quiet P b

@[simp] theorem allQuiet_nil (P : Prop) : AllQuiet P [] := by simp [AllQuiet]

@[simp] theorem allQuiet_append (P : Prop) (l₁ l₂ : List UInt8) :
    AllQuiet P (l₁ ++ l₂) ↔ AllQuiet P l₁ ∧ AllQuiet P l₂ := by
  simp only [AllQuiet, List.mem_append]
  exact ⟨fun h => ⟨fun b hb => h b (Or.inl hb), fun b hb => h b (Or.inr hb)⟩,
    fun h b hb => hb.elim (h.1 b) (h.2 b)⟩

@[simp] theorem allQuiet_cons (P : Prop) (b : UInt8) (l : List UInt8) :
    AllQuiet P (b :: l) ↔ Quiet P b ∧ AllQuiet P l := by
  simp only [AllQuiet, List.mem_cons, forall_eq_or_imp]

theorem allQuiet_mono {P Q : Prop} {l : List UInt8} (h : AllQuiet P l) (hpq : P → Q) : AllQuiet Q l :=
  fun b hb => quiet_mono (h b hb) hpq

theorem hexByte_quiet (P : Prop) : ∀ d : Fin 16, Quiet P (hexByte d.val) := by
  intro d
  apply quiet_of_ge
  revert d; decide

theorem hex4_quiet (P : Prop) (n : Nat) : ∀ b ∈ hex4 n, Quiet P b := by
  intro b hb
  simp only [hex4, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact quiet_of_ge (by decide)
  · exact quiet_of_ge (by decide)
  · exact hexByte_quiet P ⟨_, Nat.mod_lt _ (by decide)⟩
  · exact hexByte_quiet P ⟨_, Nat.mod_lt _ (by decide)⟩
  · exact hexByte_quiet P ⟨_, Nat.mod_lt _ (by decide)⟩
  · exact hexByte_quiet P ⟨_, Nat.mod_lt _ (by decide)⟩

theorem enc_all_high (c : Char) (h : 128 ≤ c.toNat) : ∀ b ∈ String.utf8EncodeChar c, 128 ≤ b.toNat := by
  have hlt : 127 < c.val := by rw [UInt32.lt_iff_toNat_lt]; exact h
  intro b hb
  rcases Char.utf8Size_eq c with h1 | h1 | h1 | h1
  · have := Char.utf8Size_eq_one_iff.mp h1
    rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt] at hlt
    exact absurd this (Nat.not_le.mpr hlt)
  · rw [String.utf8EncodeChar_eq_cons_cons h1] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact or_ge _ _ (by decide)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h1] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> exact or_ge _ _ (by decide)
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h1] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact or_ge _ _ (by decide)

theorem escapeChar_quiet (ascii : Bool) (c : Char) : ∀ b ∈ escapeChar ascii c, Quiet (c = ' ') b := by
  intro b hb
  unfold escapeChar at hb
  simp only at hb
  by_cases h34 : c.toNat = 34
  · rw [ite_eq_left h34] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h34] at hb
  by_cases h92 : c.toNat = 92
  · rw [ite_eq_left h92] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h92] at hb
  by_cases h8 : c.toNat = 8
  · rw [ite_eq_left h8] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h8] at hb
  by_cases h12 : c.toNat = 12
  · rw [ite_eq_left h12] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h12] at hb
  by_cases h10 : c.toNat = 10
  · rw [ite_eq_left h10] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h10] at hb
  by_cases h13 : c.toNat = 13
  · rw [ite_eq_left h13] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h13] at hb
  by_cases h9 : c.toNat = 9
  · rw [ite_eq_left h9] at hb; simp at hb; rcases hb with rfl | rfl <;> exact quiet_of_ge (by decide)
  rw [ite_eq_right h9] at hb
  by_cases h32 : c.toNat < 32
  · rw [ite_eq_left h32] at hb; exact hex4_quiet _ _ b hb
  rw [ite_eq_right h32] at hb
  by_cases hA : ascii = true ∧ 128 ≤ c.toNat
  · rw [ite_eq_left hA] at hb
    split at hb
    · exact hex4_quiet _ _ b hb
    · simp only [List.mem_append] at hb
      rcases hb with hb | hb <;> exact hex4_quiet _ _ b hb
  rw [ite_eq_right hA] at hb
  by_cases hlo : c.toNat < 128
  · rw [enc_ascii c hlo] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    have hbn : (UInt8.ofNat c.toNat).toNat = c.toNat := by simp; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e; rw [e] at hbn; simp at hbn; omega
    · intro e; rw [e] at hbn; simp at hbn; omega
    · intro e; rw [e] at hbn; simp at hbn; omega
    · intro e; rw [e] at hbn; simp at hbn
      rw [char_eq_ofNat c 32 hbn.symm]
  · exact quiet_of_ge (by have := enc_all_high c (by omega) b hb; omega)

theorem quiet_lit {P : Prop} {b : UInt8} (h : 33 ≤ b.toNat) : Quiet P b := quiet_of_ge h

/-- Split a conjunction of quiet facts and close the literal ones. -/
macro "quiet_split" : tactic => `(tactic| (repeat' apply And.intro) <;>
  first | assumption | exact allQuiet_nil _ | decide | (intro h; exact absurd h (by decide)))

theorem allQuiet_flatMap {P : Prop} {ascii : Bool} {s : String} (hP : ' ' ∈ s.toList → P) :
    AllQuiet P (s.toList.flatMap (escapeChar ascii)) := by
  intro b hb
  simp only [List.mem_flatMap] at hb
  obtain ⟨c, hc, hb⟩ := hb
  exact quiet_mono (escapeChar_quiet ascii c b hb) (fun e => hP (e ▸ hc))

theorem printString_quiet (ascii : Bool) (s : String) :
    AllQuiet (' ' ∈ s.toList) (printString ascii s) := by
  simp only [printString, allQuiet_cons, allQuiet_append, allQuiet_nil, and_true]
  have := allQuiet_flatMap (ascii := ascii) (s := s) id
  quiet_split

theorem allQuiet_digits (P : Prop) (ds : List Nat) (h : ∀ x ∈ ds, x < 10) :
    AllQuiet P (ds.map digitByte) := by
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨x, hx, rfl⟩ := hb
  apply quiet_lit
  have key : ∀ d : Fin 10, 33 ≤ (digitByte d.val).toNat := by decide
  exact key ⟨x, h x hx⟩

theorem printNat_quiet (P : Prop) (n : Nat) : AllQuiet P (printNat n) :=
  allQuiet_digits P _ (fun _ h => natDigits_lt10 h)

theorem printNumber_quiet (P : Prop) (n : Number) : AllQuiet P (printNumber n) := by
  cases n with
  | int i =>
    simp only [printNumber, printInt]
    split
    · simp only [allQuiet_cons]; exact ⟨quiet_lit (by decide), printNat_quiet P _⟩
    · exact printNat_quiet P _
  | float d =>
    obtain ⟨ip, fp, ex, S⟩ := layoutShape d
    simp only [printNumber, printDecimal, S.bytes, allQuiet_append]
    refine ⟨?_, ⟨⟨allQuiet_digits P ip S.hip.2.1, ?_⟩, ?_⟩⟩
    · cases d.neg
      · exact allQuiet_nil P
      · simp only [↓reduceIte, allQuiet_cons, allQuiet_nil, and_true]; exact quiet_lit (by decide)
    · cases fp with
      | none => simp [fracBytes]
      | some fs =>
        simp only [fracBytes, allQuiet_cons]
        exact ⟨quiet_lit (by decide), allQuiet_digits P fs (S.hfp fs rfl).2⟩
    · cases ex with
      | none => simp [expBytes]
      | some i =>
        simp only [expBytes, printExp, allQuiet_cons]
        refine ⟨quiet_lit (by decide), ?_⟩
        split
        · simp only [allQuiet_cons]; exact ⟨quiet_lit (by decide), printNat_quiet P _⟩
        · simp only [allQuiet_cons]; exact ⟨quiet_lit (by decide), printNat_quiet P _⟩

section
variable (o : PrintOpts) (ho : o.indent = none)
include ho

theorem nl_none (d : Nat) : o.nl d = [] := by simp [PrintOpts.nl, ho]
theorem colon_none : o.colon = [58] := by simp [PrintOpts.colon, ho]

mutual
theorem printWith_quiet : ∀ (v : Json) (d : Nat), AllQuiet (HasSpaceInString v) (printWith o d v)
  | .null, d => by
    simp only [printWith, litNull, allQuiet_cons, allQuiet_nil, and_true]
    exact ⟨quiet_lit (by decide), quiet_lit (by decide), quiet_lit (by decide), quiet_lit (by decide)⟩
  | .bool true, d => by
    simp only [printWith, litTrue, allQuiet_cons, allQuiet_nil, and_true]
    exact ⟨quiet_lit (by decide), quiet_lit (by decide), quiet_lit (by decide), quiet_lit (by decide)⟩
  | .bool false, d => by
    simp only [printWith, litFalse, allQuiet_cons, allQuiet_nil, and_true]
    exact ⟨quiet_lit (by decide), quiet_lit (by decide), quiet_lit (by decide), quiet_lit (by decide),
      quiet_lit (by decide)⟩
  | .num n, d => printNumber_quiet _ n
  | .str s, d => printString_quiet _ s
  | .arr [], d => by
    simp only [printWith, allQuiet_cons, allQuiet_nil, and_true]
    exact ⟨quiet_lit (by decide), quiet_lit (by decide)⟩
  | .arr (x :: xs), d => by
    have h1 := allQuiet_mono (printWith_quiet x (d + 1)) (Q := HasSpaceInString (.arr (x :: xs))) Or.inl
    have h2 := allQuiet_mono (printElems_quiet xs (d + 1)) (Q := HasSpaceInString (.arr (x :: xs))) Or.inr
    simp only [printWith, nl_none o ho, List.append_nil, allQuiet_cons,
      allQuiet_append, allQuiet_nil, and_true]
    quiet_split
  | .obj [], d => by
    simp only [printWith, allQuiet_cons, allQuiet_nil, and_true]
    exact ⟨quiet_lit (by decide), quiet_lit (by decide)⟩
  | .obj ((k, v) :: kvs), d => by
    have h1 := allQuiet_mono (printString_quiet o.ensureAscii k)
      (Q := HasSpaceInString (.obj ((k, v) :: kvs))) Or.inl
    have h2 := allQuiet_mono (printWith_quiet v (d + 1))
      (Q := HasSpaceInString (.obj ((k, v) :: kvs))) (fun h => Or.inr (Or.inl h))
    have h3 := allQuiet_mono (printMembers_quiet kvs (d + 1))
      (Q := HasSpaceInString (.obj ((k, v) :: kvs))) (fun h => Or.inr (Or.inr h))
    simp only [printWith, nl_none o ho, colon_none o ho, List.append_nil,
      allQuiet_cons, allQuiet_append, allQuiet_nil, and_true]
    quiet_split
theorem printElems_quiet : ∀ (xs : List Json) (d : Nat), AllQuiet (HasSpaceInList xs) (printElems o d xs)
  | [], d => by simp [printElems]
  | x :: xs, d => by
    have h1 := allQuiet_mono (printWith_quiet x d) (Q := HasSpaceInList (x :: xs)) Or.inl
    have h2 := allQuiet_mono (printElems_quiet xs d) (Q := HasSpaceInList (x :: xs)) Or.inr
    simp only [printElems, nl_none o ho, allQuiet_cons, allQuiet_append]
    quiet_split
theorem printMembers_quiet : ∀ (kvs : List (String × Json)) (d : Nat),
    AllQuiet (HasSpaceInFields kvs) (printMembers o d kvs)
  | [], d => by simp [printMembers]
  | (k, v) :: kvs, d => by
    have h1 := allQuiet_mono (printString_quiet o.ensureAscii k) (Q := HasSpaceInFields ((k, v) :: kvs)) Or.inl
    have h2 := allQuiet_mono (printWith_quiet v d) (Q := HasSpaceInFields ((k, v) :: kvs))
      (fun h => Or.inr (Or.inl h))
    have h3 := allQuiet_mono (printMembers_quiet kvs d) (Q := HasSpaceInFields ((k, v) :: kvs))
      (fun h => Or.inr (Or.inr h))
    simp only [printMembers, nl_none o ho, colon_none o ho, allQuiet_cons,
      allQuiet_append, allQuiet_nil, and_true]

    quiet_split
end
end

/-- **Compact output**: no tab, LF or CR byte, and a space only inside a string
that has one, for every compact option set (with or without `ensureAscii`). -/
theorem print_compact (o : PrintOpts) (ho : o.indent = none) (v : Json) :
    (9 : UInt8) ∉ printWith o 0 v ∧ (10 : UInt8) ∉ printWith o 0 v ∧ (13 : UInt8) ∉ printWith o 0 v ∧
      ((32 : UInt8) ∈ printWith o 0 v → HasSpaceInString v) :=
  ⟨fun h => (printWith_quiet o ho v 0 _ h).1 rfl, fun h => (printWith_quiet o ho v 0 _ h).2.1 rfl,
   fun h => (printWith_quiet o ho v 0 _ h).2.2.1 rfl, fun h => (printWith_quiet o ho v 0 _ h).2.2.2 rfl⟩

theorem print_compact_spec : Compact printBytes := print_compact {} rfl

end LeanJson
