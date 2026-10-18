import LeanJson.Proofs.String

/-!
# Proofs: the value codec

`parseValue_printWith_ext`, the headline: every value, printed with any
options at any depth, parses back to itself on any continuation that cannot
extend a number, with the cursor just past it. By mutual structural
recursion over `Json`, its element lists and its member lists, using the
string and number lemmas at the leaves.
-/

namespace LeanJson

open Spec

/-- Every byte is JSON whitespace. -/
def WsList (l : List UInt8) : Prop := ∀ b ∈ l, isWs b = true

theorem wsList_nl (o : PrintOpts) (d : Nat) : WsList (o.nl d) := by
  unfold PrintOpts.nl WsList
  split
  · simp
  · intro b hb
    simp only [List.mem_cons, List.mem_replicate] at hb
    rcases hb with rfl | ⟨_, rfl⟩ <;> decide

theorem colon_eq (o : PrintOpts) : ∃ ws, o.colon = 58 :: ws ∧ WsList ws := by
  unfold PrintOpts.colon
  split
  · exact ⟨[], rfl, by simp [WsList]⟩
  · exact ⟨[32], rfl, by simp [WsList]; decide⟩

theorem skipWs_ext {bs : ByteArray} :
    ∀ (ws : List UInt8) (p fuel : Nat) {b : UInt8} {t R : List UInt8}, WsList ws → isWs b = false →
      At bs p (ws ++ b :: t) R → ws.length ≤ fuel → skipWs bs p fuel = p + ws.length
  | [], p, fuel, b, t, R, _, hb, h, _ => by
    cases fuel with
    | zero => rfl
    | succ f => simp [skipWs, h.get, hb]
  | w :: ws, p, fuel, b, t, R, hw, hb, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hw1 : isWs w = true := hw w (by simp)
    simp only [skipWs, List.cons_append] at h ⊢
    rw [h.get]
    simp only [hw1, ↓reduceIte]
    rw [skipWs_ext ws (p + 1) f (fun x hx => hw x (by simp [hx])) hb h.next (by simp at hf; omega)]
    simp; omega

/-- `skipWs` with the parser's fuel. -/
theorem skipWs_at {bs : ByteArray} {ws : List UInt8} {p : Nat} {b : UInt8} {t R : List UInt8}
    (hw : WsList ws) (hb : isWs b = false) (h : At bs p (ws ++ b :: t) R) :
    skipWs bs p bs.size = p + ws.length := by
  apply skipWs_ext ws p bs.size hw hb h
  have := h.le_size (by simp); simp at this; omega

theorem skipWs_nil {bs : ByteArray} {p : Nat} {b : UInt8} {t R : List UInt8}
    (hb : isWs b = false) (h : At bs p (b :: t) R) : skipWs bs p bs.size = p := by
  have := skipWs_at (ws := []) (by simp [WsList]) hb h
  simpa using this

theorem expectLit_ext {bs : ByteArray} :
    ∀ (lit : List UInt8) (p : Nat) {R : List UInt8}, At bs p lit R → expectLit bs p lit = .ok (p + lit.length)
  | [], p, R, _ => by simp [expectLit]
  | c :: cs, p, R, h => by
    simp only [expectLit, h.get, beq_self_eq_true, ↓reduceIte]
    rw [expectLit_ext cs (p + 1) h.next]
    simp; omega

/-- The first byte of a printed number is `-` or a digit. -/
theorem printNumber_head (n : Number) :
    ∃ b t, printNumber n = b :: t ∧ (b = 45 ∨ ∃ d : Fin 10, b = digitByte d) := by
  cases n with
  | int i =>
    unfold printNumber printInt
    by_cases hi : i < 0
    · simp only [hi, ↓reduceIte]; exact ⟨_, _, rfl, Or.inl rfl⟩
    · simp only [hi, ↓reduceIte, printNat]
      obtain ⟨_, h10, d, t, e, _⟩ := natDigits_spec i.toNat
      rw [e]; exact ⟨_, _, rfl, Or.inr ⟨⟨d, h10 d (by rw [e]; simp)⟩, rfl⟩⟩
  | float dec =>
    unfold printNumber printDecimal
    cases hneg : dec.neg
    · obtain ⟨ip, fp, ex, S⟩ := layoutShape dec
      simp only [hneg, Bool.false_eq_true, ↓reduceIte, List.nil_append, S.bytes]
      obtain ⟨hne, h10, _⟩ := S.hip
      match ip, hne, h10 with
      | d :: t, _, h10 => exact ⟨_, _, rfl, Or.inr ⟨⟨d, h10 d (by simp)⟩, rfl⟩⟩
    · simp only [hneg, ↓reduceIte, List.cons_append, List.nil_append]
      exact ⟨_, _, rfl, Or.inl rfl⟩

/-- What a printed value can start with. -/
def ValueHead (b : UInt8) : Prop :=
  b = 110 ∨ b = 116 ∨ b = 102 ∨ b = 34 ∨ b = 91 ∨ b = 123 ∨ b = 45 ∨ ∃ d : Fin 10, b = digitByte d

theorem valueHead_props {b : UInt8} (h : ValueHead b) :
    isWs b = false ∧ b ≠ 93 ∧ b ≠ 125 ∧ b ≠ 44 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩
  all_goals first | decide | (revert d; decide)

theorem printWith_head (o : PrintOpts) (d : Nat) (v : Json) :
    ∃ b t, printWith o d v = b :: t ∧ ValueHead b := by
  cases v with
  | null => exact ⟨_, _, rfl, Or.inl rfl⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, by simp [ValueHead]⟩
  | num n =>
    obtain ⟨b, t, e, h⟩ := printNumber_head n
    refine ⟨b, t, by simp [printWith, e], ?_⟩
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  | str s => exact ⟨_, _, rfl, by simp [ValueHead]⟩
  | arr xs => cases xs <;> exact ⟨_, _, rfl, by simp [ValueHead]⟩
  | obj kvs =>
    match kvs with
    | [] => exact ⟨_, _, rfl, by simp [ValueHead]⟩
    | (_, _) :: _ => exact ⟨_, _, rfl, by simp [ValueHead]⟩

theorem printWith_ne_nil (o : PrintOpts) (d : Nat) (v : Json) : printWith o d v ≠ [] := by
  obtain ⟨b, t, e, _⟩ := printWith_head o d v; rw [e]; simp

theorem numStop_of_head {l : List UInt8} {b : UInt8} {t : List UInt8} (e : l = b :: t)
    (h : b = 44 ∨ b = 93 ∨ b = 125 ∨ isWs b = true) : NumStop l := by
  intro x hx; rw [e] at hx; simp at hx; subst hx
  rcases h with rfl | rfl | rfl | h
  · decide
  · decide
  · decide
  · have : ((b = 32 ∨ b = 9) ∨ b = 10) ∨ b = 13 := by simpa [isWs] using h
    rcases this with ((rfl | rfl) | rfl) | rfl <;> decide

/-- The elements of a nonempty array, first one unprefixed. -/
def printFirst (o : PrintOpts) (d : Nat) : List Json → List UInt8
  | [] => []
  | x :: xs => printWith o d x ++ printElems o d xs

/-- The members of a nonempty object, first one unprefixed. -/
def printFirstM (o : PrintOpts) (d : Nat) : List (String × Json) → List UInt8
  | [] => []
  | (k, v) :: kvs => printString o.ensureAscii k ++ o.colon ++ printWith o d v ++ printMembers o d kvs

theorem wsList_nil : WsList [] := by simp [WsList]

theorem at_ws_head {bs : ByteArray} {p : Nat} {ws l R : List UInt8} (h : At bs p (ws ++ l) R)
    (hw : WsList ws) {b : UInt8} {t : List UInt8} (e : l = b :: t) (hb : isWs b = false) :
    skipWs bs p bs.size = p + ws.length := by
  rw [e] at h; exact skipWs_at hw hb h

theorem numHead_facts {b : UInt8} (h : b = 45 ∨ ∃ d : Fin 10, b = digitByte d) :
    (b == 34) = false ∧ (b == 91) = false ∧ (b == 123) = false ∧ (b == 116) = false ∧
      (b == 102) = false ∧ (b == 110) = false ∧ (b == 45 || isDigit b) = true := by
  rcases h with rfl | ⟨d, rfl⟩
  · decide
  · revert d; decide

theorem printWith_arr_cons (o : PrintOpts) (d : Nat) (x : Json) (xs : List Json) :
    printWith o d (.arr (x :: xs)) = 91 :: (o.nl (d + 1) ++ (printFirst o (d + 1) (x :: xs) ++ o.nl d ++ [93])) := by
  simp [printWith, printFirst]

theorem printWith_obj_cons (o : PrintOpts) (d : Nat) (k : String) (v : Json) (kvs : List (String × Json)) :
    printWith o d (.obj ((k, v) :: kvs)) =
      123 :: (o.nl (d + 1) ++ (printFirstM o (d + 1) ((k, v) :: kvs) ++ o.nl d ++ [125])) := by
  simp [printWith, printFirstM]

theorem printFirst_head (o : PrintOpts) (d : Nat) (x : Json) (xs : List Json) :
    ∃ b t, printFirst o d (x :: xs) = b :: t ∧ ValueHead b := by
  obtain ⟨b, t, e, hb⟩ := printWith_head o d x
  exact ⟨b, t ++ printElems o d xs, by simp [printFirst, e], hb⟩

theorem printFirstM_head (o : PrintOpts) (d : Nat) (k : String) (v : Json) (kvs : List (String × Json)) :
    ∃ t, printFirstM o d ((k, v) :: kvs) = 34 :: t := by
  exact ⟨_, by simp [printFirstM, printString]; rfl⟩

mutual
theorem parseValue_ext (o : PrintOpts) (cfg : ParseCfg) : ∀ (v : Json) (d : Nat) {bs : ByteArray} {pos : Nat}
    {ws rest : List UInt8} (fuel : Nat), WsList ws → At bs pos (ws ++ printWith o d v) rest →
    NumStop rest → (printWith o d v).length < fuel → Spec.Fits cfg v →
    parseValueWith cfg bs pos fuel = .ok (v, pos + ws.length + (printWith o d v).length)
  | .null, d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    simp only [printWith, litNull] at hp ⊢
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((110 : UInt8) == 34) = false by decide, show ((110 : UInt8) == 91) = false by decide,
      show ((110 : UInt8) == 123) = false by decide, show ((110 : UInt8) == 116) = false by decide,
      show ((110 : UInt8) == 102) = false by decide, show ((110 : UInt8) == 110) = true by decide,
      Bool.false_eq_true, ↓reduceIte]
    rw [expectLit_ext _ _ hp.next]
    simp
  | .bool true, d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    simp only [printWith, litTrue] at hp ⊢
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((116 : UInt8) == 34) = false by decide, show ((116 : UInt8) == 91) = false by decide,
      show ((116 : UInt8) == 123) = false by decide, show ((116 : UInt8) == 116) = true by decide,
      Bool.false_eq_true, ↓reduceIte]
    rw [expectLit_ext _ _ hp.next]
    simp
  | .bool false, d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    simp only [printWith, litFalse] at hp ⊢
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((102 : UInt8) == 34) = false by decide, show ((102 : UInt8) == 91) = false by decide,
      show ((102 : UInt8) == 123) = false by decide, show ((102 : UInt8) == 116) = false by decide,
      show ((102 : UInt8) == 102) = true by decide, Bool.false_eq_true, ↓reduceIte]
    rw [expectLit_ext _ _ hp.next]
    simp
  | .num x, d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    obtain ⟨b, t, e, hb⟩ := printNumber_head x
    have hpw : printWith o d (.num x) = printNumber x := rfl
    rw [hpw] at h ⊢
    have hfacts := numHead_facts hb
    have hws : isWs b = false := by
      rcases hb with rfl | ⟨dd, rfl⟩
      · decide
      · exact (digitByte_ne dd).2.2.2.2.2
    have hsk := at_ws_head h hw e hws
    have hp := h.app
    unfold parseValueWith
    simp only [hsk]
    rw [show bs[pos + ws.length]? = some b by rw [e] at hp; exact hp.get]
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hfacts
    simp only [f1, f2, f3, f4, f5, f6, f7, Bool.false_eq_true, ↓reduceIte]
    rw [parseNumber_printNumber_ext cfg x hfit hp hr]
  | .str s, d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    have hpw : printWith o d (.str s) = printString o.ensureAscii s := rfl
    rw [hpw] at hp ⊢
    unfold parseValueWith
    simp only [hsk]
    rw [show bs[pos + ws.length]? = some 34 by unfold printString at hp; exact hp.get]
    simp only [show ((34 : UInt8) == 34) = true by decide, ↓reduceIte]
    rw [parseString_printString_ext _ s hp]
  | .arr [], d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    simp only [printWith] at hp ⊢
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((91 : UInt8) == 34) = false by decide, show ((91 : UInt8) == 91) = true by decide,
      Bool.false_eq_true, ↓reduceIte]
    rw [skipWs_nil (by decide) hp.next, hp.next.get]
    simp
  | .arr (x :: xs), d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    rw [printWith_arr_cons] at h hf ⊢
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((91 : UInt8) == 34) = false by decide, show ((91 : UInt8) == 91) = true by decide,
      Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b, t, e, hb⟩ := printFirst_head o (d + 1) x xs
    have hp1 := hp.next
    rw [List.append_assoc] at hp1
    have hq := at_ws_head hp1 (wsList_nl o (d + 1)) (by rw [e]; rfl) (valueHead_props hb).1
    rw [hq]
    have hp2 := hp1.app
    rw [show bs[pos + ws.length + 1 + (o.nl (d + 1)).length]? = some b by
      rw [e] at hp2; exact hp2.get]
    have hb93 := (valueHead_props hb).2.1
    split
    · rename_i heq; cases heq
    · rename_i heq; simp at heq; exact absurd heq hb93
    · simp only [List.length_cons, List.length_append] at hf
      rw [parseElems_ext o cfg (x :: xs) (d + 1) d n [] (by simp) (by simpa [List.append_assoc] using hp2) (by omega) hfit]
      simp only [List.reverse_nil, List.nil_append, List.length_cons, List.length_append]
      congr 2; omega
  | .obj [], d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    simp only [printWith] at hp ⊢
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((123 : UInt8) == 34) = false by decide, show ((123 : UInt8) == 91) = false by decide,
      show ((123 : UInt8) == 123) = true by decide, Bool.false_eq_true, ↓reduceIte]
    rw [skipWs_nil (by decide) hp.next, hp.next.get]
    simp
  | .obj ((k, v) :: kvs), d, bs, pos, ws, rest, fuel, hw, h, hr, hf, hfit => by
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    rw [printWith_obj_cons] at h hf ⊢
    have hsk := at_ws_head h hw rfl (by decide)
    have hp := h.app
    unfold parseValueWith
    simp only [hsk, hp.get]
    simp only [show ((123 : UInt8) == 34) = false by decide, show ((123 : UInt8) == 91) = false by decide,
      show ((123 : UInt8) == 123) = true by decide, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t, e⟩ := printFirstM_head o (d + 1) k v kvs
    have hp1 := hp.next
    rw [List.append_assoc] at hp1
    have hq := at_ws_head hp1 (wsList_nl o (d + 1)) (by rw [e]; rfl) (by decide)
    rw [hq]
    have hp2 := hp1.app
    rw [show bs[pos + ws.length + 1 + (o.nl (d + 1)).length]? = some 34 by
      rw [e] at hp2; exact hp2.get]
    simp only
    simp only [List.length_cons, List.length_append] at hf
    rw [parseMembers_ext o cfg ((k, v) :: kvs) (d + 1) d n [] (by simp) (by simpa [List.append_assoc] using hp2) (by omega) hfit]
    simp only [List.reverse_nil, List.nil_append, List.length_cons, List.length_append]
    congr 2; omega

theorem parseElems_ext (o : PrintOpts) (cfg : ParseCfg) : ∀ (xs : List Json) (d e : Nat) {bs : ByteArray} {pos : Nat}
    {rest : List UInt8} (fuel : Nat) (acc : List Json), xs ≠ [] →
    At bs pos (printFirst o d xs ++ o.nl e ++ [93]) rest → (printFirst o d xs).length + 1 < fuel →
    Spec.FitsList cfg xs →
    parseElems cfg bs pos fuel acc = .ok (.arr (acc.reverse ++ xs), pos + (printFirst o d xs ++ o.nl e ++ [93]).length)
  | [], _, _, _, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | x :: xs, d, e, bs, pos, rest, fuel, acc, _, h, hf, hfit => by
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    simp only [printFirst, List.length_append] at h hf ⊢
    unfold parseElems
    match xs with
    | [] =>
      simp only [printElems, List.append_nil] at h ⊢
      have hns : NumStop (o.nl e ++ [93] ++ rest) := by
        unfold PrintOpts.nl
        split
        · exact numStop_of_head (b := 93) (t := rest) rfl (by simp)
        · exact numStop_of_head (b := 10) rfl (by decide)
      have hx : At bs pos ([] ++ printWith o d x) (o.nl e ++ [93] ++ rest) := by
        simpa [List.append_assoc] using h.assoc.assoc
      rw [parseValue_ext o cfg x d m wsList_nil hx hns (by simp at hf; omega) hfit.1]
      simp only [List.length_nil, Nat.add_zero]
      have h1 : At bs (pos + (printWith o d x).length) (o.nl e ++ [93]) rest :=
        (by simpa [List.append_assoc] using h : At bs pos (printWith o d x ++ (o.nl e ++ [93])) rest).app
      rw [at_ws_head (ws := o.nl e) (by simpa using h1) (wsList_nl o e) rfl (by decide)]
      have h2 := h1.app
      rw [h2.get]
      simp
      omega
    | y :: ys =>
      simp only [printElems, List.cons_append, List.append_assoc] at h ⊢
      have hx : At bs pos ([] ++ printWith o d x)
          (44 :: (o.nl d ++ (printWith o d y ++ (printElems o d ys ++ (o.nl e ++ ([93] ++ rest)))))) := by
        simpa [List.append_assoc] using h.assoc
      rw [parseValue_ext o cfg x d m wsList_nil hx (numStop_of_head rfl (by simp)) (by simp at hf; omega) hfit.1]
      simp only [List.length_nil, Nat.add_zero]
      have h1 := h.app
      rw [skipWs_nil (by decide) h1, h1.get]
      simp only
      obtain ⟨b, t, eb, hb⟩ := printWith_head o d y
      have h2 := h1.next
      have hq := at_ws_head h2 (wsList_nl o d) (by rw [eb]; rfl) (valueHead_props hb).1
      rw [hq]
      have h3 := h2.app
      rw [show bs[pos + (printWith o d x).length + 1 + (o.nl d).length]? = some b by
        rw [eb] at h3; exact h3.get]
      have hb93 : (some b == some (93 : UInt8)) = false := by
        simpa using (valueHead_props hb).2.1
      simp only [hb93, Bool.false_eq_true, ↓reduceIte]
      have IH := parseElems_ext o cfg (y :: ys) d e (bs := bs) (pos := pos + (printWith o d x).length + 1 + (o.nl d).length)
        (rest := rest) m (x :: acc) (by simp)
        (by simpa [printFirst, List.append_assoc] using h3)
        (by
          have := List.length_pos_iff.mpr (printWith_ne_nil o d x)
          simp only [printElems, printFirst, List.length_append, List.length_cons] at hf ⊢; omega)
        hfit.2
      rw [IH]
      simp only [printFirst, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_append, List.length_cons]
      congr 2; omega

theorem parseMembers_ext (o : PrintOpts) (cfg : ParseCfg) : ∀ (kvs : List (String × Json)) (d e : Nat) {bs : ByteArray}
    {pos : Nat} {rest : List UInt8} (fuel : Nat) (acc : List (String × Json)), kvs ≠ [] →
    At bs pos (printFirstM o d kvs ++ o.nl e ++ [125]) rest → (printFirstM o d kvs).length + 1 < fuel →
    Spec.FitsFields cfg kvs →
    parseMembers cfg bs pos fuel acc =
      .ok (.obj (acc.reverse ++ kvs), pos + (printFirstM o d kvs ++ o.nl e ++ [125]).length)
  | [], _, _, _, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | (k, v) :: kvs, d, e, bs, pos, rest, fuel, acc, _, h, hf, hfit => by
    obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 1 :=
      ⟨fuel - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) hf)).symm⟩
    obtain ⟨cws, ecol, hcws⟩ := colon_eq o
    simp only [printFirstM, ecol, List.length_append, List.length_cons] at h hf ⊢
    unfold parseMembers
    have hk : At bs pos (printString o.ensureAscii k)
        (58 :: cws ++ printWith o d v ++ printMembers o d kvs ++ o.nl e ++ [125] ++ rest) := by
      unfold At at h ⊢; rw [h]; simp only [List.append_assoc, List.cons_append]
    rw [parseString_printString_ext _ k hk]
    simp only
    have h1 : At bs (pos + (printString o.ensureAscii k).length)
        (58 :: (cws ++ printWith o d v ++ printMembers o d kvs ++ o.nl e ++ [125])) rest :=
      At.drop (by simpa [List.append_assoc] using hk)
    rw [skipWs_nil (by decide) h1, h1.get]
    simp only
    have hlen := List.length_pos_iff.mpr (printWith_ne_nil o d v)
    match kvs with
    | [] =>
      simp only [printMembers, List.append_nil] at h1 hf ⊢
      have hns : NumStop (o.nl e ++ [125] ++ rest) := by
        unfold PrintOpts.nl
        split
        · exact numStop_of_head (b := 125) (t := rest) rfl (by simp)
        · exact numStop_of_head (b := 10) rfl (by decide)
      have hv : At bs (pos + (printString o.ensureAscii k).length + 1) (cws ++ printWith o d v)
          (o.nl e ++ [125] ++ rest) := h1.next.re rfl (by simp)
      rw [parseValue_ext o cfg v d m hcws hv hns (by omega) hfit.1]
      simp only
      have h2 : At bs (pos + (printString o.ensureAscii k).length + 1 + cws.length + (printWith o d v).length)
          (o.nl e ++ [125]) rest :=
        (At.drop (hv.re rfl (by simp) (l' := cws ++ printWith o d v))).re (by simp; omega) rfl
      rw [at_ws_head (ws := o.nl e) h2 (wsList_nl o e) rfl (by decide)]
      rw [h2.app.get]
      simp
      omega
    | (k', v') :: kvs' =>
      simp only [printMembers, List.cons_append, List.append_assoc] at h1 hf ⊢
      have hv : At bs (pos + (printString o.ensureAscii k).length + 1) (cws ++ printWith o d v)
          (44 :: (o.nl d ++ (printFirstM o d ((k', v') :: kvs') ++ (o.nl e ++ ([125] ++ rest))))) :=
        h1.next.re rfl (by simp [printFirstM, ecol])
      rw [parseValue_ext o cfg v d m hcws hv (numStop_of_head rfl (by simp)) (by omega) hfit.1]
      simp only
      have h2 : At bs (pos + (printString o.ensureAscii k).length + 1 + cws.length + (printWith o d v).length)
          (44 :: (o.nl d ++ printFirstM o d ((k', v') :: kvs') ++ o.nl e ++ [125])) rest :=
        (At.drop (hv.re rfl (by simp) (l' := cws ++ printWith o d v)
          (r' := (44 :: (o.nl d ++ printFirstM o d ((k', v') :: kvs') ++ o.nl e ++ [125])) ++ rest))).re
          (by simp; omega) rfl
      rw [skipWs_nil (by decide) h2, h2.get]
      simp only
      obtain ⟨t, et⟩ := printFirstM_head o d k' v' kvs'
      have h3 := h2.next
      have h3' : At bs (pos + (printString o.ensureAscii k).length + 1 + cws.length + (printWith o d v).length + 1)
          (o.nl d ++ (34 :: t ++ o.nl e ++ [125])) rest := h3.re rfl (by simp [et])
      rw [at_ws_head h3' (wsList_nl o d) rfl (by decide)]
      have h4 := h3'.app
      rw [h4.get]
      simp only
      have IH := parseMembers_ext o cfg ((k', v') :: kvs') d e (bs := bs) (rest := rest) m ((k, v) :: acc)
        (by simp) (h4.re rfl (by simp [et]))
        (by simp only [printFirstM, ecol, List.length_append, List.length_cons] at hf ⊢; omega)
        hfit.2
      rw [IH]
      simp only [printFirstM, ecol, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_append, List.length_cons, et]
      congr 2; simp; omega
end

end LeanJson
