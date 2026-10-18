import LeanJson.Proofs.Step

/-!
# Proofs: the value round trip

`valueGo_ext`: every value, printed with any options at any depth, is read
back by the nesting loop from any view that holds the printing followed by a
continuation that cannot extend a number, with the end just past it,
whenever the loop has more levels left than the value is high and the value
is within the configuration's limits.

One step at a time: `valueStep_ext` reads a value whose nested values its
child reads (`Reads`), using the string and number lemmas at the leaves;
`valueGo_ext` closes the loop by induction on the levels left.
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

theorem wsList_sep (o : PrintOpts) (d : Nat) : WsList (o.sep d) := by
  unfold PrintOpts.sep WsList
  split
  · split <;> simp; decide
  · intro b hb
    simp only [List.mem_cons, List.mem_replicate] at hb
    rcases hb with rfl | ⟨_, rfl⟩ <;> decide

theorem colon_eq (o : PrintOpts) : ∃ ws, o.colon = 58 :: ws ∧ WsList ws := by
  unfold PrintOpts.colon
  split
  · split
    · exact ⟨[32], rfl, by simp [WsList]; decide⟩
    · exact ⟨[], rfl, by simp [WsList]⟩
  · exact ⟨[32], rfl, by simp [WsList]; decide⟩

theorem skipWs_at {get : Nat → Option UInt8} {n : Nat} :
    ∀ {ws : List UInt8} {p : Nat} {b : UInt8} {t R : List UInt8}, WsList ws → isWs b = false →
      AtV get n p (ws ++ b :: t) R → skipWs get n p = p + ws.length
  | [], p, b, t, R, _, hb, h => by
    rw [skipWs]; simp [h.lt, h.get, hb]
  | w :: ws, p, b, t, R, hw, hb, h => by
    have hw1 : isWs w = true := hw w (by simp)
    simp only [List.cons_append] at h
    rw [skipWs]
    simp only [h.lt, h.get, hw1, ↓reduceIte]
    rw [skipWs_at (fun x hx => hw x (by simp [hx])) hb h.next]
    simp; omega

theorem skipWs_nil {get : Nat → Option UInt8} {n : Nat} {p : Nat} {b : UInt8} {t R : List UInt8}
    (hb : isWs b = false) (h : AtV get n p (b :: t) R) : skipWs get n p = p := by
  simpa using skipWs_at (ws := []) (by simp [WsList]) hb h

/-- The first byte of a printed number other than `NaN` and `Infinity` is `-`
or a digit. -/
theorem printNumber_head (n : Number) (h1 : n ≠ .nan) (h2 : n ≠ .inf) :
    ∃ b t, printNumber n = b :: t ∧ (b = 45 ∨ ∃ d : Fin 10, b = digitByte d) := by
  cases n with
  | nan => exact absurd rfl h1
  | inf => exact absurd rfl h2
  | negInf => exact ⟨_, _, rfl, Or.inl rfl⟩
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

theorem or_left_of_and {A B C : Prop} (h : A ∨ (B ∧ C)) : A ∨ B := h.imp id And.left
theorem or_right_of_and {A B C : Prop} (h : A ∨ (B ∧ C)) : A ∨ C := h.imp id And.right

/-- What a printed value can start with. -/
def ValueHead (b : UInt8) : Prop :=
  b = 110 ∨ b = 116 ∨ b = 102 ∨ b = 34 ∨ b = 91 ∨ b = 123 ∨ b = 78 ∨ b = 73 ∨ b = 45 ∨
    ∃ d : Fin 10, b = digitByte d

theorem valueHead_props {b : UInt8} (h : ValueHead b) :
    isWs b = false ∧ b ≠ 93 ∧ b ≠ 125 ∧ b ≠ 44 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨d, rfl⟩
  all_goals first | decide | (revert d; decide)

theorem printNumberIn_head (o : PrintOpts) (n : Number) :
    ∃ b t, printNumberIn o n = b :: t ∧ ValueHead b := by
  unfold printNumberIn
  have fin : ∀ (h1 : n ≠ .nan) (h2 : n ≠ .inf), ∃ b t, printNumber n = b :: t ∧ ValueHead b := by
    intro h1 h2
    obtain ⟨b, t, e, h⟩ := printNumber_head n h1 h2
    refine ⟨b, t, e, ?_⟩
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
  split
  · rename_i hf
    exact fin (by rintro rfl; simp [Number.isFinite] at hf) (by rintro rfl; simp [Number.isFinite] at hf)
  · split
    · cases n with
      | nan => exact ⟨_, _, rfl, by simp [ValueHead]⟩
      | inf => exact ⟨_, _, rfl, by simp [ValueHead]⟩
      | _ => exact fin (by simp) (by simp)
    · exact ⟨_, _, rfl, by simp [ValueHead]⟩
    · exact ⟨_, _, rfl, by simp [ValueHead]⟩

theorem printWith_head (o : PrintOpts) (d : Nat) (v : Json) :
    ∃ b t, printWith o d v = b :: t ∧ ValueHead b := by
  cases v with
  | null => exact ⟨_, _, rfl, Or.inl rfl⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, by simp [ValueHead]⟩
  | num n => exact printNumberIn_head o n
  | str s => exact ⟨_, _, rfl, by simp [ValueHead]⟩
  | arr xs => rcases xs with ⟨_ | _⟩ <;> exact ⟨_, _, rfl, by simp [ValueHead]⟩
  | obj kvs =>
    match kvs with
    | ⟨[]⟩ => exact ⟨_, _, rfl, by simp [ValueHead]⟩
    | ⟨(_, _) :: _⟩ => exact ⟨_, _, rfl, by simp [ValueHead]⟩

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

theorem numHead_facts {b : UInt8} (h : b = 45 ∨ ∃ d : Fin 10, b = digitByte d) :
    (b == 34) = false ∧ (b == 91) = false ∧ (b == 123) = false ∧ (b == 116) = false ∧
      (b == 102) = false ∧ (b == 110) = false ∧ (b == 45 || isDigit b) = true := by
  rcases h with rfl | ⟨d, rfl⟩
  · decide
  · revert d; decide

theorem printWith_arr_cons (o : PrintOpts) (d : Nat) (x : Json) (xs : List Json) :
    printWith o d (.arr ⟨x :: xs⟩) = 91 :: (o.nl (d + 1) ++ (printFirst o (d + 1) (x :: xs) ++ o.nl d ++ [93])) := by
  simp [printWith, printFirst]

theorem printWith_obj_cons (o : PrintOpts) (d : Nat) (k : String) (v : Json) (kvs : List (String × Json)) :
    printWith o d (.obj ⟨(k, v) :: kvs⟩) =
      123 :: (o.nl (d + 1) ++ (printFirstM o (d + 1) ((k, v) :: kvs) ++ o.nl d ++ [125])) := by
  simp [printWith, printFirstM]

theorem printFirst_head (o : PrintOpts) (d : Nat) (x : Json) (xs : List Json) :
    ∃ b t, printFirst o d (x :: xs) = b :: t ∧ ValueHead b := by
  obtain ⟨b, t, e, hb⟩ := printWith_head o d x
  exact ⟨b, t ++ printElems o d xs, by simp [printFirst, e], hb⟩

theorem printFirstM_head (o : PrintOpts) (d : Nat) (k : String) (v : Json) (kvs : List (String × Json)) :
    ∃ t, printFirstM o d ((k, v) :: kvs) = 34 :: t := by
  exact ⟨_, by simp [printFirstM, printString]; rfl⟩


section
variable {get : Nat → Option UInt8} {n : Nat}

/-- `c` reads `w`, printed at depth `d`, wherever it is printed past the
view's first byte and followed by a continuation that cannot extend a
number. -/
def Reads (o : PrintOpts) (d : Nat) (get : Nat → Option UInt8) (n : Nat) (c : Child) (w : Json) : Prop :=
  ∀ j R, 0 < j → AtV get n j (printWith o d w) R → NumStop R → c j = .ok (w, j + (printWith o d w).length)

theorem numStop_close (o : PrintOpts) (e : Nat) (b : UInt8) (hb : b = 93 ∨ b = 125) (rest : List UInt8) :
    NumStop (o.nl e ++ b :: rest) := by
  unfold PrintOpts.nl
  split
  · exact numStop_of_head rfl (by rcases hb with rfl | rfl <;> simp)
  · exact numStop_of_head rfl (by decide)

theorem parseElems_ext (o : PrintOpts) {c : Child} {d e : Nat} {rest : List UInt8} :
    ∀ (xs : List Json) (pos : Nat) (acc : Array Json), 0 < pos → xs ≠ [] → (∀ x ∈ xs, Reads o d get n c x) →
    AtV get n pos (printFirst o d xs ++ o.nl e ++ [93]) rest →
    parseElems c get n pos acc = .ok (.arr ⟨acc.toList ++ xs⟩, pos + (printFirst o d xs ++ o.nl e ++ [93]).length)
  | [], _, _, _, hne, _, _ => absurd rfl hne
  | [x], pos, acc, h0, _, hc, h => by
    simp only [printFirst, printElems, List.append_nil] at h ⊢
    have hx : AtV get n pos (printWith o d x) (o.nl e ++ 93 :: rest) := h.re rfl (by simp)
    rw [parseElems, hc x (by simp) pos _ h0 hx (numStop_close o e 93 (by simp) rest)]
    have h1 : AtV get n (pos + (printWith o d x).length) (o.nl e ++ [93]) rest := (h.re rfl (by simp)).app
    simp only
    rw [skipWs_at (b := 93) (t := []) (wsList_nl o e) (by decide) h1, h1.app.get]
    simp only [List.length_append, List.length_cons, List.length_nil, Except.ok.injEq, Prod.mk.injEq]
    exact ⟨by cases acc; simp, by omega⟩
  | x :: y :: ys, pos, acc, h0, _, hc, h => by
    simp only [printFirst, printElems, List.append_assoc, List.cons_append] at h ⊢
    have hx : AtV get n pos (printWith o d x)
        (44 :: (o.sep d ++ (printWith o d y ++ (printElems o d ys ++ (o.nl e ++ ([93] ++ rest)))))) :=
      h.re rfl (by simp)
    rw [parseElems, hc x (by simp) pos _ h0 hx (numStop_of_head rfl (by simp))]
    simp only
    have h2 := h.app
    rw [skipWs_nil (by decide) h2, h2.get]
    simp only
    obtain ⟨b, t, eb, hb⟩ := printWith_head o d y
    have h3 := h2.next
    rw [eb] at h3
    rw [skipWs_at (wsList_sep o d) (valueHead_props hb).1 h3]
    have h4 := h3.app
    have hq := h4.get
    split
    · rename_i hq'; rw [hq] at hq'; cases hq'; exact absurd rfl (valueHead_props hb).2.1
    · rw [dite_eq_left ⟨by omega, h4.lt⟩]
      rw [← eb] at h4
      rw [parseElems_ext o (y :: ys) _ (acc.push x) (by omega) (by simp) (fun z hz => hc z (by simp_all))
        (by simpa [printFirst, List.append_assoc] using h4)]
      simp only [printFirst, Array.toList_push, List.append_assoc, List.singleton_append,
        List.length_append, List.length_cons, Except.ok.injEq, Prod.mk.injEq]
      exact ⟨trivial, by omega⟩
    · rename_i hq'; rw [hq] at hq'; cases hq'

theorem parseMembers_ext (o : PrintOpts) {c : Child} {dedup : Bool} {d e : Nat} {rest : List UInt8} :
    ∀ (kvs : List (String × Json)) (pos : Nat) (acc : Fields), kvs ≠ [] →
    (∀ kv ∈ kvs, Reads o d get n c kv.2) → AtV get n pos (printFirstM o d kvs ++ o.nl e ++ [125]) rest →
    acc.Indexed → (dedup = true → (acc.1.toList.map Prod.fst ++ kvs.map Prod.fst).Nodup) →
    parseMembers dedup c get n pos acc =
      .ok (.obj ⟨acc.1.toList ++ kvs⟩, pos + (printFirstM o d kvs ++ o.nl e ++ [125]).length)
  | [], _, _, hne, _, _, _, _ => absurd rfl hne
  | (key, v) :: kvs, pos, acc, _, hc, h, hidx, hnd => by
    have hfresh : dedup = true → key ∉ acc.1.toList.map Prod.fst := fun hd hm => by
      have := hnd hd
      simp only [List.map_cons] at this
      exact (List.nodup_append.mp this).2.2 key hm key (by simp) rfl
    obtain ⟨hadd, hidx'⟩ := Fields.add_fresh (v := v) hidx hfresh
    obtain ⟨cws, ecol, hcws⟩ := colon_eq o
    obtain ⟨b, t, eb, hb⟩ := printWith_head o d v
    simp only [printFirstM, ecol, List.append_assoc, List.cons_append] at h ⊢
    rw [parseMembers, parseString_printString_ext _ key h.assoc]
    simp only
    have h1 := h.app
    rw [skipWs_nil (by decide) h1, h1.get]
    simp only
    have h2 := h1.next
    rw [eb] at h2
    rw [skipWs_at hcws (valueHead_props hb).1 h2]
    have h3 := h2.app
    rw [h3.get]
    simp only
    rw [← eb] at h3
    have hv := hc (key, v) (by simp)
    match kvs with
    | [] =>
      simp only [printMembers, List.nil_append] at h3 ⊢
      rw [hv _ _ (by omega) h3.assoc (by simpa using numStop_close o e 125 (by simp) rest)]
      simp only
      have h4 := h3.app
      rw [skipWs_at (b := 125) (t := []) (wsList_nl o e) (by decide) h4, h4.app.get, hadd]
      simp only [List.length_append, List.length_cons, List.length_nil, Except.ok.injEq, Prod.mk.injEq]
      exact ⟨by rcases acc with ⟨⟨_⟩, _⟩; simp, by omega⟩
    | (k', v') :: kvs' =>
      simp only [printMembers, List.cons_append, List.append_assoc] at h3 ⊢
      rw [hv _ _ (by omega) h3.assoc (numStop_of_head rfl (by simp))]
      simp only
      have h4 := h3.app
      rw [skipWs_nil (by decide) h4, h4.get]
      simp only
      have h5 := h4.next
      obtain ⟨ts, ets⟩ : ∃ ts, printString o.ensureAscii k' = 34 :: ts := ⟨_, by simp [printString]; rfl⟩
      rw [ets] at h5
      rw [skipWs_at (wsList_sep o d) (by decide) h5]
      have h6 := h5.app
      rw [h6.get]
      simp only
      rw [dite_eq_left ⟨by omega, h6.lt⟩]
      rw [← ets] at h6
      have IH := parseMembers_ext o (c := c) (dedup := dedup) (d := d) (e := e) (rest := rest) ((k', v') :: kvs') _ (acc.add dedup key v) (by simp)
        (fun kv hkv => hc kv (by simp_all)) (h6.re rfl (by simp [printFirstM, ecol])) hidx'
        (fun hd => by rw [hadd]; simpa using hnd hd)
      rw [IH, hadd]
      simp only [printFirstM, ecol, Array.toList_push, List.append_assoc, List.singleton_append,
        List.length_append, List.length_cons, Except.ok.injEq, Prod.mk.injEq]
      exact ⟨trivial, by omega⟩

/-- The values nested one level in `v` satisfy `P`. -/
def Kids (P : Json → Prop) : Json → Prop
  | .arr ⟨xs⟩ => ∀ x ∈ xs, P x
  | .obj ⟨kvs⟩ => ∀ kv ∈ kvs, P kv.2
  | _ => True

theorem valueStep_lit {c : Child} {cfg : ParseCfg} {b : UInt8} {l rest : List UInt8} {w : Json}
    (h : AtV get n 0 (b :: l) rest)
    (hs : valueStep cfg c get n = (expectLit get 1 l).map (fun p => (w, p))) :
    valueStep cfg c get n = .ok (w, (b :: l).length) := by
  rw [hs, expectLit_ext l 1 h.next]; simp [Except.map, Nat.add_comm]

/-- **One step reads a printed value**, given a child that reads the values
nested in it: on any view holding the printing at `0` followed by a
continuation that cannot extend a number, for any value within `cfg`'s
limits whose printing reads back. -/
theorem valueStep_ext (o : PrintOpts) (cfg : ParseCfg) {c : Child} (v : Json) (d k : Nat) {rest : List UInt8}
    (h : AtV get n 0 (printWith o d v) rest) (hr : NumStop rest) (hfit : FitsAt cfg k v)
    (hrb : ReadsBack o v) (hc : Kids (Reads o (d + 1) get n c) v) :
    valueStep cfg c get n = .ok (v, (printWith o d v).length) := by
  match v with
  | .null =>
    simp only [printWith, litNull] at h ⊢
    exact valueStep_lit h (by unfold valueStep; rw [h.get]; rfl)
  | .bool true =>
    simp only [printWith, litTrue] at h ⊢
    exact valueStep_lit h (by unfold valueStep; rw [h.get]; rfl)
  | .bool false =>
    simp only [printWith, litFalse] at h ⊢
    exact valueStep_lit h (by unfold valueStep; rw [h.get]; rfl)
  | .str s =>
    have hp : printWith o d (.str s) = printString o.ensureAscii s := rfl
    rw [hp] at h ⊢
    unfold valueStep
    rw [show get 0 = some 34 by unfold printString at h; exact h.get]
    simp only [show ((34 : UInt8) == 34) = true by decide, ↓reduceIte]
    rw [parseString_printString_ext _ s h]
    simp [Except.map]
  | .num x =>
    have hallow : x.isFinite = false → cfg.allowInfNan = true := by
      intro hx; rcases hfit.2.2 with h' | h'
      · exact h'
      · rw [hx] at h'; cases h'
    have hconst : x.isFinite = false → o.infNan = .constants := by
      intro hx; rcases hrb with h' | h'
      · exact h'
      · simp [Json.allFinite, hx] at h'
    have hpw : printWith o d (.num x) = printNumberIn o x := rfl
    rw [hpw] at h ⊢
    by_cases hnan : x = .nan
    · subst hnan
      have hpn : printNumberIn o .nan = litNaN := by
        simp [printNumberIn, Number.isFinite, hconst rfl, printNumber]
      rw [hpn] at h ⊢
      simp only [litNaN] at h ⊢
      exact valueStep_lit h (by unfold valueStep; rw [h.get]; simp [hallow rfl, isDigit])
    by_cases hinf : x = .inf
    · subst hinf
      have hpn : printNumberIn o .inf = litInfinity := by
        simp [printNumberIn, Number.isFinite, hconst rfl, printNumber]
      rw [hpn] at h ⊢
      simp only [litInfinity] at h ⊢
      exact valueStep_lit h (by unfold valueStep; rw [h.get]; simp [hallow rfl, isDigit])
    have hpn : printNumberIn o x = printNumber x := by
      unfold printNumberIn
      split
      · rfl
      · rename_i hf; rw [hconst (by simpa using hf)]
    rw [hpn] at h ⊢
    obtain ⟨b, t, e, hb⟩ := printNumber_head x hnan hinf
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := numHead_facts hb
    unfold valueStep
    rw [show get 0 = some b by rw [e] at h; exact h.get]
    simp only [f1, f2, f3, f4, f5, f6, f7, Bool.false_eq_true, ↓reduceIte]
    have hfin : x.isFinite = true ∨ (x = .negInf ∧ cfg.allowInfNan = true) := by
      cases hx : x.isFinite
      · right; refine ⟨?_, hallow hx⟩
        cases x <;> simp_all [Number.isFinite]
      · left; rfl
    rw [parseNumber_printNumber_ext cfg x hfit.2.1 hfin h hr]
    simp [Json.ofNumber_eq, Except.map]
  | .arr ⟨[]⟩ =>
    simp only [printWith] at h ⊢
    unfold valueStep
    rw [h.get]
    simp only [show ((91 : UInt8) == 34) = false by decide, show ((91 : UInt8) == 91) = true by decide,
      Bool.false_eq_true, ↓reduceIte]
    rw [skipWs_nil (by decide) h.next, h.next.get]
    rfl
  | .arr ⟨x :: xs⟩ =>
    rw [printWith_arr_cons] at h ⊢
    unfold valueStep
    rw [h.get]
    simp only [show ((91 : UInt8) == 34) = false by decide, show ((91 : UInt8) == 91) = true by decide,
      Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b, t, e, hb⟩ := printFirst_head o (d + 1) x xs
    have h1 := h.next
    rw [e] at h1
    rw [skipWs_at (wsList_nl o (d + 1)) (valueHead_props hb).1 h1]
    have h2 := h1.app
    split
    · rename_i hq; rw [h2.get] at hq; cases hq; exact absurd rfl (valueHead_props hb).2.1
    · rw [← e] at h2
      rw [parseElems_ext o (e := d) (rest := rest) (x :: xs) _ #[] (by omega) (by simp) hc h2]
      simp only [List.length_cons, List.length_append, Except.ok.injEq, Prod.mk.injEq]
      exact ⟨by simp, by omega⟩
    · rename_i hq; rw [h2.get] at hq; cases hq
  | .obj ⟨[]⟩ =>
    simp only [printWith] at h ⊢
    unfold valueStep
    rw [h.get]
    simp only [show ((123 : UInt8) == 34) = false by decide, show ((123 : UInt8) == 91) = false by decide,
      show ((123 : UInt8) == 123) = true by decide, Bool.false_eq_true, ↓reduceIte]
    rw [skipWs_nil (by decide) h.next, h.next.get]
    rfl
  | .obj ⟨(key, w) :: kvs⟩ =>
    rw [printWith_obj_cons] at h ⊢
    unfold valueStep
    rw [h.get]
    simp only [show ((123 : UInt8) == 34) = false by decide, show ((123 : UInt8) == 91) = false by decide,
      show ((123 : UInt8) == 123) = true by decide, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨t, e⟩ := printFirstM_head o (d + 1) key w kvs
    have h1 := h.next
    rw [e] at h1
    rw [skipWs_at (wsList_nl o (d + 1)) (by decide) h1]
    have h2 := h1.app
    rw [h2.get]
    simp only
    rw [← e] at h2
    rw [parseMembers_ext o (e := d) (rest := rest) ((key, w) :: kvs) _ .empty (by simp) hc h2
      Fields.indexed_empty (by simpa [Fields.empty] using hfit.2.1)]
    simp only [Fields.empty, List.nil_append, List.length_cons, List.length_append, Except.ok.injEq,
      Prod.mk.injEq]
    exact ⟨by simp, by omega⟩
end

/-! ## Closing the loop -/

open Spec in
theorem fitsList_mem {cfg : ParseCfg} {k : Nat} : ∀ {xs : List Json} {x : Json}, FitsList cfg k xs → x ∈ xs →
    FitsAt cfg k x
  | _ :: _, _, h, .head _ => h.1
  | _ :: _, _, h, .tail _ hx => fitsList_mem h.2 hx

open Spec in
theorem fitsFields_mem {cfg : ParseCfg} {k : Nat} : ∀ {kvs : List (String × Json)} {kv : String × Json},
    FitsFields cfg k kvs → kv ∈ kvs → FitsAt cfg k kv.2
  | (_, _) :: _, _, h, .head _ => h.1
  | (_, _) :: _, _, h, .tail _ hx => fitsFields_mem h.2 hx

theorem allFiniteList_mem : ∀ {xs : List Json} {x : Json}, Json.allFiniteList xs = true → x ∈ xs →
    x.allFinite = true
  | _ :: _, _, h, .head _ => by simp [Json.allFiniteList] at h; exact h.1
  | _ :: _, _, h, .tail _ hx => by simp [Json.allFiniteList] at h; exact allFiniteList_mem h.2 hx

theorem allFiniteFields_mem : ∀ {kvs : List (String × Json)} {kv : String × Json},
    Json.allFiniteFields kvs = true → kv ∈ kvs → kv.2.allFinite = true
  | (_, _) :: _, _, h, .head _ => by simp [Json.allFiniteFields] at h; exact h.1
  | (_, _) :: _, _, h, .tail _ hx => by simp [Json.allFiniteFields] at h; exact allFiniteFields_mem h.2 hx

theorem height_le_list {x : Json} {xs : List Json} (h : x ∈ xs) : x.height ≤ Json.heightList xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [Json.heightList]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem height_le_fields {kv : String × Json} {kvs : List (String × Json)} (h : kv ∈ kvs) :
    kv.2.height ≤ Json.heightFields kvs := by
  induction kvs with
  | nil => cases h
  | cons y ys ih =>
    obtain ⟨k, v⟩ := y
    simp only [Json.heightFields]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem height_lt_arr {x : Json} {xs : List Json} (h : x ∈ xs) : x.height < (Json.arr ⟨xs⟩).height := by
  match xs, h with
  | y :: ys, h =>
    have := height_le_list h
    simp only [Json.height, Json.heightList] at this ⊢; omega

theorem height_lt_obj {kv : String × Json} {kvs : List (String × Json)} (h : kv ∈ kvs) :
    kv.2.height < (Json.obj ⟨kvs⟩).height := by
  match kvs, h with
  | (k, w) :: ys, h =>
    have := height_le_fields h
    simp only [Json.height, Json.heightFields] at this ⊢; omega

/-- **The value round trip**, for the nesting loop at `base` with `D` levels
left: every value higher than `D` reads back, whatever the options and
depth it was printed at, on any continuation that cannot extend a number,
when it is within `cfg`'s limits and its printing reads back. -/
theorem valueGo_ext (o : PrintOpts) (cfg : ParseCfg) {get : Nat → Option UInt8} {n : Nat} :
    ∀ (D : Nat) (v : Json) (d k base : Nat) {rest : List UInt8}, AtV get n base (printWith o d v) rest →
      NumStop rest → FitsAt cfg k v → ReadsBack o v → v.height < D →
      valueGo cfg get n D base = .ok (v, (printWith o d v).length)
  | 0, _, _, _, _, _, _, _, _, _, hD => absurd hD (Nat.not_lt_zero _)
  | D + 1, v, d, k, base, rest, h, hr, hfit, hrb, hD => by
    have hb : base ≤ n := by have := h.len; omega
    unfold valueGo
    refine valueStep_ext o cfg v d k (h.re (Nat.add_zero base).symm rfl).shift hr hfit hrb ?_
    have kid : ∀ {w : Json}, FitsAt cfg (k + 1) w → ReadsBack o w → w.height < D →
        Reads o (d + 1) (fun i => get (base + i)) (n - base)
          (fun j => shiftRes j (valueGo cfg get n D (base + j))) w := by
      intro w hf hw hh j R _ hj hR
      dsimp only
      rw [valueGo_ext o cfg D w (d + 1) (k + 1) (base + j) (hj.unshift hb) hR hf hw hh]
      simp [shiftRes, Nat.add_comm]
    match v, hfit, hrb with
    | .arr ⟨xs⟩, hfit, hrb =>
      exact fun x hx => kid (fitsList_mem hfit.2 hx)
        (hrb.imp id fun h => allFiniteList_mem h hx) (by have := height_lt_arr hx; omega)
    | .obj ⟨kvs⟩, hfit, hrb =>
      exact fun kv hkv => kid (fitsFields_mem hfit.2.2 hkv)
        (hrb.imp id fun h => allFiniteFields_mem h hkv) (by have := height_lt_obj hkv; omega)
    | .null, _, _ | .bool _, _, _ | .num _, _, _ | .str _, _, _ => trivial

end LeanJson
