import LeanJson.Proofs.Digits

/-!
# Proofs: the number codec

`parseNumber_printNumber_ext`: every `Number` round-trips through
`printNumber`/`parseNumber` on any continuation that cannot extend it.
The proof goes through one shape lemma (`parseNumber_shape`): sign, integer
digits, optional fraction, optional exponent; each of ryu's five layouts is
an instance of the shape.
-/

namespace LeanJson

open Spec

/-- A valid integer part: nonempty decimal digits, no leading zero unless it
is the single digit `0`. -/
def IntDigits (ds : List Nat) : Prop :=
  ds ≠ [] ∧ (∀ d ∈ ds, d < 10) ∧ (ds.head? = some 0 → ds = [0])

/-- A nonempty run of decimal digits. -/
def Digits1 (ds : List Nat) : Prop := ds ≠ [] ∧ ∀ d ∈ ds, d < 10

theorem fuel_of_at {bs : ByteArray} {pos : Nat} {l rest : List UInt8} (h : At bs pos l rest) :
    l.length ≤ bs.size := by
  by_cases hl : l = []
  · subst hl; simp
  · have := h.le_size hl; omega

theorem digits1_ext {bs : ByteArray} {pos : Nat} {ds : List Nat} {rest : List UInt8}
    (hd : Digits1 ds) (h : At bs pos (ds.map digitByte) rest) (hr : DigitStop rest) :
    digits1 bs pos = .ok (ofDigits ds, ds.length, pos + ds.length) := by
  unfold digits1
  rw [scanDigits_ext bs rest hr ds pos 0 hd.2 h]
  have : ds.length ≠ 0 := by simpa using hd.1
  simp only [Nat.zero_add, this, ↓reduceIte]
  rw [digitsValue_ext ds pos hd.2 h]

theorem parseIntPart_ext {bs : ByteArray} {pos : Nat} {ds : List Nat} {rest : List UInt8}
    (hd : IntDigits ds) (h : At bs pos (ds.map digitByte) rest) (hr : DigitStop rest) :
    parseIntPart bs pos = .ok (ofDigits ds, pos + ds.length) := by
  obtain ⟨hne, h10, h0⟩ := hd
  match ds, hne, h10, h0, h with
  | d :: t, _, h10, h0, h =>
    have hd10 : d < 10 := h10 d (by simp)
    unfold parseIntPart
    rw [At.get h]
    by_cases hz : d = 0
    · subst hz
      have ht : t = [] := by simpa using h0 rfl
      subst ht
      have h' := At.nil (At.next h)
      have : (digitByte 0 == 48) = true := by decide
      simp only [this, ↓reduceIte, h']
      cases hh : rest.head? with
      | none => simp [ofDigits]
      | some c => simp [hr c hh, ofDigits]
    · have hne48 : (digitByte d == 48) = false := by
        have : digitByte d ≠ 48 := fun e => hz ((digitByte_zero_iff ⟨d, hd10⟩).mp e)
        simpa using this
      simp only [hne48, Bool.false_eq_true, ↓reduceIte, digitByte_isDigit ⟨d, hd10⟩]
      rw [scanDigits_ext bs rest hr (d :: t) pos 0 h10 h]
      simp only [Nat.zero_add]
      rw [digitsValue_ext (d :: t) pos h10 h]

/-- The bytes of an optional fraction. -/
def fracBytes : Option (List Nat) → List UInt8
  | none => []
  | some fs => 46 :: fs.map digitByte

/-- The bytes of an optional exponent. -/
def expBytes : Option Int → List UInt8
  | none => []
  | some i => 101 :: printExp i

theorem printNat_eq (n : Nat) : printNat n = (natDigits n).map digitByte := rfl

theorem natDigits_digits1 (n : Nat) : Digits1 (natDigits n) :=
  ⟨natDigits_ne_nil n, fun _ h => natDigits_lt10 h⟩

theorem natDigits_intDigits (n : Nat) : IntDigits (natDigits n) := by
  obtain ⟨_, h2, h, t, e, h4, h5⟩ := natDigits_spec n
  refine ⟨natDigits_ne_nil n, h2, ?_⟩
  rw [e]; intro hh; simp at hh; subst hh; rw [h5 rfl]

theorem parseFrac_none {bs : ByteArray} {pos : Nat} {rest : List UInt8}
    (h : At bs pos [] rest) (hr : rest.head? ≠ some 46) : parseFrac bs pos = .ok (0, 0, pos) := by
  unfold parseFrac
  rw [At.nil h]
  cases hh : rest.head? with
  | none => rfl
  | some b =>
    rw [hh] at hr
    have : b ≠ 46 := fun e => hr (by rw [e])
    split
    · rename_i heq; simp at heq; exact absurd heq this
    · rfl

theorem parseFrac_some {bs : ByteArray} {pos : Nat} {fs : List Nat} {rest : List UInt8}
    (hd : Digits1 fs) (h : At bs pos (fracBytes (some fs)) rest) (hr : DigitStop rest) :
    parseFrac bs pos = .ok (ofDigits fs, fs.length, pos + 1 + fs.length) := by
  unfold parseFrac
  simp only [fracBytes] at h
  rw [At.get h]
  exact digits1_ext hd (At.next h) hr

theorem parseExp_none {bs : ByteArray} {pos : Nat} {rest : List UInt8}
    (h : At bs pos [] rest) (hr : NumStop rest) : parseExp bs pos = .ok (false, 0, pos) := by
  unfold parseExp
  rw [At.nil h]
  cases hh : rest.head? with
  | none => rfl
  | some b =>
    obtain ⟨_, _, h1, h2⟩ := hr b hh
    simp [h1, h2]

theorem printInt_length (i : Int) :
    (printInt i).length = (if i < 0 then 1 else 0) + (natDigits i.natAbs).length := by
  unfold printInt printNat
  by_cases h : i < 0
  · simp [h]; omega
  · simp [h]
    have : i.toNat = i.natAbs := by omega
    rw [this]

theorem printExp_length (i : Int) : (printExp i).length = 1 + (natDigits i.natAbs).length := by
  unfold printExp printNat
  by_cases h : i < 0
  · simp [h]; omega
  · simp [h]
    have : i.toNat = i.natAbs := by omega
    rw [this]; omega

theorem parseExp_some {bs : ByteArray} {pos : Nat} {i : Int} {rest : List UInt8}
    (h : At bs pos (expBytes (some i)) rest) (hr : DigitStop rest) :
    parseExp bs pos = .ok (true, i, pos + (expBytes (some i)).length) := by
  unfold parseExp
  simp only [expBytes] at h
  rw [At.get h]
  simp only [show ((101 : UInt8) == 101 || (101 : UInt8) == 69) = true by decide, ↓reduceIte]
  have h1 := At.next h
  unfold printExp at h1
  by_cases hneg : i < 0
  · simp only [hneg, ↓reduceIte] at h1
    rw [At.get h1]
    simp only
    rw [digits1_ext (natDigits_digits1 _) (At.next h1) hr]
    simp only [bind, Except.bind, expBytes, List.length_cons, printExp_length, ofDigits_natDigits]
    rw [show -(i.natAbs : Int) = i by omega]
    congr 3; omega
  · simp only [hneg, ↓reduceIte] at h1
    have hnn : i.toNat = i.natAbs := by omega
    rw [hnn] at h1
    rw [At.get h1]
    simp only
    rw [printNat_eq] at h1
    rw [digits1_ext (natDigits_digits1 _) (At.next h1) hr]
    simp only [bind, Except.bind, expBytes, List.length_cons, printExp_length, ofDigits_natDigits]
    rw [show (i.natAbs : Int) = i by omega]
    congr 3; omega

theorem digitStop_frac_exp (fp : Option (List Nat)) (ex : Option Int) (rest : List UInt8)
    (hr : NumStop rest) : DigitStop (fracBytes fp ++ expBytes ex ++ rest) := by
  intro b hb
  cases fp with
  | some fs => simp [fracBytes] at hb; subst hb; decide
  | none =>
    cases ex with
    | some i => simp [fracBytes, expBytes] at hb; subst hb; decide
    | none => simp [fracBytes, expBytes] at hb; exact (hr b hb).1

theorem digitStop_exp (ex : Option Int) (rest : List UInt8)
    (hr : NumStop rest) : DigitStop (expBytes ex ++ rest) := by
  have := digitStop_frac_exp none ex rest hr
  simpa [fracBytes] using this

theorem expBytes_head (ex : Option Int) (rest : List UInt8) (hr : NumStop rest) :
    (expBytes ex ++ rest).head? ≠ some 46 := by
  cases ex with
  | some i => simp [expBytes]
  | none =>
    simp only [expBytes, List.nil_append]
    intro h; exact (hr 46 h).2.1 rfl

theorem digitByte_ne_73 : ∀ d : Fin 10, digitByte d.val ≠ 73 := by decide

/-- The shape every printed number has: optional `-`, integer digits,
optional fraction, optional exponent. -/
theorem parseNumber_shape (cfg : ParseCfg) {bs : ByteArray} {pos : Nat} (sneg : Bool) (ip : List Nat)
    (fp : Option (List Nat)) (ex : Option Int) {rest : List UInt8}
    (hip : IntDigits ip) (hfp : ∀ fs, fp = some fs → Digits1 fs)
    (hlen : cfg.intLenOk ((if sneg then 1 else 0) + ip.length) = true)
    (h : At bs pos ((if sneg then [45] else []) ++ ip.map digitByte ++ fracBytes fp ++ expBytes ex) rest)
    (hr : NumStop rest) :
    parseNumber cfg bs pos = .ok (mkNumber sneg (ofDigits ip) ((fp.map ofDigits).getD 0)
      ((fp.map List.length).getD 0) ex.isSome (ex.getD 0),
      pos + ((if sneg then [45] else []) ++ ip.map digitByte ++ fracBytes fp ++ expBytes ex).length) := by
  have hneg : (bs[pos]? == some 45) = sneg := by
    cases sneg
    · obtain ⟨d, t, e⟩ : ∃ d t, ip = d :: t := by
        cases ip with
        | nil => exact absurd rfl hip.1
        | cons d t => exact ⟨d, t, rfl⟩
      have hd10 : d < 10 := hip.2.1 d (by simp [e])
      subst e
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.map_cons, List.cons_append] at h
      rw [At.get h]
      have := (digitByte_ne ⟨d, hd10⟩).2.2.2.1
      simpa using this
    · simp only [↓reduceIte, List.cons_append] at h
      rw [At.get h]; rfl
  have h0 : At bs (pos + (if sneg then 1 else 0)) (ip.map digitByte) (fracBytes fp ++ expBytes ex ++ rest) := by
    cases sneg
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at h
      simpa [List.append_assoc] using h.assoc.assoc
    · simp only [↓reduceIte, List.cons_append] at h
      have := h.next
      simpa [List.append_assoc] using this.assoc.assoc
  have hI := parseIntPart_ext hip h0 (digitStop_frac_exp fp ex rest hr)
  have h1 : At bs (pos + (if sneg then 1 else 0) + ip.length) (fracBytes fp ++ expBytes ex) rest := by
    simpa using h0.app'.app
  have hbody : parseNumber cfg bs pos = parseNumberBody cfg bs pos sneg (pos + (if sneg then 1 else 0)) := by
    unfold parseNumber
    simp only [hneg]
    cases sneg
    · simp
    · obtain ⟨d, t, e⟩ : ∃ d t, ip = d :: t := by
        cases ip with
        | nil => exact absurd rfl hip.1
        | cons d t => exact ⟨d, t, rfl⟩
      have hd10 : d < 10 := hip.2.1 d (by simp [e])
      rw [e] at h0
      have hg : bs[pos + 1]? = some (digitByte d) := by simpa using h0.get
      have h73 : (bs[pos + 1]? == some 73) = false := by
        rw [hg]
        simpa using digitByte_ne_73 ⟨d, hd10⟩
      simp [h73]
  rw [hbody]
  unfold parseNumberBody
  rw [hI]
  simp only [bind, Except.bind]
  rw [show pos + (if sneg then 1 else 0) + ip.length - pos = (if sneg then 1 else 0) + ip.length by omega,
    hlen]
  simp only [Bool.true_eq_false, ↓reduceIte]
  cases fp with
  | none =>
    simp only [fracBytes, List.nil_append] at h1
    rw [parseFrac_none (by simpa using h1.assoc) (expBytes_head ex rest hr)]
    simp only
    cases ex with
    | none =>
      simp only [expBytes] at h1
      rw [parseExp_none (by simpa using h1) hr]
      cases sneg <;> simp [fracBytes, expBytes] <;> omega
    | some i =>
      rw [parseExp_some h1 (NumStop.digitStop hr)]
      cases sneg <;> simp [fracBytes, expBytes] <;> omega
  | some fs =>
    have hfs := hfp fs rfl
    rw [parseFrac_some hfs h1.assoc (digitStop_exp ex rest hr)]
    simp only
    have h2 := h1.app
    simp only [fracBytes, List.length_cons, List.length_map] at h2
    cases ex with
    | none =>
      simp only [expBytes] at h2
      rw [show pos + (if sneg then 1 else 0) + ip.length + (fs.length + 1) =
        pos + (if sneg then 1 else 0) + ip.length + 1 + fs.length by omega] at h2
      rw [parseExp_none (by simpa using h2) hr]
      cases sneg <;> simp [fracBytes, expBytes] <;> omega
    | some i =>
      rw [show pos + (if sneg then 1 else 0) + ip.length + (fs.length + 1) =
        pos + (if sneg then 1 else 0) + ip.length + 1 + fs.length by omega] at h2
      rw [parseExp_some h2 (NumStop.digitStop hr)]
      cases sneg <;> simp [fracBytes, expBytes] <;> omega

theorem zeros_eq (k : Nat) : zeros k = (List.replicate k 0).map digitByte := by
  simp [zeros, List.map_replicate, show digitByte 0 = 48 by decide]

/-- The layout of a float in shape form. -/
structure LayoutShape (d : Decimal) (ip : List Nat) (fp : Option (List Nat)) (ex : Option Int) : Prop where
  hip : IntDigits ip
  hfp : ∀ fs, fp = some fs → Digits1 fs
  len : ip.length = layoutIntLen (natDigits d.mant).length d.exp
  bytes : layoutDecimal (natDigits d.mant) d.exp = ip.map digitByte ++ fracBytes fp ++ expBytes ex
  value : mkNumber d.neg (ofDigits ip) ((fp.map ofDigits).getD 0) ((fp.map List.length).getD 0)
    ex.isSome (ex.getD 0) = .float d

theorem digits_take {ds : List Nat} (h : ∀ d ∈ ds, d < 10) (n : Nat) : ∀ d ∈ ds.take n, d < 10 :=
  fun d hd => h d (List.mem_of_mem_take hd)

theorem digits_drop {ds : List Nat} (h : ∀ d ∈ ds, d < 10) (n : Nat) : ∀ d ∈ ds.drop n, d < 10 :=
  fun d hd => h d (List.mem_of_mem_drop hd)

theorem normalize_eq_self (d : Decimal) : Decimal.normalize d.neg d.mant d.exp = d := by
  have := normalize_self d 0
  simpa using this

theorem mkNumber_float (neg : Bool) (iv fv fc : Nat) (he : Bool) (ev : Int)
    (h : fc ≠ 0 ∨ he = true) :
    mkNumber neg iv fv fc he ev = .float (Decimal.normalize neg (iv * 10 ^ fc + fv) (ev - fc)) := by
  unfold mkNumber
  rw [ite_eq_right (by rintro ⟨h1, h2⟩; rcases h with h | h <;> simp_all)]

theorem normalize_key (d : Decimal) (X : Nat) (Y : Int) (j : Nat)
    (hx : X = d.mant * 10 ^ j) (hy : Y = d.exp - j) : Decimal.normalize d.neg X Y = d := by
  subst hx hy; exact normalize_self d j

section layout
variable (ds : List Nat) (k : Int)

theorem layout_A (h : 0 ≤ k ∧ (ds.length : Int) + k ≤ 16) :
    layoutDecimal ds k = ds.map digitByte ++ zeros k.toNat ++ [46, 48] := by
  unfold layoutDecimal; dsimp only; rw [ite_eq_left h]

theorem layout_B (hA : ¬(0 ≤ k ∧ (ds.length : Int) + k ≤ 16))
    (h : 0 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 16) :
    layoutDecimal ds k = (ds.take ((ds.length : Int) + k).toNat).map digitByte ++
      46 :: (ds.drop ((ds.length : Int) + k).toNat).map digitByte := by
  unfold layoutDecimal; dsimp only; rw [ite_eq_right hA, ite_eq_left h]

theorem layout_C (hA : ¬(0 ≤ k ∧ (ds.length : Int) + k ≤ 16))
    (hB : ¬(0 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 16))
    (h : -5 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 0) :
    layoutDecimal ds k = [48, 46] ++ zeros (-((ds.length : Int) + k)).toNat ++ ds.map digitByte := by
  unfold layoutDecimal; dsimp only; rw [ite_eq_right hA, ite_eq_right hB, ite_eq_left h]

theorem layout_D (hA : ¬(0 ≤ k ∧ (ds.length : Int) + k ≤ 16))
    (hB : ¬(0 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 16))
    (hC : ¬(-5 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 0)) (h : ds.length = 1) :
    layoutDecimal ds k = ds.map digitByte ++ 101 :: printExp ((ds.length : Int) + k - 1) := by
  unfold layoutDecimal; dsimp only; rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hC, ite_eq_left h]

theorem layout_E (hA : ¬(0 ≤ k ∧ (ds.length : Int) + k ≤ 16))
    (hB : ¬(0 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 16))
    (hC : ¬(-5 < (ds.length : Int) + k ∧ (ds.length : Int) + k ≤ 0)) (h : ¬ ds.length = 1) :
    layoutDecimal ds k = (ds.take 1).map digitByte ++ 46 :: (ds.drop 1).map digitByte ++
      101 :: printExp ((ds.length : Int) + k - 1) := by
  unfold layoutDecimal; dsimp only; rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hC, ite_eq_right h]

end layout

theorem layoutShape (d : Decimal) : ∃ ip fp ex, LayoutShape d ip fp ex := by
  obtain ⟨hval, h10, h, t, he, hh0, hh1⟩ := natDigits_spec d.mant
  have hL : (natDigits d.mant).length = t.length + 1 := by rw [he]; simp
  have hm0 : d.mant = 0 → d.exp = 0 := by
    intro h0; rcases d.h_norm with ⟨_, h2⟩ | h2
    · exact h2
    · rw [h0] at h2; simp at h2
  generalize hds : natDigits d.mant = ds at *
  by_cases hA : 0 ≤ d.exp ∧ (ds.length : Int) + d.exp ≤ 16
  · refine ⟨ds ++ List.replicate d.exp.toNat 0, some [0], none, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · refine ⟨by simp [he], ?_, ?_⟩
      · intro x hx; simp only [List.mem_append, List.mem_replicate] at hx
        rcases hx with hx | ⟨_, hx⟩
        · exact h10 x hx
        · omega
      · rw [he]; simp only [List.cons_append, List.head?_cons, Option.some.injEq]
        intro h0; subst h0
        have ht := hh1 rfl; subst ht
        have : d.mant = 0 := by rw [← hval, he]; rfl
        rw [hm0 this]; simp
    · intro fs hfs; simp at hfs; subst hfs; exact ⟨by simp, by simp⟩
    · rw [hds]; unfold layoutIntLen; rw [ite_eq_left hA]; simp; omega
    · rw [hds, layout_A _ _ hA]; simp [fracBytes, expBytes, zeros_eq, (by decide : digitByte 0 = 48)]
    · simp only [Option.map_some, Option.getD_some, Option.isSome_none, Option.getD_none]
      rw [mkNumber_float _ _ _ _ _ _ (by simp)]
      congr 1
      apply normalize_key d _ _ (d.exp.toNat + 1)
      · rw [ofDigits_replicate_zero_right, hval]; simp [ofDigits, Nat.pow_succ, Nat.mul_assoc]
      · simp; omega
  by_cases hB : 0 < (ds.length : Int) + d.exp ∧ (ds.length : Int) + d.exp ≤ 16
  · have hk : d.exp < 0 := by omega
    have hmne : d.mant ≠ 0 := fun h0 => by have := hm0 h0; omega
    have hkkL : ((ds.length : Int) + d.exp).toNat < ds.length := by omega
    refine ⟨ds.take ((ds.length : Int) + d.exp).toNat, some (ds.drop ((ds.length : Int) + d.exp).toNat),
      none, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · refine ⟨List.ne_nil_of_length_pos (by simp; omega), digits_take h10 _, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j, ((ds.length : Int) + d.exp).toNat = j + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
      rw [hj, he]; simp only [List.take_succ_cons, List.head?_cons, Option.some.injEq]
      intro h0; exact absurd h0 (hh0 hmne)
    · intro fs hfs; simp only [Option.some.injEq] at hfs; subst hfs
      exact ⟨List.ne_nil_of_length_pos (by simp; omega), digits_drop h10 _⟩
    · rw [hds]; unfold layoutIntLen; rw [ite_eq_right hA, ite_eq_left hB]; simp; omega
    · rw [hds, layout_B _ _ hA hB]; simp [fracBytes, expBytes]
    · simp only [Option.map_some, Option.getD_some, Option.isSome_none, Option.getD_none]
      rw [mkNumber_float _ _ _ _ _ _ (by simp; omega)]
      congr 1
      apply normalize_key d _ _ 0
      · rw [← ofDigits_append, List.take_append_drop, hval]; simp
      · simp; omega
  by_cases hC : -5 < (ds.length : Int) + d.exp ∧ (ds.length : Int) + d.exp ≤ 0
  · refine ⟨[0], some (List.replicate (-((ds.length : Int) + d.exp)).toNat 0 ++ ds), none,
      ⟨⟨by simp, by simp, fun _ => rfl⟩, ?_, ?_, ?_, ?_⟩⟩
    · intro fs hfs; simp at hfs; subst hfs
      refine ⟨by simp [he], ?_⟩
      intro x hx; simp only [List.mem_append, List.mem_replicate] at hx
      rcases hx with ⟨_, hx⟩ | hx
      · omega
      · exact h10 x hx
    · rw [hds]; unfold layoutIntLen; rw [ite_eq_right hA, ite_eq_right hB]; rfl
    · rw [hds, layout_C _ _ hA hB hC]; simp [fracBytes, expBytes, zeros_eq, (by decide : digitByte 0 = 48)]
    · simp only [Option.map_some, Option.getD_some, Option.isSome_none, Option.getD_none]
      rw [mkNumber_float _ _ _ _ _ _ (by simp [he])]
      congr 1
      apply normalize_key d _ _ 0
      · rw [ofDigits_replicate_zero, hval]; simp [ofDigits]
      · simp; omega
  by_cases hD : ds.length = 1
  · refine ⟨ds, none, some ((ds.length : Int) + d.exp - 1), ⟨?_, by simp, ?_, ?_, ?_⟩⟩
    · rw [← hds]; exact natDigits_intDigits _
    · rw [hds]; unfold layoutIntLen; rw [ite_eq_right hA, ite_eq_right hB]; exact hD
    · rw [hds, layout_D _ _ hA hB hC hD]; simp [fracBytes, expBytes]
    · simp only [Option.map_none, Option.getD_none, Option.isSome_some, Option.getD_some]
      rw [mkNumber_float _ _ _ _ _ _ (by simp)]
      congr 1
      apply normalize_key d _ _ 0
      · rw [hval]; simp
      · simp; omega
  · have hL2 : 2 ≤ ds.length := by omega
    refine ⟨ds.take 1, some (ds.drop 1), some ((ds.length : Int) + d.exp - 1), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [he]; exact ⟨by simp, by simpa using h10 h (by rw [he]; simp), by simp⟩
    · intro fs hfs; simp only [Option.some.injEq] at hfs; subst hfs
      exact ⟨List.ne_nil_of_length_pos (by simp; omega), digits_drop h10 _⟩
    · rw [hds]; unfold layoutIntLen; rw [ite_eq_right hA, ite_eq_right hB]; simp; omega
    · rw [hds, layout_E _ _ hA hB hC hD]; simp [fracBytes, expBytes]
    · simp only [Option.map_some, Option.getD_some, Option.isSome_some]
      rw [mkNumber_float _ _ _ _ _ _ (by simp)]
      congr 1
      apply normalize_key d _ _ 0
      · rw [← ofDigits_append, List.take_append_drop, hval]; simp
      · simp; omega

theorem expectLit_ext {bs : ByteArray} :
    ∀ (lit : List UInt8) (p : Nat) {R : List UInt8}, At bs p lit R → expectLit bs p lit = .ok (p + lit.length)
  | [], p, R, _ => by simp [expectLit]
  | c :: cs, p, R, h => by
    simp only [expectLit, h.get, beq_self_eq_true, ↓reduceIte]
    rw [expectLit_ext cs (p + 1) h.next]
    simp; omega

/-- **Number round trip on any continuation**: integers and decimals under
every configuration within its integer limit, and `-Infinity` when NaN and
the infinities are allowed (`NaN` and `Infinity` are read at the value level,
by `parseValue`, since they do not start like a number). -/
theorem parseNumber_printNumber_ext (cfg : ParseCfg) (n : Number) {bs : ByteArray} {pos : Nat}
    {rest : List UInt8} (hfit : cfg.intLenOk n.intLen = true)
    (hfin : n.isFinite = true ∨ (n = .negInf ∧ cfg.allowInfNan = true))
    (h : At bs pos (printNumber n) rest) (hr : NumStop rest) :
    parseNumber cfg bs pos = .ok (n, pos + (printNumber n).length) := by
  cases n with
  | nan => simp [Number.isFinite] at hfin
  | inf => simp [Number.isFinite] at hfin
  | negInf =>
    have hallow : cfg.allowInfNan = true := by simpa [Number.isFinite] using hfin
    simp only [printNumber, litInfinity] at h ⊢
    unfold parseNumber
    rw [h.get, h.next.get]
    simp only [beq_self_eq_true, ↓reduceIte, hallow, Bool.and_self]
    rw [expectLit_ext _ _ (by simpa using h.next.next)]
    rfl
  | int i =>
    have hb : printNumber (.int i) =
        (if decide (i < 0) then [45] else []) ++ (natDigits i.natAbs).map digitByte ++
          fracBytes none ++ expBytes none := by
      simp only [printNumber, printInt, printNat, fracBytes, expBytes, List.append_nil]
      by_cases hi : i < 0
      · simp [hi]
      · simp [hi]; rw [show i.toNat = i.natAbs by omega]
    have hl : (if decide (i < 0) = true then 1 else 0) + (natDigits i.natAbs).length = (Number.int i).intLen := by
      simp only [Number.intLen, printInt_length, decide_eq_true_eq]
    rw [hb] at h ⊢
    rw [parseNumber_shape cfg _ _ none none (natDigits_intDigits _) (by simp) (by rw [hl]; exact hfit) h hr]
    simp only [mkNumber, Option.map_none, Option.getD_none, Option.isSome_none, and_self,
      ↓reduceIte, ofDigits_natDigits]
    congr 3
    by_cases hi : i < 0 <;> simp [hi] <;> omega
  | float d =>
    obtain ⟨ip, fp, ex, S⟩ := layoutShape d
    have hb : printNumber (.float d) =
        (if d.neg then [45] else []) ++ ip.map digitByte ++ fracBytes fp ++ expBytes ex := by
      simp only [printNumber, printDecimal, S.bytes, List.append_assoc]
    have hl : (if d.neg = true then 1 else 0) + ip.length = (Number.float d).intLen := by
      simp only [Number.intLen, S.len]
    rw [hb] at h ⊢
    rw [parseNumber_shape cfg _ _ _ _ S.hip S.hfp (by rw [hl]; exact hfit) h hr, S.value]

end LeanJson
