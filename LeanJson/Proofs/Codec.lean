import LeanJson.Proofs.Value

/-!
# Proofs: the codec theory and the headline round trip

One pattern covers every production of the grammar: a **codec** pairs an
encoder (to bytes) with a decoder (from a buffer and cursor), and its law says
the decoder reads back exactly what the encoder wrote, out of any buffer that
holds the encoding followed by a continuation the codec can stop at, reporting
the cursor just past it. The string, number and value codecs below are
instances; the headline `parse_print` and `print_injective` follow from the
law once, in general (`Codec.decode_encode`, `Codec.encode_injective`).
-/

namespace LeanJson

open Spec

/-- A lawful byte codec. `Valid` restricts the values the law covers (for the
value codec: numbers within the parser's limits), `Stop` the continuations it
can stop at (for numbers: anything that cannot extend a literal). -/
structure Codec (α : Type) where
  encode : α → List UInt8
  decode : ByteArray → Nat → Except ParseErr (α × Nat)
  Valid : α → Prop
  Stop : List UInt8 → Prop
  law : ∀ (a : α) (bs : ByteArray) (pos : Nat) (rest : List UInt8), Valid a →
    At bs pos (encode a) rest → Stop rest → decode bs pos = .ok (a, pos + (encode a).length)

namespace Codec

variable {α : Type} (c : Codec α)

/-- The law on a concrete buffer: the encoding followed by any stop. -/
theorem decode_encode {a : α} (ha : c.Valid a) {rest : List UInt8} (hr : c.Stop rest) :
    c.decode (c.encode a ++ rest).toByteArray 0 = .ok (a, (c.encode a).length) := by
  simpa using c.law a _ 0 rest ha (At.ofList _ _) hr

/-- A lawful encoder is injective on valid values. -/
theorem encode_injective (hs : c.Stop []) {a b : α} (ha : c.Valid a) (hb : c.Valid b)
    (h : c.encode a = c.encode b) : a = b := by
  have e1 := c.decode_encode ha hs
  have e2 := c.decode_encode hb hs
  rw [h] at e1
  rw [e1] at e2
  cases e2; rfl

end Codec

/-- Strings, in either escape mode. -/
def stringCodec (ascii : Bool) : Codec String where
  encode := printString ascii
  decode := parseString
  Valid _ := True
  Stop _ := True
  law s _ _ _ _ h _ := parseString_printString_ext ascii s h

/-- Numbers, under a parser configuration. -/
def numberCodec (cfg : ParseCfg) : Codec Number where
  encode := printNumber
  decode := parseNumber cfg
  Valid n := cfg.intLenOk n.intLen = true ∧ (n.isFinite = true ∨ (n = .negInf ∧ cfg.allowInfNan = true))
  Stop := NumStop
  law n _ _ _ hv h hr := parseNumber_printNumber_ext cfg n hv.1 hv.2 h hr

theorem length_le_of_at {bs : ByteArray} {pos : Nat} {l rest : List UInt8} (h : At bs pos l rest) :
    l.length ≤ bs.size - pos := by
  by_cases hl : l = []
  · subst hl; simp
  · have := h.le_size hl; omega

/-- Values, under a parser configuration and print options. -/
def valueCodec (cfg : ParseCfg) (o : PrintOpts) (d : Nat) : Codec Json where
  encode := printWith o d
  decode := parseValueAt cfg
  Valid v := Fits cfg v ∧ ReadsBack o v
  Stop := NumStop
  law v bs pos rest hv h hr := by
    have := parseValue_ext o cfg v d 0 (ws := []) wsList_nil (by simpa using h) hr hv.1 hv.2
    simpa [parseValueAt_zero] using this

theorem numStop_nil : NumStop [] := by intro b hb; cases hb

mutual
theorem fitsAt_lossless : ∀ (k : Nat) (v : Json), FitsAt .lossless k v
  | _, .null | _, .bool _ | _, .str _ => rfl
  | _, .num _ => ⟨rfl, rfl, Or.inl rfl⟩
  | k, .arr xs => ⟨rfl, fitsList_lossless (k + 1) xs⟩
  | k, .obj kvs => ⟨rfl, fitsFields_lossless (k + 1) kvs⟩
theorem fitsList_lossless : ∀ (k : Nat) (xs : List Json), FitsList .lossless k xs
  | _, [] => trivial
  | k, x :: xs => ⟨fitsAt_lossless k x, fitsList_lossless k xs⟩
theorem fitsFields_lossless : ∀ (k : Nat) (kvs : List (String × Json)), FitsFields .lossless k kvs
  | _, [] => trivial
  | k, (_, v) :: kvs => ⟨fitsAt_lossless k v, fitsFields_lossless k kvs⟩
end

theorem fits_lossless (v : Json) : Fits .lossless v := fitsAt_lossless 0 v

/-- **Round trip on any continuation**, the `_ext` form: for the lossless
parser, every value under every print option. -/
theorem parse_print_ext : ParsePrintExt (parseValueAt .lossless) printWith :=
  fun o d v _ _ rest hrb h hr => (valueCodec .lossless o d).law v _ _ rest ⟨fits_lossless v, hrb⟩ h hr

theorem string_ext : StringExt parseString printString :=
  fun ascii s _ _ _ h => parseString_printString_ext ascii s h

theorem number_ext : NumberExt (parseNumber .lossless) printNumber := by
  intro n _ _ _ h1 h2 h hr
  apply parseNumber_printNumber_ext .lossless n rfl _ h hr
  cases n <;> simp_all [Number.isFinite] <;> rfl

/-- A document parse of the printed bytes. -/
theorem parseDocumentWith_print (cfg : ParseCfg) (o : PrintOpts) (j : Json) (h : Fits cfg j)
    (hrb : ReadsBack o j) : parseDocumentWith cfg (printWith o 0 j).toByteArray = .ok j := by
  unfold parseDocumentWith
  have e := (valueCodec cfg o 0).decode_encode (rest := []) ⟨h, hrb⟩ numStop_nil
  simp only [valueCodec, List.append_nil] at e
  rw [e]
  simp only
  have hs : skipWs (printWith o 0 j).toByteArray (printWith o 0 j).length = (printWith o 0 j).length := by
    rw [skipWs, dite_eq_right (by simp)]
  rw [hs, ite_eq_right (by simp)]

/-- **`parse (print j) = .ok j`** for every value within the default limits
(integers within 4300 bytes, height at most 200), under every print option
whose NaN/infinity mode reads back (the default `constants`, or any mode for
a value with no NaN or infinity). Each condition is necessary: upstream
rejects longer integer literals and deeper nesting, and `null`/`strings`
modes print a NaN as something else. -/
theorem parse_print (j : Json) (o : PrintOpts := {}) (h : Fits {} j) (hrb : ReadsBack o j) :
    parseDocument (printWith o 0 j).toByteArray = .ok j :=
  parseDocumentWith_print {} o j h hrb

/-- The lossless parser reads back every printed value whose NaN/infinity mode
reads back. -/
theorem parseLossless_print (j : Json) (o : PrintOpts := {}) (hrb : ReadsBack o j) :
    parseDocumentWith .lossless (printWith o 0 j).toByteArray = .ok j :=
  parseDocumentWith_print .lossless o j (fits_lossless j) hrb


/-! ## Limits only add errors

A successful parse under any configuration is also the lossless parser's
answer: `ParseCfg` limits can turn an answer into `number out of range`, never
into a different value. -/

theorem parseNumberBody_relax {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {neg : Bool} {p0 : Nat}
    {r : Number × Nat} (h : parseNumberBody cfg bs pos neg p0 = .ok r) :
    parseNumberBody .lossless bs pos neg p0 = .ok r := by
  unfold parseNumberBody at h ⊢
  simp only [bind, Except.bind] at h ⊢
  split at h
  · cases h
  · rename_i x1 h1
    split at h
    · cases h
    · simp only [ParseCfg.intLenOk, ParseCfg.lossless, Bool.true_eq_false, ↓reduceIte]
      exact h

theorem parseNumberBody_I {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {neg : Bool} {p0 : Nat}
    (hI : bs[p0]? = some 73) (r : Number × Nat) : parseNumberBody cfg bs pos neg p0 ≠ .ok r := by
  intro h
  unfold parseNumberBody at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i x1 h1
    unfold parseIntPart at h1
    rw [hI] at h1
    simp (config := { decide := true }) [] at h1

theorem parseNumber_relax {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {r : Number × Nat}
    (h : parseNumber cfg bs pos = .ok r) : parseNumber .lossless bs pos = .ok r := by
  unfold parseNumber at h ⊢
  by_cases c45 : (bs[pos]? == some 45) = true
  · rw [ite_eq_left c45] at h ⊢
    by_cases ci : (cfg.allowInfNan && bs[pos + 1]? == some 73) = true
    · rw [ite_eq_left ci] at h
      have h73 : (bs[pos + 1]? == some 73) = true := by simp at ci; simp [ci.2]
      rw [ite_eq_left (by simp [ParseCfg.lossless, h73])]
      exact h
    · rw [ite_eq_right ci] at h
      by_cases h73 : (bs[pos + 1]? == some 73) = true
      · exact absurd h (parseNumberBody_I (by simpa using h73) r)
      · rw [ite_eq_right (by simp [ParseCfg.lossless, h73])]
        exact parseNumberBody_relax h
  · rw [ite_eq_right c45] at h ⊢
    exact parseNumberBody_relax h

/-- The value parser's answer under `cfg`, if successful, is the lossless one. -/
def RelaxV (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Prop :=
  ∀ k r, parseValueAtD cfg bs k pos = .ok r → parseValueAtD .lossless bs k pos = .ok r
def RelaxE (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Prop :=
  ∀ k start acc r, start ≤ pos → parseElemsAt cfg bs k start pos acc = .ok r →
    parseElemsAt .lossless bs k start pos acc = .ok r
def RelaxM (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) : Prop :=
  ∀ k start acc r, start ≤ pos → parseMembersAt cfg bs k start pos acc = .ok r →
    parseMembersAt .lossless bs k start pos acc = .ok r

theorem parseValueAtD_progress {cfg : ParseCfg} {bs : ByteArray} {k pos : Nat} {r : Json × Nat}
    (h : parseValueAtD cfg bs k pos = .ok r) : pos < r.2 ∧ r.2 ≤ bs.size := by
  unfold parseValueAtD at h
  cases hv : parseValueWith cfg bs k pos with
  | error e => rw [hv] at h; cases h
  | ok s => rw [hv] at h; cases h; exact ⟨s.lt, s.le⟩

theorem parseValueAt_progress {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {r : Json × Nat}
    (h : parseValueAt cfg bs pos = .ok r) : pos < r.2 ∧ r.2 ≤ bs.size := parseValueAtD_progress h

theorem lossless_depthOk (k : Nat) : ParseCfg.lossless.depthOk k = true := rfl

theorem relaxV_step (cfg : ParseCfg) (bs : ByteArray) (pos : Nat)
    (IHe : ∀ p, bs.size - p < bs.size - pos → RelaxE cfg bs p)
    (IHm : ∀ p, bs.size - p < bs.size - pos → RelaxM cfg bs p) : RelaxV cfg bs pos := by
  intro k r h
  rw [parseValueAtD_eq] at h ⊢
  have g0 := skipWs_ge bs pos
  have g1 := skipWs_ge bs (skipWs bs pos + 1)
  split at h
  · rename_i hb; (try rw [hb]); exact h
  rename_i b hb
  (try rw [hb]); try simp only
  by_cases hd : cfg.depthOk k = false
  · rw [ite_eq_left hd] at h; cases h
  rw [ite_eq_right hd] at h
  rw [lossless_depthOk]; simp only [Bool.true_eq_false, ↓reduceIte]
  by_cases c34 : (b == 34) = true
  · rw [ite_eq_left c34] at h ⊢; exact h
  rw [ite_eq_right c34] at h ⊢
  by_cases c91 : (b == 91) = true
  · rw [ite_eq_left c91] at h ⊢
    split at h
    · rename_i hp; (try rw [hp]); exact h
    · rename_i c hp
      (try rw [hp]); try simp only
      have := lt_size_of_get hp
      split at h
      · rename_i e; rw [ite_eq_left e]; exact h
      · rename_i e; rw [ite_eq_right e]; exact IHe _ (by omega) _ _ [] r (by omega) h
  rw [ite_eq_right c91] at h ⊢
  by_cases c123 : (b == 123) = true
  · rw [ite_eq_left c123] at h ⊢
    split at h
    · rename_i hp; (try rw [hp]); exact h
    · rename_i c hp
      (try rw [hp]); try simp only
      have := lt_size_of_get hp
      split at h
      · rename_i e; rw [ite_eq_left e]; exact h
      · rename_i e; rw [ite_eq_right e]
        split at h
        · rename_i e2; rw [ite_eq_left e2]; exact IHm _ (by omega) _ _ [] r (by omega) h
        · rename_i e2; rw [ite_eq_right e2]; exact h
  rw [ite_eq_right c123] at h ⊢
  by_cases c116 : (b == 116) = true
  · rw [ite_eq_left c116] at h ⊢; exact h
  rw [ite_eq_right c116] at h ⊢
  by_cases c102 : (b == 102) = true
  · rw [ite_eq_left c102] at h ⊢; exact h
  rw [ite_eq_right c102] at h ⊢
  by_cases c110 : (b == 110) = true
  · rw [ite_eq_left c110] at h ⊢; exact h
  rw [ite_eq_right c110] at h ⊢
  by_cases cn : (b == 45 || isDigit b) = true
  · rw [ite_eq_left cn] at h ⊢
    cases hx : parseNumber cfg bs (skipWs bs pos) with
    | error e => rw [hx] at h; cases h
    | ok x => rw [hx] at h; rw [parseNumber_relax hx]; exact h
  rw [ite_eq_right cn] at h ⊢
  by_cases ha : cfg.allowInfNan = true
  · have hl : ParseCfg.lossless.allowInfNan = true := rfl
    rw [ha] at h; rw [hl]; exact h
  · have hf : cfg.allowInfNan = false := by simpa using ha
    rw [hf] at h
    simp at h

theorem relaxE_step (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) (hV : RelaxV cfg bs pos)
    (IHe : ∀ p, bs.size - p < bs.size - pos → RelaxE cfg bs p) : RelaxE cfg bs pos := by
  intro k start acc r hsp h
  rw [parseElemsAt_eq _ _ _ _ _ _ hsp] at h ⊢
  split at h
  · cases h
  · rename_i v p1 hv
    have pr := parseValueAtD_progress hv
    rw [hV _ _ hv]
    simp only
    have g1 := skipWs_ge bs p1
    have g2 := skipWs_ge bs (skipWs bs p1 + 1)
    split at h
    · rename_i hp; (try rw [hp]); exact h
    · rename_i c hp
      (try rw [hp]); try simp only
      split at h
      · rename_i e; rw [ite_eq_left e]
        split at h
        · rename_i e2; rw [ite_eq_left e2]; exact h
        · rename_i e2; rw [ite_eq_right e2]
          exact IHe _ (by simp at pr; omega) _ _ _ r (by simp at pr; omega) h
      · rename_i e; rw [ite_eq_right e]; exact h

theorem relaxM_step (cfg : ParseCfg) (bs : ByteArray) (pos : Nat)
    (IHv : ∀ p, bs.size - p < bs.size - pos → RelaxV cfg bs p)
    (IHm : ∀ p, bs.size - p < bs.size - pos → RelaxM cfg bs p) : RelaxM cfg bs pos := by
  intro k start acc r hsp h
  rw [parseMembersAt_eq _ _ _ _ _ _ hsp] at h ⊢
  split at h
  · cases h
  · rename_i key p1 hk
    have pk := (parseString_adv hk).2
    (try rw [hk]); try simp only
    have g1 := skipWs_ge bs p1
    split at h
    · rename_i hp; (try rw [hp]); exact h
    · rename_i c hp
      (try rw [hp]); try simp only
      have hps := lt_size_of_get hp
      split at h
      · rename_i e; rw [ite_eq_left e]
        split at h
        · cases h
        · rename_i v p2 hv
          have pr := parseValueAtD_progress hv
          rw [IHv _ (by omega) _ _ hv]
          simp only
          have g2 := skipWs_ge bs p2
          have g3 := skipWs_ge bs (skipWs bs p2 + 1)
          split at h
          · rename_i hd; (try rw [hd]); exact h
          · rename_i d hd
            (try rw [hd]); try simp only
            split at h
            · rename_i e3; rw [ite_eq_left e3]
              split at h
              · rename_i he; (try rw [he]); exact h
              · rename_i f he
                (try rw [he]); try simp only
                have hqs := lt_size_of_get he
                split at h
                · rename_i e4; rw [ite_eq_left e4]
                  exact IHm _ (by simp at pr; omega) _ _ _ r (by simp at pr; omega) h
                · rename_i e4; rw [ite_eq_right e4]; exact h
            · rename_i e3; rw [ite_eq_right e3]; exact h
      · rename_i e; rw [ite_eq_right e]; exact h

/-- Limits only add errors: by strong induction on the remaining input. -/
theorem relax_all (cfg : ParseCfg) (bs : ByteArray) :
    ∀ n pos, bs.size - pos ≤ n → RelaxV cfg bs pos ∧ RelaxE cfg bs pos ∧ RelaxM cfg bs pos := by
  intro n
  induction n with
  | zero =>
    intro pos hp
    have IH0 : ∀ p, bs.size - p < bs.size - pos → False := fun p h => by omega
    have hv := relaxV_step cfg bs pos (fun p h => (IH0 p h).elim) (fun p h => (IH0 p h).elim)
    exact ⟨hv, relaxE_step cfg bs pos hv (fun p h => (IH0 p h).elim),
      relaxM_step cfg bs pos (fun p h => (IH0 p h).elim) (fun p h => (IH0 p h).elim)⟩
  | succ n ih =>
    intro pos hp
    have IH : ∀ p, bs.size - p < bs.size - pos → RelaxV cfg bs p ∧ RelaxE cfg bs p ∧ RelaxM cfg bs p :=
      fun p h => ih p (by omega)
    have hv := relaxV_step cfg bs pos (fun p h => (IH p h).2.1) (fun p h => (IH p h).2.2)
    exact ⟨hv, relaxE_step cfg bs pos hv (fun p h => (IH p h).2.1),
      relaxM_step cfg bs pos (fun p h => (IH p h).1) (fun p h => (IH p h).2.2)⟩

theorem parseValue_relax (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) (r : Json × Nat)
    (h : parseValueAt cfg bs pos = .ok r) : parseValueAt .lossless bs pos = .ok r :=
  (relax_all cfg bs _ pos (Nat.le_refl _)).1 0 r h

/-- **Step progress**: every successful value parse consumes at least one byte
and ends within the buffer. It is the `Step` type of the parser, read back. -/
theorem step_progress (cfg : ParseCfg) : StepProgress (parseValueAt cfg) :=
  fun _ _ _ _ h => parseValueAt_progress h

theorem parseDocument_relax {cfg : ParseCfg} {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : parseDocumentWith .lossless bs = .ok v := by
  unfold parseDocumentWith at h ⊢
  split at h
  · cases h
  · rename_i w p hw
    rw [parseValue_relax cfg bs 0 _ hw]
    exact h

/-- A successful parse of a canonical printing is the value printed. -/
theorem parse_canonical {cfg : ParseCfg} {bs : ByteArray} {v w : Json} {o : PrintOpts}
    (h : parseDocumentWith cfg bs = .ok v) (hrb : ReadsBack o w) (hw : printWith o 0 w = bs.data.toList) :
    w = v := by
  have e1 := parseLossless_print w o hrb
  have hb : (printWith o 0 w).toByteArray = bs := by
    apply ByteArray.ext; rw [List.data_toByteArray, hw]
  rw [hb, parseDocument_relax h] at e1
  cases e1; rfl

/-- **The printer is injective** under every option that prints NaN and the
infinities as constants (the default). (`null` and `strings` modes are not:
they print `NaN` as `null` or `"NaN"`.) -/
theorem print_injective (o : PrintOpts) (ho : o.infNan = .constants) :
    Function.Injective (printWith o 0) := fun _ _ h =>
  (valueCodec .lossless o 0).encode_injective numStop_nil ⟨fits_lossless _, Or.inl ho⟩
    ⟨fits_lossless _, Or.inl ho⟩ h

theorem print_injective_spec : PrintInjective printWith := fun o _ _ ho h => print_injective o ho h

end LeanJson
