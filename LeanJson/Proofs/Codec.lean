import LeanJson.Proofs.Fuel

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
  Valid n := cfg.intLenOk n.intLen = true
  Stop := NumStop
  law n _ _ _ hv h hr := parseNumber_printNumber_ext cfg n hv h hr

theorem length_le_of_at {bs : ByteArray} {pos : Nat} {l rest : List UInt8} (h : At bs pos l rest) :
    l.length ≤ bs.size - pos := by
  by_cases hl : l = []
  · subst hl; simp
  · have := h.le_size hl; omega

/-- Values, under a parser configuration and print options, at the fuel the
entry points pass. -/
def valueCodec (cfg : ParseCfg) (o : PrintOpts) (d : Nat) : Codec Json where
  encode := printWith o d
  decode bs pos := parseValueWith cfg bs pos (fuelFor bs pos)
  Valid := Fits cfg
  Stop := NumStop
  law v bs pos rest hv h hr := by
    have := parseValue_ext o cfg v d (ws := []) (fuelFor bs pos) wsList_nil (by simpa using h) hr
      (by have := length_le_of_at h; unfold fuelFor; omega) hv
    simpa using this

theorem numStop_nil : NumStop [] := by intro b hb; cases hb

mutual
theorem fits_lossless : ∀ v : Json, Fits .lossless v
  | .null | .bool _ | .str _ => trivial
  | .num _ => rfl
  | .arr xs => fitsList_lossless xs
  | .obj kvs => fitsFields_lossless kvs
theorem fitsList_lossless : ∀ xs : List Json, FitsList .lossless xs
  | [] => trivial
  | x :: xs => ⟨fits_lossless x, fitsList_lossless xs⟩
theorem fitsFields_lossless : ∀ kvs : List (String × Json), FitsFields .lossless kvs
  | [] => trivial
  | (_, v) :: kvs => ⟨fits_lossless v, fitsFields_lossless kvs⟩
end

/-- **Round trip on any continuation**, the `_ext` form: for the lossless
parser, every value under every print option. -/
theorem parse_print_ext : ParsePrintExt (parseValueWith .lossless) printWith := by
  intro o d v bs pos rest fuel h hr hf
  have := parseValue_ext o .lossless v d (ws := []) fuel wsList_nil (by simpa using h) hr hf
    (fits_lossless v)
  simpa using this

theorem string_ext : StringExt parseString printString :=
  fun ascii s _ _ _ h => parseString_printString_ext ascii s h

theorem number_ext : NumberExt (parseNumber .lossless) printNumber :=
  fun n _ _ _ h hr => parseNumber_printNumber_ext .lossless n rfl h hr

/-- A document parse of the printed bytes. -/
theorem parseDocumentWith_print (cfg : ParseCfg) (o : PrintOpts) (j : Json) (h : Fits cfg j) :
    parseDocumentWith cfg (printWith o 0 j).toByteArray = .ok j := by
  unfold parseDocumentWith
  have e := (valueCodec cfg o 0).decode_encode (rest := []) h numStop_nil
  simp only [valueCodec, List.append_nil] at e
  rw [e]
  simp only
  have hs : skipWs (printWith o 0 j).toByteArray (printWith o 0 j).length
      (printWith o 0 j).toByteArray.size = (printWith o 0 j).length := by
    cases hsz : (printWith o 0 j).toByteArray.size with
    | zero => rfl
    | succ f =>
      unfold skipWs
      rw [getElem?_neg _ _ (by simp)]
  rw [hs, ite_eq_right (by simp)]

/-- **`parse (print j) = .ok j`** for every value whose integers are within
jiter's 4300-byte limit, under every print option (compact, indented,
ASCII-only). The side condition is necessary: upstream rejects longer integer
literals, so their printing cannot parse back. -/
theorem parse_print (j : Json) (o : PrintOpts := {}) (h : Fits {} j) :
    parseDocument (printWith o 0 j).toByteArray = .ok j :=
  parseDocumentWith_print {} o j h

/-- The lossless parser reads back every printed value, with no side condition. -/
theorem parseLossless_print (j : Json) (o : PrintOpts := {}) :
    parseDocumentWith .lossless (printWith o 0 j).toByteArray = .ok j :=
  parseDocumentWith_print .lossless o j (fits_lossless j)


/-! ## Limits only add errors

A successful parse under any configuration is also the lossless parser's
answer: `ParseCfg` limits can turn an answer into `number out of range`, never
into a different value. -/

theorem parseNumber_relax {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {r : Number × Nat}
    (h : parseNumber cfg bs pos = .ok r) : parseNumber .lossless bs pos = .ok r := by
  unfold parseNumber at h ⊢
  simp only [bind, Except.bind] at h ⊢
  split at h
  · cases h
  · rename_i x1 h1
    split at h
    · cases h
    · simp only [ParseCfg.intLenOk, ParseCfg.lossless, Bool.true_eq_false, ↓reduceIte]
      exact h

mutual
theorem parseValue_relax (cfg : ParseCfg) (bs : ByteArray) : ∀ (n pos : Nat) (r : Json × Nat),
    parseValueWith cfg bs pos n = .ok r → parseValueWith .lossless bs pos n = .ok r
  | 0, pos, r, h => by simp [parseValueWith] at h
  | n + 1, pos, r, h => by
    unfold parseValueWith at h ⊢
    try simp only at h ⊢
    generalize skipWs bs pos bs.size = q at h ⊢
    split at h
    · rename_i hb; (try rw [hb]); exact h
    rename_i b hb
    (try rw [hb]); try simp only
    by_cases c34 : (b == 34) = true
    · rw [ite_eq_left c34] at h ⊢; exact h
    rw [ite_eq_right c34] at h ⊢
    by_cases c91 : (b == 91) = true
    · rw [ite_eq_left c91] at h ⊢
      generalize skipWs bs (q + 1) bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); exact h
      · exact parseElems_relax cfg bs n p [] r h
    rw [ite_eq_right c91] at h ⊢
    by_cases c123 : (b == 123) = true
    · rw [ite_eq_left c123] at h ⊢
      generalize skipWs bs (q + 1) bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); exact parseMembers_relax cfg bs n p [] r h
      · exact h
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
      split at h
      · rename_i x p hx; cases h; rw [parseNumber_relax hx]
      · cases h
    rw [ite_eq_right cn] at h ⊢
    exact h
theorem parseElems_relax (cfg : ParseCfg) (bs : ByteArray) : ∀ (n pos : Nat) (acc : List Json)
    (r : Json × Nat), parseElems cfg bs pos n acc = .ok r → parseElems .lossless bs pos n acc = .ok r
  | 0, pos, acc, r, h => by simp [parseElems] at h
  | n + 1, pos, acc, r, h => by
    unfold parseElems at h ⊢
    split at h
    · cases h
    · rename_i v p1 hv
      rw [parseValue_relax cfg bs n pos _ hv]
      try simp only at h ⊢
      generalize skipWs bs p1 bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); try simp only at h ⊢
        generalize skipWs bs (p + 1) bs.size = q at h ⊢
        split at h
        · rename_i c; rw [ite_eq_left c]; exact h
        · rename_i c; rw [ite_eq_right c]; exact parseElems_relax cfg bs n q _ r h
      · rename_i hp; (try rw [hp]); exact h
      · exact h
theorem parseMembers_relax (cfg : ParseCfg) (bs : ByteArray) : ∀ (n pos : Nat) (acc : List (String × Json))
    (r : Json × Nat), parseMembers cfg bs pos n acc = .ok r → parseMembers .lossless bs pos n acc = .ok r
  | 0, pos, acc, r, h => by simp [parseMembers] at h
  | n + 1, pos, acc, r, h => by
    unfold parseMembers at h ⊢
    split at h
    · cases h
    · rename_i k p1 hk
      (try rw [hk]); try simp only at h ⊢
      generalize skipWs bs p1 bs.size = p at h ⊢
      split at h
      · rename_i hp; (try rw [hp]); exact h
      · rename_i hp; (try rw [hp]); try simp only
        split at h
        · cases h
        · rename_i v p2 hv
          rw [parseValue_relax cfg bs n (p + 1) _ hv]
          try simp only at h ⊢
          generalize skipWs bs p2 bs.size = p3 at h ⊢
          split at h
          · rename_i hp3; (try rw [hp3]); exact h
          · rename_i hp3; (try rw [hp3]); try simp only at h ⊢
            generalize skipWs bs (p3 + 1) bs.size = q at h ⊢
            split at h
            · rename_i hq; (try rw [hq]); exact h
            · rename_i hq; (try rw [hq]); exact parseMembers_relax cfg bs n q _ r h
            · rename_i hq; (try rw [hq]); exact h
            · exact h
          · rename_i hp3; (try rw [hp3]); exact h
          · exact h
      · exact h
end

theorem parseDocument_relax {cfg : ParseCfg} {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : parseDocumentWith .lossless bs = .ok v := by
  unfold parseDocumentWith at h ⊢
  split at h
  · cases h
  · rename_i w p hw
    rw [parseValue_relax cfg bs _ 0 _ hw]
    exact h

/-- A successful parse of a canonical printing is the value printed. -/
theorem parse_canonical {cfg : ParseCfg} {bs : ByteArray} {v w : Json} {o : PrintOpts}
    (h : parseDocumentWith cfg bs = .ok v) (hw : printWith o 0 w = bs.data.toList) : w = v := by
  have e1 := parseLossless_print w o
  have hb : (printWith o 0 w).toByteArray = bs := by
    apply ByteArray.ext; rw [List.data_toByteArray, hw]
  rw [hb, parseDocument_relax h] at e1
  cases e1; rfl

/-- **The printer is injective**, under every option. -/
theorem print_injective (o : PrintOpts) : Function.Injective (printWith o 0) := fun _ _ h =>
  (valueCodec .lossless o 0).encode_injective numStop_nil (fits_lossless _) (fits_lossless _) h

theorem print_injective_spec : PrintInjective printWith := fun o _ _ h => print_injective o h

end LeanJson
