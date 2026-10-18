import LeanJson.Proofs.Depth
import Keel.Codec

/-!
# Proofs: the codecs and the headline round trip

The string, number and value codecs are `Keel.Codec`s: an encoder (the
printer), a Keel decoder, and Keel's law, `parse (encode a ++ rest) = .ok a
rest`, on any continuation the codec tolerates. The string and number
decoders are the grammar's lexers (`lexerCodec`); the value decoder is
`jsonParser`, the grammar's step tied by `Parser.fixDepth`. `print_injective`
is then Keel's `Codec.encode_injective`.

The headline facts about the fast parser on buffers (`parseValueAt_print`,
`parse_print`, `parse_canonical`) come from the same round trip
(`valueGo_ext`) and the agreement with the Keel parser (`valueL_deepen`, by
`fixDepth_ok`).
-/

namespace LeanJson

open Spec Keel Parser

/-! ## Codecs -/

/-- **A lexer with a round-trip law is a Keel codec**: if, on every list
holding `encode a ++ rest`, the lexer reads `a` and stops just past the
encoding, then `lexer f` decodes what `encode` writes. -/
def lexerCodec {α : Type} (encode : α → List UInt8) (f : (Nat → Option UInt8) → Nat → Except ParseErr (α × Nat))
    (valid : α → Prop) (follow : List UInt8 → Prop)
    (law : ∀ a rest, valid a → follow rest →
      f (lv (encode a ++ rest)) (encode a ++ rest).length = .ok (a, (encode a).length)) :
    Keel.Codec UInt8 α where
  encode := encode
  parser := lexer f
  valid := valid
  follow := follow
  parse_encode a rest hv hf := by
    have e := law a rest hv hf
    simp only [List.length_append] at e
    simp [Parser.parse, lexer, Input.rest, e, toResult]

/-- Strings, in either escape mode (`ensure_ascii` or raw UTF-8). -/
def stringCodec (ascii : Bool) : Keel.Codec UInt8 String :=
  lexerCodec (printString ascii) (fun get n => parseString get n 0) (fun _ => True) (fun _ => True)
    fun s rest _ _ => by simpa using parseString_printString_ext ascii s (AtV.ofList _ rest)

/-- Numbers within `cfg`'s integer limit, before anything that cannot extend
them. -/
def numberCodec (cfg : ParseCfg) : Keel.Codec UInt8 Number :=
  lexerCodec printNumber (fun get n => parseNumber cfg get n 0)
    (fun x => cfg.intLenOk x.intLen = true ∧ (x.isFinite = true ∨ (x = .negInf ∧ cfg.allowInfNan = true)))
    NumStop
    fun x rest hv hr => by simpa using parseNumber_printNumber_ext cfg x hv.1 hv.2 (AtV.ofList _ rest) hr

theorem numStop_nil : NumStop [] := by intro b hb; cases hb

/-- A value within `cfg`'s limits reads back with `cfg`'s budget of levels
for any input at least as long. -/
theorem valueL_print (cfg : ParseCfg) (o : PrintOpts) (d : Nat) {v : Json} {rest : List UInt8} {N : Nat}
    (hfit : Fits cfg v) (hrb : ReadsBack o v) (hr : NumStop rest) (hN : (printWith o d v ++ rest).length ≤ N) :
    valueL cfg (cfg.budget N) (printWith o d v ++ rest) = .ok (v, (printWith o d v).length) := by
  have h := AtV.ofList (printWith o d v) rest
  unfold ParseCfg.budget
  cases hm : cfg.maxDepth with
  | some L => exact valueGo_ext o cfg L v d 0 0 h hr hfit hrb (fits_height hm hfit)
  | none =>
    rw [Option.getD_none]
    exact valueL_deepen cfg (valueGo_ext o cfg (v.height + 1) v d 0 0 h hr hfit hrb (by omega)) (by omega)

/-- Values within `cfg`'s limits, printed under options that read back. The
decoder is `jsonParser cfg`: Keel's `fixDepth` at jiter's nesting limit. -/
def valueCodec (cfg : ParseCfg) (o : PrintOpts) (d : Nat) : Keel.Codec UInt8 Json where
  encode := printWith o d
  parser := jsonParser cfg
  valid v := Fits cfg v ∧ ReadsBack o v
  follow := NumStop
  parse_encode := fun {ε} _ v rest hv hr => by
    have h := valueL_print cfg o d hv.1 hv.2 hr (Nat.le_refl _)
    have hrun := (valueL_ok_iff (ε := ε) cfg _ _ v _).mp h
    have hparse : (fixDepth (cfg.budget (printWith o d v ++ rest).length) (valueNode cfg (ε := ε))).parse
        (printWith o d v ++ rest) = .ok v rest := by
      unfold Parser.parse; rw [hrun]; simp
    unfold jsonParser
    unfold ParseCfg.budget at hparse
    split
    · rename_i L hm; rw [hm] at hparse; exact hparse
    · rename_i hm
      rw [hm] at hparse
      exact fixDepth_ok (valueNode_monotone cfg) hparse

/-! ## Limits -/

mutual
theorem fitsAt_lossless : ∀ (k : Nat) (v : Json), FitsAt .lossless k v
  | _, .null | _, .bool _ | _, .str _ => rfl
  | _, .num _ => ⟨rfl, rfl, Or.inl rfl⟩
  | k, .arr ⟨xs⟩ => ⟨rfl, fitsList_lossless (k + 1) xs⟩
  | k, .obj ⟨kvs⟩ => ⟨rfl, nofun, fitsFields_lossless (k + 1) kvs⟩
theorem fitsList_lossless : ∀ (k : Nat) (xs : List Json), FitsList .lossless k xs
  | _, [] => trivial
  | k, x :: xs => ⟨fitsAt_lossless k x, fitsList_lossless k xs⟩
theorem fitsFields_lossless : ∀ (k : Nat) (kvs : List (String × Json)), FitsFields .lossless k kvs
  | _, [] => trivial
  | k, (_, v) :: kvs => ⟨fitsAt_lossless k v, fitsFields_lossless k kvs⟩
end

theorem fits_lossless (v : Json) : Fits .lossless v := fitsAt_lossless 0 v

/-- A value whose keys are unique, where `cfg` collapses them, is within
`cfg.relax`. -/
theorem fits_relax {cfg : ParseCfg} {w : Json} (h : cfg.dedupKeys = true → KeysUnique w) :
    Fits cfg.relax w := by
  unfold ParseCfg.relax
  cases hd : cfg.dedupKeys
  · exact fits_lossless w
  · exact h hd

/-! ## On buffers -/

/-- The nesting loop on a buffer at `q` is the loop on the buffer's bytes from
`q` on. -/
theorem valueGo_bv (cfg : ParseCfg) (bs : ByteArray) (D q : Nat) :
    valueGo cfg (bv bs) bs.size D q = valueL cfg D (bs.data.toList.drop q) := by
  rw [valueGo_rebase]
  congr 1
  · funext k
    simp only [bv, lv, List.getElem?_drop]
    exact Keel.Input.get?_eq bs (q + k)
  · simp

theorem le_size_of_at {bs : ByteArray} {pos : Nat} {l rest : List UInt8} (h : At bs pos l rest) (hl : l ≠ []) :
    pos ≤ bs.size := by
  have e := congrArg List.length h
  simp only [List.length_drop, Array.length_toList, List.length_append] at e
  have : bs.data.size = bs.size := rfl
  have := List.length_pos_iff.mpr hl
  omega

/-- **Round trip on a buffer**: a printed value within `cfg`'s limits, at any
position, before anything that cannot extend a number, reads back with the
end just past it. -/
theorem parseValueAt_print (cfg : ParseCfg) (o : PrintOpts) (d : Nat) {v : Json} {bs : ByteArray}
    {pos : Nat} {rest : List UInt8} (hfit : Fits cfg v) (hrb : ReadsBack o v)
    (h : At bs pos (printWith o d v) rest) (hr : NumStop rest) :
    parseValueAt cfg bs pos = .ok (v, pos + (printWith o d v).length) := by
  obtain ⟨b, t, e, hb⟩ := printWith_head o d v
  have hv := AtV.ofAt h (le_size_of_at h (by rw [e]; simp))
  rw [e] at hv
  unfold parseValueAt parseValueIn
  simp only
  rw [skipWs_nil (valueHead_props hb).1 hv, hv.get]
  simp only
  have hN := congrArg List.length h
  simp only [List.length_drop, Array.length_toList] at hN
  rw [valueGo_bv, h, valueL_print cfg o d hfit hrb hr (N := bs.size) (by have : bs.data.size = bs.size := rfl; omega)]
  simp [shiftRes, Nat.add_comm]

theorem at_toByteArray (l : List UInt8) : At l.toByteArray 0 l [] := by
  simp [At, List.data_toByteArray]

/-- A document parse of the printed bytes. -/
theorem parseDocumentWith_print (cfg : ParseCfg) (o : PrintOpts) (j : Json) (h : Fits cfg j)
    (hrb : ReadsBack o j) : parseDocumentWith cfg (printWith o 0 j).toByteArray = .ok j := by
  have e := parseValueAt_print cfg o 0 h hrb (at_toByteArray _) numStop_nil
  unfold parseDocumentWith parseDocumentIn
  unfold parseValueAt at e
  rw [e]
  simp only [Nat.zero_add]
  have hs : (printWith o 0 j).toByteArray.size = (printWith o 0 j).length := by simp
  rw [show skipWs (bv (printWith o 0 j).toByteArray) (printWith o 0 j).toByteArray.size
      (printWith o 0 j).length = (printWith o 0 j).length by rw [skipWs]; simp [hs]]
  simp [hs]

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

/-- **Round trip on any continuation**, the `_ext` form: for the lossless
parser, every value under every print option. -/
theorem parse_print_ext : ParsePrintExt (parseValueAt .lossless) printWith :=
  fun o d v _ _ _ hrb h hr => parseValueAt_print .lossless o d (fits_lossless v) hrb h hr

theorem string_ext : StringExt parseStringAt printString := fun ascii s bs pos _ h => by
  have hv := AtV.ofAt h (le_size_of_at h (by simp [printString]))
  exact parseString_printString_ext ascii s hv

theorem number_ext : NumberExt (parseNumberAt .lossless) printNumber := by
  intro x bs pos _ h1 h2 h hr
  have hv := AtV.ofAt h (le_size_of_at h (by obtain ⟨_, _, e, _⟩ := printNumber_head x h1 h2; rw [e]; simp))
  apply parseNumber_printNumber_ext .lossless x rfl _ hv hr
  cases x <;> simp_all [Number.isFinite] <;> rfl

/-! ## Limits only add errors

A successful parse under any configuration `cfg` is also the answer of
`cfg.relax` (limits lifted, keys collapsed as in `cfg`): `ParseCfg` limits
can turn an answer into an error, never into a different value. The integer
and NaN limits by `valueStep_relax`, level by level; the depth limit by
`valueL_deepen`. -/

theorem valueL_relax (cfg : ParseCfg) :
    ∀ (d : Nat) (L : List UInt8) {r : Json × Nat}, valueL cfg d L = .ok r → valueL cfg.relax d L = .ok r
  | 0, _, _, h => by simp [valueL, valueGo] at h
  | d + 1, L, r, h => by
    rw [valueL_succ] at h ⊢
    have h' := valueStep_relax cfg h
    have sim : ∀ j, 0 < j → j < L.length → Sim (fun _ _ => True) L.length
        (shiftRes j (valueL cfg d (L.drop j))) (shiftRes j (valueL cfg.relax d (L.drop j))) := by
      intro j hj hjn
      cases hc : valueL cfg d (L.drop j) with
      | error e => exact Or.inr ⟨j, _, hj, hjn, trivial, rfl⟩
      | ok r => rw [valueL_relax cfg d _ hc]; exact Or.inl rfl
    rcases valueStep_sim cfg.relax (viewOk_lv L) sim with e | ⟨_, _, _, _, _, e⟩
    · rw [← e, h']
    · rw [h'] at e; cases e

theorem parseValue_relax (cfg : ParseCfg) (bs : ByteArray) (pos : Nat) (r : Json × Nat)
    (h : parseValueAt cfg bs pos = .ok r) : parseValueAt cfg.relax bs pos = .ok r := by
  unfold parseValueAt parseValueIn at h ⊢
  simp only at h ⊢
  split at h
  · cases h
  rw [valueGo_bv] at h ⊢
  cases hc : valueL cfg (cfg.budget bs.size) (bs.data.toList.drop (skipWs (bv bs) bs.size pos)) with
  | error e => rw [hc] at h; cases h
  | ok r' =>
    rw [hc] at h
    have hb : (bs.data.toList.drop (skipWs (bv bs) bs.size pos)).length < cfg.relax.budget bs.size := by
      simp [ParseCfg.budget, ParseCfg.relax, ParseCfg.lossless]; omega
    rw [valueL_deepen cfg.relax (valueL_relax cfg _ _ hc) hb]
    exact h

/-- **Step progress**: every successful value parse consumes at least one byte
and ends within the buffer. -/
theorem parseValueAt_progress {cfg : ParseCfg} {bs : ByteArray} {pos : Nat} {r : Json × Nat}
    (h : parseValueAt cfg bs pos = .ok r) : pos < r.2 ∧ r.2 ≤ bs.size := by
  unfold parseValueAt parseValueIn at h
  simp only at h
  split at h
  · cases h
  rw [valueGo_bv] at h
  have g := skipWs_ge (bv bs) bs.size pos
  cases hc : valueL cfg (cfg.budget bs.size) (bs.data.toList.drop (skipWs (bv bs) bs.size pos)) with
  | error e => rw [hc] at h; cases h
  | ok r' =>
    obtain ⟨w, p⟩ := r'
    rw [hc] at h; cases h
    have := valueL_progress cfg _ _ hc
    simp at this
    have : bs.data.size = bs.size := rfl
    simp only; omega

theorem step_progress (cfg : ParseCfg) : StepProgress (parseValueAt cfg) :=
  fun _ _ _ _ h => parseValueAt_progress h

theorem parseDocument_relax {cfg : ParseCfg} {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : parseDocumentWith cfg.relax bs = .ok v := by
  unfold parseDocumentWith parseDocumentIn at h ⊢
  split at h
  · cases h
  · rename_i w p hw
    rw [show parseValueIn cfg.relax (bv bs) bs.size 0 = .ok (w, p) from parseValue_relax cfg bs 0 _ hw]
    exact h

/-- A successful parse of a canonical printing is the value printed. -/
theorem parse_canonical {cfg : ParseCfg} {bs : ByteArray} {v w : Json} {o : PrintOpts}
    (h : parseDocumentWith cfg bs = .ok v) (hrb : ReadsBack o w) (hk : cfg.dedupKeys = true → KeysUnique w)
    (hw : printWith o 0 w = bs.data.toList) : w = v := by
  have e1 := parseDocumentWith_print cfg.relax o w (fits_relax hk) hrb
  have hb : (printWith o 0 w).toByteArray = bs := by
    apply ByteArray.ext; rw [List.data_toByteArray, hw]
  rw [hb, parseDocument_relax h] at e1
  cases e1; rfl

/-! ## Injectivity -/

/-- **The printer is injective** under every option that prints NaN and the
infinities as constants (the default). (`null` and `strings` modes are not:
they print `NaN` as `null` or `"NaN"`.) Keel's `Codec.encode_injective`. -/
theorem print_injective (o : PrintOpts) (ho : o.infNan = .constants) :
    Function.Injective (printWith o 0) := fun _ _ h =>
  (valueCodec .lossless o 0).encode_injective numStop_nil ⟨fits_lossless _, Or.inl ho⟩
    ⟨fits_lossless _, Or.inl ho⟩ h

/-- **…and on finite values under every option**, `null` and `strings` modes
included: a value with no NaN or infinity prints the same in every mode, and
distinct such values print differently. -/
theorem print_injective_finite (o : PrintOpts) {v w : Json} (hv : v.allFinite = true)
    (hw : w.allFinite = true) (h : printWith o 0 v = printWith o 0 w) : v = w :=
  (valueCodec .lossless o 0).encode_injective numStop_nil ⟨fits_lossless _, Or.inr hv⟩
    ⟨fits_lossless _, Or.inr hw⟩ h

theorem print_injective_spec : PrintInjective printWith := fun o _ _ ho h => print_injective o ho h

/-! ## What a parsed document satisfies -/

theorem parseDocument_value {cfg : ParseCfg} {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) :
    ∃ q p, valueL cfg (cfg.budget bs.size) (bs.data.toList.drop q) = .ok (v, p) := by
  unfold parseDocumentWith parseDocumentIn at h
  split at h
  · cases h
  rename_i w p hw
  simp only at h
  split at h
  · cases h
  cases h
  unfold parseValueIn at hw
  simp only at hw
  split at hw
  · cases hw
  rw [valueGo_bv] at hw
  cases hc : valueL cfg (cfg.budget bs.size) (bs.data.toList.drop (skipWs (bv bs) bs.size 0)) with
  | error e => rw [hc] at hw; cases hw
  | ok r => obtain ⟨w', p'⟩ := r; rw [hc] at hw; cases hw; exact ⟨_, _, hc⟩

/-- **The depth bound.** Under `maxDepth = some L`, a successful document
parse returns a value of height below `L`. -/
theorem parse_height {cfg : ParseCfg} {L : Nat} (hL : cfg.maxDepth = some L) {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : v.height < L := by
  obtain ⟨_, _, hv⟩ := parseDocument_value h
  have := valueL_height cfg _ _ hv
  simpa [ParseCfg.budget, hL] using this

/-- `from_json` never returns a value nested deeper than jiter allows. -/
theorem parseDocument_height {bs : ByteArray} {v : Json} (h : parseDocument bs = .ok v) :
    v.height ≤ 200 := by
  have := parse_height (cfg := {}) (L := 201) rfl h
  omega

/-- **Strict mode returns RFC 8259 JSON**: no `NaN` or infinity. -/
theorem parse_finite {cfg : ParseCfg} (hs : cfg.allowInfNan = false) {bs : ByteArray} {v : Json}
    (h : parseDocumentWith cfg bs = .ok v) : v.allFinite = true := by
  obtain ⟨_, _, hv⟩ := parseDocument_value h
  exact valueL_finite cfg hs _ _ hv

end LeanJson
