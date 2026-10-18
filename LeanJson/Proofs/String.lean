import LeanJson.Proofs.Number

/-!
# Proofs: the string codec

`parseString_printString_ext`: every string round-trips through
`printString`/`parseString` in both escape modes, on any continuation.
The heart is `strStep`: one escaped character is consumed exactly and
decodes to itself, whether it was written raw (UTF-8, decoded by core's
`ByteArray.utf8DecodeChar?`), as a short escape (`\n`, `\"`), as `\u00XX`,
as `\uXXXX`, or as a surrogate pair.
-/

namespace LeanJson

open Spec

theorem hexVal_hexByte : ∀ d : Fin 16, hexVal (hexByte d.val) = some d.val := by decide

theorem hexByte_ne_ws : ∀ d : Fin 16, isWs (hexByte d) = false := by decide

theorem parseHex4_ext {get : Nat → Option UInt8} {sz : Nat} {p n : Nat} {R : List UInt8} (hn : n < 65536)
    (h : AtV get sz p [hexByte (n / 4096 % 16), hexByte (n / 256 % 16), hexByte (n / 16 % 16),
      hexByte (n % 16)] R) : parseHex4 get sz p = .ok n := by
  have g0 := h.get
  have g1 := h.next.get
  have g2 := h.next.next.get
  have g3 := h.next.next.next.get
  have v0 := hexVal_hexByte ⟨n / 4096 % 16, by omega⟩
  have v1 := hexVal_hexByte ⟨n / 256 % 16, by omega⟩
  have v2 := hexVal_hexByte ⟨n / 16 % 16, by omega⟩
  have v3 := hexVal_hexByte ⟨n % 16, by omega⟩
  simp only at v0 v1 v2 v3
  have hs : ¬ sz < p + 4 := by have := h.le_size; simp at this; omega
  unfold parseHex4
  rw [ite_eq_right hs]
  simp only [hexAt, g0, g1, g2, g3, v0, v1, v2, v3]
  congr 1; omega

/-- The window at `pos` is the next four bytes of the view (fewer near its end). -/
theorem window_eq {get : Nat → Option UInt8} {pos : Nat} {M : List UInt8}
    (h : ∀ k, get (pos + k) = M[k]?) : window get pos = (M.take 4).toByteArray := by
  have g0 := h 0; have g1 := h 1; have g2 := h 2; have g3 := h 3
  simp only [Nat.add_zero] at g0
  unfold window
  match M, g0, g1, g2, g3 with
  | [], g0, _, _, _ => simp [g0]
  | [b0], g0, g1, _, _ => simp [g0, g1]; rfl
  | [b0, b1], g0, g1, g2, _ => simp [g0, g1, g2]; rfl
  | [b0, b1, b2], g0, g1, g2, g3 => simp [g0, g1, g2, g3]; rfl
  | b0 :: b1 :: b2 :: b3 :: _, g0, g1, g2, g3 => simp [g0, g1, g2, g3]; rfl

theorem decode_ext {get : Nat → Option UInt8} {sz : Nat} {pos : Nat} {c : Char} {R : List UInt8}
    (h : AtV get sz pos (String.utf8EncodeChar c) R) : decodeChar? get pos = some c := by
  unfold decodeChar?
  rw [window_eq h.get_eq, List.take_append,
    List.take_of_length_le (by rw [String.length_utf8EncodeChar]; exact Char.utf8Size_le_four c),
    List.toByteArray_append, ByteArray.utf8DecodeChar?_utf8EncodeChar_append]
theorem toNat_valid (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have hv := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at hv
  exact hv

theorem enc_ascii (c : Char) (h : c.toNat < 128) :
    String.utf8EncodeChar c = [UInt8.ofNat c.toNat] := by
  rw [String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr
    (by rw [UInt32.le_iff_toNat_le]; exact Nat.le_of_lt_succ h))]
  rfl

theorem or_ge (x y : UInt8) (h : 128 ≤ y.toNat) : 128 ≤ (x ||| y).toNat := by
  rw [UInt8.toNat_or]; exact Nat.le_trans h Nat.right_le_or

theorem enc_high (c : Char) (h : 128 ≤ c.toNat) :
    ∃ b t, String.utf8EncodeChar c = b :: t ∧ 128 ≤ b.toNat := by
  have hlt : 127 < c.val := by rw [UInt32.lt_iff_toNat_lt]; exact h
  rcases Char.utf8Size_eq c with h1 | h1 | h1 | h1
  · have := Char.utf8Size_eq_one_iff.mp h1
    rw [UInt32.le_iff_toNat_le] at this; rw [UInt32.lt_iff_toNat_lt] at hlt
    exact absurd this (Nat.not_le.mpr hlt)
  · rw [String.utf8EncodeChar_eq_cons_cons h1]; exact ⟨_, _, rfl, or_ge _ _ (by decide)⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h1]; exact ⟨_, _, rfl, or_ge _ _ (by decide)⟩
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h1]; exact ⟨_, _, rfl, or_ge _ _ (by decide)⟩

theorem char_eq_ofNat (c : Char) (n : Nat) (h : c.toNat = n) : c = Char.ofNat n := by
  rw [← h, Char.ofNat_toNat]

theorem hex4_eq (n : Nat) : hex4 n = 92 :: 117 :: [hexByte (n / 4096 % 16), hexByte (n / 256 % 16),
    hexByte (n / 16 % 16), hexByte (n % 16)] := rfl

/-- A `\uXXXX` escape of a non-surrogate code point decodes to it. -/
theorem parseEscape_u (get : Nat → Option UInt8) (sz : Nat) (pos : Nat) (c : Char) (R : List UInt8)
    (hn : c.toNat < 65536) (hs : c.toNat < 0xD800 ∨ 0xDFFF < c.toNat)
    (h : AtV get sz pos (hex4 c.toNat) R) : parseEscape get sz (pos + 1) = .ok (c, pos + 6) := by
  rw [hex4_eq] at h
  have h1 := h.next
  unfold parseEscape
  rw [h1.get]
  simp only [show ((117 : UInt8) == 34) = false by decide, show ((117 : UInt8) == 92) = false by decide,
    show ((117 : UInt8) == 47) = false by decide, show ((117 : UInt8) == 98) = false by decide,
    show ((117 : UInt8) == 102) = false by decide, show ((117 : UInt8) == 110) = false by decide,
    show ((117 : UInt8) == 114) = false by decide, show ((117 : UInt8) == 116) = false by decide,
    show ((117 : UInt8) == 117) = true by decide, Bool.false_eq_true, ↓reduceIte]
  rw [parseHex4_ext hn h1.next]
  simp only [bind, Except.bind]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [← char_eq_ofNat c _ rfl]

/-- One step of the string body at a byte that exists. -/
theorem strBody_at {get : Nat → Option UInt8} {sz : Nat} {pos : Nat} {acc : String} {b : UInt8}
    (hlt : pos < sz) (hb : get pos = some b) :
    parseStrBody get sz pos acc =
      if b == 34 then .ok (acc, pos + 1)
      else if b == 92 then
        match parseEscape get sz (pos + 1) with
        | .ok (c, p) => parseStrBody get sz p (acc.push c)
        | .error e => .error e
      else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
      else if b < 128 then parseStrBody get sz (pos + 1) (acc.push (Char.ofNat b.toNat))
      else
        match decodeChar? get pos with
        | some c => parseStrBody get sz (pos + c.utf8Size) (acc.push c)
        | none => .error ⟨.invalidUnicodeCodePoint, pos + 1⟩ := by
  rw [parseStrBody]
  simp only [hlt, ↓reduceIte]
  simp only [hb]
  by_cases h1 : (b == 34) = true
  · simp only [h1, ↓reduceIte]
  · by_cases h2 : (b == 92) = true
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i heq <;> simp [heq]
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
      rfl

theorem step_backslash {get : Nat → Option UInt8} {sz : Nat} {pos : Nat} {acc : String} {c : Char} {p : Nat}
    (hlt : pos < sz) (hb : get pos = some 92) (he : parseEscape get sz (pos + 1) = .ok (c, p)) :
    parseStrBody get sz pos acc = parseStrBody get sz p (acc.push c) := by
  rw [strBody_at hlt hb]; simp [he]

theorem step_ascii {get : Nat → Option UInt8} {sz : Nat} {pos : Nat} {acc : String} {b : UInt8}
    (hlt : pos < sz) (hb : get pos = some b) (h1 : b ≠ 34) (h2 : b ≠ 92) (h3 : 32 ≤ b.toNat) (h4 : b.toNat < 128) :
    parseStrBody get sz pos acc = parseStrBody get sz (pos + 1) (acc.push (Char.ofNat b.toNat)) := by
  rw [strBody_at hlt hb]
  have e1 : (b == 34) = false := by simpa using h1
  have e2 : (b == 92) = false := by simpa using h2
  have e3 : ¬ b < 32 := by rw [UInt8.lt_iff_toNat_lt]; simp; omega
  have e4 : b < 128 := by rw [UInt8.lt_iff_toNat_lt]; simpa using h4
  simp [e1, e2, e3, e4]

theorem step_high {get : Nat → Option UInt8} {sz : Nat} {pos : Nat} {acc : String} {b : UInt8} {c : Char}
    (hlt : pos < sz) (hb : get pos = some b) (h3 : 128 ≤ b.toNat) (hd : decodeChar? get pos = some c) :
    parseStrBody get sz pos acc = parseStrBody get sz (pos + c.utf8Size) (acc.push c) := by
  rw [strBody_at hlt hb]
  have e1 : (b == 34) = false := by
    apply beq_false_of_ne; intro e; subst e; simp at h3
  have e2 : (b == 92) = false := by
    apply beq_false_of_ne; intro e; subst e; simp at h3
  have e3 : ¬ b < 32 := by rw [UInt8.lt_iff_toNat_lt]; simp; omega
  have e4 : ¬ b < 128 := by rw [UInt8.lt_iff_toNat_lt]; simp; omega
  simp [e1, e2, e3, e4, hd]

theorem pe_byte {get : Nat → Option UInt8} {sz : Nat} {q : Nat} {b : UInt8} {R : List UInt8} (h : AtV get sz q [b] R) :
    get q = some b := h.get

theorem parseEscape_quote {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 34) :
    parseEscape get sz q = .ok ('"', q + 1) := by simp [parseEscape, hb]
theorem parseEscape_backslash {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 92) :
    parseEscape get sz q = .ok ('\\', q + 1) := by simp [parseEscape, hb]
theorem parseEscape_b {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 98) :
    parseEscape get sz q = .ok (Char.ofNat 8, q + 1) := by simp [parseEscape, hb]
theorem parseEscape_f {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 102) :
    parseEscape get sz q = .ok (Char.ofNat 12, q + 1) := by simp [parseEscape, hb]
theorem parseEscape_n {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 110) :
    parseEscape get sz q = .ok ('\n', q + 1) := by simp [parseEscape, hb]
theorem parseEscape_r {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 114) :
    parseEscape get sz q = .ok ('\r', q + 1) := by simp [parseEscape, hb]
theorem parseEscape_t {get : Nat → Option UInt8} {sz : Nat} {q : Nat} (hb : get q = some 116) :
    parseEscape get sz q = .ok ('\t', q + 1) := by simp [parseEscape, hb]

theorem parseEscape_pair_gen (get : Nat → Option UInt8) (sz : Nat) (pos : Nat) (u l : Nat) (R : List UInt8)
    (hu : 0xD800 ≤ u ∧ u < 0xDC00) (hl : 0xDC00 ≤ l ∧ l < 0xE000)
    (h : AtV get sz pos (hex4 u ++ hex4 l) R) :
    parseEscape get sz (pos + 1) = .ok (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)), pos + 12) := by
  rw [hex4_eq, hex4_eq] at h
  have h1 := h.next
  unfold parseEscape
  rw [h1.get]
  simp only [show ((117 : UInt8) == 34) = false by decide, show ((117 : UInt8) == 92) = false by decide,
    show ((117 : UInt8) == 47) = false by decide, show ((117 : UInt8) == 98) = false by decide,
    show ((117 : UInt8) == 102) = false by decide, show ((117 : UInt8) == 110) = false by decide,
    show ((117 : UInt8) == 114) = false by decide, show ((117 : UInt8) == 116) = false by decide,
    show ((117 : UInt8) == 117) = true by decide, Bool.false_eq_true, ↓reduceIte]
  have h2 := h1.next
  have h2' : AtV get sz (pos + 1 + 1) [hexByte (u / 4096 % 16), hexByte (u / 256 % 16), hexByte (u / 16 % 16),
      hexByte (u % 16)] (92 :: 117 :: [hexByte (l / 4096 % 16), hexByte (l / 256 % 16),
        hexByte (l / 16 % 16), hexByte (l % 16)] ++ R) := by
    exact h2.re rfl (by simp)
  rw [parseHex4_ext (by omega) h2']
  simp only [bind, Except.bind]
  rw [ite_eq_right (by omega), ite_eq_left hu]
  have h3 := h2'.app'.app
  simp only [List.length_cons, List.length_nil] at h3
  have g5 : get (pos + 1 + 5) = some 92 := by
    have := h3.get; rw [show pos + 1 + 1 + 4 = pos + 1 + 5 by omega] at this; exact this
  have g6 : get (pos + 1 + 6) = some 117 := by
    have := h3.next.get; rw [show pos + 1 + 1 + 4 + 1 = pos + 1 + 6 by omega] at this; exact this
  simp only [g5, g6]
  have h4 := h3.next.next
  rw [show pos + 1 + 1 + 4 + 1 + 1 = pos + 1 + 7 by omega] at h4
  rw [parseHex4_ext (by omega) h4]
  simp only []
  rw [ite_eq_left hl, show pos + 1 + 11 = pos + 12 by omega]

/-- A surrogate pair decodes to the astral character it encodes. -/
theorem parseEscape_pair (get : Nat → Option UInt8) (sz : Nat) (pos : Nat) (c : Char) (R : List UInt8)
    (hn : 65536 ≤ c.toNat)
    (h : AtV get sz pos (hex4 (0xD800 + (c.toNat - 0x10000) / 1024) ++
      hex4 (0xDC00 + (c.toNat - 0x10000) % 1024)) R) :
    parseEscape get sz (pos + 1) = .ok (c, pos + 12) := by
  have hmax := toNat_valid c
  generalize hu : 0xD800 + (c.toNat - 0x10000) / 1024 = u at h
  generalize hl : 0xDC00 + (c.toNat - 0x10000) % 1024 = l at h
  rw [parseEscape_pair_gen get sz pos u l R (by omega) (by omega) h]
  have : 0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00) = c.toNat := by omega
  rw [this, Char.ofNat_toNat]

/-- One escaped character is consumed exactly and decodes to itself. -/
theorem strStep (ascii : Bool) (c : Char) {get : Nat → Option UInt8} {sz : Nat} {pos : Nat} {R : List UInt8}
    (acc : String) (h : AtV get sz pos (escapeChar ascii c) R) :
    parseStrBody get sz pos acc =
      parseStrBody get sz (pos + (escapeChar ascii c).length) (acc.push c) := by
  have hv := toNat_valid c
  have hc : c = Char.ofNat c.toNat := (Char.ofNat_toNat c).symm
  by_cases h34 : c.toNat = 34
  · have e : escapeChar ascii c = [92, 34] := by simp [escapeChar, h34]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_quote h.next.get), hc, h34]; rfl
  by_cases h92 : c.toNat = 92
  · have e : escapeChar ascii c = [92, 92] := by simp [escapeChar, h92]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_backslash h.next.get), hc, h92]; rfl
  by_cases h8 : c.toNat = 8
  · have e : escapeChar ascii c = [92, 98] := by simp [escapeChar, h8]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_b h.next.get), hc, h8]; rfl
  by_cases h12 : c.toNat = 12
  · have e : escapeChar ascii c = [92, 102] := by simp [escapeChar, h12]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_f h.next.get), hc, h12]; rfl
  by_cases h10 : c.toNat = 10
  · have e : escapeChar ascii c = [92, 110] := by simp [escapeChar, h10]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_n h.next.get), hc, h10]; rfl
  by_cases h13 : c.toNat = 13
  · have e : escapeChar ascii c = [92, 114] := by simp [escapeChar, h13]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_r h.next.get), hc, h13]; rfl
  by_cases h9 : c.toNat = 9
  · have e : escapeChar ascii c = [92, 116] := by simp [escapeChar, h9]
    rw [e] at h ⊢
    rw [step_backslash h.lt h.get (parseEscape_t h.next.get), hc, h9]; rfl
  by_cases h32 : c.toNat < 32
  · have e : escapeChar ascii c = hex4 c.toNat := by
      simp [escapeChar, h34, h92, h8, h12, h10, h13, h9, h32]
    rw [e] at h ⊢
    have hb : get pos = some 92 := by rw [hex4_eq] at h; exact h.get
    rw [step_backslash (by rw [hex4_eq] at h; exact h.lt) hb (parseEscape_u get sz pos c R (by omega) (by omega) h)]
    rfl
  by_cases hA : ascii = true ∧ 128 ≤ c.toNat
  · by_cases hB : c.toNat < 65536
    · have e : escapeChar ascii c = hex4 c.toNat := by
        simp [escapeChar, h34, h92, h8, h12, h10, h13, h9, h32, hA, hB]
      rw [e] at h ⊢
      have hb : get pos = some 92 := by rw [hex4_eq] at h; exact h.get
      rw [step_backslash (by rw [hex4_eq] at h; exact h.lt) hb (parseEscape_u get sz pos c R hB (by omega) h)]
      rfl
    · have e : escapeChar ascii c = hex4 (0xD800 + (c.toNat - 0x10000) / 1024) ++
          hex4 (0xDC00 + (c.toNat - 0x10000) % 1024) := by
        simp [escapeChar, h34, h92, h8, h12, h10, h13, h9, h32, hA, hB]
      rw [e] at h ⊢
      have hb : get pos = some 92 := by rw [hex4_eq] at h; exact h.get
      rw [step_backslash (by rw [hex4_eq] at h; exact h.lt) hb (parseEscape_pair get sz pos c R (by omega) h)]
      rfl
  · have e : escapeChar ascii c = String.utf8EncodeChar c := by
      unfold escapeChar; simp only [h34, h92, h8, h12, h10, h13, h9, h32, hA, ↓reduceIte]
    rw [e] at h ⊢
    by_cases hlo : c.toNat < 128
    · rw [enc_ascii c hlo] at h ⊢
      have hb := h.get
      have hbn : (UInt8.ofNat c.toNat).toNat = c.toNat := by
        simp; omega
      rw [step_ascii h.lt hb (by intro e; apply h34; rw [← hbn, e]; rfl)
        (by intro e; apply h92; rw [← hbn, e]; rfl) (by omega) (by omega), hbn, ← hc]
      rfl
    · obtain ⟨b, t, ebt, hb128⟩ := enc_high c (by omega)
      have hb : get pos = some b := by rw [ebt] at h; exact h.get
      rw [step_high (by rw [ebt] at h; exact h.lt) hb hb128 (decode_ext h), String.length_utf8EncodeChar]

theorem escapeChar_ne_nil (ascii : Bool) (c : Char) : escapeChar ascii c ≠ [] := by
  unfold escapeChar
  simp only
  repeat' split
  all_goals simp [hex4, String.utf8EncodeChar_ne_nil]

theorem flatMap_escape_length (ascii : Bool) (cs : List Char) :
    cs.length ≤ (cs.flatMap (escapeChar ascii)).length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := List.length_pos_iff.mpr (escapeChar_ne_nil ascii c)
    omega

theorem parseStrBody_ext (ascii : Bool) {get : Nat → Option UInt8} {sz : Nat} {R : List UInt8} :
    ∀ (cs : List Char) (acc : String) (pos : Nat),
      AtV get sz pos (cs.flatMap (escapeChar ascii) ++ [34]) R →
      parseStrBody get sz pos acc = .ok (String.ofList (acc.toList ++ cs), pos + (cs.flatMap (escapeChar ascii)).length + 1)
  | [], acc, pos, h => by
    simp only [List.flatMap_nil, List.nil_append] at h
    rw [strBody_at h.lt h.get]; simp
  | c :: cs, acc, pos, h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    rw [strStep ascii c acc h.assoc]
    rw [parseStrBody_ext ascii cs (acc.push c) _ h.app]
    simp only [String.toList_push, List.append_assoc, List.cons_append, List.nil_append,
      List.flatMap_cons, List.length_append]
    congr 2; omega

/-- **String round trip on any continuation**, both escape modes. -/
theorem parseString_printString_ext (ascii : Bool) (s : String) {get : Nat → Option UInt8} {sz : Nat} {pos : Nat}
    {R : List UInt8} (h : AtV get sz pos (printString ascii s) R) :
    parseString get sz pos = .ok (s, pos + (printString ascii s).length) := by
  unfold parseString
  have hsz := h.le_size
  unfold printString at h hsz ⊢
  have hl := flatMap_escape_length ascii s.toList
  simp only [List.length_cons, List.length_append, List.length_nil] at hsz
  rw [parseStrBody_ext ascii s.toList "" (pos + 1) (by simpa [List.append_assoc] using h.next)]
  simp only [String.toList_empty, List.nil_append, String.ofList_toList, List.length_cons,
    List.length_append, List.length_nil]
  congr 2; omega

end LeanJson
