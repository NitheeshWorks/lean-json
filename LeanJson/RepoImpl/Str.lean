import LeanJson.RepoImpl.Lex

/-!
# RepoImpl: string literals

The body of a string literal, decoded escape by escape and UTF-8 character by
character; recursion on the remaining input.
-/

namespace LeanJson

/-- The (at most four) bytes from `pos` on, up to the end of the view: enough
to decode one UTF-8 character. -/
@[specialize] def window (get : Nat → Option UInt8) (pos : Nat) : ByteArray :=
  match get pos with
  | none => .empty
  | some b0 =>
    match get (pos + 1) with
    | none => ByteArray.empty.push b0
    | some b1 =>
      match get (pos + 2) with
      | none => (ByteArray.empty.push b0).push b1
      | some b2 =>
        match get (pos + 3) with
        | none => ((ByteArray.empty.push b0).push b1).push b2
        | some b3 => (((ByteArray.empty.push b0).push b1).push b2).push b3

/-- The UTF-8 character starting at `pos`, if the bytes there encode one. -/
@[specialize] def decodeChar? (get : Nat → Option UInt8) (pos : Nat) : Option Char :=
  (window get pos).utf8DecodeChar? 0

/-- The body of a string literal from `pos` (just after the opening quote)
to the closing quote; the characters (appended to `acc`) and the position
after the closing quote. -/
@[specialize] def parseStrBody (get : Nat → Option UInt8) (n pos : Nat) (acc : String) :
    Except ParseErr (String × Nat) :=
  if pos < n then
    match get pos with
    | none => .error ⟨.eofWhileParsingString, pos⟩
    | some b =>
      if b == 34 then .ok (acc, pos + 1)
      else if b == 92 then
        match _he : parseEscape get n (pos + 1) with
        | .ok (c, p) => parseStrBody get n p (acc.push c)
        | .error e => .error e
      else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
      else if b < 128 then parseStrBody get n (pos + 1) (acc.push (Char.ofNat b.toNat))
      else
        match decodeChar? get pos with
        | some c => parseStrBody get n (pos + c.utf8Size) (acc.push c)
        | none => .error ⟨.invalidUnicodeCodePoint, pos + 1⟩
  else .error ⟨.eofWhileParsingString, pos⟩
termination_by n - pos
decreasing_by
  all_goals first
    | omega
    | (have := parseEscape_next _he; simp at this; omega)
    | (have := Char.utf8Size_pos c; omega)

/-- The character a one-letter escape (`\"`, `\\`, `\/`, `\b`, `\f`, `\n`,
`\r`, `\t`) stands for, from the byte after the backslash. -/
@[inline] def simpleEscape (b : UInt8) : Option Char :=
  if b == 34 then some '"'
  else if b == 92 then some '\\'
  else if b == 47 then some '/'
  else if b == 98 then some (Char.ofNat 8)
  else if b == 102 then some (Char.ofNat 12)
  else if b == 110 then some '\n'
  else if b == 114 then some '\r'
  else if b == 116 then some '\t'
  else none

theorem parseEscape_simple {get : Nat → Option UInt8} {n q : Nat} {b : UInt8} {c : Char}
    (hg : get q = some b) (hs : simpleEscape b = some c) : parseEscape get n q = .ok (c, q + 1) := by
  unfold parseEscape
  rw [hg]
  simp only [simpleEscape] at hs
  dsimp only
  repeat' split at hs
  all_goals first
    | (cases hs; simp_all)
    | cases hs

/-- The code point of the one-letter escape whose letter is at `q`, or
`0x110000` (no character) when there is none: a scalar, so asking costs no
allocation. -/
@[specialize] def escCode (get : Nat → Option UInt8) (q : Nat) : UInt32 :=
  match get q with
  | some e =>
    match simpleEscape e with
    | some c => c.val
    | none => 0x110000
  | none => 0x110000

theorem escCode_spec {get : Nat → Option UInt8} {q : Nat} (h : escCode get q < 0x110000) :
    ∃ e c, get q = some e ∧ simpleEscape e = some c ∧ Char.ofNat (escCode get q).toNat = c := by
  unfold escCode at h ⊢
  split at h
  · rename_i e he
    split at h
    · rename_i c hc
      exact ⟨e, c, he, hc, Char.ofNat_toNat c⟩
    · simp at h
  · simp at h

/-- `parseStrBody` with the one-letter escapes decoded in the loop itself,
so the common escapes allocate nothing (`parseStrBody_eq_fast`, used by the
compiler through `@[csimp]`). The loop reads the view once, so the read
inlines. -/
@[specialize] def parseStrBodyFast (get : Nat → Option UInt8) (n pos : Nat) (acc : String) :
    Except ParseErr (String × Nat) :=
  if pos < n then
    match get pos with
    | none => .error ⟨.eofWhileParsingString, pos⟩
    | some b =>
      if b == 34 then .ok (acc, pos + 1)
      else if b == 92 then
        let c := escCode get (pos + 1)
        if c < 0x110000 then parseStrBodyFast get n (pos + 2) (acc.push (Char.ofNat c.toNat))
        else
          match _he : parseEscape get n (pos + 1) with
          | .ok (c, p) => parseStrBodyFast get n p (acc.push c)
          | .error e => .error e
      else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
      else if b < 128 then parseStrBodyFast get n (pos + 1) (acc.push (Char.ofNat b.toNat))
      else
        match decodeChar? get pos with
        | some c => parseStrBodyFast get n (pos + c.utf8Size) (acc.push c)
        | none => .error ⟨.invalidUnicodeCodePoint, pos + 1⟩
  else .error ⟨.eofWhileParsingString, pos⟩
termination_by n - pos
decreasing_by
  all_goals first
    | omega
    | (have := parseEscape_next _he; simp at this; omega)
    | (have := Char.utf8Size_pos c; omega)

theorem parseStrBody_eq_fast_at (get : Nat → Option UInt8) (n pos : Nat) (acc : String) :
    parseStrBody get n pos acc = parseStrBodyFast get n pos acc := by
  rw [parseStrBody, parseStrBodyFast]
  by_cases hp : pos < n
  · rw [ite_eq_left hp, ite_eq_left hp]
    cases hg : get pos with
    | none => rfl
    | some b =>
      dsimp only
      by_cases c34 : (b == 34) = true
      · rw [ite_eq_left c34, ite_eq_left c34]
      rw [ite_eq_right c34, ite_eq_right c34]
      by_cases c92 : (b == 92) = true
      · rw [ite_eq_left c92, ite_eq_left c92]
        by_cases hc : escCode get (pos + 1) < 0x110000
        · rw [ite_eq_left hc]
          obtain ⟨e, c, he, hs, hch⟩ := escCode_spec hc
          have := parseEscape_simple (n := n) he hs
          split
          · rename_i c' p h
            rw [this] at h; cases h
            rw [hch]
            exact parseStrBody_eq_fast_at get n (pos + 1 + 1) _
          · rename_i e h; rw [this] at h; cases h
        · rw [ite_eq_right hc]
          split
          · rename_i c p h
            have := parseEscape_next h
            simp at this
            exact parseStrBody_eq_fast_at get n p _
          · rfl
      rw [ite_eq_right c92, ite_eq_right c92]
      by_cases c32 : b < 32
      · rw [ite_eq_left c32, ite_eq_left c32]
      rw [ite_eq_right c32, ite_eq_right c32]
      by_cases c128 : b < 128
      · rw [ite_eq_left c128, ite_eq_left c128]
        exact parseStrBody_eq_fast_at get n (pos + 1) _
      rw [ite_eq_right c128, ite_eq_right c128]
      cases hc : decodeChar? get pos with
      | none => rfl
      | some c =>
        have := Char.utf8Size_pos c
        exact parseStrBody_eq_fast_at get n (pos + c.utf8Size) _
  · rw [ite_eq_right hp, ite_eq_right hp]
termination_by n - pos
decreasing_by all_goals (simp at *; omega)

@[csimp] theorem parseStrBody_eq_fast : @parseStrBody = @parseStrBodyFast := by
  funext get n pos acc; exact parseStrBody_eq_fast_at get n pos acc

/-- A string literal whose opening quote is at `pos`. -/
@[inline] def parseString (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (String × Nat) :=
  parseStrBody get n (pos + 1) ""

end LeanJson
