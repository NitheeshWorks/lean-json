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

/-- A string literal whose opening quote is at `pos`. -/
@[inline] def parseString (get : Nat → Option UInt8) (n pos : Nat) : Except ParseErr (String × Nat) :=
  parseStrBody get n (pos + 1) ""

end LeanJson
