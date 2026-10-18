import LeanJson.RepoImpl.Lex

/-!
# RepoImpl: string literals

The body of a string literal, decoded escape by escape and UTF-8 character by
character; recursion on the remaining input.
-/

namespace LeanJson

/-- The body of a string literal from `pos` (just after the opening quote)
to the closing quote; the characters (appended to `acc`) and the position
after the closing quote. -/
def parseStrBody (bs : ByteArray) (pos : Nat) (acc : String) : Except ParseErr (String × Nat) :=
  if h : pos < bs.size then
    let b := bs[pos]
    if b == 34 then .ok (acc, pos + 1)
    else if b == 92 then
      match he : parseEscape bs (pos + 1) with
      | .ok (c, p) => parseStrBody bs p (acc.push c)
      | .error e => .error e
    else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
    else if b < 128 then parseStrBody bs (pos + 1) (acc.push (Char.ofNat b.toNat))
    else
      match bs.utf8DecodeChar? pos with
      | some c => parseStrBody bs (pos + c.utf8Size) (acc.push c)
      | none => .error ⟨.invalidUnicodeCodePoint, pos + 1⟩
  else .error ⟨.eofWhileParsingString, pos⟩
termination_by bs.size - pos
decreasing_by
  all_goals first
    | omega
    | (have := parseEscape_next he; simp at this; omega)
    | (have := Char.utf8Size_pos c; omega)

/-- A string literal whose opening quote is at `pos`. -/
def parseString (bs : ByteArray) (pos : Nat) : Except ParseErr (String × Nat) :=
  parseStrBody bs (pos + 1) ""

end LeanJson
