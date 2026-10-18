import LeanJson.RepoImpl.Parse

/-!
# RepoImpl: partial JSON (`allow_partial`)

`from_json(data, allow_partial=True)` reads JSON that was cut off, such as
the output of a model still streaming it. This is jiter's partial mode:

* A container that reaches the end of input ends there, holding what was
  complete: `'["aa", "bb", "c'` reads as `["aa", "bb"]`. An element or member
  value that the end of input cuts short is dropped (`'[tru'` is `[]`,
  `'{"a": "x'` is `{}`), and so is a member whose key or colon is cut off.
* A container also ends at a byte it does not expect after an element or
  member (`'[1 x'` is `[1]`), and once one container ends early every
  container around it ends too (`'[{"a": 1 ], 5]'` is `[{"a": 1}]`). Nothing
  after the value is checked (`'[1] x'` is `[1]`).
* Errors that are not about the end of input are kept: a bad value, number or
  escape, a key that is not a string, a missing colon, a trailing comma.
* At the top level a scalar cut short is still an error.
* `'trailing-strings'` mode also keeps the decoded part of a cut-off string
  value (not of a key), without a cut-off escape: `'["a\u12'` is `["a"]`.

The parser is `pGo`, the same nesting scheme as `valueGo` (rebased views, a
level budget) over `pStep`, which reuses `valueStep` for scalars and the
lexical productions for strings. `Proofs/Partial.lean` proves that partial
mode changes nothing on a complete document.
-/

namespace LeanJson

/-- How `from_json` treats input that ends early: pydantic-core's
`allow_partial` (`False`/`'off'`, `True`/`'on'`, `'trailing-strings'`). -/
inductive PartialMode where
  | off
  | on
  | trailingStrings
  deriving DecidableEq, Repr, Inhabited

/-- `allow_partial=True` and `False`. -/
instance : Coe Bool PartialMode := ⟨fun b => if b then .on else .off⟩

/-- The errors that say the input ended early. -/
def ErrorKind.isEof : ErrorKind → Bool
  | .eofWhileParsingList | .eofWhileParsingObject | .eofWhileParsingString
  | .eofWhileParsingValue => true
  | _ => false

/-- What one value of partial input reads as. -/
inductive PRes where
  /-- Complete, ending before position `p`. -/
  | done (v : Json) (p : Nat)
  /-- Ended early (the input ran out, or an unexpected byte): what was read;
  every enclosing container ends too. -/
  | stop (v : Json)
  /-- Cut short with nothing to keep (`e`, an end-of-input error). -/
  | drop (e : ParseErr)

/-- `shiftRes` for partial results. -/
@[inline] def shiftP (k : Nat) : Except ParseErr PRes → Except ParseErr PRes
  | .ok (.done v p) => .ok (.done v (p + k))
  | .ok (.drop e) => .ok (.drop ⟨e.kind, e.offset + k⟩)
  | .ok (.stop v) => .ok (.stop v)
  | .error e => .error ⟨e.kind, e.offset + k⟩

/-- The body of a string literal as `parseStrBody` reads it, except that the
end of input ends it: then the characters so far (without a cut-off escape)
and `none`. -/
@[specialize] def partialStrBody (get : Nat → Option UInt8) (n pos : Nat) (acc : String) :
    Except ParseErr (String × Option Nat) :=
  if pos < n then
    match get pos with
    | none => .ok (acc, none)
    | some b =>
      if b == 34 then .ok (acc, some (pos + 1))
      else if b == 92 then
        match _he : parseEscape get n (pos + 1) with
        | .ok (c, p) => partialStrBody get n p (acc.push c)
        | .error e => if e.kind.isEof then .ok (acc, none) else .error e
      else if b < 32 then .error ⟨.controlCharacterWhileParsingString, pos⟩
      else if b < 128 then partialStrBody get n (pos + 1) (acc.push (Char.ofNat b.toNat))
      else
        match decodeChar? get pos with
        | some c => partialStrBody get n (pos + c.utf8Size) (acc.push c)
        | none => .error ⟨.invalidUnicodeCodePoint, pos + 1⟩
  else .ok (acc, none)
termination_by n - pos
decreasing_by
  all_goals first
    | omega
    | (have := parseEscape_next _he; simp at this; omega)
    | (have := Char.utf8Size_pos c; omega)

/-- Array elements of partial input from `pos`, where an element is due. -/
@[specialize] def pElems (child : Nat → Except ParseErr PRes) (get : Nat → Option UInt8)
    (n pos : Nat) (acc : Array Json) : Except ParseErr PRes :=
  match child pos with
  | .error e => .error e
  | .ok (.drop _) => .ok (.stop (.arr acc))
  | .ok (.stop v) => .ok (.stop (.arr (acc.push v)))
  | .ok (.done v j) =>
    let p := skipWs get n j
    match get p with
    | some 44 =>
      let q := skipWs get n (p + 1)
      match get q with
      | some 93 => .error ⟨.trailingComma, q⟩
      | some _ =>
        if _h : pos < q ∧ q < n then pElems child get n q (acc.push v)
        else .error ⟨.expectedSomeValue, q⟩
      | none => .ok (.stop (.arr (acc.push v)))
    | some 93 => .ok (.done (.arr (acc.push v)) (p + 1))
    | some _ => .ok (.stop (.arr (acc.push v)))
    | none => .ok (.stop (.arr (acc.push v)))
termination_by n - pos
decreasing_by all_goals (simp only [q, p] at *; omega)

/-- Object members of partial input from `pos`, which holds the opening
quote of a key. -/
@[specialize] def pMembers (dedup : Bool) (child : Nat → Except ParseErr PRes)
    (get : Nat → Option UInt8) (n pos : Nat) (acc : Fields) : Except ParseErr PRes :=
  match parseString get n pos with
  | .error e => if e.kind.isEof then .ok (.stop (.obj acc.1)) else .error e
  | .ok (k, kn) =>
    let p := skipWs get n kn
    match get p with
    | some 58 =>
      let q := skipWs get n (p + 1)
      match get q with
      | none => .ok (.stop (.obj acc.1))
      | some _ =>
        match child q with
        | .error e => .error e
        | .ok (.drop _) => .ok (.stop (.obj acc.1))
        | .ok (.stop v) => .ok (.stop (.obj (acc.add dedup k v).1))
        | .ok (.done v j) =>
          let p3 := skipWs get n j
          match get p3 with
          | some 44 =>
            let q2 := skipWs get n (p3 + 1)
            match get q2 with
            | some 34 =>
              if _h : pos < q2 ∧ q2 < n then pMembers dedup child get n q2 (acc.add dedup k v)
              else .error ⟨.keyMustBeAString, q2⟩
            | some 125 => .error ⟨.trailingComma, q2⟩
            | some _ => .error ⟨.keyMustBeAString, q2⟩
            | none => .ok (.stop (.obj (acc.add dedup k v).1))
          | some 125 => .ok (.done (.obj (acc.add dedup k v).1) (p3 + 1))
          | some _ => .ok (.stop (.obj (acc.add dedup k v).1))
          | none => .ok (.stop (.obj (acc.add dedup k v).1))
    | some _ => .error ⟨.expectedColon, p⟩
    | none => .ok (.stop (.obj acc.1))
termination_by n - pos
decreasing_by all_goals (simp only [q2, p3] at *; omega)

/-- A scalar's result in partial mode: an end-of-input error drops it. -/
@[inline] def scalarP : Except ParseErr (Json × Nat) → Except ParseErr PRes
  | .ok (v, p) => .ok (.done v p)
  | .error e => if e.kind.isEof then .ok (.drop e) else .error e

/-- One value of partial input, its first byte at position `0` of the view;
`ts` keeps cut-off string values (`'trailing-strings'`). -/
@[specialize] def pStep (cfg : ParseCfg) (ts : Bool) (child : Nat → Except ParseErr PRes)
    (get : Nat → Option UInt8) (n : Nat) : Except ParseErr PRes :=
  match get 0 with
  | some 91 =>
    let p := skipWs get n 1
    match get p with
    | some 93 => .ok (.done (.arr #[]) (p + 1))
    | some _ => pElems child get n p #[]
    | none => .ok (.stop (.arr #[]))
  | some 123 =>
    let p := skipWs get n 1
    match get p with
    | some 125 => .ok (.done (.obj #[]) (p + 1))
    | some 34 => pMembers cfg.dedupKeys child get n p .empty
    | some _ => .error ⟨.keyMustBeAString, p⟩
    | none => .ok (.stop (.obj #[]))
  | some 34 =>
    if ts then
      match partialStrBody get n 1 "" with
      | .ok (s, some p) => .ok (.done (.str s) p)
      | .ok (s, none) => .ok (.stop (.str s))
      | .error e => .error e
    else scalarP (valueStep cfg (fun _ => .error ⟨.recursionLimitExceeded, 0⟩) get n)
  | _ => scalarP (valueStep cfg (fun _ => .error ⟨.recursionLimitExceeded, 0⟩) get n)

/-- `valueGo` for partial input. -/
@[specialize] def pGo (cfg : ParseCfg) (ts : Bool) (get : Nat → Option UInt8) (n : Nat) :
    (d base : Nat) → Except ParseErr PRes
  | 0, _ => .error ⟨.recursionLimitExceeded, 0⟩
  | d + 1, base =>
    pStep cfg ts (fun j => shiftP j (pGo cfg ts get n d (base + j))) (fun k => get (base + k)) (n - base)

/-- A whole document of partial input under `mode` (not `.off`): optional
whitespace and one value; what follows it is not read. A value cut short
with nothing to keep is the end-of-input error. -/
@[specialize] def parsePartialIn (cfg : ParseCfg) (mode : PartialMode) (get : Nat → Option UInt8)
    (n : Nat) : Except ParseErr Json :=
  let q := skipWs get n 0
  match get q with
  | none => .error ⟨.eofWhileParsingValue, q⟩
  | some _ =>
    match shiftP q (pGo cfg (mode == .trailingStrings) get n (cfg.budget n) q) with
    | .ok (.done v _) => .ok v
    | .ok (.stop v) => .ok v
    | .ok (.drop e) => .error e
    | .error e => .error e

/-- `parsePartialIn` on a buffer. -/
def parsePartialWith (cfg : ParseCfg) (mode : PartialMode) (bs : ByteArray) : Except ParseErr Json :=
  parsePartialIn cfg mode (bv bs) bs.size

end LeanJson
