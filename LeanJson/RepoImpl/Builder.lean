import LeanJson.RepoImpl.Print

/-!
# RepoImpl: the printer as a byte builder

`printTo o d acc v` appends the printing of `v` to the buffer `acc` one
byte at a time, so printing is linear in the output however deep the
nesting (the list-based `printWith` copies a child once per level). It is
proved equal to `printWith` (`Proofs/Builder.lean`), which stays the
specification.
-/

namespace LeanJson

/-- Append a list of bytes. -/
def pushList (acc : ByteArray) (l : List UInt8) : ByteArray := l.foldl ByteArray.push acc

/-- Append a string literal, escaping as `printString` does. -/
def pushString (ascii : Bool) (acc : ByteArray) (s : String) : ByteArray :=
  (s.toList.foldl (fun a c => pushList a (escapeChar ascii c)) (acc.push 34)).push 34

mutual
/-- Append the printing of `v` at depth `d`. Containers are walked by index,
never converted to a list. -/
def printTo (o : PrintOpts) (d : Nat) (acc : ByteArray) : Json → ByteArray
  | .null => pushList acc litNull
  | .bool true => pushList acc litTrue
  | .bool false => pushList acc litFalse
  | .num n => pushList acc (printNumberIn o n)
  | .str s => pushString o.ensureAscii acc s
  | .arr a =>
    if h : 0 < a.size then
      (pushList (printElemsFrom o (d + 1) (printTo o (d + 1) (pushList (acc.push 91) (o.nl (d + 1))) a[0])
        a 1) (o.nl d)).push 93
    else (acc.push 91).push 93
  | .obj a =>
    if h : 0 < a.size then
      (pushList (printMembersFrom o (d + 1)
        (printTo o (d + 1) (pushList (pushString o.ensureAscii (pushList (acc.push 123) (o.nl (d + 1)))
          a[0].1) o.colon) a[0].2) a 1) (o.nl d)).push 125
    else (acc.push 123).push 125
termination_by v => (sizeOf v, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_getElem a 0 h; omega)
    | (have := Array.sizeOf_getElem a 0 h
       have : sizeOf a[0].2 < sizeOf a[0] := by
         cases a[0]; simp; omega
       omega)
    | (apply Prod.Lex.left; omega)
/-- Append `,` and element `i`, then the rest, from index `i` on. -/
def printElemsFrom (o : PrintOpts) (d : Nat) (acc : ByteArray) (a : Array Json) (i : Nat) : ByteArray :=
  if h : i < a.size then printElemsFrom o d (printTo o d (pushList (acc.push 44) (o.sep d)) a[i]) a (i + 1)
  else acc
termination_by (sizeOf a, a.size - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; have := Array.sizeOf_getElem a i h; omega)
    | (apply Prod.Lex.left
       have := Array.sizeOf_getElem a i h
       have : sizeOf a[i].2 < sizeOf a[i] := by cases a[i]; simp; omega
       omega)
/-- Append `,` and member `i`, then the rest, from index `i` on. -/
def printMembersFrom (o : PrintOpts) (d : Nat) (acc : ByteArray) (a : Array (String × Json)) (i : Nat) :
    ByteArray :=
  if h : i < a.size then
    printMembersFrom o d
      (printTo o d (pushList (pushString o.ensureAscii (pushList (acc.push 44) (o.sep d)) a[i].1) o.colon)
        a[i].2) a (i + 1)
  else acc
termination_by (sizeOf a, a.size - i)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; have := Array.sizeOf_getElem a i h; omega)
    | (apply Prod.Lex.left
       have := Array.sizeOf_getElem a i h
       have : sizeOf a[i].2 < sizeOf a[i] := by cases a[i]; simp; omega
       omega)
end

/-- The printing of `v` under `o`, as bytes. -/
def printBA (o : PrintOpts) (v : Json) : ByteArray := printTo o 0 .empty v

end LeanJson
