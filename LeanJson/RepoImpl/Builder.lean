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
def printTo (o : PrintOpts) (d : Nat) (acc : ByteArray) : Json → ByteArray
  | .null => pushList acc litNull
  | .bool true => pushList acc litTrue
  | .bool false => pushList acc litFalse
  | .num n => pushList acc (printNumberIn o n)
  | .str s => pushString o.ensureAscii acc s
  | .arr ⟨[]⟩ => (acc.push 91).push 93
  | .arr ⟨x :: xs⟩ =>
    (pushList (printElemsTo o (d + 1) (printTo o (d + 1) (pushList (acc.push 91) (o.nl (d + 1))) x) xs)
      (o.nl d)).push 93
  | .obj ⟨[]⟩ => (acc.push 123).push 125
  | .obj ⟨(k, v) :: kvs⟩ =>
    (pushList (printMembersTo o (d + 1)
      (printTo o (d + 1) (pushList (pushString o.ensureAscii (pushList (acc.push 123) (o.nl (d + 1))) k)
        o.colon) v) kvs) (o.nl d)).push 125
def printElemsTo (o : PrintOpts) (d : Nat) (acc : ByteArray) : List Json → ByteArray
  | [] => acc
  | x :: xs => printElemsTo o d (printTo o d (pushList (acc.push 44) (o.sep d)) x) xs
def printMembersTo (o : PrintOpts) (d : Nat) (acc : ByteArray) : List (String × Json) → ByteArray
  | [] => acc
  | (k, v) :: kvs =>
    printMembersTo o d
      (printTo o d (pushList (pushString o.ensureAscii (pushList (acc.push 44) (o.sep d)) k) o.colon) v) kvs
end

/-- The printing of `v` under `o`, as bytes. -/
def printBA (o : PrintOpts) (v : Json) : ByteArray := printTo o 0 .empty v

end LeanJson
