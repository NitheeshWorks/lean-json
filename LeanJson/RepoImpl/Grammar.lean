import LeanJson.RepoImpl.Parse
import Keel.Parse

/-!
# RepoImpl: the value grammar as a Keel parser

`valueNode cfg h` is one JSON value as a `Keel.Parser` body: the grammar's
`valueStep`, on the tokens from the cursor, with the recursive handle `h`
reading the values nested in it. `jsonParser cfg` ties the knot with Keel's
depth-bounded fixpoint `Parser.fixDepth` at jiter's nesting limit (or `fix`
with no limit). It is the decoder of the value codec (`Proofs/Codec.lean`).

The fast parser (`valueGo`) and this one share the grammar, so they cannot
drift; `Proofs/Grammar.lean` proves they agree on every success, and the
laws of `fixDepth` (`fixDepth_ok`, `fixDepth_eq_fix`) then say what the depth
limit does. Its errors are Keel's (`unexpected`, `depthExceeded`); the fast
parser keeps jiter's kinds and offsets.
-/

namespace LeanJson

open Keel

/-- A grammar result as a Keel result: the value and its end, or a failure
(as `unexpected`) where it was detected, positions kept within the input. -/
def toResult {ε α : Type} [ParseError ε] (n : Nat) : Except ParseErr (α × Nat) → Result ε α
  | .ok (v, p) => .ok v (min p n)
  | .error e => .error ParseError.unexpected (min e.offset n)

/-- A Keel result as a grammar result (a failure's kind is not kept). -/
def ofResult {ε α : Type} : Result ε α → Except ParseErr (α × Nat)
  | .ok v p => .ok (v, p)
  | .error _ p => .error ⟨.expectedSomeValue, p⟩

theorem toResult_pos_le {ε α : Type} [ParseError ε] (n : Nat) (r : Except ParseErr (α × Nat)) :
    (toResult (ε := ε) n r).pos ≤ n := by
  rcases r with e | ⟨v, p⟩ <;> exact Nat.min_le_right _ _

/-- A lexer of the grammar (`parseString`, `parseNumber`: a token whose
first byte is at position `0` of a view) as a Keel parser. -/
def lexer {ε α : Type} [ParseError ε] (f : (Nat → Option UInt8) → Nat → Except ParseErr (α × Nat)) :
    Parser UInt8 ε α where
  run s i :=
    let L := Input.rest s i
    (toResult L.length (f (lv L) L.length)).shift i
  run_eq s i := by simp [Input.rest]
  pos_le l := by simpa [Input.rest] using toResult_pos_le _ _

/-- A JSON string literal, as a Keel parser. -/
def stringParser {ε : Type} [ParseError ε] : Parser UInt8 ε String := lexer fun get n => parseString get n 0

/-- A JSON number literal under `cfg`, as a Keel parser. -/
def numberParser (cfg : ParseCfg) {ε : Type} [ParseError ε] : Parser UInt8 ε Number :=
  lexer fun get n => parseNumber cfg get n 0

/-- **One JSON value as a Keel parser body**: `valueStep` on the tokens from
the cursor, `h` reading the values nested in it. -/
def valueNode (cfg : ParseCfg) {ε : Type} [ParseError ε] (h : Parser UInt8 ε Json) :
    Parser UInt8 ε Json where
  run s i :=
    let L := Input.rest s i
    (toResult L.length (valueStep cfg (fun j => ofResult (h.run L j)) (lv L) L.length)).shift i
  run_eq s i := by simp [Input.rest]
  pos_le l := by simpa [Input.rest] using toResult_pos_le _ _

/-- **The JSON value parser, the Keel way**: `valueNode` tied by
`Parser.fixDepth` at jiter's nesting limit, or by `Parser.fix` with none. -/
def jsonParser (cfg : ParseCfg) {ε : Type} [ParseError ε] : Parser UInt8 ε Json :=
  match cfg.maxDepth with
  | some L => Parser.fixDepth L (valueNode cfg)
  | none => Parser.fix (valueNode cfg)

end LeanJson
