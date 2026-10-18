/-!
# DataTypes: the JSON value, its numbers, and parse errors

`Json` is this library's own inductive rather than a re-export of core
`Lean.Json`. The reasons are recorded in `CONTRIBUTING.md` ("Why not
`Lean.Json`"): core objects are a sorted `Std.TreeMap.Raw`, which forgets
key order and duplicate keys, and core `JsonNumber` cannot tell `1` from
`1e0` or carry `-0.0`. pydantic-core (via jiter) keeps all three, and an
exact round trip needs them. Conversions to and from `Lean.Json` live in
`LeanJson/RepoImpl/Access.lean`.

Invariants are fields (`Decimal.h_norm`), never comments.
-/

namespace LeanJson

/-- An exact decimal, `(-1)^neg * mant * 10^exp`, in normal form: the
mantissa has no trailing decimal zero, and zero is stored as `mant = 0,
exp = 0`. The sign is a separate bit so that `-0.0` survives a round trip,
as it does through Python's `float`. This is how a JSON number with a
fraction or an exponent (pydantic-core: a float) is held, exactly, before
anyone rounds it to an IEEE double. -/
structure Decimal where
  neg : Bool
  mant : Nat
  exp : Int
  h_norm : (mant = 0 ∧ exp = 0) ∨ mant % 10 ≠ 0
  deriving DecidableEq

instance : Repr Decimal where
  reprPrec d _ := s!"Decimal.mk {d.neg} {d.mant} {d.exp}"

/-- A JSON number as pydantic-core's parser classifies it: a literal with no
fraction and no exponent is an integer (any size: Python `int`, jiter
`Int`/`BigInt`); anything else is a float, held as an exact `Decimal`. The
three non-finite floats are not JSON (RFC 8259); they arise only from the
lenient parser (`ParseCfg.allowInfNan`, pydantic-core's `allow_inf_nan`, the
`from_json` default) and from `Float` values, and print as `to_json`'s
`inf_nan_mode` says. -/
inductive Number where
  | int (i : Int)
  | float (d : Decimal)
  /-- `NaN` -/
  | nan
  /-- `Infinity` -/
  | inf
  /-- `-Infinity` -/
  | negInf
  deriving DecidableEq, Repr

/-- Finite: an integer or a decimal. -/
def Number.isFinite : Number → Bool
  | .int _ | .float _ => true
  | _ => false

/-- A JSON value (RFC 8259, plus the non-finite numbers of the lenient mode).
Arrays are `Array`s (one pointer per element, as a Python `list`); objects
are arrays of members in document order. `from_json` collapses duplicate keys
as a Python `dict` does (first position, last value; `ParseCfg.dedupKeys`);
with that off they are kept, as jiter's `JsonValue` keeps them, and lookup
(`Json.getObjVal?`, `j["key"]?`) is last-wins. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Number)
  | str (s : String)
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json))
  deriving Inhabited

mutual
/-- Structural decidable equality (the derive handler does not cover nested
inductives). -/
def Json.decEq : (a b : Json) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .num a, .num b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .str a, .str b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .arr ⟨a⟩, .arr ⟨b⟩ =>
    match Json.decEqList a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .obj ⟨a⟩, .obj ⟨b⟩ =>
    match Json.decEqFields a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .null, .bool _ | .null, .num _ | .null, .str _ | .null, .arr _ | .null, .obj _
  | .bool _, .null | .bool _, .num _ | .bool _, .str _ | .bool _, .arr _ | .bool _, .obj _
  | .num _, .null | .num _, .bool _ | .num _, .str _ | .num _, .arr _ | .num _, .obj _
  | .str _, .null | .str _, .bool _ | .str _, .num _ | .str _, .arr _ | .str _, .obj _
  | .arr _, .null | .arr _, .bool _ | .arr _, .num _ | .arr _, .str _ | .arr _, .obj _
  | .obj _, .null | .obj _, .bool _ | .obj _, .num _ | .obj _, .str _ | .obj _, .arr _ =>
    isFalse (fun e => by cases e)
def Json.decEqList : (a b : List Json) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
  | x :: xs, y :: ys =>
    match Json.decEq x y, Json.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
def Json.decEqFields : (a b : List (String × Json)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
  | (k, x) :: xs, (l, y) :: ys =>
    if hk : k = l then
      match Json.decEq x y, Json.decEqFields xs ys with
      | isTrue h1, isTrue h2 => isTrue (hk ▸ h1 ▸ h2 ▸ rfl)
      | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
      | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
    else isFalse (fun e => by cases e; exact hk rfl)
end

instance : DecidableEq Json := Json.decEq

/-- A location inside a JSON document: object keys and array indices from
the root, as pydantic's `loc` tuples (`('field_a', 2)`). -/
abbrev Loc := List (String ⊕ Nat)

/-- Why a parse failed. The constructors and their `message`s follow jiter's
`JsonErrorType`, which is what pydantic-core puts in a `json_invalid` error. -/
inductive ErrorKind where
  | eofWhileParsingList
  | eofWhileParsingObject
  | eofWhileParsingString
  | eofWhileParsingValue
  | expectedColon
  | expectedListCommaOrEnd
  | expectedObjectCommaOrEnd
  | expectedSomeIdent
  | expectedSomeValue
  | invalidEscape
  | invalidNumber
  | invalidUnicodeCodePoint
  | controlCharacterWhileParsingString
  | keyMustBeAString
  | loneLeadingSurrogateInHexEscape
  | trailingComma
  | trailingCharacters
  | unexpectedEndOfHexEscape
  | numberOutOfRange
  /-- jiter's nesting limit (`ParseCfg.maxDepth`): a value inside too many
  containers. -/
  | recursionLimitExceeded
  deriving DecidableEq, Repr, Inhabited

/-- The message text, as jiter (and serde_json) print it. -/
def ErrorKind.message : ErrorKind → String
  | .eofWhileParsingList => "EOF while parsing a list"
  | .eofWhileParsingObject => "EOF while parsing an object"
  | .eofWhileParsingString => "EOF while parsing a string"
  | .eofWhileParsingValue => "EOF while parsing a value"
  | .expectedColon => "expected `:`"
  | .expectedListCommaOrEnd => "expected `,` or `]`"
  | .expectedObjectCommaOrEnd => "expected `,` or `}`"
  | .expectedSomeIdent => "expected ident"
  | .expectedSomeValue => "expected value"
  | .invalidEscape => "invalid escape"
  | .invalidNumber => "invalid number"
  | .invalidUnicodeCodePoint => "invalid unicode code point"
  | .controlCharacterWhileParsingString =>
    "control character (\\u0000-\\u001F) found while parsing a string"
  | .keyMustBeAString => "key must be a string"
  | .loneLeadingSurrogateInHexEscape => "lone leading surrogate in hex escape"
  | .trailingComma => "trailing comma"
  | .trailingCharacters => "trailing characters"
  | .unexpectedEndOfHexEscape => "unexpected end of hex escape"
  | .numberOutOfRange => "number out of range"
  | .recursionLimitExceeded => "recursion limit exceeded"

/-- A low-level parse error: what went wrong and the byte offset where it was
detected (an offset equal to the input size means end of input). -/
structure ParseErr where
  kind : ErrorKind
  offset : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A parse error as the public API reports it: the byte offset plus jiter's
1-based line and column, ready to print as pydantic-core's `json_invalid`
context (`description`, e.g. `EOF while parsing a string at line 1 column 7`). -/
structure JsonError where
  kind : ErrorKind
  offset : Nat
  line : Nat
  column : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `"<message> at line <l> column <c>"`: the `error` field of pydantic-core's
`json_invalid` context. The full pydantic message is `"Invalid JSON: " ++`
this. -/
def JsonError.description (e : JsonError) : String :=
  s!"{e.kind.message} at line {e.line} column {e.column}"

instance : ToString JsonError := ⟨JsonError.description⟩

/-- How a non-finite number prints, as pydantic-core's `inf_nan_mode` /
`ser_json_inf_nan`: `constants` writes `NaN`, `Infinity`, `-Infinity`
(`to_json`'s default; not valid RFC 8259 JSON), `null` writes `null`,
`strings` writes `"NaN"`, `"Infinity"`, `"-Infinity"`. -/
inductive InfNanMode where
  | null
  | constants
  | strings
  deriving DecidableEq, Repr, Inhabited

/-- Printer options, mirroring pydantic-core's `to_json(indent=, ensure_ascii=)`.
`indent = none` is the compact form (`,` and `:` with no spaces, as
Starlette's `JSONResponse` emits); `indent = some k` is serde_json's pretty
form with `k` spaces per level. `ensureAscii` escapes every non-ASCII
character as `\uXXXX` (astral characters as a surrogate pair). -/
structure PrintOpts where
  indent : Option Nat := none
  ensureAscii : Bool := false
  /-- How NaN and the infinities print (pydantic-core's `inf_nan_mode`). -/
  infNan : InfNanMode := .constants
  /-- Python `json.dumps` separators, `", "` and `": "`, in the one-line
  layout (`indent = none`); the pretty layout already uses `": "` and puts a
  newline after `,`. Off by default (`to_json` prints `,` and `:`). -/
  spaced : Bool := false
  deriving DecidableEq, Repr, Inhabited

end LeanJson
