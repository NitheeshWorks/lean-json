import LeanJson

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/pydantic/pydantic-core,
`tests/`) in Lean and names it, so `docs/traceability.toml` can point at both.
Cases marked `from_json (2.50.1)` pin error texts and columns that the upstream
suite does not test directly; they were checked against the released
pydantic-core 2.50.1. No upstream code is copied.

Run with `lake exe conformance`.
-/

open LeanJson

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_json.py::test_dict`. -/
  upstream : String
  name : String
  run : IO Bool

/-- The `json_invalid` context string for an input, or the compact re-print. -/
def outcome (s : String) : String :=
  match from_json s with
  | .ok v => printStr v.val
  | .error e => "ERR " ++ e.description

def outcomeBytes (b : ByteArray) : String :=
  match from_json b with
  | .ok v => printStr v.val
  | .error e => "ERR " ++ e.description

def expect (got want : String) : IO Bool := do
  if got == want then pure true
  else do IO.println s!"      got  {got}\n      want {want}"; pure false

def ok (upstream name input want : String) : Case :=
  ⟨upstream, name, expect (outcome input) want⟩

def err (upstream name input want : String) : Case :=
  ⟨upstream, name, expect (outcome input) ("ERR " ++ want)⟩

def toJsonStr {α : Type} [IntoJson α] (v : α) (indent : Option Nat := none) (ascii := false) : String :=
  (String.fromUTF8? (to_json v indent ascii).val).getD "<invalid utf-8>"

def rep (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

def probe := "from_json (2.50.1)"

def cases : List Case := [
  -- tests/test_json.py
  err "tests/test_json.py::test_json_invalid" "unterminated string" "\"foobar"
    "EOF while parsing a string at line 1 column 7",
  err "tests/test_json.py::test_json_invalid" "trailing comma, multi-line" "[1,\n2,\n3,]"
    "trailing comma at line 3 column 3",
  err "tests/test_json.py::test_partial_parse" "partial input is an error" "[\"aa\", \"bb\", \"c"
    "EOF while parsing a string at line 1 column 15",
  ok "tests/test_json.py::test_int" "big integer" ("1" ++ rep '0' 40) ("1" ++ rep '0' 40),
  ok "tests/test_json.py::test_int" "123.0 is a float" "123.0" "123.0",
  ok "tests/test_json.py::test_float" "123.4" "123.4" "123.4",
  ok "tests/test_json.py::test_input_types" "array with spaces" "[1, 2, 3]" "[1,2,3]",
  ⟨"tests/test_json.py::test_input_types", "bytes input", expect (outcomeBytes "[1, 2, 3]".toUTF8) "[1,2,3]"⟩,
  ⟨"tests/test_json.py::test_dict", "duplicate keys: last value wins",
    expect (match from_json "{\"1\": 1, \"1\": 2}" with
      | .ok v => toString (v.val.getObjVal? "1") ++ " " ++ printStr (.obj (Json.dedupKeys (v.val.getObj?.getD [])))
      | .error e => e.description) "(some 2) {\"1\":2}"⟩,
  ⟨"tests/test_json.py::test_typed_dict", "duplicate field: last wins, position kept",
    expect (match from_json "{\"field_a\": \"a\", \"field_a\": \"b\", \"field_b\": 1}" with
      | .ok v => printStr (.obj (Json.dedupKeys (v.val.getObj?.getD [])))
      | .error e => e.description) "{\"field_a\":\"b\",\"field_b\":1}"⟩,
  ok "tests/test_json.py::test_dict_any_value" "mixed values" "{\"1\": 1, \"2\": \"a\", \"3\": null}"
    "{\"1\":1,\"2\":\"a\",\"3\":null}",
  ⟨"tests/test_json.py::test_to_json", "to_json([1, 2])", expect (toJsonStr [1, 2]) "[1,2]"⟩,
  ⟨"tests/test_json.py::test_to_json", "to_json([1, 2], indent=2)",
    expect (toJsonStr [1, 2] (some 2)) "[\n  1,\n  2\n]"⟩,
  ⟨"tests/test_json.py::test_to_json", "to_json(['à', 'é'])", expect (toJsonStr ["à", "é"]) "[\"à\",\"é\"]"⟩,
  ⟨"tests/test_json.py::test_to_json", "to_json(['à', 'é'], indent=2)",
    expect (toJsonStr ["à", "é"] (some 2)) "[\n  \"à\",\n  \"é\"\n]"⟩,
  ⟨"tests/test_json.py::test_to_json", "to_json(['à', 'é'], indent=2, ensure_ascii=True)",
    expect (toJsonStr ["à", "é"] (some 2) true) "[\n  \"\\u00e0\",\n  \"\\u00e9\"\n]"⟩,
  ⟨"tests/test_json.py::test_to_jsonable_python_schema_serializer", "nested objects, compact",
    expect (toJsonStr (json% {"myFoo": 1, "myInners": [{"myFoo": 2, "myInners": []}]}))
      "{\"myFoo\":1,\"myInners\":[{\"myFoo\":2,\"myInners\":[]}]}"⟩,
  err "tests/test_json.py::test_inf_nan_allow" "Infinity is rejected (deviation)" "Infinity"
    "expected value at line 1 column 1",
  -- tests/validators/test_json.py, tests/validators/test_int.py
  ok "tests/validators/test_json.py::test_any" "object" "{\"a\": 1}" "{\"a\":1}",
  ok "tests/validators/test_json.py::test_any" "string" "\"a\"" "\"a\"",
  ok "tests/validators/test_json.py::test_any" "list" "[1, 2, 3, \"4\"]" "[1,2,3,\"4\"]",
  err "tests/validators/test_json.py::test_any" "non-string key" "{1: 2}"
    "key must be a string at line 1 column 2",
  err "tests/validators/test_json.py::test_any_python" "garbage" "xx" "expected value at line 1 column 1",
  ⟨"tests/validators/test_json.py::test_any_python", "garbage bytes",
    expect (outcomeBytes "xx".toUTF8) "ERR expected value at line 1 column 1"⟩,
  err "tests/validators/test_json.py::test_dict_key" "bare word" "x" "expected value at line 1 column 1",
  ok "tests/validators/test_int.py::test_long_json" "400-digit negative" ("-" ++ rep '1' 400) ("-" ++ rep '1' 400),
  err "tests/validators/test_int.py::test_long_json" "nan is not JSON" "nan" "expected ident at line 1 column 2",
  -- tests/serializers
  ⟨"tests/serializers/test_simple.py::test_simple_serializers", "float 1.0", expect (toJsonStr (1.0 : Float)) "1.0"⟩,
  ⟨"tests/serializers/test_simple.py::test_simple_serializers", "float 42.31415",
    expect (toJsonStr (42.31415 : Float)) "42.31415"⟩,
  ⟨"tests/serializers/test_simple.py::test_simple_serializers", "float 42.0 (subclass)",
    expect (toJsonStr (42 : Float)) "42.0"⟩,
  ⟨"tests/serializers/test_simple.py::test_numpy_float", "inf serialises as null",
    expect (toJsonStr (1.0 / 0.0 : Float)) "null"⟩,
  ⟨"tests/serializers/test_json.py::test_list_json", "['a', [1, 2], None]",
    expect (toJsonStr (json% ["a", [1, 2], null])) "[\"a\",[1,2],null]"⟩,
  ⟨"tests/serializers/test_json.py::test_custom_serializer", "{1: 2} with string key",
    expect (toJsonStr (json% {"1": 2})) "{\"1\":2}"⟩,
  ⟨"tests/serializers/test_json.py::test_json_int", "to_json(1)", expect (toJsonStr (1 : Nat)) "1"⟩,
  -- jiter behaviour pinned against the release
  err probe "number of 4301 digits" (rep '1' 4301) "number out of range at line 1 column 4301",
  err probe "negative number of 4300 digits" ("-" ++ rep '1' 4300) "number out of range at line 1 column 4301",
  ok probe "4300 digits accepted" (rep '9' 4300) (rep '9' 4300),
  err probe "long integer part of a float" (rep '1' 4301 ++ ".0") "number out of range at line 1 column 4302",
  ok probe "long fraction accepted" ("0." ++ rep '1' 5000) ("0." ++ rep '1' 5000),
  ok probe "float layout" "[1e16, 1.5e300, 1e-7, 0.000001, 1e-5, 100000.0, 1e15, -0.0, 0e5, 1E-2, 123.456e10]"
    "[1e+16,1.5e+300,1e-7,1e-6,0.00001,100000.0,1000000000000000.0,-0.0,0.0,0.01,1234560000000.0]",
  ok probe "-0 is the integer 0" "-0" "0",
  ok probe "huge exponent kept exactly" "1e10000000000" "1e+10000000000",
  err probe "lone trailing surrogate" "\"\\udc00\"" "lone leading surrogate in hex escape at line 1 column 7",
  err probe "high surrogate then non-low escape" "\"\\ud800\\u0041\"" "lone leading surrogate in hex escape at line 1 column 13",
  err probe "high surrogate then high" "\"\\ud800\\ud800\"" "lone leading surrogate in hex escape at line 1 column 13",
  err probe "high surrogate then \\n" "\"\\ud800\\n\"" "unexpected end of hex escape at line 1 column 9",
  err probe "high surrogate then quote" "\"\\ud800\"" "unexpected end of hex escape at line 1 column 8",
  err probe "high surrogate at end" "\"\\ud800" "EOF while parsing a string at line 1 column 7",
  err probe "short \\u escape" "\"\\u12\"" "EOF while parsing a string at line 1 column 6",
  err probe "bad hex in second escape" "\"\\ud800\\udc0x\"" "invalid escape at line 1 column 13",
  err probe "bad hex digit" "\"\\uzzzz\"" "invalid escape at line 1 column 4",
  err probe "unknown escape" "\"\\x\"" "invalid escape at line 1 column 3",
  ok probe "surrogate pair" "\"\\udbff\\udfff\"" ("\"" ++ (Char.ofNat 0x10FFFF).toString ++ "\""),
  ok probe "escaped slash" "\"\\/\"" "\"/\"",
  err probe "control character" "\"\x01\"" "control character (\\u0000-\\u001F) found while parsing a string at line 1 column 2",
  ⟨probe, "invalid UTF-8 lead", expect (outcomeBytes ⟨#[34, 0xc0, 0x80, 34]⟩) "ERR invalid unicode code point at line 1 column 3"⟩,
  ⟨probe, "invalid UTF-8 later", expect (outcomeBytes ⟨#[34, 97, 98, 0xff, 34]⟩) "ERR invalid unicode code point at line 1 column 5"⟩,
  err probe "EOF in list" "[1" "EOF while parsing a list at line 1 column 2",
  err probe "EOF after comma" "[1," "EOF while parsing a value at line 1 column 3",
  err probe "EOF in object" "{\"a\"" "EOF while parsing an object at line 1 column 4",
  err probe "EOF after colon" "{\"a\":" "EOF while parsing a value at line 1 column 5",
  err probe "EOF after member" "{\"a\":1" "EOF while parsing an object at line 1 column 6",
  err probe "missing colon" "{\"a\" 1}" "expected `:` at line 1 column 6",
  err probe "comma as key" "{,}" "key must be a string at line 1 column 2",
  err probe "comma as element" "[,]" "expected value at line 1 column 2",
  err probe "missing comma" "[1 2]" "expected `,` or `]` at line 1 column 4",
  err probe "missing comma in object" "{\"a\":1 \"b\"}" "expected `,` or `}` at line 1 column 8",
  err probe "object trailing comma" "{\"a\":1,}" "trailing comma at line 1 column 8",
  err probe "truncated literal" "tru" "EOF while parsing a value at line 1 column 3",
  err probe "bad literal" "trux" "expected ident at line 1 column 4",
  err probe "lone minus" "-" "EOF while parsing a value at line 1 column 1",
  err probe "minus then letter" "-x" "invalid number at line 1 column 2",
  err probe "dot at end" "1." "EOF while parsing a value at line 1 column 2",
  err probe "dot then letter" "1.x" "invalid number at line 1 column 3",
  err probe "exponent sign at end" "1e+" "EOF while parsing a value at line 1 column 3",
  err probe "leading zero" "01" "invalid number at line 1 column 2",
  err probe "negative leading zero" "-01" "invalid number at line 1 column 3",
  err probe "whitespace only" "  " "EOF while parsing a value at line 1 column 2",
  err probe "trailing characters" "1 2" "trailing characters at line 1 column 3",
  err probe "trailing characters after object" "{\"a\":1}x" "trailing characters at line 1 column 8",
  err probe "empty input" "" "EOF while parsing a value at line 1 column 0"
]

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
