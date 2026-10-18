# lean-json

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

pydantic-core's JSON layer (`from_json`, `to_json`, and the jiter parser behind
them) in Lean 4: a total parser and a compact printer, with the round trip
proved. Part of the verified FastAPI stack under
[NitheeshWorks](https://github.com/NitheeshWorks); it depends on Lean core
only.

## Quickstart

pydantic-core:

```python
from pydantic_core import from_json, to_json

data = from_json('{"name": "Alice", "tags": ["a", "b"]}')
data["tags"][1]           # 'b'
to_json(data)             # b'{"name":"Alice","tags":["a","b"]}'
to_json(data, indent=2)   # pretty, two spaces
from_json('[1,\n2,\n3,]') # ValueError: trailing comma at line 3 column 3
```

lean-json (`examples/Quickstart.lean` is the same, compiled by CI):

```lean
import LeanJson
open LeanJson

-- from_json: String or ByteArray in; the value, or a jiter-style error, out
#eval (from_json "{\"name\": \"Alice\", \"tags\": [\"a\", \"b\"]}").map (·.val)
-- Except.ok json% {"name":"Alice","tags":["a","b"]}

-- indexing as in Python, with `Option` for the missing case
#eval (from_json "{\"name\": \"Alice\", \"tags\": [\"a\", \"b\"]}").map (·.val["tags"]?[1]?)
-- Except.ok (some json% "b")

-- to_json: compact by default (`,` and `:`), like Starlette's JSONResponse
#eval String.fromUTF8! (to_json (json% {"name": "Alice", "tags": ["a", "b"]})).val
-- {"name":"Alice","tags":["a","b"]}
#eval String.fromUTF8! (to_json [1, 2] (indent := some 2)).val          -- "[\n  1,\n  2\n]"
#eval String.fromUTF8! (to_json ["à", "é"] (ensure_ascii := true)).val  -- ["\u00e0","\u00e9"]

-- json% splices Lean values in, as handlers do
def readItem (item_id : Int) (q : Option String := none) : Json :=
  json% {"item_id": item_id, "q": q}             -- {"item_id":42,"q":null}

-- errors carry jiter's kind, byte offset, line and column
#eval match from_json "[1,\n2,\n3,]" with
  | .ok _ => ""
  | .error e => s!"Invalid JSON: {e.description}"   -- trailing comma at line 3 column 3
```

`from_json` returns `{v : Json // Spec.Parsed bs v}` and `to_json` returns
`{b : ByteArray // Spec.Printed o v b}`: the value travels with what is
proved about it (below). Take `.val` when you only want the value.

| pydantic-core | lean-json |
|---|---|
| `from_json(data)` | `from_json data` / `fromJson data` |
| `from_json(data, allow_inf_nan=False)` | `from_json data (allow_inf_nan := false)` |
| `to_json(value, indent=None, ensure_ascii=False, inf_nan_mode='constants')` | `to_json value (indent := none) (ensure_ascii := false) (inf_nan_mode := .constants)` / `toJson` |
| JSON value (`dict`, `list`, `str`, `int`, `float`, `bool`, `None`) | `Json`: `obj`, `arr`, `str`, `num (.int _ / .float _)`, `bool`, `null` |
| `ValueError` / `json_invalid` context | `JsonError`, `JsonError.description` |
| `data["name"]`, `data[0]` | `data["name"]?`, `data[0]?` (chain: `data["a"]?["b"]?[0]?`) |
| `dict` from duplicate keys (last value, first position) | the default; `parseWith { dedupKeys := false }` keeps them all |
| `json.dumps(value, indent=None, ensure_ascii=True)` | `dumps value (indent := none) (ensure_ascii := true)` |

## What is proved

Every theorem is machine-checked; CI rejects `sorry`, `partial`, and any axiom
beyond Lean's `propext`, `Quot.sound`, `Classical.choice`.

* **`from_json (to_json j) = j`.** `from_json_to_json`, under every `indent`
  and `ensure_ascii`, for every value whose integers fit jiter's 4300-byte
  limit (`IntsFit`), whose objects repeat no key (`KeysUnique`) and whose
  `height` is at most 200 (jiter's nesting limit). Each condition is
  necessary: upstream rejects longer integer literals and deeper nesting, and
  `from_json` returns a `dict`, which keeps one value per key. `to_json_injective`: distinct values print differently.
* **NaN and infinity.** `from_json` reads `NaN`, `Infinity`, `-Infinity` by
  default, as pydantic-core does; `from_json data (allow_inf_nan := false)` is
  strict RFC 8259 and `parse_finite` proves it never returns one.
  `from_json_to_json_strict`: a value without them round-trips through strict
  mode under every `inf_nan_mode`.
* **The depth bound.** `parse_height`: under `maxDepth = some L` no returned
  value has height `L` or more; `parseDocument_height`: `from_json` never
  returns anything deeper than 200, so hostile nesting is rejected (at jiter's
  column), and wide input runs in constant stack.
* **Round trip, low level.** `parse_print`: for every value within the
  default limits (`Fits {} j`), under every print option (compact, indented,
  ASCII-only, `json.dumps` separators),
  `parseDocument (printWith o 0 j).toByteArray = .ok j`. Without the limits
  and without collapsing keys (`ParseCfg.lossless`) there is no side
  condition: `parseLossless_print`.
* **On any continuation.** `parse_print_ext`: the printed form followed by any
  bytes that cannot extend a number parses back with the cursor just past it,
  so values compose inside larger buffers.
* **Keel codecs.** Strings (`stringCodec`, with `\uXXXX` and surrogate
  pairs), numbers (`numberCodec`: integers of any size, floats with exact
  mantissa, exponent and the sign of zero) and values (`valueCodec`) are
  `Keel.Codec`s, so Keel's `Codec.decode_encode` and `Codec.encode_injective`
  hold of them. The value decoder is `jsonParser`: the grammar's step tied by
  Keel's depth-bounded `Parser.fixDepth` at jiter's limit, and
  `valueL_ok_iff` proves the fast parser succeeds exactly where it does.
* **The printer is injective**: `print_injective o : Function.Injective (printWith o 0)`
  in `constants` mode, and `print_injective_finite` / `to_json_injective_finite`
  on finite values in every `inf_nan_mode`.
* **Compact output**: `print_compact` — no tab, LF or CR byte, and a space only
  inside a string that contains one.
* **Total parsing, no fuel.** Nesting is structural on a budget of levels and
  every loop is well founded on the bytes left; `step_progress`: every
  success moves forward and stays in the buffer.
* **Canonical input.** `parse_canonical`: if the input is the printing of some
  value (with no repeated key, when keys are collapsed), the parse returns
  that value.
* **Fast printer, same bytes.** `printBA_eq`: the linear byte-builder printer
  produces exactly the specified bytes.

What is tested rather than proved (the `Float` bridge, duplicate-key helpers,
error offsets, the `Lean.Json` bridge, `json%`) is listed with reasons in
[CONTRIBUTING.md](CONTRIBUTING.md#verification).

## Memory

Arrays and objects are `Array`s, strings are built in place, small integers
are shared, and repeated keys collapse while the object is read, so a parse
needs memory close to pydantic-core's. `lake exe bench` (CI asserts the parse
adds at most 8 × the input + 32 MB):

| input | pydantic-core 2.50.1 peak | lean-json peak |
|---|---|---|
| 20 MB `[1,1,...]` (10^7 integers) | 211 MB | 232 MB |
| 60 MB object repeating one key | 136 MB | 124 MB |

Wide objects parse in linear time: each key is collapsed in constant time
through a hash index. `lake exe bench wide|dups` (CI bounds the time, so a
quadratic step fails the build):

| input | pydantic-core 2.50.1 | lean-json |
|---|---|---|
| 2 MB object, 152k distinct keys | 44-52 ms | 91-150 ms |
| 20 MB object, 1.4 M distinct keys | 1.4 s | 1.8-2.1 s |
| 20 MB object, keys cycling through 1000 names | 174 ms | 0.56-0.88 s |

## Differences from pydantic-core

* Floats are kept as exact decimals; `Number.toFloat` rounds on demand
  (upstream rounds at parse time, so `1e400` becomes `inf`).
* `allow_partial` and `cache_strings` are not implemented.
* `dumps` prints numbers as `to_json` does, so an exponent is not padded
  (`1e-7`, where Python's `json.dumps` writes `1e-07`).

## Getting started

```
lake build            # library, proofs, tests, quickstart
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0`.

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
