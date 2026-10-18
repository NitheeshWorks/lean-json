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
| `to_json(value, indent=None, ensure_ascii=False)` | `to_json value (indent := none) (ensure_ascii := false)` / `toJson` |
| JSON value (`dict`, `list`, `str`, `int`, `float`, `bool`, `None`) | `Json`: `obj`, `arr`, `str`, `num (.int _ / .float _)`, `bool`, `null` |
| `ValueError` / `json_invalid` context | `JsonError`, `JsonError.description` |
| `dict` from duplicate keys | `Json.getObjVal?` (last wins), `Json.dedupKeys` |

## What is proved

Every theorem is machine-checked; CI rejects `sorry`, `partial`, and any axiom
beyond Lean's `propext`, `Quot.sound`, `Classical.choice`.

* **Round trip.** `parse_print`: for every value whose integers fit jiter's
  4300-byte limit, under every print option (compact, indented, ASCII-only),
  `parseDocument (printWith o 0 j).toByteArray = .ok j`. Without the limit
  (`ParseCfg.lossless`) there is no side condition: `parseLossless_print`.
* **On any continuation.** `parse_print_ext`: the printed form followed by any
  bytes that cannot extend a number parses back with the cursor just past it,
  so values compose inside larger buffers.
* **One codec theory.** `Codec` packages an encoder, a decoder and the law
  above; strings (`stringCodec`, with `\uXXXX` and surrogate pairs), numbers
  (`numberCodec`: integers of any size, floats with exact mantissa, exponent
  and the sign of zero) and values (`valueCodec`) are its instances, and
  `Codec.decode_encode` and `Codec.encode_injective` are proved once for all.
* **The printer is injective**: `print_injective o : Function.Injective (printWith o 0)`.
* **Compact output**: `print_compact` — no tab, LF or CR byte, and a space only
  inside a string that contains one.
* **Total parsing, no fuel.** Every production returns a `Step` whose type
  records that the cursor moved forward and stayed in the buffer, so the
  recursion is well founded on the remaining input; `step_progress` reads that
  back for the public parser.
* **Canonical input.** `parse_canonical`: if the input is the printing of some
  value, the parse returns that value.
* **Fast printer, same bytes.** `printBA_eq`: the linear byte-builder printer
  produces exactly the specified bytes.

What is tested rather than proved (the `Float` bridge, duplicate-key helpers,
error offsets, the `Lean.Json` bridge, `json%`) is listed with reasons in
[CONTRIBUTING.md](CONTRIBUTING.md#verification).

## Differences from pydantic-core

* `NaN`, `Infinity` and `-Infinity` are not JSON; the type cannot hold them and
  the parser rejects them (`from_json` accepts them by default).
* Floats are kept as exact decimals; `Number.toFloat` rounds on demand
  (upstream rounds at parse time, so `1e400` becomes `inf`).
* No nesting-depth limit (jiter stops at 200); parsing is total and linear.
* `allow_partial` and `cache_strings` are not implemented.

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
