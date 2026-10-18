# Examples: pydantic-core's JSON functions, ported

pydantic-core ships no example programs. Its JSON parser and serialiser are
documented in pydantic's docs page `docs/concepts/json.md` and in the
pydantic-core README, so their Python code blocks are the examples, ported
1:1 in upstream order (pydantic-core 2.50.1). Each Lean file's first comment
names its page, and each block appears with its Python above its Lean.
[`MANIFEST.toml`](MANIFEST.toml) maps every upstream block to its port or
gives the reason it is not here (`stack-tools/check-examples.py` checks it).

| # | Upstream | Lean | Blocks |
|---|---|---|---|
| 1 | `docs/concepts/json.md` block 1: `Event.model_validate_json` | excluded: `BaseModel` validation (lean-pydantic) | – |
| 2 | `docs/concepts/json.md` block 2: `from_json(..., allow_partial=False/True)` | [`concepts/Json.lean`](concepts/Json.lean) | 1 |
| 3 | `docs/concepts/json.md` block 3: partial dog JSON | [`concepts/Json.lean`](concepts/Json.lean) | 1 |
| 4 | `docs/concepts/json.md` block 4: `Dog.model_validate(from_json(...))` | excluded: `BaseModel` validation (lean-pydantic) | – |
| 5 | `docs/concepts/json.md` block 5: `WrapValidator`, `PydanticUseDefault` | excluded: validators (lean-pydantic) | – |
| 6 | `pydantic-core/README.md` block 1: `SchemaValidator` | excluded: core-schema validation (lean-pydantic) | – |

The ports build as the `Examples` library (a default target), and
`tests/Conformance.lean` checks every value they print against what the same
calls print on pydantic-core 2.50.1 (cases `docs example: …`).

`Quickstart.lean` is not a port: it is this repository's own README
quickstart, compiled (`lake exe quickstart`).
