# Contributing to lean-json

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanJson/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `Transport.lean` (if present) | the only effectful module | no; tested |

Everything except the transport module is a pure function. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanJson/`. Byte parsers recurse
  on a `Nat` fuel equal to the remaining input, with a progress lemma per
  production.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanJson` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`. (Nothing yet.)

## Why not `Lean.Json` <a name="why-not-lean-json"></a>

The plan proposed re-exporting core `Lean.Json`. Checked against v4.35 it
cannot carry the round trip the plan asks for, so `LeanJson.Json` is this
library's own inductive, with `Json.toLean` / `Json.ofLean` bridges:

* `Lean.Json.obj` holds a `Std.TreeMap.Raw String Json`: keys sorted, one
  value per key. pydantic-core's parser (jiter) keeps members in document
  order and keeps duplicate keys (lookup is last-wins). A round trip
  `parse (print v) = v` against `Lean.Json` would hold only up to key order
  and duplicates, and `print_injective` would be false.
* `Lean.JsonNumber` is `mantissa * 10^-exponent` with `exponent : Nat`: it
  cannot tell the integer `1` from the float `1e0`, and has no `-0.0`.
  pydantic-core distinguishes int from float literals (`int_from_float`
  errors depend on it), and Python keeps `-0.0`.
* Core's parser, `compress` and `render` are `partial def`, so nothing about
  them is provable.

So: `Json.obj : List (String × Json)` (order and duplicates kept, as jiter),
`Json.arr : List Json`, and `Number := int Int | float Decimal`, where
`Decimal` is an exact normalised decimal with a sign bit (invariant
`h_norm` is a field). `Json.getObjVal?` is last-wins and `Json.dedupKeys`
gives Python `dict` semantics (first position, last value).

## Decisions following upstream

* **Duplicate keys** are kept by the parser, in order, exactly as jiter's
  `JsonValue`; lookup is last-wins (`tests/test_json.py::test_dict`).
* **Big integers** are `Int`, unbounded (jiter `BigInt`,
  `tests/validators/test_int.py::test_long_json`).
* **Floats** are kept exactly as decimals. Upstream rounds to an IEEE double
  (so `1e400` becomes `inf`); `Number.toFloat` does that rounding on demand.
  Deviation: exactness rather than early rounding.
* **Float printing** follows serde_json/ryu (`1.0`, `1e16`, `1e-7`,
  `1.5e300`), which is what `to_json` emits.
* **NaN / Infinity** are not representable and are rejected by the parser.
  Deviation: `from_json` accepts them by default (`allow_inf_nan=True`).
* **No recursion limit.** jiter stops at depth 200; this parser is total by
  fuel and has no depth limit. Deviation.
* **Error messages** use jiter's texts and its line/column convention
  (`EOF while parsing a string at line 1 column 7`).

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
