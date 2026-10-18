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
| `APIs/` | the public surface (`from_json`, `to_json`, `parseAt`), returning refinements proved from `Proofs/` | by construction |
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
* **Totality.** No `partial def` or `unsafe` under `LeanJson/`, and no fuel in
  the parser: scanners recurse on `bs.size - pos`, and the value parser returns
  `Step`s (value, next position, and the proofs `pos < next ≤ size`), so its
  mutual recursion is well founded on the remaining input.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanJson` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### The proof map

| Module | What it proves |
|---|---|
| `Proofs/Bytes.lean` | `Spec.At`: reading bytes of a buffer whose suffix is a known list |
| `Proofs/Digits.lean` | digit lists, digit runs (`scanDigits_ext`, `digitsValue_ext`), the decimal normal form (`normalize_mul`) |
| `Proofs/Number.lean` | `parseNumber_printNumber_ext`, via one shape lemma for ryu's five layouts |
| `Proofs/String.lean` | `parseString_printString_ext`, via `strStep` (one character, every escape form) |
| `Proofs/Value.lean` | `parseValue_ext`, by mutual structural recursion over values, element lists and member lists |
| `RepoImpl/Step.lean` | progress of every lexical production (`Adv`), used by the parser's types |
| `Proofs/Unfold.lean` | the parser's equations with progress proofs erased (`parseValueAt_eq`, …), via two `Step` lemmas |
| `Proofs/Codec.lean` | the `Codec` theory (`decode_encode`, `encode_injective`), its instances, `parse_print`, `print_injective`, `parse_canonical`, config relaxation |
| `Proofs/Depth.lean` | `parse_height` (the depth bound), `fits_default` (the round trip's side condition in plain terms) |
| `Proofs/Compact.lean` | `print_compact` |
| `Proofs/Builder.lean` | `printBA_eq`: the linear printer equals the specification |
| `Proofs/Verified.lean` | `VerifiedJson`, one field per headline specification |

The codec law is the one pattern behind every round trip: an encoder, a
decoder from a buffer and cursor, and `decode (encode a ++ rest) = .ok (a,
(encode a).length)` for every continuation the codec can stop at. Strings,
numbers and values are instances (`stringCodec`, `numberCodec`,
`valueCodec`); `parse_print` and `print_injective` are corollaries of the
general lemmas. When the shared theory library of the stack exists, `Codec`
moves there unchanged.

The parser is progress-indexed (STYLE.md, "Total parsing"): `Step bs pos α`
carries the value, the next position and the proofs that it is past `pos`
and within the buffer; `Step.lift` turns a lexical production plus its
progress lemma into a step, `Step.cast` relabels it. Totality is therefore a
property of the types, and `step_progress` is read off them. The equations
in `Proofs/Unfold.lean` erase the proofs once, so the round-trip and
relaxation proofs rewrite with ordinary equations.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **`Number.ofFloat?` / `Number.toFloat`** (the `Float` bridge). Proving
  shortest-round-trip digit generation needs a model of IEEE rounding in
  `Float.ofScientific`, which core does not provide. Tested on random bit
  patterns: `toFloat (ofFloat? x) = x` bit for bit, and the printed form
  re-parses to the same bits (`tests/Props.lean`).
* **Duplicate-key helpers** (`Json.lookupLast`, `Json.dedupKeys`): simple list
  functions; tested for Python `dict` semantics (last value, first position,
  distinct keys).
* **Error kinds and offsets** for malformed input: the proofs cover what valid
  input does; what each malformed input reports is pinned against the
  released pydantic-core 2.50.1 in `tests/Conformance.lean` (`from_json
  (2.50.1)` cases), and `tests/Props.lean` checks offsets stay in bounds.
* **The `Lean.Json` bridge** (`Json.toLean`, `Json.ofLean`): goes through core's
  `partial` printer, so nothing about it is provable; tested on its common
  fragment.
* **`json%`** notation: a macro; tested by the conformance cases that build
  values with it.

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
* **Big integers** are `Int` (jiter `BigInt`), up to the 4300-byte limit
  below (`tests/validators/test_int.py::test_long_json`).
* **Floats** are kept exactly as decimals. Upstream rounds to an IEEE double
  (so `1e400` becomes `inf`); `Number.toFloat` does that rounding on demand.
  Deviation: exactness rather than early rounding.
* **Float printing** follows serde_json/ryu (`1.0`, `1e+16`, `1e-7`,
  `1.5e+300`, `0.00001`), which is what `to_json` emits.
* **Number length.** jiter rejects a number whose sign and integer digits
  exceed 4300 bytes (`number out of range`). The default parser does the same
  (`ParseCfg.maxIntLen`); `ParseCfg.lossless` lifts it. Upstream counts the
  sign and applies the limit to floats, unlike Python's `int` (recorded as
  UP-025); the port matches upstream.
* **Error offsets** follow jiter, including its surrogate-escape and UTF-8
  cases; a lone trailing surrogate is reported as `lone leading surrogate`
  as upstream does (UP-026, pydantic/jiter#120).
* **NaN / Infinity** are not representable and are rejected by the parser.
  Deviation: `from_json` accepts them by default (`allow_inf_nan=True`).
* **Nesting limit, as jiter.** A value inside 201 containers is `recursion
  limit exceeded` at the value's offset (so 201 nested empty containers
  parse, and `[` × 202 fails at column 202). `ParseCfg.maxDepth` (default
  `some 201`) is checked inside the parser, and `parse_height` proves no
  returned value has `height` 201 or more. The element and member loops are
  tail calls, so neither nesting nor width can exhaust the stack (a 20 MB
  array of 10^7 elements, or 10^7 brackets, is handled; `lake exe wide`).
* **`ParseCfg.lossless` is not for untrusted input.** It lifts both limits so
  that `parseLossless_print` needs no side condition; without the depth limit
  the parser's stack grows with the input's nesting.
* **Printer recursion.** `to_json` recurses once per level of nesting
  (`Json.height`); element lists are a loop. Values from `from_json` have
  height at most 200. A value built in Lean nested hundreds of thousands of
  levels deep can exhaust the stack when printed (or compared); that is out of
  scope, as it is for any recursive function over such a value.
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
