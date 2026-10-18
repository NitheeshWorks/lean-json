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
  the parser: scanners and the element and member loops recurse on the bytes
  left (a loop checks its own progress before it goes round), and nesting is
  structural on a budget of levels (`valueGo`), jiter's depth limit.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `lake exe axioms LeanJson` (`scripts/Axioms.lean`, a pinned copy of
  `stack-tools/Axioms.lean` checked against `scripts/Axioms.sha256`; every
  theorem under `LeanJson` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### The proof map

| Module | What it proves |
|---|---|
| `Proofs/View.lean` | `AtV`: reading a view (`get : Nat → Option UInt8`, length `n`) whose suffix is a known list; buffers, lists and rebased views are views |
| `Proofs/Progress.lean` | progress of every lexical production (`Adv`): it moves forward and stays in the view |
| `Proofs/Digits.lean` | digit lists, digit runs (`scanDigits_ext`, `digitsValue_ext`), the decimal normal form (`normalize_mul`) |
| `Proofs/Number.lean` | `parseNumber_printNumber_ext`, via one shape lemma for ryu's five layouts |
| `Proofs/String.lean` | `parseString_printString_ext`, via `strStep` (one character, every escape form) |
| `Proofs/Step.lean` | the three laws of one step: `valueStep_sim`, `valueStep_shape`, `valueStep_relax`; `valueGo_rebase`, `valueL_progress` |
| `Proofs/Value.lean` | `valueStep_ext` (one level reads a printed value, given a child that reads its children) and `valueGo_ext`, by induction on the levels |
| `Proofs/Grammar.lean` | the fast parser is the Keel parser: `valueL_ok_iff`; `valueNode_monotone`, hence Keel's `fixDepth_ok`; `valueL_deepen` |
| `Proofs/Depth.lean` | `valueL_height` (the depth bound), `valueL_finite` (strict mode), `fits_height`, `fits_default` (the round trip's side condition in plain terms) |
| `Proofs/Codec.lean` | the `Keel.Codec` instances (`stringCodec`, `numberCodec`, `valueCodec`), `parse_print`, `print_injective`, `parse_canonical`, config relaxation, `parse_height`, `parse_finite` |
| `Proofs/Compact.lean` | `print_compact` |
| `Proofs/Builder.lean` | `printBA_eq`: the linear printer equals the specification |
| `Proofs/Verified.lean` | `VerifiedJson`, one field per headline specification |

**One grammar, two parsers.** The grammar is written once, over views:
`valueStep cfg child get n` reads the value whose first byte is at position
`0` of the view `get`, calling `child` for nested values; the lexers
(`parseString`, `parseNumber`, …) take the same views and are
`@[specialize]`d. The fast parser (`valueGo`) feeds `valueStep` itself as the
child, each nested value read through the view rebased at its first byte,
with a budget of levels. The Keel parser (`RepoImpl/Grammar.lean`) wraps the
same `valueStep` as a `Keel.Parser` body (`valueNode`) and ties it with
`Parser.fixDepth` (`jsonParser`). `valueL_ok_iff` says they succeed on the
same inputs with the same results, so Keel's laws about `fixDepth` (it agrees
with `fix` where it succeeds; beyond the input's length the bound is never
reached) are facts about the fast parser: `valueL_deepen`.

**Codecs are `Keel.Codec`s.** An encoder, a Keel decoder, and Keel's law
`parse (encode a ++ rest) = .ok a rest` for every continuation the codec
tolerates. Strings and numbers are lexers with their `_ext` law
(`lexerCodec`); values are `valueCodec`, decoded by `jsonParser`.
`print_injective` is Keel's `Codec.encode_injective`. lean-json defines no
codec theory of its own.

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **`Number.ofFloat?` / `Number.toFloat`** (the `Float` bridge). Proving
  shortest-round-trip digit generation needs a model of IEEE rounding in
  `Float.ofScientific`, which core does not provide. Tested on random bit
  patterns: `toFloat (ofFloat? x) = x` bit for bit, and the printed form
  re-parses to the same bits (`tests/Props.lean`).
* **Duplicate-key helpers** (`Json.lookupLast`, `Json.dedupKeys`): tested for
  Python `dict` semantics (last value, first position, distinct keys), and
  for agreement with the parser's own collapsing (`tests/Props.lean`). What is
  proved about the collapsing is that one step is `insertLast`
  (`Fields.add_exact`), so `Json.dedupKeys` is `Json.dedupKeysList`
  (`dedupKeys_eq`); the round trip on values with distinct keys
  (`Fields.add_fresh`); and that it returns only members it read
  (`Fields.mem_add`); and that a collapsing parse is `Json.dedupDeep`
  (the specification at every depth) of the parse that keeps every member,
  errors included (`parse_dedup`, `Proofs/Dedup.lean`).
* **Peak memory and time**: `tests/Bench.lean`, asserted in CI (the parse adds
  at most 8 × the input + 32 MB; 12 × for ten million array elements, whose
  last doubling holds old and new buffers together, see the bench's header).
* **Error kinds and offsets** for malformed input: the proofs cover what valid
  input does; what each malformed input reports is pinned against the
  released pydantic-core 2.50.1 in `tests/Conformance.lean` (`from_json
  (2.50.1)` cases), and `tests/Props.lean` checks offsets stay in bounds.
* **The `Lean.Json` bridge** (`Json.toLean`, `Json.ofLean`): goes through core's
  `partial` printer, so nothing about it is provable; tested on its common
  fragment.
* **`json%`** notation: a macro; tested by the conformance cases that build
  values with it, and by `tests/Notation.lean`, which imports `Lean` too:
  Lean core has its own `json%` (for `Lean.Json`), so ours is declared at
  `priority := high` and wins with no type ascription.

## Why not `Lean.Json` <a name="why-not-lean-json"></a>

The plan proposed re-exporting core `Lean.Json`. Checked against v4.35 it
cannot carry the round trip the plan asks for, so `LeanJson.Json` is this
library's own inductive, with `Json.toLean` / `Json.ofLean` bridges:

* `Lean.Json.obj` holds a `Std.TreeMap.Raw String Json`: keys sorted, one
  value per key. pydantic-core's parser (jiter) keeps members in document
  order (and can keep duplicate keys). A round trip `parse (print v) = v`
  against `Lean.Json` would hold only up to key order, and `print_injective`
  would be false.
* `Lean.JsonNumber` is `mantissa * 10^-exponent` with `exponent : Nat`: it
  cannot tell the integer `1` from the float `1e0`, and has no `-0.0`.
  pydantic-core distinguishes int from float literals (`int_from_float`
  errors depend on it), and Python keeps `-0.0`.
* Core's parser, `compress` and `render` are `partial def`, so nothing about
  them is provable.

So: `Json.obj : Array (String × Json)` (document order),
`Json.arr : Array Json`, and `Number := int Int | float Decimal | nan | inf
| negInf`, where `Decimal` is an exact normalised decimal with a sign bit
(invariant `h_norm` is a field). `Json.getObjVal?` is last-wins and
`Json.dedupKeys` gives Python `dict` semantics (first position, last value).

### Compact representation

`Array` rather than `List` for containers (one pointer per element, filled by
`push` with no final reverse); the proofs match `.arr ⟨x :: xs⟩` and state the
element and member loops over `acc.toList ++ rest`, so the headline
statements are unchanged. Strings accumulate with `String.push`. The parser
returns integers 0 to 1023 from a shared table (`smallInts`, through
`Json.ofNumber`, with `Json.ofNumber_eq : Json.ofNumber n = .num n`, so the
proofs see `.num`). An object under construction is a `Fields` (the members
and, when collapsing, a `KeyIndex` from key to position), dropped when the
object closes. `KeyIndex` (`RepoImpl/KeyIndex.lean`) hashes a key with
`keyHash` (FNV-1a over its length and first 64 bytes) and mixes that into a
slot under `keySeed`, a secret drawn once per process (an `initialize`
declaration; in the logic an opaque constant, so every theorem holds for every
seed). It stores only positions, and sends keys whose slot is taken to a
`Std.TreeMap`: crafted colliding keys cost `O(log n)` each, not `O(n)`
(`lake exe bench collide`, keys from `lake exe collidegen`; `bench
collide-prefix`, keys of one length sharing 64 bytes, which share one
`keyHash` whatever the seed). While parsing with `dedupKeys`, a plain ASCII key
is hashed and compared straight from the input bytes (`keyHashBA_eq`,
`addRun_eq`), and a `String` is built only for a key not seen before.

## Decisions following upstream

* **Duplicate keys** collapse as they do in the `dict` that `from_json`
  returns: the last value wins, at the key's first position
  (`tests/test_json.py::test_dict`). `ParseCfg.dedupKeys` (default `true`)
  does it while the object is read, so a 60 MB object of one repeated key
  stays small; `dedupKeys := false` keeps every member in order, as jiter's
  `JsonValue` does. With collapsing on, the round trip needs distinct keys
  (`Spec.KeysUnique`, part of `Fits` through `FitsAt`); `ParseCfg.relax` keeps
  the flag, so "limits only add errors" still holds.
* **Separators.** `to_json` prints `,` and `:` (pretty: `: ` and a newline
  after `,`). `PrintOpts.spaced` gives Python `json.dumps`'s `, ` and `: ` on
  one line, and `dumps` is `json.dumps` with its defaults (`ensure_ascii`
  on). `print_compact` assumes `spaced = false`.
* **Indexing.** `GetElem?` instances on `Json` (and `Option Json`, so lookups
  chain) for `String` keys (last-wins, `getObjVal?`) and `Nat` indices
  (`getArrVal?`): `data["name"]?`, `data[0]?`.
* **Big integers** are `Int` (jiter `BigInt`), up to the 4300-byte limit
  below (`tests/validators/test_int.py::test_long_json`). Deviation, in
  speed only: 5000 integers of 4000 digits parse in 472 ms against
  pydantic-core's 147 ms (3.2x, the one case over 2x). Each big `Nat`
  operation costs Lean's runtime a fixed 110-200 ns, and building a 4000-digit
  number from machine words takes at least 442 of them (243 ms for the 5000
  before any digit is read); Lean has no primitive that builds a `Nat` from
  limbs or digits at once. The measurements are in `docs/performance.md`.
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
* **NaN / Infinity.** `Number` has `nan`, `inf`, `negInf`. The default parser
  (`ParseCfg.allowInfNan = true`, `from_json`'s `allow_inf_nan=True`) reads
  `NaN`, `Infinity`, `-Infinity` exactly where jiter does, with jiter's errors
  for near misses (`nan` is `expected ident`, `-NaN` is `invalid number`);
  `ParseCfg.strict` rejects them as before. `to_json` prints them per
  `inf_nan_mode` (`constants` by default, as pydantic-core's `to_json`;
  `null`; `strings`). The round trip needs the mode to read back
  (`Spec.ReadsBack`: `constants`, or no non-finite number), and the strict one
  needs a finite value; `print_injective` holds in `constants` mode only,
  since `null` mode prints `NaN` and `null` alike. Starlette's `JSONResponse`
  (`allow_nan=False`) is strict: lean-starlette checks `Json.allFinite` and
  raises, rather than printing.
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
