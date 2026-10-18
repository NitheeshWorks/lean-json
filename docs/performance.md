# Performance against pydantic-core

lean-json's parser and printer are total functions whose statements the proofs
are about. The fast code is swapped in at compile time by `@[csimp]` theorems
that prove each fast function equal to the one it replaces, so none of this
changes a statement or adds a trusted primitive. The main swaps:

| swap (`@[csimp]`) | what it does |
|---|---|
| `parseDocumentWith_eq_BA`, `parseValueAt_eq_BA` | the value, element, member, whitespace and literal loops read the `ByteArray` directly (`valueGoBA`, `parseElemsBA`, `parseMembersBA`, `skipWsBA`) |
| `findFrom_eq_fast` | a run of plain bytes is found 8 bytes per step (`findBlocks`) |
| in `strBodyBA` (`strBodyBA_eq`) | a run of plain ASCII in a string is copied in one step; `\uXXXX` and surrogate pairs are decoded without allocating |
| in `parseMembersBA` (`addRun_eq`, `keyHashBA_eq`) | with `dedupKeys`, a key is hashed and compared in the input; a `String` is built only for a new key |
| in `numBA` (`numBA_eq`, `bigValBA_eq`) | an integer is read 18 digits at a time in a `UInt64` and joined by divide and conquer |
| `pushString_eq_fast` | printing copies runs of bytes that need no escape |

## Method

Both sides parse the same bytes, built in memory before timing, and report
the best of 5 warm runs in one process. pydantic-core 2.50.1 runs
`from_json(data)` (printing: `to_json(s)`) under
`upstream-spec/.venv/bin/python -I`. lean-json runs `lake exe bench <case> <mb> 0 5`.
The two sides are run alternately for 3 rounds, and the table gives the
minimum per side over the rounds. Machine: Intel Core Ultra 7 155H, 22
threads, Linux 7.0, load average 3-5 from other work during the runs.
Measured 2026-10-19 at the commit that added this file.

| case | input | pydantic-core | lean-json | ratio |
|---|---|---|---|---|
| `wide 2` | 2 MB object, 152k distinct keys | 31 ms | 54 ms | 1.74 |
| `wide 20` | 20 MB object, 1.4 M distinct keys | 1026 ms | 1290 ms | 1.26 |
| `dups 20` | 20 MB object, keys cycling through 1000 names | 169 ms | 298 ms | 1.76 |
| `longkeys` | 20000 keys of 1000 characters | 24 ms | 35 ms | 1.46 |
| `escapes 22` | one string of 11 M `\n` escapes | 56 ms | 107 ms | 1.91 |
| `surrogates 12` | one string of 1 M `😀` pairs | 34 ms | 59 ms | 1.74 |
| `bigints` | 5000 integers of 4000 digits | 147 ms | 472 ms | **3.21** (deviation, below) |
| `printstr 1` | printing a 1 MiB ASCII string | 0.60 ms | 0.47 ms | 0.78 |
| `printstr 16` | printing a 16 MiB ASCII string | 22.9 ms | 9.0 ms | 0.39 |

Hostile keys, lean-json only (`lake exe bench collide|collide-prefix 4 0 3`):
10000 keys sharing one bucket of a plain `Std.HashMap String Nat`, 4 passes,
10 ms (a plain `Std.HashMap`: 4165 ms); 10000 keys of one length sharing
their first 64 bytes, so all with one `keyHash`, 4 passes, 49 ms.

## Deviation: big integers, 3.2x

Every case is within 2x except `bigints`. The reason is the cost of Lean's
big-number operations, not the parser:

* Each `Nat` operation on a number above `2^63` costs Lean's runtime a fixed
  110-200 ns, whatever the size, for allocating and converting the GMP value.
  1 M `(x + j) % 5` with `x` of two 64-bit limbs take 219 ms (about 110 ns
  per operation), and 1 M `(x * 10^18 + j) % 5` take 501 ms.
* A 4000-digit integer can only be built from machine words, at least 18
  digits per word, by joining them: about 2 operations per 18 digits, so at
  least 442 big operations, or 49 µs at 110 ns each. For 5000 integers that
  is 243 ms before any digit is read or any limb multiplied, and 2x
  pydantic-core is 294 ms.
* Measured floor: the same divide and conquer written directly over the
  bytes, with nothing but digit reading and big operations, takes 428 ms
  (a microbenchmark outside the repo). lean-json takes 472 ms.

Lean has no primitive that builds a `Nat` from limbs or decimal digits in one
step, which is what pydantic-core (num-bigint, then CPython's own conversion)
uses. Before the work on the card, lean-json took 826 ms (5.6x); reading 18
digits in a `UInt64`, joining by divide and conquer, and taking powers of
`10^18` from a table built once (`pow18Table`) brought it to 472 ms. CI
bounds this case at 2000 ms, an absolute guard against a quadratic step, not
a ratio.

## CI guards

CI and `scripts/check.sh` run each case above with an absolute bound in ms,
best of 5 (`collide-prefix 4 500`, `longkeys 200`, `escapes 22 500`,
`surrogates 12 300`, `bigints 2000`, `printstr 1 20`, `printstr 16 200`, and the
older `wide 2 1000`, `wide 20 15000`, `dups 20 5000`, `collide 4 300`). The
hosted runners are slower than this machine and vary, so the bounds are set
to catch an asymptotic regression, not a few percent.
