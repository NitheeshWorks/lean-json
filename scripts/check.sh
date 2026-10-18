#!/usr/bin/env bash
# The whole local gate, in the order CI runs it. The verification gate
# (scripts/Axioms.lean, `lake exe axioms`) checks every declaration on the compiled environment.
# Exits on the first failure.
#
#   scripts/check.sh            # everything
#   scripts/check.sh --quick    # build and the verification gate (no tests)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIB=LeanJson

echo "== build =="
lake build

echo "== verification gate =="
# The gate is a pinned copy of stack-tools/Axioms.lean: never edit it here.
echo "$(cat scripts/Axioms.sha256)  scripts/Axioms.lean" | sha256sum -c --quiet
lake exe axioms "$LIB"

[[ "${1:-}" == "--quick" ]] && exit 0

echo "== property tests =="
lake exe props

echo "== conformance =="
lake exe conformance

echo "== examples =="
if [[ -f ../stack-tools/check-examples.py ]]; then python3 ../stack-tools/check-examples.py .; fi

echo "== json% next to Lean core's json% =="
lake exe notation

echo "== traceability =="
python3 scripts/traceability-check.py

echo "== benchmark =="
lake exe bench flat 20
lake exe bench keys 60
lake exe bench strings 20
lake exe bench e2e 20
lake exe bench wide 2 1000
lake exe bench wide 20 15000
lake exe bench dups 20 5000
lake exe bench collide 4 300
# Speed guards (best of 5, ms; docs/performance.md has the ratios to pydantic-core)
lake exe bench collide-prefix 4 500 5
lake exe bench longkeys 20 200 5
lake exe bench escapes 22 500 5
lake exe bench surrogates 12 300 5
lake exe bench bigints 20 2000 5
lake exe bench printstr 1 20 5
lake exe bench printstr 16 200 5

if [[ "${1:-}" == "--pbt" ]]; then
  echo "== plausible =="
  (cd tests/pbt && lake build && ./.lake/build/bin/pbt)
fi
echo "all clean"
