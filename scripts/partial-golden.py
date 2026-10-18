"""Golden cases for allow_partial, recorded from pydantic-core.

  upstream-spec/.venv/bin/python -I scripts/partial-golden.py > tests/fixtures/partial-golden.jsonl

Each line: {"input": text, "mode": "on" | "trailing-strings", and either
"ok": the result as JSON text, or "error": the ValueError message}.
`lake exe conformance` replays them (tests/Conformance.lean, "allow_partial
golden cases").
"""
import json
import pydantic_core
from pydantic_core import from_json

CASES = [
    # docs/concepts/json.md (Partial JSON Parsing)
    '["aa", "bb", "c', '{"breed": "lab", "name": "fluffy", "friends": ["buddy", "spot", "rufus"], "age',
    '{"foo": "x", "bar": ["world",', '{"foo": "x", "bar": ["world", 1], "nested": {"x":',
    # scalars cut short inside containers, and at the top level
    '[1', '[1.', '[1e', '[-', '[12', '[1.5', '[tru', '[true', '[nul', '[N', '[Infinity', '[Inf',
    '[NaN', '[-Inf', '[-1', '[1e5', '[1E+', '[100000000000000000000000000000',
    '1', '1.', 'tru', '"ab', '', ' ', '"a\\n',
    # containers cut short
    '[', '{', '[[[', '[  ', '{  ', '[1, ', '[1, 2', '[1,  ', '[1, 2 ,', '[[1], ',
    '{"a":', '{"a": tr', '{"a": [1, 2', '{"a": {"b": "c', '{"a"', '{"a', '{"a" ', '{"a\\u12',
    '{"a": 1,  ', '{"a": 1, ', '{"a":1,', '{"a":1, "b":', '{"a": 1, "b"', '[{', '[{"a": 1, "b":',
    '[1, {"a": "b', '{"a": [', '[[1 x', '{"x": NaN', '{"x": -', '[-Infinity, ', '{"a": 1, "a": 2, "b',
    # unexpected bytes end containers silently; nothing after the value is read
    '[1 x', '[1] x', '[[1 x], 2]', '{"a": 1 x', '[{"a": 1 ] ]', '[{"a": 1 ], 5]', '[[1 }, 2]',
    '{"a": [1 }', '{"a": [1 }, "b": 2}', '[1 2', '{"a": 1 "b": 2}', '["x" "y"]',
    '{"a": "b" "c": 1}', '[1]]', '[true false]', '{"a": "x"} y', '{"a": 1}  ', '[1, 2]]', '[1, 2], 3',
    # errors that are kept
    '{"a" x', '{"a": x', '[x', '[1,]', '[1, x', '[01', '[1.e', '["a\\x', '[nan', '{"a":1,}',
    '{"a":1, x', '{"a": 1, 2', '["\\ud83d"', '["a\\ud83dx"]',
    # strings cut short: dropped, or kept in trailing-strings mode
    '["a\\u12', '[1, "a\\', '["a\\ud83d\\ude', '["ab\\n', '["\\ud83d', '["a\\ud83d', '"', '["', '{"',
    '[1, "a"', '[1, "a" ', '{"a": "b"', '"ab\\u00e', '"\\ud83d\\ude', '"a\\ud83d\\', '"a\\ud83d',
    '"a\\ud83d\\ude00', '"a\\ud83dx', '["é世', '"😀b',
]

for c in CASES:
    for mode in ["on", "trailing-strings"]:
        try:
            r = {"ok": json.dumps(from_json(c, allow_partial=True if mode == "on" else mode),
                                  ensure_ascii=False)}
        except ValueError as e:
            r = {"error": str(e)}
        print(json.dumps({"input": c, "mode": mode, **r}, ensure_ascii=False))
