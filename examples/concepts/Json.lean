import LeanJson
open LeanJson

/-!
# JSON: partial JSON parsing

Port of pydantic `docs/concepts/json.md` ("JSON", section "Partial JSON
Parsing"), the blocks that use `pydantic_core.from_json`, block by block.
Blocks 1, 4 and 5 validate into `BaseModel`s and are lean-pydantic's
(`examples/MANIFEST.toml`).
-/

namespace Examples.Json

/-! Block 2:
```python
from pydantic_core import from_json

partial_json_data = '["aa", "bb", "c'  # (1)!

try:
    result = from_json(partial_json_data, allow_partial=False)
except ValueError as e:
    print(e)  # (2)!
    #> EOF while parsing a string at line 1 column 15

result = from_json(partial_json_data, allow_partial=True)
print(result)  # (3)!
#> ['aa', 'bb']
```
-/

def partial_json_data := "[\"aa\", \"bb\", \"c"

/-- `print(e)` of the strict parse. -/
def strictError : String :=
  match from_json partial_json_data (allow_partial := false) with
  | .ok _ => ""
  | .error e => e.description
#eval strictError               -- "EOF while parsing a string at line 1 column 15"

def result := (from_json partial_json_data (allow_partial := true)).map (·.val)
#eval result                    -- Except.ok json% ["aa","bb"]

/-! Block 3:
```python
from pydantic_core import from_json

partial_dog_json = '{"breed": "lab", "name": "fluffy", "friends": ["buddy", "spot", "rufus"], "age'
dog_dict = from_json(partial_dog_json, allow_partial=True)
print(dog_dict)
#> {'breed': 'lab', 'name': 'fluffy', 'friends': ['buddy', 'spot', 'rufus']}
```
-/

def partial_dog_json :=
  "{\"breed\": \"lab\", \"name\": \"fluffy\", \"friends\": [\"buddy\", \"spot\", \"rufus\"], \"age"

def dog_dict := (from_json partial_dog_json (allow_partial := true)).map (·.val)
#eval dog_dict                  -- Except.ok json% {"breed":"lab","name":"fluffy","friends":["buddy","spot","rufus"]}

end Examples.Json
