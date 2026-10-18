import LeanJson.DataTypes
import LeanJson.RepoImpl
import LeanJson.Specifications
import LeanJson.APIs
import LeanJson.Proofs

/-!
# LeanJson

A clean-room port of pydantic-core's JSON layer (its parser and serialiser)
to Lean 4: a total JSON parser and printer with a machine-checked round trip.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      `Json`, `Number`, `Decimal`, `ParseErr`, `JsonError`, `PrintOpts`
* `RepoImpl/`       the executable definitions; total, structural recursion on fuel
* `Specifications/` the properties, stated in `Prop`
* `APIs/`           what users call (`parse`, `parseAt`, `print`); returns refinements
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
-/
