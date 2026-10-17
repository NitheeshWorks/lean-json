import LeanJson.APIs
import LeanJson.Proofs.Verified

/-!
# LeanJson

A clean-room port of pydantic-core (its JSON parser and serialiser) to Lean 4: a total JSON parser and printer with a machine-checked round trip.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
