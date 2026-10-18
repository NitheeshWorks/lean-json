import LeanJson
import Plausible

/-!
# Plausible properties

Randomised checks run at build time with `plausible` (`#eval Testable.check`, which fails the build on a counter-example): restatements of the
proved round trip on plausible's own generators (a smoke test of the
definitions the theorems are about), and the bridges that are tested rather
than proved.
-/

namespace Pbt

open LeanJson

def reparse (j : Json) : Option Json := (from_json (to_json j).val).toOption.map (·.val)

#eval Plausible.Testable.check (∀ i : Int, reparse (.num (.int i)) = some (.num (.int i)))

#eval Plausible.Testable.check (∀ s : String, reparse (.str s) = some (.str s))

#eval Plausible.Testable.check (∀ (xs : List Int) (k : String),
    reparse (json% {"k": k, "xs": (xs : List Int)}) = some (json% {"k": k, "xs": (xs : List Int)}))

#eval Plausible.Testable.check (∀ s : String,
    (from_json (to_json s (ensure_ascii := true)).val).toOption.map (·.val) = some (.str s))

end Pbt
