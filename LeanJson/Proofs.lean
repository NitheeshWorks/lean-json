import LeanJson.Proofs.Bytes
import LeanJson.Proofs.Digits
import LeanJson.Proofs.Number
import LeanJson.Proofs.String
import LeanJson.Proofs.Value
import LeanJson.Proofs.Unfold
import LeanJson.Proofs.Codec
import LeanJson.Proofs.Compact
import LeanJson.Proofs.Builder
import LeanJson.Proofs.Verified

/-!
# Proofs

Theorems discharging `Specifications`. No admitted proof; CI checks that
every declaration reaches only `propext`, `Quot.sound` and `Classical.choice`.
-/
