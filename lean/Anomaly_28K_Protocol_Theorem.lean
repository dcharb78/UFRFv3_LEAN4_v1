import Mathlib

/-!
# 28K Anomaly Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` claim subsets
that reference `28K`:

- §2.3 (graphene),
- §6.2 (2D materials).

Arithmetic decomposition only:
`28 = 13 + 15 = 2 * 14`.

Mirrors `anomaly_28k_protocol.py`.
-/

namespace Anomaly28KPrediction

def anomalyK : Nat := 28

theorem finite_anomaly_28k_summary :
    anomalyK = 28 ∧
    anomalyK = 13 + 15 ∧
    anomalyK = 2 * 14 ∧
    anomalyK - 13 = 15 ∧
    anomalyK - 14 = 14 := by
  native_decide

end Anomaly28KPrediction
