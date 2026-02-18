import Mathlib
import GetBangCompat

/-!
# Acoustic Critical Positions (Finite Deterministic Bridge)

Finite scaffold for Predictions §7.1 critical positions using:
`f = 432 * (n / 13)` at
`n = 2.5, 5.5, 8.5, 10, 11.5`.

Mirrors `acoustic_critical_positions_protocol.py`.
-/

namespace AcousticCriticalPositionsPrediction

def criticalN : List Rat := [5 / 2, 11 / 2, 17 / 2, 10, 23 / 2]
def freqs : List Rat := criticalN.map (fun n => (432 : Rat) * (n / 13))

theorem finite_acoustic_critical_positions_summary :
    criticalN = [5 / 2, 11 / 2, 17 / 2, 10, 23 / 2] ∧
    freqs = [1080 / 13, 2376 / 13, 3672 / 13, 4320 / 13, 4968 / 13] ∧
    (criticalN.get! 3 = 10) ∧
    (freqs.get! 3 = 4320 / 13) ∧
    (freqs.get! 0 < freqs.get! 1) ∧
    (freqs.get! 1 < freqs.get! 2) ∧
    (freqs.get! 2 < freqs.get! 3) ∧
    (freqs.get! 3 < freqs.get! 4) := by
  native_decide

end AcousticCriticalPositionsPrediction
