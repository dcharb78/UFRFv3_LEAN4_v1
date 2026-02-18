import Mathlib
import GetBangCompat

/-!
# Neural Oscillation 13x Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §4.3 claim subset:

`13 Hz, 26 Hz, 39 Hz`.

Mirrors `neural_oscillation_13x_protocol.py`.
-/

namespace NeuralOscillation13xPrediction

def freqs : List Nat := [13, 26, 39]

def allMultiples13 : Bool := freqs.all (fun f => f % 13 == 0)
def constantStep13 : Bool := (List.range 2).all (fun k => freqs.get! (k + 1) - freqs.get! k == 13)

theorem finite_neural_oscillation_13x_summary :
    freqs.length = 3 ∧
    freqs = [13, 2 * 13, 3 * 13] ∧
    allMultiples13 = true ∧
    constantStep13 = true := by
  native_decide

end NeuralOscillation13xPrediction
