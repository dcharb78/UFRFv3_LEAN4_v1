import Mathlib
import GetBangCompat

/-!
# Projection Distance Monotonicity (Finite Deterministic Bridge)

Deterministic scaffold for projection-law monotonicity:
with fixed `ln O*`, `α > 0`, `S > 0`, increasing `d_M` increases observed `ln O`.

Mirrors `projection_distance_monotonicity_protocol.py`.
-/

namespace ProjectionDistanceMonotonicityPrediction

def lnO (lnOStar dM alpha S : Rat) : Rat := lnOStar + dM * alpha * S

def lnOStar : Rat := 7 / 3
def alpha : Rat := 1 / 10
def S : Rat := 3

def dms : List Rat := [0, 1, 2, 5]
def outputs : List Rat := dms.map (fun d => lnO lnOStar d alpha S)

theorem finite_projection_distance_monotonicity_summary :
    outputs = [7 / 3, 79 / 30, 44 / 15, 23 / 6] ∧
    (outputs.get! 0 < outputs.get! 1) ∧
    (outputs.get! 1 < outputs.get! 2) ∧
    (outputs.get! 2 < outputs.get! 3) ∧
    (outputs.get! 1 - outputs.get! 0 = 3 / 10) ∧
    (outputs.get! 2 - outputs.get! 1 = 3 / 10) := by
  native_decide

end ProjectionDistanceMonotonicityPrediction
