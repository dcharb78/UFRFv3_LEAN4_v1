import Mathlib

/-!
# Projection Zero-Distance Identity (Finite Deterministic Bridge)

Deterministic scaffold for the projection-law identity case:
if `d_M = 0`, then `ln O = ln O*` independently of technique factors `α, S`.

Includes one fixed non-zero-distance witness to show the condition is substantive.

Mirrors `projection_zero_distance_identity_protocol.py`.
-/

namespace ProjectionZeroDistanceIdentityPrediction

def lnO (lnOStar dM alpha S : Rat) : Rat := lnOStar + dM * alpha * S

def lnOStar : Rat := 7 / 3

def outputsAtZero : List Rat :=
  [ lnO lnOStar 0 (1 / 10) 1
  , lnO lnOStar 0 (1 / 5) 2
  , lnO lnOStar 0 (3 / 7) 5
  ]

def witnessNonZero : Rat := lnO lnOStar 2 (1 / 10) 3

theorem finite_projection_zero_distance_identity_summary :
    outputsAtZero = [7 / 3, 7 / 3, 7 / 3] ∧
    witnessNonZero = 44 / 15 ∧
    witnessNonZero ≠ lnOStar := by
  native_decide

end ProjectionZeroDistanceIdentityPrediction
