import Mathlib

/-!
# Projection Technique Variation (Finite Deterministic Bridge)

Deterministic scaffold for projection-law falsification logic:
for fixed `ln O*`, `d_M`, and `S`, varying technique coupling `α` changes
the observed log-value, and the difference equals
`d_M * S * (α₂ - α₁)`.

Mirrors `projection_technique_variation_protocol.py`.
-/

namespace ProjectionTechniqueVariationPrediction

def lnOStar : Rat := 0
def dM : Rat := 2
def S : Rat := 3
def alpha1 : Rat := 1 / 10
def alpha2 : Rat := 1 / 5

def delta1 : Rat := dM * alpha1 * S
def delta2 : Rat := dM * alpha2 * S

def lnO1 : Rat := lnOStar + delta1
def lnO2 : Rat := lnOStar + delta2

def actualDiff : Rat := lnO2 - lnO1
def expectedDiff : Rat := dM * S * (alpha2 - alpha1)

theorem finite_projection_technique_variation_summary :
    alpha1 ≠ alpha2 ∧
    lnO1 ≠ lnO2 ∧
    lnO1 = 3 / 5 ∧
    lnO2 = 6 / 5 ∧
    actualDiff = expectedDiff ∧
    actualDiff = 3 / 5 := by
  native_decide

end ProjectionTechniqueVariationPrediction
