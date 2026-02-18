import Mathlib

/-!
# Projection Versions Reduction Protocol (Finite Deterministic Bridge)

Deterministic reduction scaffold:

- V2 additive terms: `k = Σ termᵢ`,
- V3 tensor constrained form: off-diagonal zeros and equal diagonal `k`,
- V1 scalar-style axiswise map: `x ↦ x + k*x`.

In this constrained setting, all three axiswise outputs are equal.
Mirrors `projection_versions_reduction_protocol.py`.
-/

namespace ProjectionVersionsReductionPrediction

def terms : List Rat := [46, 102]
def kTotal : Rat := terms.foldl (fun acc t => acc + t) 0

def ostar : List Rat := [1, 2, 3]

def v1ScalarAxiswise (x : Rat) : Rat := x + kTotal * x
def v2AdditiveAxiswise (x : Rat) : Rat := x + terms.foldl (fun acc t => acc + t * x) 0
def v3TensorDiagAxiswise (x : Rat) : Rat := x + kTotal * x

def v1 : List Rat := ostar.map v1ScalarAxiswise
def v2 : List Rat := ostar.map v2AdditiveAxiswise
def v3 : List Rat := ostar.map v3TensorDiagAxiswise

theorem finite_projection_versions_reduction_summary :
    kTotal = 148 ∧
    v1 = [149, 298, 447] ∧
    v2 = [149, 298, 447] ∧
    v3 = [149, 298, 447] ∧
    v1 = v2 ∧
    v2 = v3 ∧
    v1 = v3 := by
  native_decide

end ProjectionVersionsReductionPrediction
