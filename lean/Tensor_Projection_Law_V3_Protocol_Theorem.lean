import Mathlib
import GetBangCompat

/-!
# Tensor Projection Law V3 Protocol (Finite Deterministic Bridge)

Additive tensor scaffold:

`ln O_d = ln O*_d + Σ_j P_{dj} * O*_j`

with a fixed 3x3 rational tensor over axes `(E, B, B')`.

This is a deterministic structural bridge (no continuous physics assumptions).
Mirrors `tensor_projection_law_v3_protocol.py`.
-/

namespace TensorProjectionLawV3Prediction

def P : List (List Rat) :=
  [ [1727 / 500, 21 / 500, 21 / 500]
  , [21 / 500, 102 / 125, 9 / 200]
  , [21 / 500, 9 / 200, 219 / 500]
  ]

def ostarOnes : List Rat := [1, 1, 1]

def entry (i j : Nat) : Rat := (P.get! i).get! j

def projectCoord (i : Nat) : Rat :=
  ostarOnes.get! i + (List.range 3).foldl (fun acc j => acc + entry i j * ostarOnes.get! j) 0

def projectedOnes : List Rat := (List.range 3).map projectCoord

def rowSum (i : Nat) : Rat := (List.range 3).foldl (fun acc j => acc + entry i j) 0
def rowSums : List Rat := (List.range 3).map rowSum

def offdiagSymmetric : Bool :=
  (entry 0 1 == entry 1 0) &&
  (entry 0 2 == entry 2 0) &&
  (entry 1 2 == entry 2 1)

def diagonalDominanceByRow : Bool :=
  (entry 0 0 > (entry 0 1 + entry 0 2)) &&
  (entry 1 1 > (entry 1 0 + entry 1 2)) &&
  (entry 2 2 > (entry 2 0 + entry 2 1))

theorem finite_tensor_projection_v3_summary :
    P.length = 3 ∧
    (P.get! 0).length = 3 ∧
    (P.get! 1).length = 3 ∧
    (P.get! 2).length = 3 ∧
    entry 0 0 = 1727 / 500 ∧
    entry 1 1 = 102 / 125 ∧
    entry 2 2 = 219 / 500 ∧
    offdiagSymmetric = true ∧
    diagonalDominanceByRow = true ∧
    rowSums = [1769 / 500, 903 / 1000, 21 / 40] ∧
    projectedOnes = [2269 / 500, 1903 / 1000, 61 / 40] := by
  native_decide

end TensorProjectionLawV3Prediction
