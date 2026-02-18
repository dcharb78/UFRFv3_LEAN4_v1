import Mathlib
import GetBangCompat

/-!
# Projection Tensor Row-Sum <-> Scalar Bridge (Finite Deterministic Bridge)

For the canonical probe `O* = [1,1,1]`, tensor correction by row equals
row-sum gain per axis. This gives a direct scalar-gain interpretation of the
V3 tensor on this probe.

Mirrors `projection_tensor_rowsum_scalar_bridge_protocol.py`.
-/

namespace ProjectionTensorRowsumScalarBridgePrediction

def P : List (List Rat) :=
  [ [1727 / 500, 21 / 500, 21 / 500]
  , [21 / 500, 102 / 125, 9 / 200]
  , [21 / 500, 9 / 200, 219 / 500]
  ]

def entry (i j : Nat) : Rat := (P.get! i).get! j
def rowSum (i : Nat) : Rat := (List.range 3).foldl (fun acc j => acc + entry i j) 0
def rowSums : List Rat := (List.range 3).map rowSum

def correctionOnes (i : Nat) : Rat :=
  (List.range 3).foldl (fun acc j => acc + entry i j * (1 : Rat)) 0
def correctionsOnes : List Rat := (List.range 3).map correctionOnes

def projectedOnes : List Rat := (List.range 3).map (fun i => (1 : Rat) + correctionOnes i)

theorem finite_projection_tensor_rowsum_scalar_bridge_summary :
    rowSums = [1769 / 500, 903 / 1000, 21 / 40] ∧
    correctionsOnes = rowSums ∧
    projectedOnes = [2269 / 500, 1903 / 1000, 61 / 40] := by
  native_decide

end ProjectionTensorRowsumScalarBridgePrediction
