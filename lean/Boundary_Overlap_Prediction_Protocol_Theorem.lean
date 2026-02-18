import REST_Seam_Core_Theorem
import Mathlib
import GetBangCompat

/-!
# Boundary-Overlap Prediction Protocol (Finite Deterministic Bridge)

Finite protocol summary for Prediction §0 in `UFRF3.1/08-ufrf-predictions-tests.md`.

This file intentionally stays discrete and bounded:
- generations `g = 0..9`,
- boundary offsets `r ∈ {1,2,3}`,
- control offsets `r ∈ {4,5,6,7,8,9,10,11,12,13}`.

It mirrors the Python artifact `boundary_overlap_prediction_protocol.py` exactly.
-/

namespace BoundaryOverlapPrediction

open RESTSeamOverlap

def generations : List Nat := List.range 10
def boundaryOffsets : List Nat := [1, 2, 3]
def controlOffsets : List Nat := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

def isParentCompleteB (s : Nat) : Bool :=
  s == 11 || s == 12 || s == 13

def isChildSeedB (s : Nat) : Bool :=
  s == 1 || s == 2 || s == 3

def overlapAt (g r : Nat) : Bool :=
  let t := seamTick g r
  let p := state g t
  let c := state (g + 1) t
  isParentCompleteB p && isChildSeedB c

def exactPairAt (g r : Nat) : Bool :=
  let t := seamTick g r
  let p := state g t
  let c := state (g + 1) t
  (p == rest + r) && (c == r)

def evalWindow (offsets : List Nat) : List Bool :=
  generations.bind (fun g => offsets.map (fun r => overlapAt g r))

def evalWindowExact (offsets : List Nat) : List Bool :=
  generations.bind (fun g => offsets.map (fun r => exactPairAt g r))

def countTrue (xs : List Bool) : Nat :=
  xs.foldl (fun acc b => if b then acc + 1 else acc) 0

def boundaryOverlaps : List Bool := evalWindow boundaryOffsets
def controlOverlaps : List Bool := evalWindow controlOffsets
def boundaryExactPairs : List Bool := evalWindowExact boundaryOffsets
def controlExactPairs : List Bool := evalWindowExact controlOffsets

theorem finite_boundary_overlap_summary :
    boundaryOverlaps.length = 30 ∧
    controlOverlaps.length = 100 ∧
    countTrue boundaryOverlaps = 30 ∧
    countTrue controlOverlaps = 0 ∧
    countTrue boundaryExactPairs = 30 ∧
    countTrue controlExactPairs = 0 := by
  native_decide

end BoundaryOverlapPrediction
