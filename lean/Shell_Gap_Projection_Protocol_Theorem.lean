import Mathlib
import GetBangCompat

/-!
# Shell-Gap Projection Protocol (Finite Deterministic Bridge)

Finite arithmetic bridge for `UFRF3.1/08-ufrf-predictions-tests.md` §1.1 claim subset:

- intrinsic progression: `2.5, 5.5, 8.5, 11.5, 14.5` (step `3`)
- projected value: `14.5 - 0.5 = 14.0`

Mirrors `shell_gap_projection_protocol.py`.
-/

namespace ShellGapProjectionPrediction

def intrinsicGaps : List Rat := [5/2, 11/2, 17/2, 23/2, 29/2]

def constantStep3 : Bool :=
  (List.range 4).all (fun k => intrinsicGaps.get! (k + 1) - intrinsicGaps.get! k == (3 : Rat))

def projectionShift : Rat := 1/2
def projectedGap : Rat := intrinsicGaps.get! 4 - projectionShift

theorem finite_shell_gap_projection_summary :
    intrinsicGaps.length = 5 ∧
    intrinsicGaps.get! 0 = (5 : Rat) / 2 ∧
    intrinsicGaps.get! 4 = (29 : Rat) / 2 ∧
    constantStep3 = true ∧
    projectedGap = (14 : Rat) := by
  native_decide

end ShellGapProjectionPrediction
