import Mathlib
import GetBangCompat

/-!
# Critical Positions Alignment Protocol (Finite Deterministic Bridge)

Deterministic synthesis bridge aligning two already-used ladders:
- shell intrinsic half-integer anchors: `2.5, 5.5, 8.5, 11.5, 14.5`
- acoustic critical anchors: `2.5, 5.5, 8.5, 10, 11.5`

The shared set is exactly:
`2.5, 5.5, 8.5, 11.5`,
and the REST value `10` is present in the acoustic set but not in the shell set.

Mirrors `critical_positions_alignment_protocol.py`.
-/

namespace CriticalPositionsAlignmentProtocol

def shellPositions : List Rat := [5 / 2, 11 / 2, 17 / 2, 23 / 2, 29 / 2]
def acousticPositions : List Rat := [5 / 2, 11 / 2, 17 / 2, 10, 23 / 2]
def sharedPositions : List Rat := [5 / 2, 11 / 2, 17 / 2, 23 / 2]

def shellStep3Constant : Bool :=
  (List.range 4).all (fun k => shellPositions.get! (k + 1) - shellPositions.get! k == (3 : Rat))

theorem finite_critical_positions_alignment_summary :
    shellPositions = [5 / 2, 11 / 2, 17 / 2, 23 / 2, 29 / 2] ∧
    acousticPositions = [5 / 2, 11 / 2, 17 / 2, 10, 23 / 2] ∧
    sharedPositions.toFinset = shellPositions.toFinset ∩ acousticPositions.toFinset ∧
    (10 : Rat) ∈ acousticPositions ∧
    (10 : Rat) ∉ shellPositions ∧
    shellStep3Constant = true := by
  native_decide

end CriticalPositionsAlignmentProtocol

