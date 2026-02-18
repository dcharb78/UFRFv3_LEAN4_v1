import Mathlib
import GetBangCompat

/-!
# Twin-Prime Occupancy Boundary Protocol (Finite Deterministic Summary)

Finite protocol mirror for:
- `twinprime_occupancy_boundary_protocol.py`
- `twinprime_occupancy_boundary_results.json`

Scope:
- canonical modulus `1001 = 7*11*13`,
- architecture capacity `495 = (7-2)*(11-2)*(13-2)`,
- occupancy claims are finite witness summaries only.
-/

namespace TwinPrimeOccupancyBoundaryProtocol

def modulus : Nat := 1001
def capacity : Nat := 495

def allowedResidueB (n : Nat) : Bool :=
  (n % 7 != 0) && (n % 7 != 5) &&
  (n % 11 != 0) && (n % 11 != 9) &&
  (n % 13 != 0) && (n % 13 != 11)

def allowedResidue (n : Nat) : Prop := allowedResidueB n = true

instance : DecidablePred allowedResidue := by
  intro n
  unfold allowedResidue
  infer_instance

def universeSet : Finset Nat := Finset.range modulus

def allowedSet : Finset Nat := universeSet.filter allowedResidue
def forbiddenSet : Finset Nat := universeSet.filter (fun n => ¬ allowedResidue n)

-- Deterministic admissible subset witness: residues in `[0,123)` that satisfy `allowedResidue`.
def subset60 : Finset Nat := (Finset.range 123).filter allowedResidue

def occupiedClassCount (W : Finset Nat) : Nat :=
  (W.image (fun n : Nat => (n : ZMod modulus))).card

theorem finite_occupancy_boundary_summary :
    allowedSet.card = 495 ∧
    forbiddenSet.card = 506 ∧
    allowedSet.card + forbiddenSet.card = modulus ∧
    subset60.card = 60 ∧
    occupiedClassCount subset60 = 60 ∧
    occupiedClassCount subset60 ≤ capacity ∧
    occupiedClassCount allowedSet = 495 ∧
    occupiedClassCount forbiddenSet = 506 ∧
    occupiedClassCount allowedSet = capacity ∧
    capacity < occupiedClassCount forbiddenSet := by
  native_decide

end TwinPrimeOccupancyBoundaryProtocol
