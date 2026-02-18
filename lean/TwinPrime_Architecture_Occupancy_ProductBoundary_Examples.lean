import TwinPrime_Architecture_Occupancy_ProductBoundary_Theorem

/-!
# Twin-Prime Occupancy Boundary: Worked Product Examples

These examples instantiate the architecture-vs-occupancy boundary on a canonical
bundle `1001 = 7 * 11 * 13` (with exponent `k=0` on each axis).

Theorems here remain conditional on witness-set admissibility (`hW`), preserving
the evidence/mechanism split.
-/

namespace TwinPrimeArchitectureOccupancyProductBoundaryExamples

open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeArchitectureOccupancyProductBoundary
open TwinPrimeAllowedCapacityCRTList

def pp7 : PrimePow := ⟨7, 0, by decide⟩
def pp11 : PrimePow := ⟨11, 0, by decide⟩
def pp13 : PrimePow := ⟨13, 0, by decide⟩

def pps1001 : List PrimePow := [pp7, pp11, pp13]

theorem co1001 : (mods pps1001).Pairwise Nat.Coprime := by
  native_decide

theorem capacity_1001 :
    (letI : NeZero (mods pps1001).prod := ⟨mods_prod_ne_zero pps1001⟩;
      Fintype.card ({x : ZMod (mods pps1001).prod //
        allowedAxisPow pps1001 (axisEquiv (mods pps1001) co1001 x)}) = 495) := by
  simpa [pps1001, pp7, pp11, pp13] using
    (card_allowedPrimePowerProduct (pps := pps1001) (co := co1001))

theorem card_occupied_1001_le_495 (W : Finset Nat)
    (hW : ∀ n ∈ W, allowedAxisPow pps1001 (axisEquiv (mods pps1001) co1001 (n : ZMod (mods pps1001).prod))) :
    (letI : NeZero (mods pps1001).prod := ⟨mods_prod_ne_zero pps1001⟩;
      (occupiedResiduesProduct pps1001 W).card ≤ 495) := by
  letI : NeZero (mods pps1001).prod := ⟨mods_prod_ne_zero pps1001⟩
  have hcap :
      (occupiedResiduesProduct pps1001 W).card
        ≤ (pps1001.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod :=
    card_occupiedResidues_le_capacityProduct (pps := pps1001) (co := co1001) (W := W) hW
  simpa [pps1001, pp7, pp11, pp13] using hcap

end TwinPrimeArchitectureOccupancyProductBoundaryExamples
