import TwinPrime_AllowedCapacity_PrimePower_Product_Theorem

/-!
# Twin-Prime Architecture vs Occupancy Boundary (Product Axis Bundle)

This module lifts the occupancy boundary from a single prime-power axis to the full
CRT product axis bundle:

- architecture capacity is fixed by `card_allowedPrimePowerProduct`,
- observed occupancy is a finite witness-set image in `ZMod (∏ modulusᵢ)`.

If every sampled residue is known to satisfy the architecture predicate, occupancy count
is bounded by architecture capacity (both subtype form and explicit product form).
-/

namespace TwinPrimeArchitectureOccupancyProductBoundary

open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityCRTList
open Finset

/-- Residue classes observed from a finite witness set `W` on the product modulus. -/
def occupiedResiduesProduct (pps : List PrimePow) (W : Finset Nat) :
    Finset (ZMod (mods pps).prod) :=
  W.image (fun n : Nat => (n : ZMod (mods pps).prod))

theorem occupied_subset_allowed_of_forall_allowed (pps : List PrimePow) (co : (mods pps).Pairwise Nat.Coprime)
    (W : Finset Nat)
    (hW : ∀ n ∈ W, allowedAxisPow pps (axisEquiv (mods pps) co (n : ZMod (mods pps).prod))) :
    letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
    occupiedResiduesProduct pps W ⊆
      (Finset.univ : Finset (ZMod (mods pps).prod)).filter
        (fun x => allowedAxisPow pps (axisEquiv (mods pps) co x)) := by
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨n, hnW, rfl⟩
  simp [hW n hnW]

/--
Boundary theorem (subtype form):
if every sampled residue is architecture-allowed, occupancy cardinality is bounded by
the product-space allowed-channel capacity.
-/
theorem card_occupiedResidues_le_capacitySubtype (pps : List PrimePow) (co : (mods pps).Pairwise Nat.Coprime)
    (W : Finset Nat)
    (hW : ∀ n ∈ W, allowedAxisPow pps (axisEquiv (mods pps) co (n : ZMod (mods pps).prod))) :
    letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
    (occupiedResiduesProduct pps W).card
      ≤ Fintype.card ({x : ZMod (mods pps).prod // allowedAxisPow pps (axisEquiv (mods pps) co x)}) := by
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
  have hsubset :
      occupiedResiduesProduct pps W ⊆
        (Finset.univ : Finset (ZMod (mods pps).prod)).filter
          (fun x => allowedAxisPow pps (axisEquiv (mods pps) co x)) :=
    occupied_subset_allowed_of_forall_allowed pps co W hW
  have hcard_le :
      (occupiedResiduesProduct pps W).card ≤
        ((Finset.univ : Finset (ZMod (mods pps).prod)).filter
          (fun x => allowedAxisPow pps (axisEquiv (mods pps) co x))).card :=
    Finset.card_le_card hsubset
  have hcard_allowed :
      ((Finset.univ : Finset (ZMod (mods pps).prod)).filter
        (fun x => allowedAxisPow pps (axisEquiv (mods pps) co x))).card =
        Fintype.card ({x : ZMod (mods pps).prod // allowedAxisPow pps (axisEquiv (mods pps) co x)}) := by
    simpa using
      (Fintype.card_subtype
        (fun x : ZMod (mods pps).prod => allowedAxisPow pps (axisEquiv (mods pps) co x))).symm
  exact hcard_le.trans (le_of_eq hcard_allowed)

/--
Boundary theorem (explicit product-capacity form):
under the same witness-set assumption, occupancy cardinality is bounded by the exact
architecture product count `∏ ((pᵢ - 2) * pᵢ^kᵢ)`.
-/
theorem card_occupiedResidues_le_capacityProduct (pps : List PrimePow) (co : (mods pps).Pairwise Nat.Coprime)
    (W : Finset Nat)
    (hW : ∀ n ∈ W, allowedAxisPow pps (axisEquiv (mods pps) co (n : ZMod (mods pps).prod))) :
    letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
    (occupiedResiduesProduct pps W).card
      ≤ (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := by
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
  have hsub :
      (occupiedResiduesProduct pps W).card
        ≤ Fintype.card ({x : ZMod (mods pps).prod // allowedAxisPow pps (axisEquiv (mods pps) co x)}) :=
    card_occupiedResidues_le_capacitySubtype pps co W hW
  have hcap :
      Fintype.card ({x : ZMod (mods pps).prod // allowedAxisPow pps (axisEquiv (mods pps) co x)})
        = (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod := by
    simpa using (card_allowedPrimePowerProduct (pps := pps) (co := co))
  exact hsub.trans (le_of_eq hcap)

end TwinPrimeArchitectureOccupancyProductBoundary
