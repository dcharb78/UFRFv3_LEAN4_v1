import TwinPrime_AllowedCapacity_PrimePower_Product_Theorem

/-!
# Twin-Prime Architecture vs Occupancy Boundary (Mechanism Layer)

This file makes an explicit scope boundary:

- **Architecture capacity** is a discrete combinatorial fact (Lean-proved).
- **Occupancy by observed prime samples** is evidence-layer data.

We formalize the bridge as an inequality:
if a sampled set of residues is known to satisfy the allowed-channel predicate,
its occupied-class count is bounded by the fixed architecture capacity.

No statistical assumptions and no placeholders.
-/

namespace TwinPrimeArchitectureOccupancyBoundary

open TwinPrimeAllowedCapacityPrimePowerProduct
open Finset

namespace PrimePow

/-- Residue classes observed from a finite witness set `W` (evidence layer). -/
def occupiedResidues (pp : PrimePow) (W : Finset Nat) : Finset (ZMod pp.modulus) :=
  W.image (fun n : Nat => (n : ZMod pp.modulus))

/-- Architecture-level allowed channel set (mechanism layer). -/
noncomputable def allowedResidues (pp : PrimePow) : Finset (ZMod pp.modulus) :=
  (Finset.univ : Finset (ZMod pp.modulus)).filter (PrimePow.allowedPow pp)

theorem occupied_subset_allowed_of_forall_allowed (pp : PrimePow) (W : Finset Nat)
    (hW : ∀ n ∈ W, PrimePow.allowedPow pp (n : ZMod pp.modulus)) :
    occupiedResidues pp W ⊆ allowedResidues pp := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨n, hnW, rfl⟩
  simp [allowedResidues, hW n hnW]

/--
Boundary theorem:
if every sampled residue is allowed, occupancy cardinality is bounded by
the architecture capacity.
-/
theorem card_occupiedResidues_le_capacity (pp : PrimePow) (W : Finset Nat)
    (hW : ∀ n ∈ W, PrimePow.allowedPow pp (n : ZMod pp.modulus)) :
    (occupiedResidues pp W).card
      ≤ Fintype.card ({x : ZMod pp.modulus // PrimePow.allowedPow pp x}) := by
  have hsubset : occupiedResidues pp W ⊆ allowedResidues pp :=
    occupied_subset_allowed_of_forall_allowed pp W hW
  have hcard_le : (occupiedResidues pp W).card ≤ (allowedResidues pp).card :=
    Finset.card_le_card hsubset
  have hcard_allowed :
      (allowedResidues pp).card = Fintype.card ({x : ZMod pp.modulus // PrimePow.allowedPow pp x}) := by
    simpa [allowedResidues] using (Fintype.card_subtype (PrimePow.allowedPow pp)).symm
  exact hcard_le.trans (le_of_eq hcard_allowed)

end PrimePow
end TwinPrimeArchitectureOccupancyBoundary
