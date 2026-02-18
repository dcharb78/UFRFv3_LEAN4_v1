import Index_Of_Indexes_Theorem
import Breathing_Cycle_LOG_Partition_Theorem

/-!
# Subcycle Fiber (Discrete “Point Contains Full 13-Cycle”)

This file adds one missing *structural* fact to the certified “index-of-indexes” spine:

At any scale level `k`, a fixed coarse index `x : Fin (13^k)` has **exactly 13 refinements**
at the next level `k+1`. Equivalently, the fiber of the projection

`Fin (13^(k+1)) → Fin (13^k)`  (take the first component of `splitEquiv`)

is in canonical bijection with `Fin 13`.

This is the precise discrete counterpart of the narrative claim:
“a point at one scale resolves into a full breathing cycle at the next finer scale”.

No axioms; it follows purely from the product decomposition `13^(k+1) = 13^k * 13`.
-/

namespace IndexOfIndexesSubcycle

open IndexOfIndexes

abbrev Fiber (k : Nat) (x : Fin (SL k)) : Type :=
  { y : Fin (SL (k + 1)) // (splitEquiv k y).1 = x }

/-!
## Fiber equivalence

Fix a coarse index `x`. The set of all next-level indices whose coarse component is `x`
is equivalent to the fine coordinate `Fin 13`.
-/

/-- The refinement fiber over a fixed coarse index is canonically `Fin 13`. -/
def fiberEquiv (k : Nat) (x : Fin (SL k)) :
    Fiber k x ≃ Fin base := by
  classical
  refine
    { toFun := fun y => (splitEquiv k y.1).2
      invFun := fun r =>
        ⟨joinEquiv k (x, r), by
          -- `splitEquiv k (joinEquiv k (x,r)) = (x,r)`, so the first coordinate is `x`.
          have h :=
            congrArg Prod.fst (split_join (k := k) (x := (x, r)))
          simpa using h⟩
      left_inv := by
        intro y
        apply Subtype.ext
        -- Use the hypothesis that the coarse coordinate is fixed, then close via `join_split`.
        have hx : (splitEquiv k y.1).1 = x := y.2
        -- Rewrite the join pair to match `splitEquiv k y.1`.
        calc
          joinEquiv k (x, (splitEquiv k y.1).2)
              = joinEquiv k ((splitEquiv k y.1).1, (splitEquiv k y.1).2) := by
                  simp [hx]
          _ = joinEquiv k (splitEquiv k y.1) := by
                  rfl
          _ = y.1 := by
                  exact join_split (k := k) (x := y.1)
      right_inv := by
        intro r
        -- Second coordinate of `splitEquiv k (joinEquiv k (x,r))` is exactly `r`.
        have h :=
          congrArg Prod.snd (split_join (k := k) (x := (x, r)))
        simpa using h }

/--
Each coarse node contains exactly `13` fine states at the next level.

This quantifies the discrete “subcycle inside a point” idea.
-/
theorem fiber_card_base (k : Nat) (x : Fin (SL k)) :
    Fintype.card (Fiber k x) = base := by
  classical
  simpa using (Fintype.card_congr (fiberEquiv (k := k) (x := x)))

/-!
## Refinement → Phase Lens (Bounded, Discrete)

Using the canonical `splitEquiv` refinement digit (`Fin 13`), show that every coarse node
sees the same breathing-cycle phase census (`3,3,3,1,3`) under the digit→phase lens.

This is a clean mechanism bridge between:
- the index-of-indexes refinement skeleton (0→1 contains a full 13-cycle), and
- the breathing-cycle phase partition on `Fin 13`.
-/

namespace RefinementPhaseLens

open BreathingCycleLOGPartition

abbrev Pos13 := BreathingCycleLOGPartition.Pos
abbrev Phase13 := BreathingCycleLOGPartition.Phase

def basePosEquiv : Fin base ≃ Pos13 := by
  -- `base = 13` and `Pos = Fin 13`, so this is definitional transport.
  simpa [IndexOfIndexes.base, BreathingCycleLOGPartition.Pos] using (Equiv.refl (Fin 13))

def fiberEquivPos (k : Nat) (x : Fin (SL k)) : Fiber k x ≃ Pos13 :=
  (fiberEquiv (k := k) (x := x)).trans basePosEquiv

def fiberPhaseEquiv (k : Nat) (x : Fin (SL k)) (p : Phase13) :
    { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = p } ≃
      { z : Pos13 // phaseOf z = p } := by
  classical
  refine
    { toFun := fun y => ⟨fiberEquivPos (k := k) (x := x) y.1, y.2⟩
      invFun := fun z =>
        ⟨(fiberEquivPos (k := k) (x := x)).symm z.1, by
          -- `fiberEquivPos _ _ ((fiberEquivPos _ _).symm z) = z`
          simpa using z.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        simp
      right_inv := by
        intro z
        apply Subtype.ext
        simp }

theorem card_phaseOf_eq (p : Phase13) :
    Fintype.card { z : Pos13 // phaseOf z = p } = (phaseSet p).card := by
  classical
  have H : ∀ z : Pos13, z ∈ phaseSet p ↔ phaseOf z = p := by
    intro z
    simpa using (mem_phaseSet_iff_phaseOf_eq z p)
  simpa using (Fintype.card_of_subtype (p := fun z : Pos13 => phaseOf z = p) (s := phaseSet p) H)

theorem fiber_phase_card (k : Nat) (x : Fin (SL k)) (p : Phase13) :
    Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = p } =
      (phaseSet p).card := by
  classical
  -- Reduce to the codomain by the explicit subtype equivalence.
  have hCard :
      Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = p } =
        Fintype.card { z : Pos13 // phaseOf z = p } := by
    simpa using (Fintype.card_congr (fiberPhaseEquiv (k := k) (x := x) p))
  -- Then rewrite the codomain cardinality via the phase-set representation.
  exact hCard.trans (card_phaseOf_eq (p := p))

theorem fiber_phase_census (k : Nat) (x : Fin (SL k)) :
    (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.L1 } = 3)
    ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.L2 } = 3)
    ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.L3 } = 3)
    ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.Rest } = 1)
    ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.Bridge } = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [phaseSet] using (fiber_phase_card (k := k) (x := x) (p := Phase.L1)).trans card_log1.symm
  · simpa [phaseSet] using (fiber_phase_card (k := k) (x := x) (p := Phase.L2)).trans card_log2.symm
  · simpa [phaseSet] using (fiber_phase_card (k := k) (x := x) (p := Phase.L3)).trans card_log3.symm
  · simpa [phaseSet] using (fiber_phase_card (k := k) (x := x) (p := Phase.Rest)).trans card_rest.symm
  · simpa [phaseSet] using (fiber_phase_card (k := k) (x := x) (p := Phase.Bridge)).trans card_bridge.symm

def refinement_phase_lens_stmt : Prop :=
    ∀ (k : Nat) (x : Fin (SL k)),
      (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.L1 } = 3)
      ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.L2 } = 3)
      ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.L3 } = 3)
      ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.Rest } = 1)
      ∧ (Fintype.card { y : Fiber k x // phaseOf (fiberEquivPos (k := k) (x := x) y) = Phase.Bridge } = 3)

theorem refinement_phase_lens : refinement_phase_lens_stmt := by
  intro k x
  exact fiber_phase_census (k := k) (x := x)

end RefinementPhaseLens

/-!
## Fiber → address image (explicit 13-point offsets)

To make the “point contains a full 13-cycle” statement *coordinate explicit*, we relate the
refinement fiber to the rational addressing map `addrQ`.
-/

/-- The set of next-level rational addresses realized by the refinement fiber over `x`. -/
def fiberAddrImage (k : Nat) (x : Fin (SL k)) : Set ℚ :=
  (fun y : { y : Fin (SL (k + 1)) // (splitEquiv k y).1 = x } => addrQ (k + 1) y.1) '' Set.univ

/-- The explicit 13-point offset set inside the coarse interval of `x`. -/
def offsetAddrImage (k : Nat) (x : Fin (SL k)) : Set ℚ :=
  (fun r : Fin base => addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ)) '' Set.univ

/--
The explicit offset map is injective: the 13 refinement offsets are pairwise distinct in `ℚ`.

This rules out “address collapse” inside a coarse interval.
-/
theorem offsetAddr_injective (k : Nat) (x : Fin (SL k)) :
    Function.Injective (fun r : Fin base => addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ)) := by
  intro r1 r2 h
  have h' :
      (r1.1 : ℚ) / (SL (k + 1) : ℚ) = (r2.1 : ℚ) / (SL (k + 1) : ℚ) := by
    exact add_left_cancel h
  have hden : (SL (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (SL_pos (k + 1)))
  have hmul := congrArg (fun q : ℚ => q * (SL (k + 1) : ℚ)) h'
  have hrr : (r1.1 : ℚ) = (r2.1 : ℚ) := by
    field_simp [hden] at hmul
    exact hmul
  have : r1.1 = r2.1 := by
    exact_mod_cast hrr
  exact Fin.ext this

/-- A finite witness for the 13 distinct refinement offsets. -/
def offsetAddrFinset (k : Nat) (x : Fin (SL k)) : Finset ℚ :=
  (Finset.univ : Finset (Fin base)).image
    (fun r : Fin base => addrQ k x + (r.1 : ℚ) / (SL (k + 1) : ℚ))

/-- The offset finset has exactly 13 elements (cardinality in address-space). -/
theorem offsetAddrFinset_card (k : Nat) (x : Fin (SL k)) :
    (offsetAddrFinset k x).card = base := by
  classical
  simpa [offsetAddrFinset] using
    (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin base)))
      (offsetAddr_injective (k := k) (x := x)))

/-- Set-level cardinality: the explicit offset address image has exactly 13 elements. -/
theorem offsetAddrImage_ncard (k : Nat) (x : Fin (SL k)) :
    (offsetAddrImage k x).ncard = base := by
  -- `offsetAddrImage` is the image of `Set.univ` under an injective map from `Fin 13`.
  calc
    (offsetAddrImage k x).ncard = (Set.univ : Set (Fin base)).ncard := by
      simpa [offsetAddrImage] using
        (Set.ncard_image_of_injective (s := (Set.univ : Set (Fin base)))
          (offsetAddr_injective (k := k) (x := x)))
    _ = base := by
      simp [Set.ncard_univ]

/--
The `addrQ` image of the refinement fiber is exactly the explicit 13-point offset set:

`{ addrQ (k+1) y | coarse(y)=x } = { addrQ k x + r/13^(k+1) | r : Fin 13 }`.
-/
theorem fiberAddrImage_eq_offsetAddrImage (k : Nat) (x : Fin (SL k)) :
    fiberAddrImage k x = offsetAddrImage k x := by
  ext q
  constructor
  · intro hq
    rcases hq with ⟨y, hy, rfl⟩
    -- Choose the fine digit `r` from `splitEquiv`; this is order-independent.
    refine ⟨(splitEquiv k y.1).2, by trivial, ?_⟩
    -- `addrQ_split` + the fiber hypothesis `coarse(y)=x` gives the exact offset formula.
    -- `Set.image` membership expects the equation in the `f r = q` direction.
    simpa [fiberAddrImage, offsetAddrImage, y.2] using (Eq.symm (addrQ_split (k := k) (y := y.1)))
  · intro hq
    rcases hq with ⟨r, hr, hqeq⟩
    -- Build the witness point in the fiber explicitly as `joinEquiv k (x,r)`.
    refine ⟨⟨joinEquiv k (x, r), ?_⟩, by trivial, ?_⟩
    · -- `splitEquiv k (joinEquiv k (x,r)) = (x,r)` so the first coordinate is `x`.
      have h := congrArg Prod.fst (split_join (k := k) (x := (x, r)))
      simpa using h
    · -- Compute the address by the join refinement equation.
      simpa [fiberAddrImage, offsetAddrImage, hqeq] using (addrQ_join (k := k) (x := x) (r := r))

/-- Set-level cardinality: the refinement fiber address-image also has exactly 13 elements. -/
theorem fiberAddrImage_ncard (k : Nat) (x : Fin (SL k)) :
    (fiberAddrImage k x).ncard = base := by
  have hEq : fiberAddrImage k x = offsetAddrImage k x :=
    fiberAddrImage_eq_offsetAddrImage (k := k) (x := x)
  have hn : (fiberAddrImage k x).ncard = (offsetAddrImage k x).ncard := by
    simpa using congrArg Set.ncard hEq
  exact hn.trans (offsetAddrImage_ncard (k := k) (x := x))

end IndexOfIndexesSubcycle
