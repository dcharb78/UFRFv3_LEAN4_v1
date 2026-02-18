/-
# UFRF Unified Proof (Canonical Spine)
=====================================

This file is intentionally small: it *imports* the repo's validated Lean theorems
from `../lean/` and packages them into one conjunction.

Key design rule:
- No new axioms or "structure fields that assume the result".
- Everything here is a restatement / bundling of already-proved theorems.

Run the full validation suite with:

  `./scripts/verify.sh`
-/

import Frobenius_Emergence_Theorem
import Monster_AP12_Filter_Theorem
import Sigma1_Pattern_Theorem
import Tn_Recurrence_Universality_Theorem
import Tn_Recurrence_Universality_Higher_Theorem
import Tn_Recurrence_Universality_Degree8_Theorem
import Tn_Recurrence_Universality_Degree9_Theorem
import Tn_Recurrence_Universality_Degree10_Theorem
import Tn_Truncated_Engine
import Tn_Exact_Definition
import Tn_Truncation_Coherence
import Tn_Singleton_ClosedForm
import Tn_Pair_ClosedForm
import Unity_Cube_Identities
import Catalan_42_Theorem
import Exact_Cancellation_Theorem
import Exact_Cancellation_Product_Theorem
import Universal_Ticks_Theorem
import Decimal_Mod13_Concurrency_Theorem
import Decimal_Mod1001_Concurrency_Theorem
import System_Node_ModProd_Theorem
import Multidimensional_Ticks_Theorem
import Index_Of_Indexes_Theorem
import Index_Of_Indexes_Subcycle_Fiber_Theorem
import Index_Of_Indexes_Subintervals_Theorem
import Recursive_Grid_Generic_Base_Theorem
import Recursive_Grid_CarryCascade_Theorem
import Recursive_Grid_BlockPeriodicity_Theorem
import Recursive_Grid_Base13_Theorem
import Recursive_Grid_Base10_Theorem
import REST_Seam_Overlap_Theorem
import Observer_Scale_Projection_Composition_Theorem
import Observer_Tick_Axis_Choice_Theorem
import Observer_Tick_Axis_Family_Theorem
import Diminished_Chord_ZMod12_Theorem
import Chromatic_Breathing_52_Concurrency_Theorem
import Quarter_Cycle_ZMod_Theorem
import Fourier_ZMod13_Packaging_Theorem
import CycleStep_Orbit_Theorem
import CycleStep_Orbit_NAxes_Theorem
import Node_Building_Monotonicity_Theorem
import RecursiveGrid_IndexOfIndexes_Bridge_Theorem
import Prime13_Depth_Boundary_Theorem
import Spherical_Harmonic_Breathing_Theorem
import Coefficient_Denominator_Emergence_Theorem
import Fibonacci_Seed_Monster_Theorem
import Gap_Set_Prime_Theorem
import Semigroup_Concurrency_Theorem
import Semigroup_Standard_Semantics_Theorem
import UFRF_Minimal_Semigroup_Seed_Theorem
import UFRF_Global_Gap_Theorem
import Seed_Inevitability_GapSignature_Theorem
import Seed_To_Frobenius_Emergence_Bridge_Theorem
import Selection_Lens_Nonredundancy_Schema_Theorem
import Trinity_HalfStep_Dual_Theorem
import Angular_Embedding_Discrete_Quotient_Theorem
import SmallWorld_Overlap_Flip_Theorem
import Riemann_Zero_Exclusion_Theorem
import J_Function_Coefficient_Theorem
import Moonshine_LogMod_Coordinates_Theorem
import QuaternionGroup_Octave_Lens_Theorem
import Octonion_Fano_Nonassociative_Witness
import Fine_Structure_Internal_Consistency_Theorem
import UFRF_Core_DualTrinity_FineStructure_Theorem

open scoped BigOperators
open scoped ZMod

-- This file intentionally bundles a large number of proved theorems into one conjunction.
-- Raising the heartbeat limit keeps the `lake env lean context/...` check stable as we extend
-- the certified surface area (e.g. higher-degree `Tₙ` closed forms).
set_option maxHeartbeats 2000000

namespace UFRFUnified

/--
`UFRF_Canonical_Synthesis` is the repo's current "unified" theorem:

- Emergence: concrete Frobenius equalities for the Monster triple.
- Center resonance: `σ₁ = 3 * middle`.
- Universality: the same low-order `Tₙ` closed forms apply to any generator list
  (and in particular to both UFRF and Monster generator sets).
- Computable statistics: gap-prime depletion and Riemann-zero lattice distances.
- Moonshine anchor example: `c₁ = 47*59*71 + 1 = 196884` (exact integer identity, one certified hook).
- Pattern-of-patterns layer:
  - **Concurrency / commutativity**: order does not matter (`List.Perm` invariance),
    and multiset union corresponds to coefficient multiplication.
  - **Scale invariance**: scaling generators scales `Tₙ` by `k^n` (homogeneity).
 - Integer-kinematics anchor example: a fully deterministic composite closure specimen at `1001 = 7*11*13`
   (decimal cube-flip/return under base-10 scaling), treated as an exemplar of the general multi-axis rule,
   not a universal constant.
-/
theorem UFRF_Canonical_Synthesis :
    -- Frobenius emergence (concrete equalities)
    FrobeniusEmergence.frobeniusNumber 5 13 = 47
  ∧ FrobeniusEmergence.frobeniusNumber 7 11 = 59
  ∧ FrobeniusEmergence.frobeniusNumber 7 13 = 71
    -- Frobenius (full) Level-2 enumeration from UFRF generators
  ∧ FrobeniusEmergence.frobeniusAll FrobeniusEmergence.ufrfGenerators =
      [7, 11, 19, 23, 23, 39, 47, 59, 71, 119]
  ∧ FrobeniusEmergence.L2Full =
      [7, 11, 19, 23, 39, 47, 59, 71, 119]
  ∧ FrobeniusEmergence.monsterGenerators ⊆ FrobeniusEmergence.L2Full
    -- Monster selection rule: unique 3-term AP with common difference 12 inside `L2Full`
  ∧ MonsterAP12Filter.ap12Triples FrobeniusEmergence.L2Full = [(47, 59, 71)]
    -- Order-invariant uniqueness: the AP(12) start-point set in `L2Full` is exactly `{47}`
  ∧ MonsterAP12Filter.ap12StartSet FrobeniusEmergence.L2Full = {47}
    -- Center resonance (σ₁ pattern for the Monster triple)
  ∧ MonsterSigma1.sigma1 MonsterSigma1.monsterGenerators = 3 * 59
    -- Tₙ universality (examples: n=2 and n=3 for UFRF + Monster generator sets)
  ∧
    (TnRecurrence.TnFromGen TnRecurrence.ufrfGenerators 2 =
        (3 * TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 1 ^ 2
            + TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 2) / 12
      ∧
      TnRecurrence.TnFromGen TnRecurrence.monsterGenerators 2 =
        (3 * TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 1 ^ 2
            + TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 2) / 12)
  ∧
    (TnRecurrence.TnFromGen TnRecurrence.ufrfGenerators 3 =
        TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 1 *
            (TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 1 ^ 2
              + TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 2) / 8
      ∧
      TnRecurrence.TnFromGen TnRecurrence.monsterGenerators 3 =
        TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 1 *
            (TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 1 ^ 2
              + TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 2) / 8)
  ∧
    (TnRecurrence.TnFromGen TnRecurrence.ufrfGenerators 4 =
          (15 * (TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 1) ^ 4
            + 30 * (TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 1) ^ 2 *
                (TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 2)
            + 5 * (TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 2) ^ 2
            - 2 * TnRecurrence.sigmaQ TnRecurrence.ufrfGenerators 4) / 240
      ∧
      TnRecurrence.TnFromGen TnRecurrence.monsterGenerators 4 =
          (15 * (TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 1) ^ 4
            + 30 * (TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 1) ^ 2 *
                (TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 2)
            + 5 * (TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 2) ^ 2
            - 2 * TnRecurrence.sigmaQ TnRecurrence.monsterGenerators 4) / 240)
    -- Tₙ universality (extended: n=5..7 via coefficient formulas through degree 7)
  ∧
    (TnRecurrenceHigher.TnFromGenUpTo7 TnRecurrenceHigher.ufrfGenerators 5 =
          (3 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 5
            + 10 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 3
            + 5 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1
            - 2 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) / 96
      ∧
      TnRecurrenceHigher.TnFromGenUpTo7 TnRecurrenceHigher.monsterGenerators 5 =
          (3 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 5
            + 10 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 3
            + 5 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1
            - 2 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) / 96)
  ∧
    (TnRecurrenceHigher.TnFromGenUpTo7 TnRecurrenceHigher.ufrfGenerators 6 =
          (16 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            - 42 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2
            - 126 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2
            + 35 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 3
            + 315 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2
            + 315 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 4
            + 63 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 6) / 4032
      ∧
      TnRecurrenceHigher.TnFromGenUpTo7 TnRecurrenceHigher.monsterGenerators 6 =
          (16 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            - 42 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2
            - 126 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2
            + 35 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 3
            + 315 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2
            + 315 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 4
            + 63 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 6) / 4032)
  ∧
    (TnRecurrenceHigher.TnFromGenUpTo7 TnRecurrenceHigher.ufrfGenerators 7 =
          (16 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1
            - 42 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1
            - 42 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4 *
                  (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 3
            + 35 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 3 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1
            + 105 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                  (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 3
            + 63 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                  (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 5
            + 9 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 7) / 1152
      ∧
      TnRecurrenceHigher.TnFromGenUpTo7 TnRecurrenceHigher.monsterGenerators 7 =
          (16 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1
            - 42 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1
            - 42 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4 *
                  (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 3
            + 35 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 3 *
                  TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1
              + 105 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                    (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 3
              + 63 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                    (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 5
              + 9 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 7) / 1152)
    -- Tₙ universality (extended: degree 8 closed form)
  ∧
    (TnRecurrenceHigher.TnFromGenUpTo8 TnRecurrenceHigher.ufrfGenerators 8 =
          (135 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 8
            + 1260 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 6 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2
            + 3150 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 4 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2
            - 1260 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 2100 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 3
            - 2520 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 960 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 175 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 4
            - 420 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 320 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 84 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4) ^ 2
            - 144 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 8) / 34560
      ∧
      TnRecurrenceHigher.TnFromGenUpTo8 TnRecurrenceHigher.monsterGenerators 8 =
          (135 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 8
            + 1260 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 6 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2
            + 3150 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 4 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2
            - 1260 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 2100 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 3
            - 2520 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 960 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 175 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 4
            - 420 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 320 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 84 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4) ^ 2
            - 144 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 8) / 34560)
    -- Tₙ universality (extended: degree 9 closed form)
  ∧
    (TnRecurrenceHigher.TnFromGenUpTo9 TnRecurrenceHigher.ufrfGenerators 9 =
          (15 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 9
            + 180 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 7 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2
            + 630 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 5 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2
            - 252 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 5 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 700 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 3 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 3
            - 840 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 3 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 320 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 3 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 175 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 4
            - 420 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 320 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 84 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4) ^ 2
            - 144 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 8) / 7680
      ∧
      TnRecurrenceHigher.TnFromGenUpTo9 TnRecurrenceHigher.monsterGenerators 9 =
          (15 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 9
            + 180 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 7 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2
            + 630 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 5 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2
            - 252 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 5 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 700 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 3 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 3
            - 840 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 3 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 320 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 3 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 175 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 4
            - 420 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 320 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 84 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4) ^ 2
            - 144 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 8) / 7680)
    -- Tₙ universality (extended: degree 10 closed form)
  ∧
    (TnRecurrenceHigher.TnFromGenUpTo10 TnRecurrenceHigher.ufrfGenerators 10 =
          (99 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 10
            + 1485 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 8 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2
            + 6930 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 6 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2
            - 2772 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 6 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 11550 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 4 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 3
            - 13860 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 5280 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 5775 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 4
            - 13860 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 10560 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 2772 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4) ^ 2
            - 4752 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 8
            + 768 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 10
            + 385 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 5
            - 1540 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 3 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4
            + 1760 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6
            + 924 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4) ^ 2
            - 1584 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 8
            - 704 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.ufrfGenerators 6) / 101376
      ∧
      TnRecurrenceHigher.TnFromGenUpTo10 TnRecurrenceHigher.monsterGenerators 10 =
          (99 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 10
            + 1485 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 8 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2
            + 6930 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 6 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2
            - 2772 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 6 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 11550 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 4 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 3
            - 13860 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 5280 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 5775 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 4
            - 13860 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 10560 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 2772 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4) ^ 2
            - 4752 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 1) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 8
            + 768 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 10
            + 385 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 5
            - 1540 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 3 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4
            + 1760 * (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2) ^ 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6
            + 924 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                (TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4) ^ 2
            - 1584 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 2 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 8
            - 704 * TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 4 *
                TnRecurrenceHigher.sigmaQ TnRecurrenceHigher.monsterGenerators 6) / 101376)
    -- Exact cancellation: after removing `exp(X/2)`, `(exp X - 1)/X` becomes an even series.
  ∧ (PowerSeries.evalNegHom (A := ℚ) (ExactCancellation.g * ExactCancellation.EnegHalf) =
        ExactCancellation.g * ExactCancellation.EnegHalf)
    -- Exact cancellation (all generators): the same parity anchor composes over any generator list.
  ∧ (∀ gens : List Nat,
        PowerSeries.evalNegHom (A := ℚ) (ExactCancellationProduct.A gens * ExactCancellationProduct.bias gens) =
          ExactCancellationProduct.A gens * ExactCancellationProduct.bias gens)
    -- Coefficient denominator emergence (degrees ≤ 10)
  ∧ CoefficientDenominatorEmergence.DenominatorEmergenceSummary
    -- Gap-prime depletion computation (Monster semigroup bound used in the file)
  ∧ (GapSetPrime.monsterGapPrimeResidues.count 0 = 1 ∧ GapSetPrime.monsterGapPrimes.length = 143)
    -- Riemann zero / A-zero lattice distance computation
  ∧ RiemannZeroExclusion.monsterLattice.length > RiemannZeroExclusion.ufrfLattice.length
  ∧ RiemannZeroExclusion.monsterMean < RiemannZeroExclusion.ufrfMean
  ∧ (RiemannZeroExclusion.ufrfLatticeTiny.length < RiemannZeroExclusion.ufrfLattice.length
      ∧ RiemannZeroExclusion.monsterLatticeTiny.length < RiemannZeroExclusion.monsterLattice.length
      ∧ RiemannZeroExclusion.ufrfMean < RiemannZeroExclusion.ufrfMeanTiny
      ∧ RiemannZeroExclusion.monsterMean < RiemannZeroExclusion.monsterMeanTiny)
    -- j-function coefficient synthesis (product + 1)
  ∧ JFunctionCoefficient.jCoefficient 1 = 196884
  ∧
    JFunctionCoefficient.jCoefficient 1 =
      JFunctionCoefficient.elementarySymmetric JFunctionCoefficient.monsterGenerators 3 + 1
    -- Moonshine in (log, mod) coordinates: exact decade/leading block + mod-13 flip signature.
  ∧ (UniversalTicks.decade 196884 = 5 ∧ UniversalTicks.leadingBlock 196884 = 1 ∧ (196884 % 13 = 12))
    -- Concurrency (order invariance)
  ∧ (∀ {xs ys : List Nat}, List.Perm xs ys → TnRecurrence.aCoeffs xs = TnRecurrence.aCoeffs ys)
  ∧ (∀ {xs ys : List Nat} {n : Nat}, List.Perm xs ys → (GapSetPrime.semigroupPred xs n ↔ GapSetPrime.semigroupPred ys n))
  ∧ (∀ (gens : List Nat) (n : Nat),
      GapSetPrime.semigroupPred gens n ↔ n ∈ AddSubmonoid.closure (GapSetPrime.genSet gens))
  ∧ (∀ n : Nat,
      GapSetPrime.semigroupPred GapSetPrime.ufrfGenerators n ↔
        GapSetPrime.semigroupPred GapSetPrime.ufrfSeedGenerators n)
    -- Seed inevitability (semigroup lens): the gap signature `{1,2,4}` forces the `[3,5,7]` semigroup.
  ∧ (∀ (gens : List Nat) (n : Nat),
      ({m : Nat | 0 < m ∧ ¬ GapSetPrime.semigroupPred gens m} = ({1, 2, 4} : Set Nat)) →
        (GapSetPrime.semigroupPred gens n ↔
          GapSetPrime.semigroupPred GapSetPrime.ufrfSeedGenerators n))
    -- Seed → Frobenius bridge: semigroup-closure redundancy does *not* carry to the Frobenius/AP(12) emergence lens.
  ∧ SeedToFrobeniusBridge.seed_variants_ap12_summary
    -- Schema-level generalization: semigroup redundancy does *not* imply emergence-selection redundancy (membership rules).
  ∧ SelectionLensNonredundancy.selection_lens_nonredundancy_summary
    -- Emergence (unbounded): for UFRF generators, everything `n ≥ 5` is reachable.
  ∧ (∀ n : Nat, 5 ≤ n → GapSetPrime.semigroupPred GapSetPrime.ufrfGenerators n)
    -- Emergence (gaps, global): the only positive gaps are `{1,2,4}`.
  ∧ ({n : Nat | 0 < n ∧ ¬ GapSetPrime.semigroupPred GapSetPrime.ufrfGenerators n} = ({1, 2, 4} : Set Nat))
    -- Trinity dual / half-step: mod-26 is the concurrent product of (mod-13, mod-2).
  ∧ (∀ a b : Nat, a ≡ b [MOD 26] ↔ (a ≡ b [MOD 13] ∧ a ≡ b [MOD 2]))
    -- Discrete angular-embedding quotient: antipodal observer identification yields 3 classes.
  ∧ AngularEmbeddingDiscreteQuotient.angular_embedding_discrete_summary
    -- Flip point (6.5) in half-step indexing: `2*6 + 1 = 13`.
  ∧ (TrinityHalfStepDual.halfIndex 6 = 13)
    -- Flip signature: source on mod-13 axis, half-step on mod-2 axis.
  ∧ ((13 ≡ 0 [MOD 13]) ∧ (13 ≡ 1 [MOD 2]))
    -- Small-world traversal: overlap (±1) + flip (±6) reaches any residue in ≤3 steps (and 3 is sometimes necessary).
  ∧ SmallWorldOverlapFlip.overlap_flip_small_world_stmt
    -- Concurrency (multiset add corresponds to coefficient multiplication)
  ∧ (∀ s t : Multiset Nat,
      TnRecurrence.aCoeffsMS (s + t) =
        TnRecurrence.mulCoeffs (TnRecurrence.aCoeffsMS s) (TnRecurrence.aCoeffsMS t))
    -- Scale invariance (homogeneity)
  ∧ (∀ (k : Nat) (gens : List Nat) (n : Nat),
      TnRecurrence.TnFromGen (gens.map (fun d => k * d)) n =
        (k : ℚ) ^ n * TnRecurrence.TnFromGen gens n)
    -- Exact (all `n`): scaling ↔ homogeneity for `Tₙ`
  ∧ (∀ (k : Nat) (gens : List Nat) (n : Nat),
      TnExact.TnFromGen (gens.map (fun d => k * d)) n =
        (k : ℚ) ^ n * TnExact.TnFromGen gens n)
    -- Exact (T-level concurrency): binomial convolution under multiset union (truncated degree `N`)
  ∧ (∀ (N : Nat) (s t : Multiset Nat) (n : Nat), n ≤ N →
      TnExact.TnTrunc N (s + t) n =
        ∑ x ∈ Finset.antidiagonal n,
          (Nat.choose n x.1 : ℚ) * TnExact.TnTrunc N s x.1 * TnExact.TnTrunc N t x.2)
    -- Exact (T-level concurrency, no truncation parameter): binomial convolution for `TnFromMS`.
  ∧ (∀ (s t : Multiset Nat) (n : Nat),
      TnExact.TnFromMS (s + t) n =
        ∑ x ∈ Finset.antidiagonal n,
          (Nat.choose n x.1 : ℚ) * TnExact.TnFromMS s x.1 * TnExact.TnFromMS t x.2)
    -- Exact (singleton closed form): `Tₙ({d}) = d^n / (n+1)`.
  ∧ (∀ (d n : Nat),
      TnExact.TnFromMS ({d} : Multiset Nat) n = (d ^ n : ℚ) / (n + 1 : ℚ))
      -- Exact (two singleton closed form): `{a,b}` is the binomial convolution of the singleton laws.
    ∧ (∀ (a b n : Nat),
        TnExact.TnFromMS ({a} + {b} : Multiset Nat) n =
          ∑ x ∈ Finset.antidiagonal n,
            (Nat.choose n x.1 : ℚ) *
              ((a ^ x.1 : ℚ) / (x.1 + 1 : ℚ)) *
              ((b ^ x.2 : ℚ) / (x.2 + 1 : ℚ)))
      -- Screenshot anchor: cube identities (mod-13 return, flip, golden-ratio cubic).
    ∧ ((3 ^ 3 : Nat) % 13 = 1)
    ∧ ((2 ^ 3 : Nat) - 1 = 7)
    ∧ (Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1)
      -- Fibonacci seed anchor: Monster primes as `-1` shifts of Fibonacci-derived products.
    ∧ ((FibonacciSeed.F 4 + FibonacciSeed.F 2) * (FibonacciSeed.F 7 - FibonacciSeed.F 2) - 1 = 47)
    ∧ ((FibonacciSeed.F 5 + FibonacciSeed.F 2) * (FibonacciSeed.F 6 + FibonacciSeed.F 3) - 1 = 59)
    ∧ ((FibonacciSeed.F 5 + FibonacciSeed.F 2) * (FibonacciSeed.F 7 - FibonacciSeed.F 2) - 1 = 71)
      -- Screenshot anchor: Catalan(5) = 42 ("architectures")
    ∧ (catalan 5 = 42)
      -- Discrete scale invariance: base-10 "universal ticks" (leading block invariant under 10^k scaling).
    ∧ (∀ (n k : Nat), n ≠ 0 → UniversalTicks.leadingBlock (n * 10 ^ k) = UniversalTicks.leadingBlock n)
    ∧ (∀ n : Nat, n ≠ 0 → 1 ≤ UniversalTicks.leadingBlock n ∧ UniversalTicks.leadingBlock n < 10)
      -- Decimal/13-cycle concurrency: scaling by `10^6` returns to the same mod-13 position.
    ∧ ((10 ^ 6 : Nat) % 13 = 1)
    ∧ (∀ n : Nat, (n * 10 ^ 6) % 13 = n % 13)
      -- Decimal/13-cycle half-period: `10^3 ≡ -1 (mod 13)` and hence a 3-decade "flip".
    ∧ ((10 ^ 3 : Nat) % 13 = 12)
    ∧ (∀ n : Nat, ((n * 10 ^ 3) + n) % 13 = 0)
      -- Decimal/1001 concurrency: `1001 = 7*11*13` and `10^6 ≡ 1 (mod 1001)`.
    ∧ (DecimalMod1001.M = 7 * 11 * 13)
    ∧ ((10 ^ 3 : Nat) + 1 = DecimalMod1001.M)
    ∧ ((10 ^ 6 : Nat) % DecimalMod1001.M = 1)
    ∧ (∀ n : Nat, (n * 10 ^ 6) % DecimalMod1001.M = n % DecimalMod1001.M)
    ∧ (∀ n : Nat, ((n * 10 ^ 3) + n) % DecimalMod1001.M = 0)
      -- Systems become nodes: coprime modular axes glue to the product modulus (CRT list form).
    ∧ (∀ (a b : Nat) (ms : List Nat), ms.Pairwise Nat.Coprime →
        (a ≡ b [MOD ms.prod] ↔ ∀ m ∈ ms, a ≡ b [MOD m]))
      -- Multidimensional modular axes under base-10 ticks (a few concrete anchors).
    ∧ (∀ n : Nat, (MultidimensionalTicks.tick10 1 n) % 3 = n % 3)
    ∧ (∀ n : Nat, (MultidimensionalTicks.tick10 2 n) % 11 = n % 11)
    ∧ (∀ n : Nat, (MultidimensionalTicks.tick10 2 n) % 4 = 0)
      -- General periodicity: if `gcd(10,m)=1`, then `10^φ(m) ≡ 1 (mod m)` and ticks return mod `m`.
    ∧ (∀ (n m : Nat), 1 < m → (10 : Nat).Coprime m →
        (MultidimensionalTicks.tick10 (Nat.totient m) n) % m = n % m)
      -- Observer-scale view: on any coprime axis, every tick is a permutation on the residue space.
    ∧ (∀ (m k : Nat), (10 : Nat).Coprime m →
        Function.Bijective (fun x : ZMod m => ((10 : ZMod m) ^ k) * x))
      -- Combined coordinates: leading-block (scale axis) + residue (cycle axis) return together at tick `φ(m)`.
    ∧ (∀ (n m : Nat), n ≠ 0 → 1 < m → (10 : Nat).Coprime m →
        (UniversalTicks.leadingBlock (MultidimensionalTicks.tick10 (Nat.totient m) n) =
            UniversalTicks.leadingBlock n
          ∧ (MultidimensionalTicks.tick10 (Nat.totient m) n) % m = n % m))
      -- Multi-axis concurrency: one tick length returns simultaneously on two modular axes.
    ∧ (∀ (n m₁ m₂ : Nat), 1 < m₁ → 1 < m₂ → (10 : Nat).Coprime m₁ → (10 : Nat).Coprime m₂ →
        (MultidimensionalTicks.tick10 (Nat.lcm (Nat.totient m₁) (Nat.totient m₂)) n) % m₁ = n % m₁
          ∧ (MultidimensionalTicks.tick10 (Nat.lcm (Nat.totient m₁) (Nat.totient m₂)) n) % m₂ = n % m₂)
      -- Finite-family concurrency: one global tick returns on every axis in a finite list of moduli.
    ∧ (∀ (n : Nat) (ms : List Nat), n ≠ 0 →
        (∀ m ∈ ms, 1 < m) → (∀ m ∈ ms, (10 : Nat).Coprime m) →
          (UniversalTicks.leadingBlock (MultidimensionalTicks.tick10 (MultidimensionalTicks.totientLCM ms) n) =
              UniversalTicks.leadingBlock n
            ∧ (∀ m ∈ ms,
                (MultidimensionalTicks.tick10 (MultidimensionalTicks.totientLCM ms) n) % m = n % m)))
      -- One global tick that does BOTH return and absorption (cycle axes + 2/5 absorption axes).
    ∧ (∀ (n : Nat) (ms : List Nat) (a₂ a₅ : Nat), n ≠ 0 →
        (∀ m ∈ ms, 1 < m) → (∀ m ∈ ms, (10 : Nat).Coprime m) →
          UniversalTicks.leadingBlock (MultidimensionalTicks.tick10
              (MultidimensionalTicks.globalTick ms a₂ a₅) n) =
            UniversalTicks.leadingBlock n
            ∧ (∀ m ∈ ms,
                (MultidimensionalTicks.tick10 (MultidimensionalTicks.globalTick ms a₂ a₅) n) % m = n % m)
            ∧ (MultidimensionalTicks.tick10 (MultidimensionalTicks.globalTick ms a₂ a₅) n) % (2 ^ a₂) = 0
            ∧ (MultidimensionalTicks.tick10 (MultidimensionalTicks.globalTick ms a₂ a₅) n) % (5 ^ a₅) = 0)
      -- Mixed observer-state packaging: cycle returns + absorption collapse under the same global tick.
    ∧ (∀ (n : Nat) (ms : List Nat) (a₂ a₅ : Nat), n ≠ 0 →
        (∀ m ∈ ms, 1 < m) → (∀ m ∈ ms, (10 : Nat).Coprime m) →
          MultidimensionalTicks.systemCoordMixed ms a₂ a₅
              (MultidimensionalTicks.tick10 (MultidimensionalTicks.globalTick ms a₂ a₅) n) =
            (UniversalTicks.leadingBlock n, ms.map (fun m => n % m), 0, 0))
      -- “System node” packaging: the whole finite coordinate vector is invariant at the global tick.
    ∧ (∀ (n : Nat) (ms : List Nat), n ≠ 0 →
        (∀ m ∈ ms, 1 < m) → (∀ m ∈ ms, (10 : Nat).Coprime m) →
          MultidimensionalTicks.systemCoord ms
              (MultidimensionalTicks.tick10 (MultidimensionalTicks.totientLCM ms) n) =
            MultidimensionalTicks.systemCoord ms n)
      -- System composition: global ticks compose by LCM under list append.
    ∧ (∀ (ms₁ ms₂ : List Nat),
        MultidimensionalTicks.totientLCM (ms₁ ++ ms₂) =
          Nat.lcm (MultidimensionalTicks.totientLCM ms₁) (MultidimensionalTicks.totientLCM ms₂))
      -- System composition: combined systems are invariant at the combined tick.
    ∧ (∀ (n : Nat) (ms₁ ms₂ : List Nat), n ≠ 0 →
        (∀ m ∈ ms₁, 1 < m) → (∀ m ∈ ms₂, 1 < m) →
        (∀ m ∈ ms₁, (10 : Nat).Coprime m) → (∀ m ∈ ms₂, (10 : Nat).Coprime m) →
          MultidimensionalTicks.systemCoord (ms₁ ++ ms₂)
              (MultidimensionalTicks.tick10
                  (Nat.lcm (MultidimensionalTicks.totientLCM ms₁)
                    (MultidimensionalTicks.totientLCM ms₂)) n) =
            MultidimensionalTicks.systemCoord (ms₁ ++ ms₂) n)
      -- Discrete nesting: index-of-indexes for the 13-cycle node counts (13, 169, 2197, ...).
    ∧ (IndexOfIndexes.SL 2 = 169)
    ∧ (IndexOfIndexes.SL 3 = 2197)
    ∧ (∀ k : Nat, Function.Bijective (IndexOfIndexes.splitEquiv k))
    ∧ (∀ k : Nat, Function.Bijective (IndexOfIndexes.digitsEquiv k))
    ∧ (∀ k : Nat, Function.Injective (IndexOfIndexes.addrQ k))
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)),
        Fintype.card { y : Fin (IndexOfIndexes.SL (k + 1)) //
          (IndexOfIndexes.splitEquiv k y).1 = x } = IndexOfIndexes.base)
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)) (r : Fin IndexOfIndexes.base),
        IndexOfIndexes.addrQ (k + 1) (IndexOfIndexes.joinEquiv k (x, r)) =
          IndexOfIndexes.addrQ k x + (r.1 : ℚ) / (IndexOfIndexes.SL (k + 1) : ℚ))
    ∧ (∀ (k : Nat) (y : Fin (IndexOfIndexes.SL (k + 1))),
        IndexOfIndexes.addrQ (k + 1) y =
          IndexOfIndexes.addrQ k (IndexOfIndexes.splitEquiv k y).1 +
            (((IndexOfIndexes.splitEquiv k y).2).1 : ℚ) / (IndexOfIndexes.SL (k + 1) : ℚ))
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)) (r : Fin IndexOfIndexes.base),
        IndexOfIndexes.addrQ k x ≤ IndexOfIndexes.addrQ (k + 1) (IndexOfIndexes.joinEquiv k (x, r))
          ∧ IndexOfIndexes.addrQ (k + 1) (IndexOfIndexes.joinEquiv k (x, r)) <
              IndexOfIndexes.addrQ k x + (1 : ℚ) / (IndexOfIndexes.SL k : ℚ))
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)),
        IndexOfIndexesSubcycle.fiberAddrImage k x = IndexOfIndexesSubcycle.offsetAddrImage k x)
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)),
        IndexOfIndexesSubcycle.fiberAddrImage k x ⊆
          IndexOfIndexesSubintervals.coarseInterval k x)
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)),
        Function.Injective (fun r : Fin IndexOfIndexes.base =>
          IndexOfIndexes.addrQ k x + (r.1 : ℚ) / (IndexOfIndexes.SL (k + 1) : ℚ)))
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)),
        (IndexOfIndexesSubcycle.offsetAddrImage k x).ncard = IndexOfIndexes.base)
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL k)),
        (IndexOfIndexesSubcycle.fiberAddrImage k x).ncard = IndexOfIndexes.base)
      -- Depth-boundary prime: if a prime divides `13^k`, it must be `13`.
    ∧ (∀ (p k : Nat), p.Prime → p ∣ 13 ^ k → p = 13)
      -- Recursive grid (base-13 depth digits + exact carry).
    ∧ (RecursiveGridBase13.digit 0 1000 = 12 ∧
        RecursiveGridBase13.digit 1 1000 = 11 ∧
        RecursiveGridBase13.digit 2 1000 = 5 ∧
        RecursiveGridBase13.digit 3 1000 = 0)
    ∧ (∀ t : Nat, t % RecursiveGridBase13.base = RecursiveGridBase13.base - 1 →
        (t + 1) % RecursiveGridBase13.base = 0 ∧
          (t + 1) / RecursiveGridBase13.base = t / RecursiveGridBase13.base + 1)
    ∧ (∀ d t : Nat,
        RecursiveGridBase13.digit (d + 1) t = RecursiveGridBase13.digit d (t / RecursiveGridBase13.base))
      -- Bridge: depth-0 digit is mod 13, and `splitEquiv` is exactly `(div, mod)` on values.
    ∧ (∀ t : Nat, RecursiveGridBase13.digit 0 t = t % 13)
    ∧ (∀ (k : Nat) (x : Fin (IndexOfIndexes.SL (k + 1))),
        ((IndexOfIndexes.splitEquiv k x).1).1 = x.1 / IndexOfIndexes.base
          ∧ ((IndexOfIndexes.splitEquiv k x).2).1 = x.1 % IndexOfIndexes.base)
      -- Block periodicity: low depths only see `t mod b^k` (node shifts are invisible below depth `k`).
    ∧ (∀ (b k d t m : Nat), 1 < b → d < k →
        RecursiveGridGenericBase.digit (b := b) d (t + m * b ^ k) =
          RecursiveGridGenericBase.digit (b := b) d t)
    ∧ (∀ (b k d m : Nat), 1 < b → d < k →
        RecursiveGridGenericBase.digit (b := b) d (m * b ^ k + (b ^ k - 1)) = b - 1)
    ∧ (∀ (b k d m : Nat), 1 < b → d < k →
        RecursiveGridGenericBase.digit (b := b) d (m * b ^ k + (b ^ k - 1) + 1) = 0)
      -- Spherical-harmonic counting anchors (self-reference + scale doubling).
    ∧ (SphericalHarmonicBreathing.harmonicsAtDegree SphericalHarmonicBreathing.flipDegree =
          SphericalHarmonicBreathing.breathingCycle
        ∧
        SphericalHarmonicBreathing.totalHarmonics (SphericalHarmonicBreathing.breathingCycle - 1) =
          SphericalHarmonicBreathing.breathingCycle ^ 2
        ∧
        (2 * SphericalHarmonicBreathing.conjugatePairs SphericalHarmonicBreathing.flipDegree + 1 =
          SphericalHarmonicBreathing.breathingCycle)
        ∧
        SphericalHarmonicBreathing.totalHarmonics (SphericalHarmonicBreathing.breathingCycle ^ 2 - 1) =
          SphericalHarmonicBreathing.breathingCycle ^ 4)
      -- Two-axis bookkeeping: polar + azimuthal complexity is conserved.
    ∧ (∀ (ℓ m : Nat) (h : m ≤ ℓ),
        SphericalHarmonicBreathing.polarNodes ℓ m h + SphericalHarmonicBreathing.azimuthalNodes m = ℓ)
      -- Generalized (all truncation orders): multiset add ↔ coefficient multiplication
    ∧ (∀ (N : Nat) (s t : Multiset Nat),
        TnTruncated.aCoeffsMS N (s + t) =
          TnTruncated.mulCoeffs N (TnTruncated.aCoeffsMS N s) (TnTruncated.aCoeffsMS N t))
      -- Generalized (all truncation orders): scaling ↔ homogeneity
    ∧ (∀ (N k : Nat) (gens : List Nat),
        TnTruncated.aCoeffs N (gens.map (fun d => k * d)) =
          TnTruncated.scaleCoeffs N k (TnTruncated.aCoeffs N gens))
      -- Cross-link: Monster dimension lies strictly between consecutive harmonic-square layers.
    ∧ (SphericalHarmonicBreathing.totalHarmonics 442 < 196884 ∧ 196884 < SphericalHarmonicBreathing.totalHarmonics 443)
      -- Extend Moonshine log/mod coordinates to `c₂`.
    ∧ (UniversalTicks.decade MoonshineLogMod.c2Nat = 7
        ∧ UniversalTicks.leadingBlock MoonshineLogMod.c2Nat = 2
        ∧ MoonshineLogMod.c2Nat % 13 = 2)
      -- Exactness of the `c₂` denominator-13 formula: `13 ∣ numerator(c₂)`.
    ∧ (13 ∣
        (8 * (JFunctionCoefficient.monster_e1 : ℤ) * (JFunctionCoefficient.monster_e3 : ℤ)
          + 61 * (JFunctionCoefficient.monster_e2 : ℤ)
          - 31 * (JFunctionCoefficient.monster_e1 : ℤ)
          + 9800))
    ∧ (∀ n : Nat, n ≠ 0 →
        RecursiveGridBase10.digit (UniversalTicks.decade n) n = UniversalTicks.leadingBlock n)
    ∧ DiminishedChordZMod12.three_nsmul_cycle_statement
    ∧ DiminishedChordZMod12.three_nsmul_cycle_scaled_statement
      ∧ ChromaticBreathing52.chromatic_breathing_52_statement
      ∧ ChromaticBreathing52.chromatic_breathing_52_orbitSize_statement
      ∧ QuarterCycleZMod.quarter_nsmul_cycle_statement
      ∧ (∀ m s : Nat, CycleStepOrbit.orbitSize m s • (s : ZMod m) = 0)
      ∧ (∀ m s n : Nat, 0 < m →
          (n • (s : ZMod m) = 0 ↔ CycleStepOrbit.orbitSize m s ∣ n))
      ∧ (∀ m₁ m₂ s : Nat, 0 < m₁ → 0 < m₂ → Nat.Coprime m₁ m₂ →
          CycleStepOrbit.orbitSize (m₁ * m₂) s =
            Nat.lcm (CycleStepOrbit.orbitSize m₁ s) (CycleStepOrbit.orbitSize m₂ s))
      ∧ (∀ k m s : Nat, 0 < k →
          CycleStepOrbit.orbitSize (k * m) (k * s) = CycleStepOrbit.orbitSize m s)
      ∧ (∀ m₁ m₂ s : Nat, Nat.Coprime m₁ m₂ →
          Nat.lcm (CycleStepOrbit.orbitSize m₁ s) (CycleStepOrbit.orbitSize m₂ s) •
            (s : ZMod (m₁ * m₂)) = 0)
    ∧ (∀ (ms : List Nat) (s : Nat), ms.Pairwise Nat.Coprime →
        CycleStepOrbit.orbitLcm ms s = (ms.map (fun m => CycleStepOrbit.orbitSize m s)).prod)
    ∧ (∀ (ms : List Nat) (s : Nat), ms.Pairwise Nat.Coprime →
        (∀ m ∈ ms, Nat.Coprime m s) →
          CycleStepOrbit.orbitLcm ms s = ms.prod)
      ∧ (∀ (ms : List Nat) (s : Nat), ms.Pairwise Nat.Coprime →
          CycleStepOrbit.orbitLcm ms s • (s : ZMod ms.prod) = 0)
      ∧ (∀ (ms : List Nat) (s : Nat), ms.Pairwise Nat.Coprime →
          (∀ m ∈ ms, 0 < m) →
            CycleStepOrbit.orbitSize ms.prod s = CycleStepOrbit.orbitLcm ms s)
      ∧ QuaternionOctaveLens.q8_card_statement
      ∧ QuaternionOctaveLens.q8_noncomm_statement
      ∧ QuaternionOctaveLens.q8_order4_statement
      ∧ OctonionFano.nonassoc_witness_statement
      ∧ (∀ {E : Type*} [AddCommGroup E] [Module ℂ E]
          (Φ : ZMod 13 → E) (t k : ZMod 13),
          𝓕 (FourierZMod.translate (N := 13) (E := E) t Φ) k =
            ZMod.stdAddChar (t * k) • 𝓕 Φ k)
      ∧ (∀ (f g : ZMod 13 → ℂ) (k : ZMod 13),
          𝓕 (FourierZMod.conv (N := 13) f g) k = (𝓕 f k) * (𝓕 g k))
      ∧ (∀ {E : Type*} [AddCommGroup E] [Module ℂ E]
          (Ψ : ZMod 13 → E) (k : ZMod 13),
          𝓕⁻ Ψ k = (13 : ℂ)⁻¹ • ∑ j : ZMod 13, ZMod.stdAddChar (j * k) • Ψ j)
      ∧ (∀ {E : Type*} [AddCommGroup E] [Module ℂ E]
          (Φ : ZMod 13 → E),
          𝓕 (𝓕 Φ) = fun j : ZMod 13 => (13 : ℂ) • Φ (-j)) := by
  refine And.intro FrobeniusEmergence.frobenius_5_13 ?_
  refine And.intro FrobeniusEmergence.frobenius_7_11 ?_
  refine And.intro FrobeniusEmergence.frobenius_7_13 ?_
  refine And.intro FrobeniusEmergence.frobeniusAll_ufrfGenerators ?_
  refine And.intro FrobeniusEmergence.L2Full_eq ?_
  refine And.intro FrobeniusEmergence.monsterGenerators_subset_L2Full ?_
  refine And.intro MonsterAP12Filter.ap12Triples_L2Full ?_
  refine And.intro MonsterAP12Filter.ap12StartSet_L2Full ?_
  refine And.intro MonsterSigma1.sigma1_is_three_times_middle ?_
  refine And.intro TnRecurrence.T2_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrence.T3_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrence.T4_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrenceHigher.T5_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrenceHigher.T6_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrenceHigher.T7_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrenceHigher.T8_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrenceHigher.T9_universal_for_ufrf_and_monster ?_
  refine And.intro TnRecurrenceHigher.T10_universal_for_ufrf_and_monster ?_
  refine And.intro ExactCancellation.g_mul_expNegHalf_is_even ?_
  refine And.intro ?_ ?_
  · intro gens
    simpa using (ExactCancellationProduct.A_mul_bias_is_even gens)
  refine And.intro CoefficientDenominatorEmergence.denominator_emergence_summary ?_
  refine And.intro GapSetPrime.position_zero_depleted ?_
  refine And.intro RiemannZeroExclusion.monster_lattice_denser ?_
  refine And.intro RiemannZeroExclusion.monster_mean_distance_smaller ?_
  refine And.intro RiemannZeroExclusion.lattice_truncation_inflates_mean ?_
  refine And.intro JFunctionCoefficient.j_coefficient_c1_value ?_
  refine And.intro JFunctionCoefficient.j_coefficient_c1_equals_product_plus_one ?_
  refine And.intro ?_ ?_
  · refine And.intro MoonshineLogMod.c1_decade_196884 ?_
    refine And.intro MoonshineLogMod.c1_leadingBlock_196884 ?_
    exact MoonshineLogMod.c1_mod13_flip_196884
  refine And.intro ?_ ?_
  · intro xs ys hperm
    simpa using (TnRecurrence.aCoeffs_perm hperm)
  refine And.intro ?_ ?_
  · intro xs ys n hperm
    simpa using (GapSetPrime.semigroupPred_perm (xs := xs) (ys := ys) hperm n)
  refine And.intro ?_ ?_
  · intro gens n
    simpa using (GapSetPrime.semigroupPred_iff_mem_closure gens n)
  refine And.intro ?_ ?_
  · intro n
    simpa using (GapSetPrime.semigroupPred_ufrf_iff_seed n)
  refine And.intro ?_ ?_
  · intro gens n hGaps
    simpa using
      (GapSetPrime.semigroupPred_iff_seed_of_positiveGaps_eq (gens := gens) (hGaps := hGaps) (n := n))
  refine And.intro SeedToFrobeniusBridge.ap12From_seed_variants_summary ?_
  refine And.intro SelectionLensNonredundancy.selection_lens_nonredundancy_summary_proof ?_
  refine And.intro ?_ ?_
  · intro n hn
    simpa using (GapSetPrime.ufrf_semigroupPred_ge_5 n hn)
  refine And.intro GapSetPrime.ufrf_positive_gaps_eq ?_
  refine And.intro ?_ ?_
  · intro a b
    simpa using (TrinityHalfStepDual.modEq_26_iff_modEq_13_and_modEq_2 a b)
  refine And.intro AngularEmbeddingDiscreteQuotient.angular_embedding_discrete_summary_proof ?_
  refine And.intro TrinityHalfStepDual.halfIndex_flip ?_
  refine And.intro TrinityHalfStepDual.flip_axis_signature ?_
  refine And.intro SmallWorldOverlapFlip.overlap_flip_small_world_stmt_proven ?_
  refine And.intro ?_ ?_
  · intro s t
    simpa using (TnRecurrence.aCoeffsMS_add s t)
  refine And.intro ?_ ?_
  · intro k gens n
    simpa using (TnRecurrence.TnFromGen_scale k gens n)
  refine And.intro ?_ ?_
  · intro k gens n
    simpa using (TnExact.TnFromGen_scale k gens n)
  refine And.intro ?_ ?_
  · intro N s t n hn
    simpa using (TnExact.TnTrunc_add N s t n hn)
  refine And.intro ?_ ?_
  · intro s t n
    simpa using (TnExact.TnFromMS_add s t n)
  refine And.intro ?_ ?_
  · intro d n
    simpa using (TnExact.TnFromMS_singleton d n)
  refine And.intro ?_ ?_
  · intro a b n
    simpa using (TnExact.TnFromMS_pair_singletons a b n)
  refine And.intro UnityCube.trinity_cubed_returns_to_source ?_
  refine And.intro UnityCube.geometry_cubed_minus_source ?_
  refine And.intro UnityCube.goldenRatio_cube ?_
  refine And.intro FibonacciSeed.monster47_fib ?_
  refine And.intro FibonacciSeed.monster59_fib ?_
  refine And.intro FibonacciSeed.monster71_fib ?_
  refine And.intro UnityCatalan.catalan_five_eq_42 ?_
  refine And.intro ?_ ?_
  · intro n k hn
    simpa using UniversalTicks.leadingBlock_mul_pow10 n k hn
  refine And.intro ?_ ?_
  · intro n hn
    simpa using UniversalTicks.leadingBlock_bounds n hn
  refine And.intro DecimalMod13.ten_pow_six_mod13 ?_
  refine And.intro DecimalMod13.mul_ten_pow_six_mod13_all ?_
  refine And.intro DecimalMod13.ten_pow_three_mod13 ?_
  refine And.intro (fun n => DecimalMod13.mul_ten_pow_three_add_self_mod13 n) ?_
  refine And.intro DecimalMod1001.M_factor ?_
  refine And.intro DecimalMod1001.ten_pow_three_add_one ?_
  refine And.intro DecimalMod1001.ten_pow_six_mod ?_
  refine And.intro DecimalMod1001.mul_ten_pow_six_mod_all ?_
  refine And.intro (fun n => DecimalMod1001.mul_ten_pow_three_add_self_mod n) ?_
  refine And.intro ?_ ?_
  · intro a b ms hcop
    simpa using (SystemNodeModProd.modEq_prod_iff_forall_mem (a := a) (b := b) (ms := ms) hcop)
  refine And.intro (fun n => MultidimensionalTicks.tick10_mod3_return_every_decade n) ?_
  refine And.intro (fun n => MultidimensionalTicks.tick10_mod11_return_every_two_decades n) ?_
  refine And.intro (fun n => MultidimensionalTicks.tick10_mod4_absorbs_after_two_decades n) ?_
  refine And.intro ?_ ?_
  · intro n m hm hcop
    simpa using (MultidimensionalTicks.tick10_mod_invariant_totient n m hm hcop)
  refine And.intro ?_ ?_
  · intro m k hcop
    simpa using (MultidimensionalTicks.tick10_zmod_bijective m k hcop)
  refine And.intro ?_ ?_
  · intro n m hn hm hcop
    simpa using (MultidimensionalTicks.tick10_totient_invariant_leadingBlock_and_mod n m hn hm hcop)
  refine And.intro ?_ ?_
  · intro n m₁ m₂ hm₁ hm₂ hcop₁ hcop₂
    simpa using (MultidimensionalTicks.tick10_mod_invariant_lcm_totients n m₁ m₂ hm₁ hm₂ hcop₁ hcop₂)
  refine And.intro ?_ ?_
  · intro n ms hn hgt hcop
    simpa using (MultidimensionalTicks.tick10_totientLCM_invariant_leadingBlock_and_mods n ms hn hgt hcop)
  refine And.intro ?_ ?_
  · intro n ms a₂ a₅ hn hgt hcop
    simpa using (MultidimensionalTicks.tick10_globalTick_return_and_absorb n ms a₂ a₅ hn hgt hcop)
  refine And.intro ?_ ?_
  · intro n ms a₂ a₅ hn hgt hcop
    simpa using (MultidimensionalTicks.systemCoordMixed_invariant_at_globalTick n ms a₂ a₅ hn hgt hcop)
  refine And.intro ?_ ?_
  · intro n ms hn hgt hcop
    simpa using (MultidimensionalTicks.systemCoord_invariant_at_totientLCM n ms hn hgt hcop)
  refine And.intro ?_ ?_
  · intro ms₁ ms₂
    simpa using (MultidimensionalTicks.totientLCM_append ms₁ ms₂)
  refine And.intro ?_ ?_
  · intro n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂
    simpa using
      (MultidimensionalTicks.systemCoord_invariant_at_lcm_subsystems n ms₁ ms₂ hn hgt₁ hgt₂ hcop₁ hcop₂)
  refine And.intro IndexOfIndexes.SL2 ?_
  refine And.intro IndexOfIndexes.SL3 ?_
  refine And.intro ?_ ?_
  · intro k
    exact (IndexOfIndexes.splitEquiv k).bijective
  refine And.intro ?_ ?_
  · intro k
    simpa using (IndexOfIndexes.digitsEquiv_bijective k)
  refine And.intro ?_ ?_
  · intro k
    simpa using (IndexOfIndexes.addrQ_injective (k := k))
  refine And.intro ?_ ?_
  · intro k x
    simpa using (IndexOfIndexesSubcycle.fiber_card_base (k := k) (x := x))
  refine And.intro ?_ ?_
  · intro k x r
    simpa using (IndexOfIndexes.addrQ_join (k := k) (x := x) (r := r))
  refine And.intro ?_ ?_
  · intro k y
    simpa using (IndexOfIndexes.addrQ_split (k := k) (y := y))
  refine And.intro ?_ ?_
  · intro k x r
    simpa using (IndexOfIndexes.addrQ_join_bounds (k := k) (x := x) (r := r))
  refine And.intro ?_ ?_
  · intro k x
    simpa using (IndexOfIndexesSubcycle.fiberAddrImage_eq_offsetAddrImage (k := k) (x := x))
  refine And.intro ?_ ?_
  · intro k x
    simpa using (IndexOfIndexesSubintervals.fiberAddrImage_subset_coarseInterval (k := k) (x := x))
  refine And.intro ?_ ?_
  · intro k x
    simpa using (IndexOfIndexesSubcycle.offsetAddr_injective (k := k) (x := x))
  refine And.intro ?_ ?_
  · intro k x
    simpa using (IndexOfIndexesSubcycle.offsetAddrImage_ncard (k := k) (x := x))
  refine And.intro ?_ ?_
  · intro k x
    simpa using (IndexOfIndexesSubcycle.fiberAddrImage_ncard (k := k) (x := x))
  refine And.intro ?_ ?_
  · intro p k hp hk
    simpa using (Prime13DepthBoundary.prime_dvd_13_pow_eq_13 p k hp hk)
  refine And.intro RecursiveGridBase13.digits_at_1000 ?_
  refine And.intro ?_ ?_
  · intro t ht
    simpa using (RecursiveGridBase13.carry_at_return t ht)
  refine And.intro ?_ ?_
  · intro d t
    simpa using (RecursiveGridBase13.digit_succ d t)
  refine And.intro ?_ ?_
  · intro t
    simpa using (RecursiveGridIndexBridge.digit0_eq_mod13 t)
  refine And.intro ?_ ?_
  · intro k x
    refine And.intro ?_ ?_
    · simpa using (RecursiveGridIndexBridge.splitEquiv_fst_val k x)
    · simpa using (RecursiveGridIndexBridge.splitEquiv_snd_val k x)
  refine And.intro ?_ ?_
  · intro b k d t m hb hd
    simpa using
      (RecursiveGridGenericBase.digit_add_mul_basePow_of_lt (b := b) (k := k) (d := d) (t := t) (m := m) hb hd)
  refine And.intro ?_ ?_
  · intro b k d m hb hd
    simpa using
      (RecursiveGridGenericBase.digit_blockBoundary_of_lt (b := b) (k := k) (d := d) (m := m) hb hd)
  refine And.intro ?_ ?_
  · intro b k d m hb hd
    simpa using
      (RecursiveGridGenericBase.digit_afterBlockBoundaryTick_of_lt (b := b) (k := k) (d := d) (m := m) hb hd)
  refine And.intro SphericalHarmonicBreathing.spherical_harmonic_ufrf_unity ?_
  refine And.intro ?_ ?_
  · intro ℓ m h
    simpa using (SphericalHarmonicBreathing.constant_total_complexity ℓ m h)
  refine And.intro ?_ ?_
  · intro N s t
    simpa using (TnTruncated.aCoeffsMS_add N s t)
  refine And.intro ?_ ?_
  · intro N k gens
    simpa using (TnTruncated.aCoeffs_scale N k gens)
  refine And.intro SphericalHarmonicBreathing.monster_between_harmonic_levels ?_
  refine And.intro ?_ ?_
  ·
    refine And.intro MoonshineLogMod.c2Nat_decade ?_
    refine And.intro MoonshineLogMod.c2Nat_leadingBlock ?_
    exact MoonshineLogMod.c2Nat_mod13
  ·
    refine And.intro ?_ ?_
    · simpa using JFunctionCoefficient.j_coefficient_c2_numerator_dvd_thirteen
    ·
      refine And.intro ?_ ?_
      · intro n hn
        simpa using (RecursiveGridBase10.digit_at_decade_eq_leadingBlock n hn)
      ·
        refine And.intro ?_ ?_
        · exact DiminishedChordZMod12.three_nsmul_cycle
        ·
          refine And.intro ?_ ?_
          · exact DiminishedChordZMod12.three_nsmul_cycle_scaled
          ·
            refine And.intro ?_ ?_
            · exact ChromaticBreathing52.chromatic_breathing_52
            ·
              refine And.intro ?_ ?_
              · exact ChromaticBreathing52.chromatic_breathing_52_orbitSize
              ·
                refine And.intro ?_ ?_
                · exact QuarterCycleZMod.quarter_nsmul_cycle
                ·
                  refine And.intro ?_ ?_
                  · intro m s
                    simpa using (CycleStepOrbit.orbitSize_nsmul_step_returns m s)
                  ·
                    refine And.intro ?_ ?_
                    · intro m s n hm
                      simpa using
                        (CycleStepOrbit.nsmul_eq_zero_iff_orbitSize_dvd (m := m) (s := s) (n := n) hm)
                    ·
                      refine And.intro ?_ ?_
                      · intro m₁ m₂ s hm₁ hm₂ hcop
                        simpa using
                          (CycleStepOrbit.orbitSize_mul_eq_lcm_orbitSize
                            (m₁ := m₁) (m₂ := m₂) (s := s) hm₁ hm₂ hcop)
                      ·
                        refine And.intro ?_ ?_
                        · intro k m s hk
                          simpa using
                            (CycleStepOrbit.orbitSize_scale_invariant (k := k) (m := m) (s := s) hk)
                        ·
                          refine And.intro ?_ ?_
                          · intro m₁ m₂ s hcop
                            simpa using (CycleStepOrbit.lcm_orbitSize_two_axes_returns m₁ m₂ s hcop)
                          ·
                            refine And.intro ?_ ?_
                            · intro ms s hcop
                              simpa using
                                (CycleStepOrbit.orbitLcm_eq_prod_of_pairwise_coprime ms hcop s)
                            ·
                              refine And.intro ?_ ?_
                              · intro ms s hcop hs
                                simpa using
                                  (CycleStepOrbit.orbitLcm_eq_prod_moduli_of_pairwise_coprime_of_forall_coprime
                                    ms hcop s hs)
                              ·
                                refine And.intro ?_ ?_
                                · intro ms s hcop
                                  simpa using (CycleStepOrbit.orbitLcm_nsmul_step_returns ms hcop s)
                                ·
                                  refine And.intro ?_ ?_
                                  · intro ms s hcop hpos
                                    simpa using
                                      (CycleStepOrbit.orbitSize_prod_eq_orbitLcm_of_pairwise_coprime
                                        ms hcop s hpos)
                                  ·
                                    refine And.intro QuaternionOctaveLens.q8_card ?_
                                    refine And.intro QuaternionOctaveLens.q8_noncomm ?_
                                    refine And.intro QuaternionOctaveLens.q8_order4 ?_
                                    refine And.intro OctonionFano.nonassoc_witness ?_
                                    refine And.intro ?_ ?_
                                    · intro E _ _ Φ t k
                                      simpa using (FourierZMod13.dft_translate_13 (E := E) Φ t k)
                                    refine And.intro ?_ ?_
                                    · intro f g k
                                      simpa using (FourierZMod13.dft_conv_13 f g k)
                                    refine And.intro ?_ ?_
                                    · intro E _ _ Ψ k
                                      simpa using (FourierZMod13.invDFT_apply_13 (E := E) Ψ k)
                                    · intro E _ _ Φ
                                      simpa using (FourierZMod13.dft_dft_13 (E := E) Φ)

/--
Discrete extension layer (built on top of the canonical synthesis):
- REST-anchored seam overlap law (`COMPLETE -> SEED`),
- projection composition across intermediate observers,
- exact scale-ladder ratio law.
-/
theorem UFRF_Discrete_Observer_Seam_Extension :
    (∀ g : Nat, RESTSeamOverlap.parentComplete_childSeed_stmt g)
  ∧ (∀ (alpha x : Rat) (obs mid tgt : Nat),
      ObserverScaleProjection.projectSL alpha
        (ObserverScaleProjection.projectSL alpha x obs mid) mid tgt
      =
      ObserverScaleProjection.projectSL alpha x obs tgt)
  ∧ (∀ a b : Nat, a ≤ b →
      ObserverScaleProjection.scaleM b / ObserverScaleProjection.scaleM a = 10 ^ (b - a))
  ∧ (∀ k m s n : Nat, 0 < k → 0 < m →
      (n • ((k * s : Nat) : ZMod (k * m)) = 0 ↔ n • (s : ZMod m) = 0))
  ∧ (∀ (ms : List Nat) (s₁ s₂ n : Nat),
      ms.Pairwise Nat.Coprime →
      (∀ m ∈ ms, 0 < m) →
      (∀ m ∈ ms, CycleStepOrbit.orbitSize m s₁ = CycleStepOrbit.orbitSize m s₂) →
      (n • (s₁ : ZMod ms.prod) = 0 ↔ n • (s₂ : ZMod ms.prod) = 0))
  ∧ (∀ (n k : Nat) (ms : List Nat),
      n ≠ 0 →
      ms.Pairwise Nat.Coprime →
      CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n →
      MultidimensionalTicks.systemCoord ms (MultidimensionalTicks.tick10 k n) =
        MultidimensionalTicks.systemCoord ms n)
  ∧ (∀ (ms : List Nat) (n k s : Nat),
      n ≠ 0 →
      ms.Pairwise Nat.Coprime →
      (∀ m ∈ ms, 0 < m) →
      (∀ m ∈ ms, CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1)) →
      CycleStepOrbit.nodeClosure ms s n →
  MultidimensionalTicks.systemCoord ms (MultidimensionalTicks.tick10 k n) =
        MultidimensionalTicks.systemCoord ms n) := by
  -- (No extra dependency anchor needed here; `UFRF_Canonical_Synthesis` is already in this module.)
  refine And.intro ?_ ?_
  · intro g
    exact RESTSeamOverlap.parentComplete_childSeed g
  refine And.intro ?_ ?_
  · intro alpha x obs mid tgt
    simpa using (ObserverScaleProjection.projectSL_compose (alpha := alpha) (x := x)
      (obs := obs) (mid := mid) (tgt := tgt))
  refine And.intro ?_ ?_
  · intro a b h
    exact ObserverScaleProjection.scaleM_div_of_le h
  refine And.intro ?_ ?_
  · intro k m s n hk hm
    simpa using (CycleStepOrbit.nsmul_eq_zero_iff_scaled_axis
      (k := k) (m := m) (s := s) (n := n) hk hm)
  refine And.intro ?_ ?_
  · intro ms s₁ s₂ n hcop hpos hEq
    simpa using
      (CycleStepOrbit.nsmul_eq_zero_iff_prod_of_forall_mem_orbitSize_eq
        (ms := ms) (hcop := hcop) (hpos := hpos) (s₁ := s₁) (s₂ := s₂) (n := n) hEq)
  refine And.intro ?_ ?_
  · intro n k ms hn hcop hnode
    simpa using
      (MultidimensionalTicks.systemCoord_invariant_of_nodeClosure
        (n := n) (k := k) (ms := ms) (hn := hn) (hcop := hcop) (hnode := hnode))
  · intro ms n k s hn hcop hpos hEq hnode
    simpa using
      (MultidimensionalTicks.systemCoord_invariant_of_nodeClosure_chart_change
        (n := n) (k := k) (ms := ms) (hn := hn) (hcop := hcop) (hpos := hpos)
        (s := s) (hEq := hEq) (hnode := hnode))

/--
Core fine-structure bridge extension:
- dual-trinity concurrency witness on the discrete side (`26 <-> 13×2`),
- core geometric decomposition for `α⁻¹`,
- transport to the candidate and numeric anchor.
-/
theorem UFRF_Core_FineStructure_Extension :
    (∀ a b : Nat, a ≡ b [MOD 26] ↔ (a ≡ b [MOD 13] ∧ a ≡ b [MOD 2]))
  ∧ (UFRFCoreDualTrinityFineStructure.alphaInvFromCore = FineStructureCandidate.alphaInvCandidate)
  ∧ ((137 : ℝ) < UFRFCoreDualTrinityFineStructure.alphaInvFromCore
      ∧ UFRFCoreDualTrinityFineStructure.alphaInvFromCore < (138 : ℝ))
  ∧ (Int.floor UFRFCoreDualTrinityFineStructure.alphaInvFromCore = 137) := by
  refine And.intro ?_ ?_
  · intro a b
    exact UFRFCoreDualTrinityFineStructure.dual_axis_concurrency_witness a b
  refine And.intro UFRFCoreDualTrinityFineStructure.alphaInvFromCore_eq_candidate ?_
  refine And.intro UFRFCoreDualTrinityFineStructure.alphaInvFromCore_between_137_and_138 ?_
  exact UFRFCoreDualTrinityFineStructure.alphaInvFromCore_floor_eq_137

end UFRFUnified
