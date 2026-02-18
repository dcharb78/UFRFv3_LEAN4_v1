import Recursive_Grid_Base13_Theorem
import REST_Seam_Transport_Theorem

/-!
# Spiral Octave Closure (Discrete Bridge Form)

This file packages two existing certified mechanisms in the wording used across UFRF notes:

1. Base-13 return/carry:
   hitting `12` then stepping once returns the local chart to `0` and advances the next scale.
2. Seam bridge window:
   parent bridge states `11,12,13` correspond to child seed states `1,2,3`.

No new axioms; these are aliases of already-proved core theorems.
-/

namespace SpiralOctaveClosure

open RecursiveGridBase13
open RESTSeamOverlap

/--
At base 13, local return at `12` closes one loop and advances the next scale.

This is the exact discrete form of "arrive back at zero, but at the next octave".
-/
theorem return12_resets_and_advances (t : Nat) (ht : t % base = 12) :
    (t + 1) % base = 0 ∧ (t + 1) / base = t / base + 1 := by
  have hbase : base - 1 = 12 := by simp [base]
  have ht' : t % base = base - 1 := by simpa [hbase] using ht
  exact carry_at_return t ht'

/--
On seam ticks (`r ≤ 3`), parent COMPLETE bridge window (`11,12,13`)
is equivalent to child SEED window (`1,2,3`).
-/
theorem bridge111213_iff_seed123 (g r : Nat) (hr : r ≤ 3) :
    isParentComplete (state g (seamTick g r))
      ↔ isChildSeed (state (g + 1) (seamTick g r)) := by
  exact parentComplete_iff_childSeed_at_seamTick g r hr

/--
Concrete state transport at seam ticks:
`parent = 10 + r`, `child = r` (for `r ≤ 3`).
-/
theorem bridge_state_values (g r : Nat) (hr : r ≤ 3) :
    state g (seamTick g r) = 10 + r ∧ state (g + 1) (seamTick g r) = r := by
  exact ⟨state_parent_at_seamTick g r hr, state_child_at_seamTick g r hr⟩

end SpiralOctaveClosure
