import REST_Seam_Transport_Core_Theorem
import REST_Seam_Classification_Theorem

/-!
# REST Seam Transport API

Reusable parent/child transport lemmas on REST-anchored seam ticks.

This upgrades pointwise overlap facts into a compact API:
- exact state transport on seam ticks (`parent = REST + child`),
- classification transport (`parent COMPLETE ↔ child SEED`) on the seam window.
-/

namespace RESTSeamOverlap

theorem parentComplete_at_seamTick_iff_window_via_generic (g r : Nat) (hr : r ≤ 3) :
    isParentComplete (state g (seamTick g r)) ↔ (r = 1 ∨ r = 2 ∨ r = 3) := by
  rw [state_parent_at_seamTick g r hr]
  exact isParentComplete_iff_window r hr

theorem parentComplete_at_seamTick_iff_window (g r : Nat) (hr : r ≤ 3) :
    isParentComplete (state g (seamTick g r)) ↔ (r = 1 ∨ r = 2 ∨ r = 3) := by
  exact parentComplete_at_seamTick_iff_window_via_generic g r hr

theorem childSeed_at_seamTick_iff_window_via_generic (g r : Nat) (hr : r ≤ 3) :
    isChildSeed (state (g + 1) (seamTick g r)) ↔ (r = 1 ∨ r = 2 ∨ r = 3) := by
  rw [state_child_at_seamTick g r hr]
  exact isChildSeed_iff_window r hr

theorem childSeed_at_seamTick_iff_window (g r : Nat) (hr : r ≤ 3) :
    isChildSeed (state (g + 1) (seamTick g r)) ↔ (r = 1 ∨ r = 2 ∨ r = 3) := by
  exact childSeed_at_seamTick_iff_window_via_generic g r hr

theorem parentComplete_iff_childSeed_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    isParentComplete (state g (seamTick g r))
      ↔ isChildSeed (state (g + 1) (seamTick g r)) := by
  constructor
  · intro hp
    have hw : r = 1 ∨ r = 2 ∨ r = 3 :=
      (parentComplete_at_seamTick_iff_window g r hr).1 hp
    exact (childSeed_at_seamTick_iff_window g r hr).2 hw
  · intro hs
    have hw : r = 1 ∨ r = 2 ∨ r = 3 :=
      (childSeed_at_seamTick_iff_window g r hr).1 hs
    exact (parentComplete_at_seamTick_iff_window g r hr).2 hw

end RESTSeamOverlap
