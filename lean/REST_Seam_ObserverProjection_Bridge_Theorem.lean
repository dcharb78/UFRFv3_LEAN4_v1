import REST_Seam_Core_Theorem
import Observer_Scale_Projection_Composition_Theorem

/-!
# REST Seam <-> Observer Projection Bridge

Bridges canonical seam ticks (`seamTick`) to the discrete affine observer/scale
projection core (`projectSL`), without adding analytic assumptions.
-/

namespace RESTSeamObserverProjectionBridge

open RESTSeamOverlap
open ObserverScaleProjection

/--
Affine projection package specialized to canonical seam ticks:
- observers: `seamTick g r` and `seamTick g 0`
- targets: `seamTick (g+1) r` and `seamTick (g+1) 0`
-/
theorem projectSL_affine_suite_at_seam_ticks
    (alpha x c : Rat) (g r : Nat) :
    (projectSL alpha x (seamTick g r) (seamTick (g + 1) r) - x
      = alpha * (deltaSL (seamTick g r) (seamTick (g + 1) r) : Rat))
    ∧ (projectSL alpha x (seamTick g r) (seamTick (g + 1) r)
      - projectSL alpha x (seamTick g 0) (seamTick (g + 1) r)
      = alpha * (deltaSL (seamTick g r) (seamTick g 0) : Rat))
    ∧ (projectSL alpha x (seamTick g r) (seamTick (g + 1) r)
      - projectSL alpha x (seamTick g r) (seamTick (g + 1) 0)
      = -alpha * (deltaSL (seamTick (g + 1) r) (seamTick (g + 1) 0) : Rat))
    ∧ (projectSL alpha (x + c) (seamTick g r) (seamTick (g + 1) r)
      = projectSL alpha x (seamTick g r) (seamTick (g + 1) r) + c) := by
  simpa using
    (projectSL_affine_suite
      alpha x c
      (seamTick g r) (seamTick g 0)
      (seamTick (g + 1) r) (seamTick (g + 1) 0))

/--
Observer-difference remains translation-invariant when observer/target scales
are instantiated with seam ticks.
-/
theorem projectSL_obs_diff_add_base_at_seam_ticks
    (alpha x c : Rat) (g r : Nat) :
    projectSL alpha (x + c) (seamTick g r) (seamTick (g + 1) r)
      - projectSL alpha (x + c) (seamTick g 0) (seamTick (g + 1) r)
      = alpha * (deltaSL (seamTick g r) (seamTick g 0) : Rat) := by
  simpa using
    (projectSL_obs_diff_add_base
      alpha x c
      (seamTick g r) (seamTick g 0) (seamTick (g + 1) r))

/-- One-call bridge package for seam-tick affine projection identities. -/
theorem seam_observer_projection_bridge_package
    (alpha x c : Rat) (g r : Nat) :
    ((projectSL alpha x (seamTick g r) (seamTick (g + 1) r) - x
      = alpha * (deltaSL (seamTick g r) (seamTick (g + 1) r) : Rat))
    ∧ (projectSL alpha x (seamTick g r) (seamTick (g + 1) r)
      - projectSL alpha x (seamTick g 0) (seamTick (g + 1) r)
      = alpha * (deltaSL (seamTick g r) (seamTick g 0) : Rat))
    ∧ (projectSL alpha x (seamTick g r) (seamTick (g + 1) r)
      - projectSL alpha x (seamTick g r) (seamTick (g + 1) 0)
      = -alpha * (deltaSL (seamTick (g + 1) r) (seamTick (g + 1) 0) : Rat))
    ∧ (projectSL alpha (x + c) (seamTick g r) (seamTick (g + 1) r)
      = projectSL alpha x (seamTick g r) (seamTick (g + 1) r) + c))
      ∧
    (projectSL alpha (x + c) (seamTick g r) (seamTick (g + 1) r)
      - projectSL alpha (x + c) (seamTick g 0) (seamTick (g + 1) r)
      = alpha * (deltaSL (seamTick g r) (seamTick g 0) : Rat)) := by
  exact ⟨projectSL_affine_suite_at_seam_ticks alpha x c g r,
    projectSL_obs_diff_add_base_at_seam_ticks alpha x c g r⟩

/-- Fixed-parameter smoke theorem for the seam/observer projection bridge package. -/
theorem seam_observer_projection_bridge_smoke :
    ((projectSL (1 : Rat) (0 : Rat) (seamTick 0 0) (seamTick (0 + 1) 0) - (0 : Rat)
      = (1 : Rat) * (deltaSL (seamTick 0 0) (seamTick (0 + 1) 0) : Rat))
    ∧ (projectSL (1 : Rat) (0 : Rat) (seamTick 0 0) (seamTick (0 + 1) 0)
      - projectSL (1 : Rat) (0 : Rat) (seamTick 0 0) (seamTick (0 + 1) 0)
      = (1 : Rat) * (deltaSL (seamTick 0 0) (seamTick 0 0) : Rat))
    ∧ (projectSL (1 : Rat) (0 : Rat) (seamTick 0 0) (seamTick (0 + 1) 0)
      - projectSL (1 : Rat) (0 : Rat) (seamTick 0 0) (seamTick (0 + 1) 0)
      = -(1 : Rat) * (deltaSL (seamTick (0 + 1) 0) (seamTick (0 + 1) 0) : Rat))
    ∧ (projectSL (1 : Rat) ((0 : Rat) + (1 : Rat)) (seamTick 0 0) (seamTick (0 + 1) 0)
      = projectSL (1 : Rat) (0 : Rat) (seamTick 0 0) (seamTick (0 + 1) 0) + (1 : Rat)))
      ∧
    (projectSL (1 : Rat) ((0 : Rat) + (1 : Rat)) (seamTick 0 0) (seamTick (0 + 1) 0)
      - projectSL (1 : Rat) ((0 : Rat) + (1 : Rat)) (seamTick 0 0) (seamTick (0 + 1) 0)
      = (1 : Rat) * (deltaSL (seamTick 0 0) (seamTick 0 0) : Rat)) := by
  exact seam_observer_projection_bridge_package (1 : Rat) (0 : Rat) (1 : Rat) 0 0

end RESTSeamObserverProjectionBridge
