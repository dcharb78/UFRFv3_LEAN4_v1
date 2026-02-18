import Seam_Generic_API_Theorem
import REST_Seam_Core_Theorem

/-!
# REST Seam Generic ↔ Canonical Equivalence

Links the generic seam API at `(cycle=14, stride=10)` to canonical `RESTSeamOverlap` definitions.
-/

namespace RESTSeamOverlap

def genericParams : SeamGeneric.Params :=
  { cycle := cycle
    stride := rest
    cycle_pos := by decide }

theorem birth_eq_generic (g : Nat) :
    birth g = SeamGeneric.birth genericParams g := by
  simp [birth, genericParams, SeamGeneric.birth, rest]

theorem stateFrom_eq_generic (b t : Nat) :
    stateFrom b t = SeamGeneric.stateFrom genericParams b t := by
  simp [stateFrom, genericParams, SeamGeneric.stateFrom]

theorem state_eq_generic (g t : Nat) :
    state g t = SeamGeneric.state genericParams g t := by
  simp [state, SeamGeneric.state, birth_eq_generic, stateFrom_eq_generic]

theorem seamTick_eq_generic (g r : Nat) :
    seamTick g r = SeamGeneric.seamTick genericParams g r := by
  simp [seamTick, genericParams, SeamGeneric.seamTick, SeamGeneric.birth, birth, rest]

theorem seamTickN_eq_generic (g j r : Nat) :
    seamTickN g j r = SeamGeneric.seamTickN genericParams g j r := by
  simp [seamTickN, genericParams, SeamGeneric.seamTickN, SeamGeneric.birth, birth, rest]

theorem state_parent_at_seamTick_mod_via_generic (g r : Nat) :
    state g (seamTick g r) = (rest + r) % cycle := by
  rw [state_eq_generic, seamTick_eq_generic]
  simpa [genericParams, cycle, rest] using
    (SeamGeneric.state_parent_at_seamTick_mod genericParams g r)

theorem state_child_at_seamTick_mod_via_generic (g r : Nat) :
    state (g + 1) (seamTick g r) = r % cycle := by
  rw [state_eq_generic, seamTick_eq_generic]
  simpa [genericParams, cycle] using
    (SeamGeneric.state_child_at_seamTick_mod genericParams g r)

theorem state_descendant_at_seamTickN_mod_via_generic (g j r : Nat) :
    state (g + j) (seamTickN g j r) = r % cycle := by
  rw [state_eq_generic, seamTickN_eq_generic]
  simpa [genericParams, cycle] using
    (SeamGeneric.state_descendant_at_seamTickN_mod genericParams g j r)

end RESTSeamOverlap
