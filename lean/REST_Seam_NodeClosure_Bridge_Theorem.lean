import REST_Seam_Core_Theorem
import NodeClosure_Singleton_Generic_Theorem
import Seam_Generic_NodeClosure_Bridge_Theorem
import REST_Seam_Generic_Canonical_Equiv_Theorem

/-!
# REST Seam ↔ NodeClosure Bridge

Bridge lemmas connecting seam-window transport to the generic `nodeClosure` predicate.
-/

namespace RESTSeamOverlap

theorem nodeClosure_singleton14_step1_iff (n : Nat) :
    CycleStepOrbit.nodeClosure ([14] : List Nat) 1 n ↔ 14 ∣ n := by
  simpa using (CycleStepOrbit.nodeClosure_singleton_step1_iff 14 n)

theorem nodeClosure_singleton14_step1_iff_zero_of_le3 (r : Nat) (hr : r ≤ 3) :
    CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r ↔ r = 0 := by
  have hlt : r < 14 := by omega
  simpa using (CycleStepOrbit.nodeClosure_singleton_step1_iff_zero_of_lt 14 r hlt)

theorem childVoid_iff_nodeClosure14_at_seamTick_via_generic (g r : Nat) (hr : r ≤ 3) :
    state (g + 1) (seamTick g r) = 0
      ↔ CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r := by
  have hrlt : r < cycle := by
    simpa [cycle] using (show r < 14 by omega)
  have hgen :
      SeamGeneric.state genericParams (g + 1) (SeamGeneric.seamTick genericParams g r) = 0
        ↔ CycleStepOrbit.nodeClosure ([genericParams.cycle] : List Nat) 1 r := by
    simpa [genericParams, cycle] using
      (SeamGeneric.childVoid_iff_nodeClosure_singleton_step1_at_seamTick genericParams g r
        (by simpa [genericParams, cycle] using hrlt))
  -- Transport left side from generic definitions to canonical definitions.
  have hstate :
      state (g + 1) (seamTick g r) =
        SeamGeneric.state genericParams (g + 1) (SeamGeneric.seamTick genericParams g r) := by
    rw [state_eq_generic (g := g + 1) (t := seamTick g r), seamTick_eq_generic]
  -- Rewrite the equivalence along the transported equality.
  simpa [hstate]
    using hgen

theorem childVoid_iff_nodeClosure14_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    state (g + 1) (seamTick g r) = 0
      ↔ CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r := by
  exact childVoid_iff_nodeClosure14_at_seamTick_via_generic g r hr

theorem parentRest_childVoid_iff_nodeClosure14_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    (state g (seamTick g r) = rest ∧ state (g + 1) (seamTick g r) = 0)
      ↔ CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r := by
  constructor
  · intro h
    exact (childVoid_iff_nodeClosure14_at_seamTick g r hr).1 h.2
  · intro hnode
    have hr0 : r = 0 := (nodeClosure_singleton14_step1_iff_zero_of_le3 r hr).1 hnode
    have hparent : state g (seamTick g r) = (rest + r) % cycle :=
      state_parent_at_seamTick_mod_via_generic g r
    have hchild : state (g + 1) (seamTick g r) = r % cycle :=
      state_child_at_seamTick_mod_via_generic g r
    constructor
    · rw [hparent, hr0]
      simp [rest, cycle]
    · rw [hchild, hr0]
      simp [cycle]

end RESTSeamOverlap
