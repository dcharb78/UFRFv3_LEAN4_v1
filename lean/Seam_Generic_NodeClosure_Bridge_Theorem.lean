import Seam_Generic_API_Theorem
import NodeClosure_Singleton_Generic_Theorem

/-!
# Seam Generic ↔ NodeClosure Bridge

Generic seam-window closure bridge parameterized by seam modulus.
-/

namespace SeamGeneric

theorem childVoid_iff_nodeClosure_singleton_step1_at_seamTick
    (P : Params) (g r : Nat) (hr : r < P.cycle) :
    state P (g + 1) (seamTick P g r) = 0
      ↔ CycleStepOrbit.nodeClosure ([P.cycle] : List Nat) 1 r := by
  rw [state_child_at_seamTick_of_lt P g r hr]
  exact (CycleStepOrbit.nodeClosure_singleton_step1_iff_zero_of_lt P.cycle r hr).symm

end SeamGeneric
