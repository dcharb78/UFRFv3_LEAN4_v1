import REST_Seam_NodeClosure_Bridge_Theorem
import Aspect_Projection_Kernel_Theorem

/-!
# REST Seam Unified Interface Core

Small reusable helper for packaging seam closure + node closure with externally supplied
system-coordinate and projection transports.
-/

namespace RESTSeamOverlap

open MultidimensionalTicks
open AspectProjectionKernel

theorem seamClosure_unified_interface_systemCoord_of_transports
    {α : Type} (f : KernelState → α)
    (g r : Nat) (hr : r ≤ 3)
    (hnode : CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
    (ms : List Nat) (K : Nat)
    (hsys : systemCoord ms (tick10 K (seamTick g r)) =
      (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
    (hproj : projectView f ms (tick10 K (seamTick g r)) =
      projectView f ms (seamTick g 0)) :
    (state (g + 1) (seamTick g r) = 0)
      ∧ (CycleStepOrbit.nodeClosure ([14] : List Nat) 1 r)
      ∧ (systemCoord ms (tick10 K (seamTick g r)) =
            (UniversalTicks.leadingBlock (seamTick g 0), ms.map (fun m => (seamTick g 0) % m)))
      ∧ (projectView f ms (tick10 K (seamTick g r)) =
            projectView f ms (seamTick g 0)) := by
  have hchild : state (g + 1) (seamTick g r) = 0 :=
    (childVoid_iff_nodeClosure14_at_seamTick g r hr).2 hnode
  exact ⟨hchild, hnode, hsys, hproj⟩

end RESTSeamOverlap

