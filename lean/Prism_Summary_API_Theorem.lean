import Prime_Choreography_Discriminant_Protocol_Theorem
import Prism_Primitive_Root_Order_Protocol_Theorem
import Prism_Complement_Vs_Inverse_Protocol_Theorem
import Prism_Projection_Compatibility_Protocol_Theorem

/-!
# PRISM Summary API

Discoverability layer for the bounded PRISM mechanism summaries.
This module introduces no new mechanism claims; it only packages already-proved
finite summary theorems into compact entry points.
-/

namespace PrismSummaryAPI

open PrimeChoreographyDiscriminantProtocol
open PrismPrimitiveRootOrderProtocol
open PrismComplementVsInverseProtocol
open PrismProjectionCompatibilityProtocol

theorem prism_discriminant_entry :
    (PrimeChoreographyDiscriminantProtocol.uniformIsDegenerate = true)
    ∧ (PrimeChoreographyDiscriminantProtocol.allNonuniformAreScrambled = true)
    ∧ (PrimeChoreographyDiscriminantProtocol.ufrfUniformInversionGap = 20) := by
  native_decide

theorem prism_primitive_root_order_entry :
    (PrismPrimitiveRootOrderProtocol.orderEqualsPhiAll = true)
    ∧ (PrismPrimitiveRootOrderProtocol.orderMinimalityAll = true)
    ∧ (PrismPrimitiveRootOrderProtocol.projectionCompatibilityAll = true)
    ∧ (PrismPrimitiveRootOrderProtocol.primitiveRootWitnessAll = true) := by
  native_decide

theorem prism_complement_vs_inverse_entry :
    (PrismComplementVsInverseProtocol.complementIsDigitLocalAll = true)
    ∧ (PrismComplementVsInverseProtocol.negIsCarryCoupledAll = true)
    ∧ (PrismComplementVsInverseProtocol.asymmetryConfirmedAll = true) := by
  native_decide

theorem prism_projection_compatibility_entry :
    (PrismProjectionCompatibilityProtocol.succCompatibleAll = true)
    ∧ (PrismProjectionCompatibilityProtocol.predCompatibleAll = true)
    ∧ (PrismProjectionCompatibilityProtocol.negCompatibleAll = true)
    ∧ (PrismProjectionCompatibilityProtocol.compCompatibleAll = true)
    ∧ (PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true) := by
  native_decide

theorem prism_summary_bundle :
    (PrimeChoreographyDiscriminantProtocol.uniformIsDegenerate = true)
    ∧ (PrimeChoreographyDiscriminantProtocol.allNonuniformAreScrambled = true)
    ∧ (PrismPrimitiveRootOrderProtocol.primitiveRootWitnessAll = true)
    ∧ (PrismPrimitiveRootOrderProtocol.projectionCompatibilityAll = true)
    ∧ (PrismComplementVsInverseProtocol.complementIsDigitLocalAll = true)
    ∧ (PrismComplementVsInverseProtocol.negIsCarryCoupledAll = true)
    ∧ (PrismComplementVsInverseProtocol.asymmetryConfirmedAll = true)
    ∧ (PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true) := by
  native_decide

theorem prism_summary_smoke :
    (PrimeChoreographyDiscriminantProtocol.ufrfUniformInversionGap = 20)
    ∧ (PrismPrimitiveRootOrderProtocol.orderEqualsPhiAll = true)
    ∧ (PrismComplementVsInverseProtocol.asymmetryConfirmedAll = true)
    ∧ (PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true) := by
  native_decide

end PrismSummaryAPI
