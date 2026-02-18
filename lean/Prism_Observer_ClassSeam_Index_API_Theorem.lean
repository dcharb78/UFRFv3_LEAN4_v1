import Mathlib
import Prism_Observer_WorkedClass_API_Theorem
import Prism_Observer_SeamClass_Bridge_Theorem

/-!
# PRISM ↔ Observer Class-Seam Index API (Bounded)

Single discoverability entrypoint over:
- observer class tables (`d mod 6`),
- worked class package wrappers,
- seam-class bridge package wrappers.

No new mechanism theorem is introduced; this module only indexes existing
bounded wrappers.
-/

namespace PrismObserverClassSeamIndexAPI

open PrismObserverWorkedClassAPI
open PrismObserverSeamClassBridge

abbrev ClassSeamIndexPackageProp : Prop :=
    (List.map (fun p => (ObserverCycleBridgeAPI.cycleShiftClass p.1, ObserverCycleBridgeAPI.cycleShiftClass p.2))
        PrismObserverWorkedClassAPI.workedClassPairs
      = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)])
    ∧ (List.map (fun p => ((10 ^ p.1) % 13, (10 ^ p.2) % 13))
        PrismObserverWorkedClassAPI.workedClassPairs
      = [(1, 1), (10, 10), (9, 9), (12, 12), (3, 3), (4, 4)])
    ∧ PrismObserverWorkedClassAPI.WorkedClassPackageProp
    ∧ PrismObserverSeamClassBridge.SeamClassPackageProp 0
    ∧ PrismObserverSeamClassBridge.SeamClassSmokeProp

theorem prism_observer_class_seam_index_package :
    ClassSeamIndexPackageProp := by
  refine ⟨PrismObserverWorkedClassAPI.workedClassPairs_shiftClass_table,
    PrismObserverWorkedClassAPI.workedClassPairs_shiftResidue_table,
    PrismObserverWorkedClassAPI.prism_observer_worked_class_package,
    PrismObserverSeamClassBridge.prism_observer_seam_class_package 0,
    PrismObserverSeamClassBridge.prism_observer_seam_class_smoke⟩

abbrev ClassSeamIndexSmokeProp : Prop :=
    PrismObserverWorkedClassAPI.WorkedClassSmokeProp
    ∧ PrismObserverSeamClassBridge.SeamClassSmokeProp
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (RESTSeamOverlap.seamTick 0 0 + 10 ^ 4)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (RESTSeamOverlap.seamTick 0 0 + 10 ^ 10))

theorem prism_observer_class_seam_index_smoke :
    ClassSeamIndexSmokeProp := by
  exact
    ⟨PrismObserverWorkedClassAPI.prism_observer_worked_class_smoke,
      PrismObserverSeamClassBridge.prism_observer_seam_class_smoke,
      PrismObserverWorkedClassAPI.cyclePos_class4 (RESTSeamOverlap.seamTick 0 0)⟩

end PrismObserverClassSeamIndexAPI
