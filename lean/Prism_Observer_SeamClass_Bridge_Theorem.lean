import Mathlib
import Prism_Observer_WorkedClass_API_Theorem
import Composed_Tick_API_Theorem

/-!
# PRISM ↔ Observer Seam-Class Bridge (Bounded)

Bounded discoverability bridge:
- PRISM/observer worked-class wrappers (`d mod 6`),
- canonical seam/global-tick package on `[3,11,13]`,
- class-equality transport instantiated at seam ticks.

No new mechanism theorem is introduced here; this file only composes existing,
already-certified wrappers.
-/

namespace PrismObserverSeamClassBridge

open PrismObserverWorkedClassAPI
open ComposedTickAPI
open RESTSeamOverlap

theorem seamTick_cyclePos_class_bundle (g : Nat) :
    (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 0)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 6))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 1)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 7))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 2)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 8))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 3)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 9))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 4)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 10))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 5)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 11)) := by
  exact cyclePos_class_bundle (seamTick g 0)

abbrev SeamClassPackageProp (g : Nat) : Prop :=
    PrismObserverWorkedClassAPI.WorkedClassSmokeProp
    ∧ ComposedTickAPI.SeamGlobalPkg31113 g
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 0)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 6))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 1)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 7))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 2)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 8))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 3)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 9))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 4)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 10))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 5)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick g 0 + 10 ^ 11))

theorem prism_observer_seam_class_package (g : Nat) :
    SeamClassPackageProp g := by
  refine ⟨PrismObserverWorkedClassAPI.prism_observer_worked_class_smoke,
    ComposedTickAPI.seam_globalTick_add_package_3_11_13_r0 g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cyclePos_class0 (seamTick g 0)
  · exact cyclePos_class1 (seamTick g 0)
  · exact cyclePos_class2 (seamTick g 0)
  · exact cyclePos_class3 (seamTick g 0)
  · exact cyclePos_class4 (seamTick g 0)
  · exact cyclePos_class5 (seamTick g 0)

abbrev SeamClassSmokeProp : Prop :=
    PrismObserverWorkedClassAPI.WorkedClassSmokeProp
    ∧ ComposedTickAPI.SeamGlobalPkg31113 0
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick 0 0 + 10 ^ 4)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (seamTick 0 0 + 10 ^ 10))

theorem prism_observer_seam_class_smoke :
    SeamClassSmokeProp := by
  exact ⟨PrismObserverWorkedClassAPI.prism_observer_worked_class_smoke,
    ComposedTickAPI.seam_globalTick_add_package_3_11_13_r0 0,
    cyclePos_class4 (seamTick 0 0)⟩

end PrismObserverSeamClassBridge
