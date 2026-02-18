import Mathlib
import Prism_Summary_API_Theorem
import Prism_Observer_Bridge_API_Theorem
import Observer_Cycle_Bridge_API_Theorem
import Observer_Digits_Cycle_Periodicity_Bridge_Theorem

/-!
# PRISM ↔ Observer Worked-Class API (Bounded)

Compact worked wrappers over the six observer shift classes (`d mod 6`) tied to
the bounded PRISM compatibility entries.

This module introduces no new mechanism theorem; it repackages already-certified
statements into class-level entry points.
-/

namespace PrismObserverWorkedClassAPI

open PrismProjectionCompatibilityProtocol
open PrismSummaryAPI
open PrismObserverBridgeAPI
open ObserverCycleBridgeAPI

def workedClassPairs : List (Nat × Nat) :=
  [(0, 6), (1, 7), (2, 8), (3, 9), (4, 10), (5, 11)]

theorem workedClassPairs_shiftClass_table :
    List.map (fun p => (cycleShiftClass p.1, cycleShiftClass p.2)) workedClassPairs
      = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (5, 5)] := by
  native_decide

theorem workedClassPairs_shiftResidue_table :
    List.map (fun p => ((10 ^ p.1) % 13, (10 ^ p.2) % 13)) workedClassPairs
      = [(1, 1), (10, 10), (9, 9), (12, 12), (3, 3), (4, 4)] := by
  native_decide

theorem cyclePos_class0 (n : Nat) :
    ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 0)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 6) := by
  exact ObserverCycleBridgeAPI.cyclePos_add_pow10_eq_of_same_class n 0 6 (by decide)

theorem cyclePos_class1 (n : Nat) :
    ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 1)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 7) := by
  exact ObserverCycleBridgeAPI.cyclePos_add_pow10_eq_of_same_class n 1 7 (by decide)

theorem cyclePos_class2 (n : Nat) :
    ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 2)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 8) := by
  exact ObserverCycleBridgeAPI.cyclePos_add_pow10_eq_of_same_class n 2 8 (by decide)

theorem cyclePos_class3 (n : Nat) :
    ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 3)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 9) := by
  exact ObserverCycleBridgeAPI.cyclePos_add_pow10_eq_of_same_class n 3 9 (by decide)

theorem cyclePos_class4 (n : Nat) :
    ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 4)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 10) := by
  exact ObserverCycleBridgeAPI.cyclePos_add_pow10_eq_of_same_class n 4 10 (by decide)

theorem cyclePos_class5 (n : Nat) :
    ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 5)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 11) := by
  exact ObserverCycleBridgeAPI.cyclePos_add_pow10_eq_of_same_class n 5 11 (by decide)

theorem cyclePos_class_bundle (n : Nat) :
    (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 0)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 6))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 1)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 7))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 2)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 8))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 3)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 9))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 4)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 10))
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 5)
      = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 11)) := by
  refine ⟨cyclePos_class0 n, cyclePos_class1 n, cyclePos_class2 n, cyclePos_class3 n, cyclePos_class4 n, cyclePos_class5 n⟩

abbrev WorkedClassPackageProp : Prop :=
    (PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true)
    ∧ ((PrismProjectionCompatibilityProtocol.succCompatibleAll = true)
        ∧ (PrismProjectionCompatibilityProtocol.predCompatibleAll = true)
        ∧ (PrismProjectionCompatibilityProtocol.negCompatibleAll = true)
        ∧ (PrismProjectionCompatibilityProtocol.compCompatibleAll = true)
        ∧ (PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true))
    ∧ ((PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true)
        ∧ (ObserverDigitsCyclePeriodicityProtocol.allShiftPeriodicity = true)
        ∧ (ObserverDigitsCyclePositionProtocol.allCycleTick10_6_return = true))
    ∧ (List.map ObserverCycleBridgeAPI.cycleShiftClass [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        = [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5])
    ∧ (∀ n : Nat,
         (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 0)
            = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 6))
         ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 1)
            = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 7))
         ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 2)
            = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 8))
         ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 3)
            = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 9))
         ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 4)
            = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 10))
         ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 5)
            = ObserverDigitsCyclePeriodicityBridge.cyclePos (n + 10 ^ 11)))

theorem prism_observer_worked_class_package : WorkedClassPackageProp := by
  refine ⟨by native_decide, PrismSummaryAPI.prism_projection_compatibility_entry,
    PrismObserverBridgeAPI.prism_observer_bridge_smoke, ?_, ?_⟩
  · simpa using ObserverCycleBridgeAPI.shiftClass_examples
  · intro n
    exact cyclePos_class_bundle n

abbrev WorkedClassSmokeProp : Prop :=
    ((PrismProjectionCompatibilityProtocol.allCompatibleAllLevels = true)
      ∧ (ObserverDigitsCyclePeriodicityProtocol.allShiftPeriodicity = true)
      ∧ (ObserverDigitsCyclePositionProtocol.allCycleTick10_6_return = true))
    ∧ (List.map ObserverCycleBridgeAPI.cycleShiftClass [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        = [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5])
    ∧ (ObserverDigitsCyclePeriodicityBridge.cyclePos (10 ^ 4)
        = ObserverDigitsCyclePeriodicityBridge.cyclePos (10 ^ 10))

theorem prism_observer_worked_class_smoke : WorkedClassSmokeProp := by
  refine ⟨PrismObserverBridgeAPI.prism_observer_bridge_smoke, ?_, ?_⟩
  · simpa using ObserverCycleBridgeAPI.shiftClass_examples
  · simpa [Nat.zero_add] using cyclePos_class4 0

end PrismObserverWorkedClassAPI
