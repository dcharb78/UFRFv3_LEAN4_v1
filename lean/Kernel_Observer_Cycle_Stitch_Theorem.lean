import Index_Of_Indexes_Subintervals_Theorem
import Observer_Digits_CyclePosition_Bridge_Theorem
import Composed_Tick_API_Theorem

/-!
# 0→1 Kernel Stitch Package (Refinement + Observer Tick + Cycle Class)

This module packages three already-certified mechanism surfaces into one theorem API:

1. index-of-indexes refinement parent law (`floorBin_parent`);
2. observer-facing decimal/cycle concurrent update (`observer_digit_cycle_bridge`);
3. cycle-position class-normalized tick law (`cyclePos_tick10_normal_form` and same-class equality).

No new axioms; this is a discoverability/consolidation bridge.
-/

namespace KernelObserverCycleStitch

open IndexOfIndexes
open IndexOfIndexesSubintervals
open MultidimensionalTicks
open ComposedTickAPI
open ObserverCycleBridgeAPI

def observerDigitCycleBridgeProp (n d : Nat) : Prop :=
  RecursiveGridBase10.digit d n < 10 ∧
    ObserverDigitsCyclePositionBridge.cyclePos n < 13 ∧
      RecursiveGridBase10.digit d (n + 10 ^ d) =
        (RecursiveGridBase10.digit d n + 1) % 10 ∧
        ObserverDigitsCyclePositionBridge.cyclePos (n + 10 ^ d) =
          (ObserverDigitsCyclePositionBridge.cyclePos n + (10 ^ d % 13)) % 13

theorem kernel_observer_cycle_stitch
    (k : Nat) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (n d e : Nat) (hclass : cycleShiftClass d = cycleShiftClass e) :
    (q ∈ coarseInterval k (floorBin k q hq0 hq1))
    ∧ (floorBin k q hq0 hq1 = (splitEquiv k (floorBin (k + 1) q hq0 hq1)).1)
    ∧ observerDigitCycleBridgeProp n d
    ∧ (ComposedTickAPI.cyclePos (tick10 d n) =
        (ComposedTickAPI.cyclePos n * ((10 ^ cycleShiftClass d) % 13)) % 13)
    ∧ (ComposedTickAPI.cyclePos (tick10 d n) = ComposedTickAPI.cyclePos (tick10 e n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact floorBin_mem_coarseInterval (k := k) (q := q) hq0 hq1
  · exact floorBin_parent (k := k) (q := q) hq0 hq1
  · exact ObserverDigitsCyclePositionBridge.observer_digit_cycle_bridge n d
  · exact ComposedTickAPI.cyclePos_tick10_normal_form n d
  · exact ComposedTickAPI.cyclePos_tick10_eq_of_same_shift_class n d e hclass

theorem kernel_observer_cycle_stitch_example :
    (0 : ℚ) ∈ coarseInterval 0 (floorBin 0 0 (by norm_num) (by norm_num))
    ∧ (floorBin 0 0 (by norm_num) (by norm_num) =
        (splitEquiv 0 (floorBin 1 0 (by norm_num) (by norm_num))).1)
    ∧ observerDigitCycleBridgeProp 1 0
    ∧ (ComposedTickAPI.cyclePos (tick10 0 1) =
        (ComposedTickAPI.cyclePos 1 * ((10 ^ cycleShiftClass 0) % 13)) % 13)
    ∧ (ComposedTickAPI.cyclePos (tick10 0 1) = ComposedTickAPI.cyclePos (tick10 6 1)) := by
  exact kernel_observer_cycle_stitch
    0 0 (by norm_num) (by norm_num) 1 0 6 (by decide)

theorem kernel_observer_cycle_stitch_example_cycle_class :
    ComposedTickAPI.cyclePos (tick10 0 1) = ComposedTickAPI.cyclePos (tick10 6 1) := by
  exact (kernel_observer_cycle_stitch_example).2.2.2.2

theorem kernel_refinement_zero_canonical :
    (0 : ℚ) ∈ coarseInterval 0 (floorBin 0 0 (by norm_num) (by norm_num))
    ∧ (floorBin 0 0 (by norm_num) (by norm_num) =
        (splitEquiv 0 (floorBin 1 0 (by norm_num) (by norm_num))).1) := by
  exact ⟨(kernel_observer_cycle_stitch_example).1, (kernel_observer_cycle_stitch_example).2.1⟩

theorem kernel_cycle_class_0_6 (n : Nat) :
    ComposedTickAPI.cyclePos (tick10 0 n) = ComposedTickAPI.cyclePos (tick10 6 n) := by
  have hpkg :=
    kernel_observer_cycle_stitch
      0 0 (by norm_num) (by norm_num) n 0 6 (by decide)
  exact hpkg.2.2.2.2

theorem kernel_observer_cycle_package_0_6 (n : Nat) :
    observerDigitCycleBridgeProp n 0
    ∧ (ComposedTickAPI.cyclePos (tick10 0 n) =
        (ComposedTickAPI.cyclePos n * ((10 ^ cycleShiftClass 0) % 13)) % 13)
    ∧ (ComposedTickAPI.cyclePos (tick10 0 n) = ComposedTickAPI.cyclePos (tick10 6 n)) := by
  have hpkg :=
    kernel_observer_cycle_stitch
      0 0 (by norm_num) (by norm_num) n 0 6 (by decide)
  exact ⟨hpkg.2.2.1, hpkg.2.2.2.1, hpkg.2.2.2.2⟩

theorem kernel_observer_cycle_smoke_1 :
    observerDigitCycleBridgeProp 1 0
    ∧ (ComposedTickAPI.cyclePos (tick10 0 1) = ComposedTickAPI.cyclePos (tick10 6 1)) := by
  exact ⟨(kernel_observer_cycle_stitch_example).2.2.1, kernel_observer_cycle_stitch_example_cycle_class⟩

end KernelObserverCycleStitch
