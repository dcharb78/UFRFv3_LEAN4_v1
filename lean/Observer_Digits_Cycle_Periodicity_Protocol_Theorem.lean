import Mathlib
import GetBangCompat

/-!
# Observer/Cycle Periodicity Protocol (Finite Deterministic Bridge)

Protocol mirror for:
- `observer_digits_cycle_periodicity_protocol.py`
- `observer_digits_cycle_periodicity_results.json`

Finite witness window:
- depths `0..23`,
- samples `0..199`.
-/

namespace ObserverDigitsCyclePeriodicityProtocol

def base : Nat := 10
def cycleMod : Nat := 13
def period : Nat := 6
def maxDepth : Nat := 24

def digitAt (depth n : Nat) : Nat :=
  (n / (base ^ depth)) % base

def cyclePos (n : Nat) : Nat := n % cycleMod

def shift (d : Nat) : Nat :=
  (base ^ d) % cycleMod

def samples : List Nat := List.range 200
def depths : List Nat := List.range maxDepth
def periodDepths : List Nat := List.range (maxDepth - period)

def periodShiftTablePow10Mod13 : List Nat :=
  (List.range period).map shift

def shiftPeriodicityHolds (d : Nat) : Bool :=
  shift (d + period) == shift d

def shiftResidueLookupHolds (d : Nat) : Bool :=
  shift d == shift (d % period)

def plusDigitShiftHolds (d n : Nat) : Bool :=
  digitAt d (n + base ^ d) == ((digitAt d n + 1) % base)

def plusCycleShiftHolds (d n : Nat) : Bool :=
  cyclePos (n + base ^ d) == ((cyclePos n + shift d) % cycleMod)

def plusCycleShiftResidueHolds (d n : Nat) : Bool :=
  cyclePos (n + base ^ d) == ((cyclePos n + shift (d % period)) % cycleMod)

def lowerDigitStable (i d n : Nat) : Bool :=
  digitAt i (n + base ^ d) == digitAt i n

def lowerDigitStableAt (d n : Nat) : Bool :=
  (List.range d).all (fun i => lowerDigitStable i d n)

def cycleAddPow10PeriodicityHolds (d n : Nat) : Bool :=
  cyclePos (n + base ^ (d + period)) == cyclePos (n + base ^ d)

def cycleMulTick10_6ReturnHolds (n : Nat) : Bool :=
  cyclePos (n * base ^ period) == cyclePos n

def allShiftPeriodicity : Bool :=
  periodDepths.all shiftPeriodicityHolds

def allShiftResidueLookup : Bool :=
  depths.all shiftResidueLookupHolds

def allPlusDigitShift : Bool :=
  depths.all (fun d => samples.all (fun n => plusDigitShiftHolds d n))

def allPlusCycleShift : Bool :=
  depths.all (fun d => samples.all (fun n => plusCycleShiftHolds d n))

def allPlusCycleShiftResidue : Bool :=
  depths.all (fun d => samples.all (fun n => plusCycleShiftResidueHolds d n))

def allLowerDigitStable : Bool :=
  depths.all (fun d => samples.all (fun n => lowerDigitStableAt d n))

def allCycleAddPow10Periodicity : Bool :=
  periodDepths.all (fun d => samples.all (fun n => cycleAddPow10PeriodicityHolds d n))

def allCycleMulTick10_6Return : Bool :=
  samples.all cycleMulTick10_6ReturnHolds

theorem finite_observer_cycle_periodicity_summary :
    periodShiftTablePow10Mod13 = [1, 10, 9, 12, 3, 4] ∧
    allShiftPeriodicity = true ∧
    allShiftResidueLookup = true ∧
    allPlusDigitShift = true ∧
    allPlusCycleShift = true ∧
    allPlusCycleShiftResidue = true ∧
    allLowerDigitStable = true ∧
    allCycleAddPow10Periodicity = true ∧
    allCycleMulTick10_6Return = true := by
  native_decide

end ObserverDigitsCyclePeriodicityProtocol
