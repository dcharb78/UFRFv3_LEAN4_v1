import Mathlib
import GetBangCompat

/-!
# Observer Digits vs Cycle Position Protocol (Finite Deterministic Bridge)

Protocol mirror for:
- `observer_digits_cycle_position_protocol.py`
- `observer_digits_cycle_position_results.json`

This stays finite and deterministic:
- depths `0..6`,
- samples `0..199`.
-/

namespace ObserverDigitsCyclePositionProtocol

def digitAt (depth n : Nat) : Nat :=
  (n / (10 ^ depth)) % 10

def cyclePos (n : Nat) : Nat := n % 13

def samples : List Nat := List.range 200
def depths : List Nat := [0, 1, 2, 3, 4, 5, 6]

def shiftTablePow10Mod13 : List Nat :=
  depths.map (fun d => (10 ^ d) % 13)

def plusDigitShiftHolds (d n : Nat) : Bool :=
  digitAt d (n + 10 ^ d) == ((digitAt d n + 1) % 10)

def plusCycleShiftHolds (d n : Nat) : Bool :=
  cyclePos (n + 10 ^ d) == ((cyclePos n + ((10 ^ d) % 13)) % 13)

def lowerDigitStable (i d n : Nat) : Bool :=
  digitAt i (n + 10 ^ d) == digitAt i n

def lowerDigitStableAt (d n : Nat) : Bool :=
  (List.range d).all (fun i => lowerDigitStable i d n)

def allPlusDigitShift : Bool :=
  depths.all (fun d => samples.all (fun n => plusDigitShiftHolds d n))

def allPlusCycleShift : Bool :=
  depths.all (fun d => samples.all (fun n => plusCycleShiftHolds d n))

def allLowerDigitStable : Bool :=
  depths.all (fun d => samples.all (fun n => lowerDigitStableAt d n))

def cycleTick10_6_return_holds (n : Nat) : Bool :=
  cyclePos (n * 10 ^ 6) == cyclePos n

def allCycleTick10_6_return : Bool :=
  samples.all cycleTick10_6_return_holds

theorem finite_observer_cycle_shift_summary :
    shiftTablePow10Mod13 = [1, 10, 9, 12, 3, 4, 1] ∧
    allPlusDigitShift = true ∧
    allPlusCycleShift = true ∧
    allLowerDigitStable = true ∧
    allCycleTick10_6_return = true := by
  native_decide

end ObserverDigitsCyclePositionProtocol
