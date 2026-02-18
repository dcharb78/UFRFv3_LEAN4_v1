import Mathlib
import Observer_Digits_Cycle_Periodicity_Bridge_Theorem

/-!
# Observer/Cycle Bridge API

Small packaged API over the observer/cycle periodicity bridge so downstream
composed-tick and smoke wrappers can consume canonical entry lemmas.
-/

namespace ObserverCycleBridgeAPI

open ObserverDigitsCyclePeriodicityBridge

def cycleShiftClass (d : Nat) : Nat := d % 6

theorem cycleShiftClass_spec (d : Nat) :
    cycleShiftClass d < 6 := by
  unfold cycleShiftClass
  exact Nat.mod_lt _ (by decide)

theorem pow10_mod13_normal_form (d : Nat) :
    (10 ^ d) % 13 = (10 ^ cycleShiftClass d) % 13 := by
  simpa [cycleShiftClass] using pow10_mod13_reduce_mod6 d

theorem cyclePos_add_pow10_normal_form (n d : Nat) :
    cyclePos (n + 10 ^ d) =
      (cyclePos n + ((10 ^ cycleShiftClass d) % 13)) % 13 := by
  simpa [cycleShiftClass] using cyclePos_add_pow10_residue_normal_form n d

theorem cyclePos_add_pow10_eq_of_same_class
    (n d e : Nat) (h : cycleShiftClass d = cycleShiftClass e) :
    cyclePos (n + 10 ^ d) = cyclePos (n + 10 ^ e) := by
  have hmod : d % 6 = e % 6 := by simpa [cycleShiftClass] using h
  exact cyclePos_add_pow10_same_residue n d e hmod

theorem cyclePos_tick10_6_return (n : Nat) :
    cyclePos (n * 10 ^ 6) = cyclePos n := by
  exact cyclePos_mul_tick10_6_return n

theorem shiftClass_examples :
    (List.map cycleShiftClass [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) =
      [0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] := by
  native_decide

end ObserverCycleBridgeAPI
