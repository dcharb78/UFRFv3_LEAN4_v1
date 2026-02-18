import Recursive_Grid_Base10_Theorem
import Multidimensional_Ticks_Theorem
import Mathlib

/-!
# Observer Digits vs Cycle Positions (Mechanism Bridge)

This file keeps two views explicit and separate:

- observer-facing decimal state: base-10 digit (`0..9`),
- cycle-facing position state: residue class mod `13`.

Both are tracked concurrently but obey different update laws.
-/

namespace ObserverDigitsCyclePositionBridge

def cyclePos (n : Nat) : Nat := n % 13

theorem cyclePos_lt (n : Nat) : cyclePos n < 13 := by
  unfold cyclePos
  exact Nat.mod_lt _ (by decide)

theorem cyclePos_add_pow10 (n d : Nat) :
    cyclePos (n + 10 ^ d) = (cyclePos n + (10 ^ d % 13)) % 13 := by
  unfold cyclePos
  simp [Nat.add_mod]

/--
Bridge package at one decimal-depth step:
- digit state stays in `{0..9}`,
- cycle position stays in `{0..12}`,
- digit follows decimal carry law,
- cycle position advances by modular shift.
-/
theorem observer_digit_cycle_bridge (n d : Nat) :
    RecursiveGridBase10.digit d n < 10 ∧
    cyclePos n < 13 ∧
    RecursiveGridBase10.digit d (n + 10 ^ d) =
      (RecursiveGridBase10.digit d n + 1) % 10 ∧
    cyclePos (n + 10 ^ d) = (cyclePos n + (10 ^ d % 13)) % 13 := by
  constructor
  · simpa [RecursiveGridBase10.base] using (RecursiveGridBase10.digit_lt_base d n)
  constructor
  · exact cyclePos_lt n
  constructor
  · simpa [RecursiveGridBase10.base] using (RecursiveGridBase10.digit_add_basePow_self d n)
  · exact cyclePos_add_pow10 n d

/-- At six decimal ticks, the mod-13 cycle position returns exactly. -/
theorem cyclePos_tick10_6_invariant (n : Nat) :
    cyclePos (MultidimensionalTicks.tick10 6 n) = cyclePos n := by
  unfold cyclePos
  simpa using (MultidimensionalTicks.tick10_mod13_return_every_six_decades n)

end ObserverDigitsCyclePositionBridge
