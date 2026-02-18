import REST_Seam_Generic_Canonical_Equiv_Theorem
import Recursive_Grid_Base10_Theorem

/-!
# REST Seam ↔ Recursive Grid (Base-10) Bridge

This file links REST seam transport bookkeeping to base-10 recursive-grid digits.
-/

namespace RESTSeamOverlap

theorem seamTick_eq_mul10_plus (g r : Nat) :
    seamTick g r = (g + 1) * 10 + r := by
  calc
    seamTick g r = birth (g + 1) + r := seamTick_as_child_birth_plus g r
    _ = (g + 1) * 10 + r := by simp [birth]

theorem digit0_at_seamTick (g r : Nat) (hr : r ≤ 9) :
    RecursiveGridBase10.digit 0 (seamTick g r) = r := by
  have hrlt : r < 10 := by omega
  calc
    RecursiveGridBase10.digit 0 (seamTick g r)
        = (seamTick g r) % 10 := by
            simp [RecursiveGridBase10.digit, RecursiveGridBase10.base]
    _ = ((g + 1) * 10 + r) % 10 := by
          simp [seamTick_eq_mul10_plus]
    _ = r % 10 := by
          simp [Nat.add_mod]
    _ = r := Nat.mod_eq_of_lt hrlt

theorem digit0_eq_childState_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    RecursiveGridBase10.digit 0 (seamTick g r) = state (g + 1) (seamTick g r) := by
  have hltCycle : r < cycle := by
    have hr4 : r < 4 := Nat.lt_of_le_of_lt hr (by decide : 3 < 4)
    have h4leCycle : 4 ≤ cycle := by
      simp [cycle]
    exact lt_of_lt_of_le hr4 h4leCycle
  rw [digit0_at_seamTick g r (by omega), state_child_at_seamTick_mod_via_generic g r]
  exact (Nat.mod_eq_of_lt hltCycle).symm

theorem digit1_at_seamTick (g r : Nat) (hr : r ≤ 9) :
    RecursiveGridBase10.digit 1 (seamTick g r) = (g + 1) % 10 := by
  have hrlt : r < 10 := by omega
  have hdiv : (((g + 1) * 10 + r) / 10) = g + 1 := by
    have hpos : 0 < 10 := by decide
    have htmp : (r + 10 * (g + 1)) / 10 = r / 10 + (g + 1) := by
      simpa [Nat.mul_comm] using (Nat.add_mul_div_right (x := r) (y := g + 1) (z := 10) hpos)
    calc
      (((g + 1) * 10 + r) / 10)
          = (r + 10 * (g + 1)) / 10 := by
              simp [Nat.add_comm, Nat.mul_comm]
      _ = r / 10 + (g + 1) := htmp
      _ = g + 1 := by simp [Nat.div_eq_of_lt hrlt]
  calc
    RecursiveGridBase10.digit 1 (seamTick g r)
        = ((seamTick g r) / 10) % 10 := by
            simp [RecursiveGridBase10.digit, RecursiveGridBase10.base]
    _ = ((((g + 1) * 10 + r) / 10) % 10) := by
          simp [seamTick_eq_mul10_plus]
    _ = (g + 1) % 10 := by simp [hdiv]

end RESTSeamOverlap
