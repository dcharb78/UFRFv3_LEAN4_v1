import Mathlib.Data.ZMod.Basic

import CycleStep_Orbit_Theorem

/-!
# Quarter-Cycle Invariant in `ZMod (4*d)`

This file records a simple, fully general version of the “diminished-chord” / `{3,6,9,0}` idea:

- In the cycle `ZMod (4*d)`, stepping by `+d` returns after **4** moves:
  `0 → d → 2d → 3d → 0`.

This is purely a ratio fact: the step is exactly one quarter of the modulus.
All results are exact and no-placeholder.
-/

namespace QuarterCycleZMod

/-- Orbit-size identity: in `ZMod (4*d)`, the step `d` has orbit size `4` (for `d > 0`). -/
theorem orbitSize_four_mul_self {d : Nat} (hd : 0 < d) :
    CycleStepOrbit.orbitSize (4 * d) d = 4 := by
  unfold CycleStepOrbit.orbitSize
  have hg : Nat.gcd (4 * d) d = d := by
    calc
      Nat.gcd (4 * d) d = Nat.gcd (4 * d) (1 * d) := by simp
      _ = Nat.gcd 4 1 * d := by
            simp
      _ = d := by simp
  -- `(4*d)/gcd(4*d,d) = (4*d)/d = 4`
  calc
    (4 * d) / Nat.gcd (4 * d) d = (4 * d) / d := by simp [hg]
    _ = 4 := by
          -- `Nat.mul_div_right` gives `d*4/d = 4`; rewrite `4*d` as `d*4`.
          simpa [Nat.mul_comm] using (Nat.mul_div_right 4 (m := d) hd)

/-- 4-step return in `ZMod (4*d)` under the step `+d` (for `d > 0`). -/
abbrev quarter_cycle_return_statement : Prop :=
    ∀ {d : Nat}, 0 < d → (4 : Nat) • (d : ZMod (4 * d)) = 0

/-- 4-step return in `ZMod (4*d)` under the step `+d` (for `d > 0`). -/
theorem quarter_cycle_return : quarter_cycle_return_statement := by
  intro d hd
  have hret : CycleStepOrbit.orbitSize (4 * d) d • (d : ZMod (4 * d)) = 0 :=
    CycleStepOrbit.orbitSize_nsmul_step_returns (4 * d) d
  simpa [orbitSize_four_mul_self (d := d) hd] using hret

/--
Exact order for the quarter-step:

In `ZMod (4*d)`, the step `+d` returns after `n` steps **iff** `4 ∣ n`.

This upgrades the "returns in 4 steps" statement to a true minimal-period fact.
-/
theorem nsmul_step_eq_zero_iff_four_dvd {d n : Nat} (hd : 0 < d) :
    n • (d : ZMod (4 * d)) = 0 ↔ 4 ∣ n := by
  have hm : 0 < 4 * d := Nat.mul_pos (by decide : 0 < 4) hd
  -- `n•s=0 ↔ orbitSize ∣ n`, then `orbitSize (4*d) d = 4`.
  simpa [orbitSize_four_mul_self (d := d) hd] using
    (CycleStepOrbit.nsmul_eq_zero_iff_orbitSize_dvd (m := 4 * d) (s := d) (n := n) hm)

/-- Explicit 0→d→2d→3d→0 cycle in `ZMod (4*d)` (for `d > 0`). -/
abbrev quarter_nsmul_cycle_statement : Prop :=
    ∀ {d : Nat}, 0 < d →
      (0 • (d : ZMod (4 * d)) = 0) ∧
      (1 • (d : ZMod (4 * d)) = d) ∧
      (2 • (d : ZMod (4 * d)) = ((2 * d : Nat) : ZMod (4 * d))) ∧
      (3 • (d : ZMod (4 * d)) = ((3 * d : Nat) : ZMod (4 * d))) ∧
      (4 • (d : ZMod (4 * d)) = 0)

/-- Explicit 0→d→2d→3d→0 cycle in `ZMod (4*d)` (for `d > 0`). -/
theorem quarter_nsmul_cycle : quarter_nsmul_cycle_statement := by
  intro d hd
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
  · simp
  · simp
  · calc
      (2 • (d : ZMod (4 * d))) = ((2 : Nat) : ZMod (4 * d)) * (d : ZMod (4 * d)) := by
            simp [nsmul_eq_mul]
      _ = ((2 * d : Nat) : ZMod (4 * d)) := by
            simp
  · calc
      (3 • (d : ZMod (4 * d))) = ((3 : Nat) : ZMod (4 * d)) * (d : ZMod (4 * d)) := by
            simp [nsmul_eq_mul]
      _ = ((3 * d : Nat) : ZMod (4 * d)) := by
            simp
  · simpa using (quarter_cycle_return (d := d) hd)

end QuarterCycleZMod
