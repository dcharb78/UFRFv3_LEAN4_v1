import Mathlib.Data.ZMod.Basic

import CycleStep_Orbit_Theorem

/-!
# Chromatic (12) × Breathing (13) Concurrency: 52-Step Return

This is a small, concrete "systems become nodes" anchor:

- The chromatic cycle is modeled as `ZMod 12`.
- The UFRF breathing cycle is modeled as `ZMod 13`.

If we step by `+3`, then:
- in `ZMod 12` the orbit size is `4` (the diminished chord `{0,3,6,9}`),
- in `ZMod 13` the orbit size is `13` (since `gcd(13,3)=1`),
- synchronizing the two axes gives `lcm(4,13)=52`.

So in the product node `ZMod (12*13)`, stepping by `+3` returns after 52 steps.

All results are exact and no-placeholder.
-/

namespace ChromaticBreathing52

/-- Concrete evaluation: `lcm(orbitSize 12 3, orbitSize 13 3) = 52`. -/
theorem lcm_orbitSize_12_13_step3 :
    Nat.lcm (CycleStepOrbit.orbitSize 12 3) (CycleStepOrbit.orbitSize 13 3) = 52 := by
  native_decide

/-- Concrete evaluation: `orbitSize (12*13) 3 = 52`. -/
theorem orbitSize_12_mul_13_step3 :
    CycleStepOrbit.orbitSize (12 * 13) 3 = 52 := by
  native_decide

/-- The synchronized orbit-size identity in the product node `ZMod (12*13)`. -/
abbrev chromatic_breathing_52_orbitSize_statement : Prop :=
    CycleStepOrbit.orbitSize (12 * 13) 3 = 52

/-- The synchronized orbit-size identity in the product node `ZMod (12*13)`. -/
theorem chromatic_breathing_52_orbitSize : chromatic_breathing_52_orbitSize_statement := by
  simpa [chromatic_breathing_52_orbitSize_statement] using orbitSize_12_mul_13_step3

/-- The synchronized 52-step return statement in the product node `ZMod (12*13)`. -/
abbrev chromatic_breathing_52_statement : Prop :=
    (52 : Nat) • (3 : ZMod (12 * 13)) = 0

/-- The synchronized 52-step return statement in the product node `ZMod (12*13)`. -/
theorem chromatic_breathing_52 : chromatic_breathing_52_statement := by
  have hcop : Nat.Coprime 12 13 := by
    native_decide
  -- Use the general two-axis synchronization theorem, then specialize the computed `lcm`.
  simpa [chromatic_breathing_52_statement, lcm_orbitSize_12_13_step3] using
    (CycleStepOrbit.lcm_orbitSize_two_axes_returns 12 13 3 hcop)

/--
Exact order for the composite node:

In `ZMod (12*13)`, stepping by `+3` returns after `n` steps **iff** `52 ∣ n`.
-/
theorem nsmul_step3_eq_zero_iff_52_dvd (n : Nat) :
    n • (3 : ZMod (12 * 13)) = 0 ↔ 52 ∣ n := by
  have hm : 0 < 12 * 13 := by decide
  -- `n•s=0 ↔ orbitSize ∣ n`, and `orbitSize (12*13) 3 = 52`.
  simpa [orbitSize_12_mul_13_step3] using
    (CycleStepOrbit.nsmul_eq_zero_iff_orbitSize_dvd (m := 12 * 13) (s := 3) (n := n) hm)

end ChromaticBreathing52
