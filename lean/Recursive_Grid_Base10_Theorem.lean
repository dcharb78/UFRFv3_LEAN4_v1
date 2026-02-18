import Mathlib
import Universal_Ticks_Theorem

/-!
# Recursive Grid (Base-10 Digits / Carry Concurrency)

This is the base-10 analogue of `Recursive_Grid_Base13_Theorem.lean`.

It formalizes a discrete version of the “universal ticks / 0-9 states” idea:

* Define the base-10 digit at depth `d` by repeated `(div, mod)`:
  `digit d t = ⌊t / 10^d⌋ mod 10`.
* Adding `10^d` increments the depth-`d` digit mod 10 and does not affect lower digits `< d`.
* If the ones digit is at the return state `9`, then the next tick carries:
  the ones digit resets to `0` and the next digit increments.

All statements are **exact** and use only `Nat` arithmetic (no floats, no approximations).
-/

namespace RecursiveGridBase10

def base : Nat := 10

/-- The depth-`d` digit of time `t` in base 10: `digit d t = ⌊t/10^d⌋ mod 10`. -/
def digit (d t : Nat) : Nat :=
  (t / base ^ d) % base

theorem base_pos : 0 < base := by
  simp [base]

theorem base_gt_one : 1 < base := by
  simp [base]

theorem digit_lt_base (d t : Nat) : digit d t < base := by
  unfold digit
  exact Nat.mod_lt _ base_pos

-- ------------------------------------------------------------
-- Structural: base-power ticks (increment at a chosen depth)
-- ------------------------------------------------------------

/--
Adding `10^d` advances the depth-`d` digit by one step (mod 10).
-/
theorem digit_add_basePow_self (d t : Nat) :
    digit d (t + base ^ d) = (digit d t + 1) % base := by
  unfold digit
  have hpos : 0 < base ^ d := by
    simpa using (Nat.pow_pos base_pos : 0 < base ^ d)
  have hdiv : (t + base ^ d) / base ^ d = t / base ^ d + 1 := by
    -- `(t + (base^d)*1) / (base^d) = t/(base^d) + 1`.
    simpa [Nat.mul_one] using (Nat.add_mul_div_left (x := t) (z := 1) (y := base ^ d) hpos)
  -- Reduce the modulo statement.
  simp [hdiv, Nat.add_mod, Nat.mod_eq_of_lt base_gt_one]

/--
Adding `10^d` does **not** change any digit strictly below depth `d`.
-/
theorem digit_add_basePow_lt (i d t : Nat) (hi : i < d) :
    digit i (t + base ^ d) = digit i t := by
  unfold digit
  have hpos : 0 < base ^ i := by
    simpa using (Nat.pow_pos base_pos : 0 < base ^ i)
  have hle : i ≤ d := Nat.le_of_lt hi
  have hsum : i + (d - i) = d := by
    -- `d - i + i = d`, then commute.
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hle)
  have hpow : base ^ d = base ^ i * base ^ (d - i) := by
    calc
      base ^ d = base ^ (i + (d - i)) := by simp [hsum]
      _ = base ^ i * base ^ (d - i) := by simp [Nat.pow_add]
  have hdiv : (t + base ^ d) / base ^ i = t / base ^ i + base ^ (d - i) := by
    have :=
      (Nat.add_mul_div_left (x := t) (z := base ^ (d - i)) (y := base ^ i) hpos)
    simpa [hpow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- Since `i < d`, the added term is divisible by `base`, hence vanishes mod `base`.
  have hne : d - i ≠ 0 := Nat.sub_ne_zero_of_lt hi
  have hdivBase : base ∣ base ^ (d - i) := dvd_pow (dvd_rfl : base ∣ base) hne
  have hmod0 : (base ^ (d - i)) % base = 0 := Nat.mod_eq_zero_of_dvd hdivBase
  calc
    ((t + base ^ d) / base ^ i) % base = (t / base ^ i + base ^ (d - i)) % base := by
      simp [hdiv]
    _ = ((t / base ^ i) % base + (base ^ (d - i)) % base) % base := by
      simp [Nat.add_mod]
    _ = ((t / base ^ i) % base + 0) % base := by
      simp [hmod0]
    _ = (t / base ^ i) % base := by
      simp

-- ------------------------------------------------------------
-- Structural: carry at the return digit (9)
-- ------------------------------------------------------------

/--
If the ones digit is at the return state (`9`), then the next tick resets it to `0`
and increments the next digit (carry).
-/
theorem carry_at_return (t : Nat) (ht : t % base = base - 1) :
    (t + 1) % base = 0 ∧ (t + 1) / base = t / base + 1 := by
  have hdecomp : t = t % base + base * (t / base) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mod_add_div t base).symm
  have ht' : t = (base - 1) + base * (t / base) := by
    simpa [ht] using hdecomp
  have hmul : t + 1 = base * (t / base + 1) := by
    calc
      t + 1 = ((base - 1) + base * (t / base)) + 1 := congrArg (fun x => x + 1) ht'
      _ = (base - 1 + 1) + base * (t / base) := by
        simp [Nat.add_left_comm, Nat.add_comm]
      _ = base + base * (t / base) := by
        have h : base - 1 + 1 = base := Nat.sub_add_cancel (Nat.succ_le_iff.2 base_pos)
        simp [h]
      _ = base * (t / base) + base := by
        simp [Nat.add_comm]
      _ = base * (t / base + 1) := by
        simp [Nat.mul_add, Nat.add_comm]
  constructor
  · -- Mod part: `base * k % base = 0`.
    calc
      (t + 1) % base = (base * (t / base + 1)) % base := by simp [hmul]
      _ = 0 := by simp
  · -- Div part: `(base*k) / base = k`.
    have : base * (t / base + 1) / base = t / base + 1 := by
      -- Rewrite `base * k` as `k * base` and cancel.
      simpa [Nat.mul_comm] using
        (Nat.mul_div_right (t / base + 1) (Nat.zero_lt_one.trans base_gt_one))
    simpa [hmul] using this

-- ------------------------------------------------------------
-- Concrete anchor (example)
-- ------------------------------------------------------------

theorem digits_at_1000 :
    digit 0 1000 = 0 ∧ digit 1 1000 = 0 ∧ digit 2 1000 = 0 ∧ digit 3 1000 = 1 := by
  native_decide

/-!
## Bridge to `UniversalTicks.leadingBlock`

At the decade depth `d = log_10 n`, the digit-extraction view and the `leadingBlock` view coincide:

* `leadingBlock n = n / 10^d`
* `digit d n = (n / 10^d) % 10`

Since `n / 10^d < 10` (for `n ≠ 0`), the modulo is redundant, so `digit d n = leadingBlock n`.
-/

theorem digit_at_decade_eq_leadingBlock (n : Nat) (hn : n ≠ 0) :
    digit (UniversalTicks.decade n) n = UniversalTicks.leadingBlock n := by
  -- Expand definitions; the only nontrivial step is that the quotient is `< 10`.
  unfold digit UniversalTicks.leadingBlock
  have hlt : n / 10 ^ UniversalTicks.decade n < 10 := (UniversalTicks.leadingBlock_bounds n hn).2
  -- If `q < 10`, then `q % 10 = q`.
  simp [base, Nat.mod_eq_of_lt hlt]

end RecursiveGridBase10
