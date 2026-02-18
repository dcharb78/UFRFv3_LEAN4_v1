import Mathlib

/-!
# Recursive Grid (Base-13 Depth / Phase Coupling)

This file formalizes the discrete "recursive grid" mechanism that shows up in UFRF notes:

* There is a base cycle length `13`.
* A "depth" coordinate is obtained by repeated `(div, mod)` in base 13.
* When the inner (depth-0) digit returns (hits `12` then advances), the next depth advances: this
  is exactly the **carry chain** of base-13 counting.
* Simultaneous depth closings occur at `13^k`: all digits below depth `k` are `0`.

This is intentionally **exact and discrete**; no floating points and no empirical assumptions.
-/

namespace RecursiveGridBase13

def base : Nat := 13

/-- The depth-`d` phase digit of time `t` in base-13: `digit d t = ⌊t/13^d⌋ mod 13`. -/
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
-- Structural: digit recursion (shifting one depth is division by the base)
-- ------------------------------------------------------------

/--
Depth shift law:

`digit (d+1) t = digit d (t / 13)`.

This is the exact discrete version of “higher-depth phase is the lower-depth phase of the
coarser (divided) clock”.
-/
theorem digit_succ (d t : Nat) : digit (d + 1) t = digit d (t / base) := by
  unfold digit
  -- `(t/base) / base^d = t / (base * base^d)` and `base^(d+1) = base^d * base`.
  -- Commutativity reconciles the order of multiplication.
  simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

-- ------------------------------------------------------------
-- Structural: base-power ticks (increment at a chosen depth)
-- ------------------------------------------------------------

/--
Adding `13^d` advances the depth-`d` digit by one step (mod 13).

This is the exact discrete version of “depth `d` has tick-size `13^d`”.
-/
theorem digit_add_basePow_self (d t : Nat) :
    digit d (t + base ^ d) = (digit d t + 1) % base := by
  unfold digit
  have hpos : 0 < base ^ d := by
    simpa using (Nat.pow_pos base_pos : 0 < base ^ d)
  have hdiv : (t + base ^ d) / base ^ d = t / base ^ d + 1 := by
    -- `(t + (base^d)*1) / (base^d) = t/(base^d) + 1`.
    simpa [Nat.mul_one] using (Nat.add_mul_div_left (x := t) (z := 1) (y := base ^ d) hpos)
  -- Now reduce the modulo statement.
  -- `((q+1) % base) = ((q % base) + 1) % base` since `1 % base = 1`.
  simp [hdiv, Nat.add_mod, Nat.mod_eq_of_lt base_gt_one]

/--
Adding `13^d` does **not** change any digit strictly below depth `d`.

This certifies one exact form of concurrency:
lower depths evolve "faster", and a tick for depth `d` is invisible to all depths `< d`.
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
    -- `base^(i + (d-i)) = base^i * base^(d-i)`.
    calc
      base ^ d = base ^ (i + (d - i)) := by
        simp [hsum]
      _ = base ^ i * base ^ (d - i) := by
        simp [Nat.pow_add]
  have hdiv : (t + base ^ d) / base ^ i = t / base ^ i + base ^ (d - i) := by
    -- `(t + (base^i) * base^(d-i)) / (base^i) = t/(base^i) + base^(d-i)`.
    have :=
      (Nat.add_mul_div_left (x := t) (z := base ^ (d - i)) (y := base ^ i) hpos)
    simpa [hpow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- Since `i < d`, the added term is divisible by `base`, hence vanishes mod `base`.
  have hne : d - i ≠ 0 := Nat.sub_ne_zero_of_lt hi
  have hdivBase : base ∣ base ^ (d - i) := by
    exact dvd_pow (dvd_rfl : base ∣ base) hne
  have hmod0 : (base ^ (d - i)) % base = 0 := Nat.mod_eq_zero_of_dvd hdivBase
  -- Conclude using `Nat.add_mod`.
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
-- Concrete anchors (matches the "phase across depths" observation)
-- ------------------------------------------------------------

theorem digits_at_1000 :
    digit 0 1000 = 12 ∧ digit 1 1000 = 11 ∧ digit 2 1000 = 5 ∧ digit 3 1000 = 0 := by
  native_decide

theorem digits_at_169 :
    digit 0 169 = 0 ∧ digit 1 169 = 0 ∧ digit 2 169 = 1 := by
  native_decide

theorem digits_at_2197 :
    digit 0 2197 = 0 ∧ digit 1 2197 = 0 ∧ digit 2 2197 = 0 ∧ digit 3 2197 = 1 := by
  native_decide

-- ------------------------------------------------------------
-- Structural: depth closings at 13^k
-- ------------------------------------------------------------

theorem pow_div_pow_eq_pow_sub (k d : Nat) (hd : d ≤ k) :
    base ^ k / base ^ d = base ^ (k - d) := by
  -- Use: `base^k = base^(k-d) * base^d` and divide by `base^d`.
  have hpos : 0 < base ^ d := by
    simpa using (Nat.pow_pos base_pos : 0 < base ^ d)
  apply Nat.div_eq_of_eq_mul_left hpos
  -- `base^(k-d) * base^d = base^(k-d+d) = base^k`.
  have : k - d + d = k := Nat.sub_add_cancel hd
  calc
    base ^ k = base ^ (k - d + d) := by simp [this]
    _ = base ^ (k - d) * base ^ d := by
      simp [Nat.pow_add, Nat.mul_comm]
    _ = base ^ (k - d) * base ^ d := rfl

theorem digit_basePow_of_lt (k d : Nat) (hd : d < k) : digit d (base ^ k) = 0 := by
  unfold digit
  have hle : d ≤ k := Nat.le_of_lt hd
  -- Reduce the quotient to `base^(k-d)`.
  have hq : base ^ k / base ^ d = base ^ (k - d) := pow_div_pow_eq_pow_sub k d hle
  -- Since `d < k`, `k - d ≠ 0`, so `base ∣ base^(k-d)`.
  have hne : k - d ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt hd
  have hdiv : base ∣ base ^ (k - d) := by
    -- `base ∣ base` and `dvd_pow` lifts divisibility to positive powers.
    exact dvd_pow (dvd_rfl : base ∣ base) hne
  -- Conclude the mod is zero.
  simpa [hq] using (Nat.mod_eq_zero_of_dvd hdiv)

theorem digit_basePow_self (k : Nat) : digit k (base ^ k) = 1 := by
  unfold digit
  have hpos : 0 < base ^ k := by
    simpa using (Nat.pow_pos base_pos : 0 < base ^ k)
  have hdiv : base ^ k / base ^ k = 1 := Nat.div_self hpos
  -- `1 % base = 1` since `base > 1`.
  have hmod : (1 : Nat) % base = 1 := by
    exact Nat.mod_eq_of_lt base_gt_one
  simp [hdiv, hmod]

theorem digit_basePow_le (k d : Nat) (hd : d ≤ k) :
    digit d (base ^ k) = if d = k then 1 else 0 := by
  by_cases hdk : d = k
  · subst hdk
    simp [digit_basePow_self]
  · have hlt : d < k := lt_of_le_of_ne hd hdk
    simp [hdk, digit_basePow_of_lt k d hlt]

-- ------------------------------------------------------------
-- Structural: "carry" at the return position (12) advances the next depth
-- ------------------------------------------------------------

/--
If the depth-0 digit is at the return state (`base-1`, i.e. `12` for base 13),
then the next tick resets the inner digit to `0` and increments the next depth.

This is the exact discrete content of:
“when depth-0 hits RETURN, depth-1 advances one position”.
-/
theorem carry_at_return (t : Nat) (ht : t % base = base - 1) :
    (t + 1) % base = 0 ∧ (t + 1) / base = t / base + 1 := by
  -- Decompose `t` into `t % base + base*(t/base)`.
  have hdecomp : t = t % base + base * (t / base) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mod_add_div t base).symm
  -- Specialize the remainder to `base-1` (for base=13, this is `12`).
  have ht' : t = (base - 1) + base * (t / base) := by
    simpa [ht] using hdecomp
  -- Now `t+1 = base*(t/base + 1)`.
  have hmul : t + 1 = base * (t / base + 1) := by
    calc
      t + 1 = ((base - 1) + base * (t / base)) + 1 := by
        exact congrArg (fun x => x + 1) ht'
      _ = (base - 1) + (base * (t / base) + 1) := by
        simp [Nat.add_assoc]
      _ = (base - 1) + (1 + base * (t / base)) := by
        simp [Nat.add_comm]
      _ = (base - 1 + 1) + base * (t / base) := by
        simp [Nat.add_assoc]
      _ = base + base * (t / base) := by
        have h : base - 1 + 1 = base := Nat.sub_add_cancel (Nat.succ_le_iff.2 base_pos)
        simp [h]
      _ = base * (t / base) + base := by
        simp [Nat.add_comm]
      _ = base * (t / base + 1) := by
        simp [Nat.mul_add]
  constructor
  · -- Remainder is 0 since `base ∣ t+1`.
    have : base ∣ (t + 1) := by
      refine ⟨t / base + 1, ?_⟩
      exact hmul
    simpa using (Nat.mod_eq_zero_of_dvd this)
  · -- Quotient increments by 1.
    calc
      (t + 1) / base = (base * (t / base + 1)) / base := by simp [hmul]
      _ = t / base + 1 := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.mul_div_cancel_left (t / base + 1) base_pos)

end RecursiveGridBase13
