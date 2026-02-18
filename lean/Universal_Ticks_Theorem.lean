import Mathlib

namespace UniversalTicks

/-!
Universal Ticks (Base-10 Scale Invariance)
=========================================

This file formalizes a discrete version of the "universal ticks" idea:

Represent a natural number `n` by its base-10 *decade* (order of magnitude) and a scale-invariant
*leading block*.

The key certified property is scale invariance under multiplication by powers of 10:

`leadingBlock (n * 10^k) = leadingBlock n` (for `n ≠ 0`).

This is a precise, Lean-checkable form of:
"log100 is log1 in the cycle", "log200 is log2", etc.
-/

def decade (n : Nat) : Nat :=
  Nat.log 10 n

/--
Scale-invariant "leading block" of `n` in base 10:

`leadingBlock n = n / 10^(decade n)`.

For `n ≠ 0`, this is the integer quotient after removing the largest power of 10 not exceeding `n`.
-/
def leadingBlock (n : Nat) : Nat :=
  n / 10 ^ decade n

theorem decade_mul10 (n : Nat) (hn : n ≠ 0) : decade (n * 10) = decade n + 1 := by
  -- `Nat.log_mul_base` is exactly the "advance one decade" law.
  simpa [decade, Nat.mul_comm] using (Nat.log_mul_base (b := 10) (n := n) (by decide) hn)

theorem leadingBlock_bounds (n : Nat) (hn : n ≠ 0) :
    1 ≤ leadingBlock n ∧ leadingBlock n < 10 := by
  unfold leadingBlock decade
  -- Let `d = log 10 n`. Then `10^d ≤ n < 10^(d+1)`.
  have hpow_pos : 0 < (10 ^ Nat.log 10 n) := Nat.pow_pos (a := 10) (n := Nat.log 10 n) (by decide)
  have hlow : (10 ^ Nat.log 10 n) ≤ n := Nat.pow_log_le_self 10 hn
  have hhigh : n < 10 ^ (Nat.log 10 n).succ := Nat.lt_pow_succ_log_self (b := 10) (by decide) n
  constructor
  · -- Lower bound: `1 ≤ n / 10^d` iff `10^d ≤ n`.
    exact (Nat.one_le_div_iff hpow_pos).2 hlow
  · -- Upper bound: `n / 10^d < 10` iff `n < 10 * 10^d`.
    have : n < 10 * (10 ^ Nat.log 10 n) := by
      -- `10^(d+1) = 10^d * 10`.
      simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhigh
    exact (Nat.div_lt_iff_lt_mul hpow_pos).2 this

theorem decade_mul_pow10 (n k : Nat) (hn : n ≠ 0) :
    decade (n * 10 ^ k) = decade n + k := by
  induction k with
  | zero =>
      simp [decade]
  | succ k ih =>
      have hn' : n * 10 ^ k ≠ 0 := by
        exact Nat.mul_ne_zero hn (pow_ne_zero k (by decide : (10 : Nat) ≠ 0))
      -- Step by one factor of 10.
      have hstep : decade ((n * 10 ^ k) * 10) = decade (n * 10 ^ k) + 1 := by
        simpa [decade, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (Nat.log_mul_base (b := 10) (n := n * 10 ^ k) (by decide) hn')
      -- Rewrite `10^(k+1)` as `10^k * 10` and finish.
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ih] using hstep

theorem leadingBlock_mul_pow10 (n k : Nat) (hn : n ≠ 0) :
    leadingBlock (n * 10 ^ k) = leadingBlock n := by
  unfold leadingBlock
  -- Rewrite the exponent using `decade_mul_pow10`.
  have hdec : decade (n * 10 ^ k) = decade n + k := decade_mul_pow10 n k hn
  -- `10^(decade n + k) = 10^(decade n) * 10^k`, so we can cancel the common factor `10^k` in the division.
  -- This is a discrete, exact counterpart to scale-invariance of `frac(log10 n)`.
  simpa [hdec, Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    (Nat.mul_div_mul_right (n := n) (k := 10 ^ decade n) (m := 10 ^ k)
      (Nat.pow_pos (a := 10) (n := k) (by decide : 0 < (10 : Nat))))

end UniversalTicks
