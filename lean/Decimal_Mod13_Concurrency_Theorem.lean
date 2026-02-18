/-
# Decimal / Mod-13 Concurrency (Universal Ticks Meets 13-Cycle)

This file formalizes a concrete "concurrent nesting" bridge:

* Decimal scaling by `10^k` changes magnitude/decade, but preserves the *log phase* (captured
  discretely in `Universal_Ticks_Theorem.lean` via `leadingBlock` invariance).
* Mod-13 positions are the basic 13-cycle coordinate used throughout the repo.

Key fact:

* `10^6 ≡ 1 (mod 13)` (because `10^3 ≡ -1 (mod 13)`), hence multiplying by `10^6` returns a
  number to the same mod-13 residue.

This is **not** a claim about primes; it is an exact modular identity connecting base-10 ticks
to the 13-cycle.
-/

import Mathlib

namespace DecimalMod13

/-!
## Half-period "flip"

Before the full return at 6 decades, there is a clean half-period identity:

* `10^3 ≡ -1 (mod 13)` (i.e. `10^3 % 13 = 12`)

So multiplying by `10^3` is an involution on the mod-13 coordinate: applying it twice
is the same as multiplying by `10^6`, which returns to the same residue.
-/

theorem ten_pow_three_mod13 : (10 ^ 3 : Nat) % 13 = 12 := by
  native_decide

theorem ten_pow_three_add_one_mod13 : ((10 ^ 3 : Nat) + 1) % 13 = 0 := by
  native_decide

theorem mul_ten_pow_three_add_self_mod13 (n : Nat) : ((n * 10 ^ 3) + n) % 13 = 0 := by
  -- `n*10^3 + n = n*(10^3 + 1)`, and `10^3 + 1` is divisible by 13.
  have hrewrite : n * 10 ^ 3 + n = n * (10 ^ 3 + 1) := by
    -- Expand `n*(a+1)` and cancel `n*1`.
    have : n * (10 ^ 3 + 1) = n * 10 ^ 3 + n := by
      -- `n*(a+1) = n*a + n*1`.
      simpa [Nat.mul_one] using (Nat.mul_add n (10 ^ 3) 1)
    simpa using this.symm
  calc
    ((n * 10 ^ 3) + n) % 13 = (n * (10 ^ 3 + 1)) % 13 := by
      simpa using congrArg (fun x => x % 13) hrewrite
    _ = ((n % 13) * (((10 ^ 3 + 1) : Nat) % 13)) % 13 := by
      simp [Nat.mul_mod]
    _ = ((n % 13) * 0) % 13 := by
      simp
    _ = 0 := by simp

theorem ten_pow_six_mod13 : (10 ^ 6 : Nat) % 13 = 1 := by
  native_decide

theorem ten_pow_six_mul_mod13 (m : Nat) : (10 ^ (6 * m) : Nat) % 13 = 1 := by
  -- Use `a^(m*n) = (a^m)^n` and reduce modulo 13.
  calc
    (10 ^ (6 * m) : Nat) % 13 = ((10 ^ 6) ^ m) % 13 := by
      simp [pow_mul]
    _ = (((10 ^ 6) % 13) ^ m) % 13 := by
      simp [Nat.pow_mod]
    _ = (1 ^ m) % 13 := by
      simp
    _ = 1 := by
      simp

theorem mul_ten_pow_six_mod13 (n : Nat) : (n * 10 ^ 6) % 13 = n % 13 := by
  have hlt : n % 13 < 13 := Nat.mod_lt _ (by decide)
  calc
    (n * 10 ^ 6) % 13 = ((n % 13) * ((10 ^ 6) % 13)) % 13 := by
      simp [Nat.mul_mod]
    _ = ((n % 13) * 1) % 13 := by
      simp
    _ = (n % 13) % 13 := by
      simp
    _ = n % 13 := by
      simp [Nat.mod_eq_of_lt hlt]

theorem mul_ten_pow_six_mul_mod13 (n m : Nat) : (n * 10 ^ (6 * m)) % 13 = n % 13 := by
  have hlt : n % 13 < 13 := Nat.mod_lt _ (by decide)
  calc
    (n * 10 ^ (6 * m)) % 13 = ((n % 13) * ((10 ^ (6 * m)) % 13)) % 13 := by
      simp [Nat.mul_mod]
    _ = ((n % 13) * 1) % 13 := by
      simp [ten_pow_six_mul_mod13]
    _ = (n % 13) % 13 := by
      simp
    _ = n % 13 := by
      simp [Nat.mod_eq_of_lt hlt]

theorem mul_ten_pow_six_mod13_all : ∀ n : Nat, (n * 10 ^ 6) % 13 = n % 13 :=
  mul_ten_pow_six_mod13

theorem mul_ten_pow_six_mul_mod13_all : ∀ n m : Nat, (n * 10 ^ (6 * m)) % 13 = n % 13 :=
  mul_ten_pow_six_mul_mod13

end DecimalMod13
