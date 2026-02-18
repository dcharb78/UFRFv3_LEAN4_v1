import Recursive_Grid_CarryCascade_Theorem

/-!
# Recursive Grid: Block Periodicity (`mod b^k` invariance)

This file extends the generic recursive-grid digit model with a key scale-invariant fact:

For any base `b > 1`, depths `< k` only depend on the residue class `t mod b^k`.

Equivalently:
- adding any multiple of `b^k` does not change any digit at depth `< k`.

This matches the repo's narrative of concurrent nesting:
"nodes become positions of other nodes" and lower-scale state is invariant under higher-scale
index shifts.

All results are exact `Nat` arithmetic (no floats, no placeholders).
-/

namespace RecursiveGridGenericBase

variable {b : Nat}

private theorem pow_eq_mul_pow_sub (k d : Nat) (hd : d ≤ k) :
    b ^ k = b ^ d * b ^ (k - d) := by
  have hk : k = d + (k - d) := (Nat.add_sub_of_le hd).symm
  calc
    b ^ k = b ^ (d + (k - d)) := congrArg (fun n => b ^ n) hk
    _ = b ^ d * b ^ (k - d) := by simp [Nat.pow_add]

/--
**Scale invariance of lower digits:**

If `d < k`, then the depth-`d` digit is invariant under adding any multiple of `b^k`.
-/
theorem digit_add_mul_basePow_of_lt (k d t m : Nat) (hb : 1 < b) (hd : d < k) :
    digit (b := b) d (t + m * b ^ k) = digit (b := b) d t := by
  unfold digit
  have hb0 : 0 < b := base_pos (b := b) hb
  have hpos : 0 < b ^ d := by
    simpa using (Nat.pow_pos hb0 : 0 < b ^ d)
  have hle : d ≤ k := Nat.le_of_lt hd
  have hmul : m * b ^ k = b ^ d * (m * b ^ (k - d)) := by
    calc
      m * b ^ k = m * (b ^ d * b ^ (k - d)) := by
        simp [pow_eq_mul_pow_sub (b := b) k d hle]
      _ = b ^ d * (m * b ^ (k - d)) := by
        simp [Nat.mul_left_comm]
  have hdiv : (t + m * b ^ k) / b ^ d = t / b ^ d + m * b ^ (k - d) := by
    -- `(t + (b^d)*z) / (b^d) = t/(b^d) + z`.
    simpa [hmul] using
      (Nat.add_mul_div_left (x := t) (z := m * b ^ (k - d)) (y := b ^ d) hpos)
  have hne : k - d ≠ 0 := Nat.sub_ne_zero_of_lt hd
  have hpowdvd : b ∣ b ^ (k - d) := dvd_pow (dvd_rfl : b ∣ b) hne
  have hmulvd : b ∣ m * b ^ (k - d) := dvd_mul_of_dvd_right hpowdvd m
  have hmod0 : (m * b ^ (k - d)) % b = 0 := Nat.mod_eq_zero_of_dvd hmulvd
  calc
    ((t + m * b ^ k) / b ^ d) % b = (t / b ^ d + m * b ^ (k - d)) % b := by
      simp [hdiv]
    _ = ((t / b ^ d) % b + (m * b ^ (k - d)) % b) % b := by
      simp [Nat.add_mod]
    _ = ((t / b ^ d) % b + 0) % b := by
      simp [hmod0]
    _ = (t / b ^ d) % b := by simp

/--
Any pure `b^k`-block shift has zero digits below depth `k`.
-/
theorem digit_mul_basePow_of_lt (k d m : Nat) (hb : 1 < b) (hd : d < k) :
    digit (b := b) d (m * b ^ k) = 0 := by
  -- Reduce to invariance from `t = 0`.
  have h :=
    digit_add_mul_basePow_of_lt (b := b) (k := k) (d := d) (t := 0) (m := m) hb hd
  -- `digit d 0 = 0`.
  have h' : digit (b := b) d (m * b ^ k) = digit (b := b) d 0 := by
    simpa using h
  simpa [digit] using h'

/--
At a block boundary, all depths `< k` are in the return state.

This is the periodic form of the carry-cascade boundary:
the all-return event occurs at every `t ≡ -1 (mod b^k)`.
-/
theorem digit_blockBoundary_of_lt (k d m : Nat) (hb : 1 < b) (hd : d < k) :
    digit (b := b) d (m * b ^ k + (b ^ k - 1)) = b - 1 := by
  -- Commute the block shift to the right and use invariance.
  calc
    digit (b := b) d (m * b ^ k + (b ^ k - 1))
        = digit (b := b) d ((b ^ k - 1) + m * b ^ k) := by
            simp [Nat.add_comm]
    _ = digit (b := b) d (b ^ k - 1) := by
          simpa using
            (digit_add_mul_basePow_of_lt (b := b) (k := k) (d := d) (t := b ^ k - 1) (m := m) hb hd)
    _ = b - 1 := digit_basePow_sub_one_of_lt (b := b) k d hb hd

/--
One tick after the block boundary, all depths `< k` reset to `0`.
-/
theorem digit_afterBlockBoundaryTick_of_lt (k d m : Nat) (hb : 1 < b) (hd : d < k) :
    digit (b := b) d (m * b ^ k + (b ^ k - 1) + 1) = 0 := by
  have hb0 : 0 < b := base_pos (b := b) hb
  have hk1 : 1 ≤ b ^ k := Nat.succ_le_of_lt (Nat.pow_pos hb0 : 0 < b ^ k)
  have hstep : m * b ^ k + (b ^ k - 1) + 1 = (m + 1) * b ^ k := by
    calc
      m * b ^ k + (b ^ k - 1) + 1 = m * b ^ k + ((b ^ k - 1) + 1) := by
        simp [Nat.add_assoc]
      _ = m * b ^ k + b ^ k := by
        simp [Nat.sub_add_cancel hk1]
      _ = (m + 1) * b ^ k := by
        calc
          m * b ^ k + b ^ k = m * b ^ k + 1 * b ^ k := by simp
          _ = (m + 1) * b ^ k := by
            exact (Nat.add_mul m 1 (b ^ k)).symm
  -- Reduce to a pure block shift, which has zero low digits.
  simpa [hstep] using (digit_mul_basePow_of_lt (b := b) (k := k) (d := d) (m := m + 1) hb hd)

end RecursiveGridGenericBase
