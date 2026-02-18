import Mathlib

/-!
# Recursive Grid (Generic Base `b`)

This file extracts the shared discrete mechanism behind:

- `lean/Recursive_Grid_Base10_Theorem.lean`
- `lean/Recursive_Grid_Base13_Theorem.lean`

Namely, for any base `b > 1`, define the depth-`d` digit of time `t` by repeated `(div, mod)`:

`digit b d t = ⌊t / b^d⌋ mod b`.

Then:

- adding `b^d` increments the depth-`d` digit (mod `b`),
- adding `b^d` does not affect any lower digit `< d`,
- when the depth-0 digit is at the return state `b-1`, the next tick carries.

All statements are exact `Nat` arithmetic; no placeholders.
-/

namespace RecursiveGridGenericBase

variable {b : Nat}

/-- The depth-`d` digit of time `t` in base `b`: `digit d t = ⌊t/b^d⌋ mod b`. -/
def digit (d t : Nat) : Nat :=
  (t / b ^ d) % b

theorem base_pos (hb : 1 < b) : 0 < b :=
  lt_trans (Nat.zero_lt_one) hb

theorem digit_lt_base (d t : Nat) (hb : 1 < b) : digit (b := b) d t < b := by
  unfold digit
  exact Nat.mod_lt _ (base_pos (b := b) hb)

-- ------------------------------------------------------------
-- Structural: depth shift law
-- ------------------------------------------------------------

/--
Depth shift law:

`digit (d+1) t = digit d (t / b)`.

This is the exact discrete version of “higher depth is the lower depth of the coarser clock”.
-/
theorem digit_succ (d t : Nat) : digit (b := b) (d + 1) t = digit (b := b) d (t / b) := by
  unfold digit
  -- `(t/b) / b^d = t / (b * b^d)` and `b^(d+1) = b^d * b`.
  simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

-- ------------------------------------------------------------
-- Structural: base-power ticks (increment at a chosen depth)
-- ------------------------------------------------------------

/--
Adding `b^d` advances the depth-`d` digit by one step (mod `b`).
-/
theorem digit_add_basePow_self (d t : Nat) (hb : 1 < b) :
    digit (b := b) d (t + b ^ d) = (digit (b := b) d t + 1) % b := by
  unfold digit
  have hpos : 0 < b ^ d := by
    simpa using (Nat.pow_pos (base_pos (b := b) hb) : 0 < b ^ d)
  have hdiv : (t + b ^ d) / b ^ d = t / b ^ d + 1 := by
    -- `(t + (b^d)*1) / (b^d) = t/(b^d) + 1`.
    simpa [Nat.mul_one] using (Nat.add_mul_div_left (x := t) (z := 1) (y := b ^ d) hpos)
  simp [hdiv, Nat.add_mod, Nat.mod_eq_of_lt hb]

/--
Adding `b^d` does **not** change any digit strictly below depth `d`.

This is the exact concurrency statement: slower (higher) ticks are invisible to all lower depths.
-/
theorem digit_add_basePow_lt (i d t : Nat) (hb : 1 < b) (hi : i < d) :
    digit (b := b) i (t + b ^ d) = digit (b := b) i t := by
  unfold digit
  have hpos : 0 < b ^ i := by
    simpa using (Nat.pow_pos (base_pos (b := b) hb) : 0 < b ^ i)
  have hle : i ≤ d := Nat.le_of_lt hi
  have hsum : i + (d - i) = d := by
    simpa [Nat.add_comm] using (Nat.sub_add_cancel hle)
  have hpow : b ^ d = b ^ i * b ^ (d - i) := by
    calc
      b ^ d = b ^ (i + (d - i)) := by simp [hsum]
      _ = b ^ i * b ^ (d - i) := by simp [Nat.pow_add]
  have hdiv : (t + b ^ d) / b ^ i = t / b ^ i + b ^ (d - i) := by
    have :=
      (Nat.add_mul_div_left (x := t) (z := b ^ (d - i)) (y := b ^ i) hpos)
    simpa [hpow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  -- Since `i < d`, the added term is divisible by `b`, hence vanishes mod `b`.
  have hne : d - i ≠ 0 := Nat.sub_ne_zero_of_lt hi
  have hdivBase : b ∣ b ^ (d - i) := dvd_pow (dvd_rfl : b ∣ b) hne
  have hmod0 : (b ^ (d - i)) % b = 0 := Nat.mod_eq_zero_of_dvd hdivBase
  calc
    ((t + b ^ d) / b ^ i) % b = (t / b ^ i + b ^ (d - i)) % b := by
      simp [hdiv]
    _ = ((t / b ^ i) % b + (b ^ (d - i)) % b) % b := by
      simp [Nat.add_mod]
    _ = ((t / b ^ i) % b + 0) % b := by
      simp [hmod0]
    _ = (t / b ^ i) % b := by
      simp

-- ------------------------------------------------------------
-- Structural: carry at the return digit (`b-1`)
-- ------------------------------------------------------------

/--
If the depth-0 digit is at the return state (`b-1`), then the next tick resets it to `0`
and increments the next digit (carry).
-/
theorem carry_at_return (t : Nat) (hb : 1 < b) (ht : t % b = b - 1) :
    (t + 1) % b = 0 ∧ (t + 1) / b = t / b + 1 := by
  have hb0 : 0 < b := base_pos (b := b) hb
  have hdecomp : t = t % b + b * (t / b) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mod_add_div t b).symm
  have ht' : t = (b - 1) + b * (t / b) := by
    simpa [ht] using hdecomp
  have hmul : t + 1 = b * (t / b + 1) := by
    calc
      t + 1 = ((b - 1) + b * (t / b)) + 1 := congrArg (fun x => x + 1) ht'
      _ = (b - 1 + 1) + b * (t / b) := by
        simp [Nat.add_left_comm, Nat.add_comm]
      _ = b + b * (t / b) := by
        have h : b - 1 + 1 = b := Nat.sub_add_cancel (Nat.succ_le_iff.2 hb0)
        simp [h]
      _ = b * (t / b) + b := by
        simp [Nat.add_comm]
      _ = b * (t / b + 1) := by
        simp [Nat.mul_add, Nat.add_comm]
  constructor
  · -- Mod part: `b * k % b = 0`.
    have : b ∣ (t + 1) := by
      refine ⟨t / b + 1, ?_⟩
      exact hmul
    simpa using (Nat.mod_eq_zero_of_dvd this)
  · -- Div part: `(b*k)/b = k`.
    calc
      (t + 1) / b = (b * (t / b + 1)) / b := by simp [hmul]
      _ = t / b + 1 := by
        simpa [Nat.mul_comm] using
          (Nat.mul_div_cancel_left (t / b + 1) hb0)

-- ------------------------------------------------------------
-- Structural: depth closings at `b^k`
-- ------------------------------------------------------------

theorem pow_div_pow_eq_pow_sub (k d : Nat) (hb : 1 < b) (hd : d ≤ k) :
    b ^ k / b ^ d = b ^ (k - d) := by
  have hpos : 0 < b ^ d := by
    simpa using (Nat.pow_pos (base_pos (b := b) hb) : 0 < b ^ d)
  apply Nat.div_eq_of_eq_mul_left hpos
  have : k - d + d = k := Nat.sub_add_cancel hd
  calc
    b ^ k = b ^ (k - d + d) := by simp [this]
    _ = b ^ (k - d) * b ^ d := by
      simp [Nat.pow_add, Nat.mul_comm]

theorem digit_basePow_of_lt (k d : Nat) (hb : 1 < b) (hd : d < k) :
    digit (b := b) d (b ^ k) = 0 := by
  unfold digit
  have hle : d ≤ k := Nat.le_of_lt hd
  have hq : b ^ k / b ^ d = b ^ (k - d) := pow_div_pow_eq_pow_sub (b := b) k d hb hle
  have hne : k - d ≠ 0 := Nat.sub_ne_zero_of_lt hd
  have hdiv : b ∣ b ^ (k - d) := dvd_pow (dvd_rfl : b ∣ b) hne
  simpa [hq] using (Nat.mod_eq_zero_of_dvd hdiv)

theorem digit_basePow_self (k : Nat) (hb : 1 < b) : digit (b := b) k (b ^ k) = 1 := by
  unfold digit
  have hpos : 0 < b ^ k := by
    simpa using (Nat.pow_pos (base_pos (b := b) hb) : 0 < b ^ k)
  have hdiv : b ^ k / b ^ k = 1 := Nat.div_self hpos
  have hmod : (1 : Nat) % b = 1 := Nat.mod_eq_of_lt hb
  simp [hdiv, hmod]

theorem digit_basePow_le (k d : Nat) (hb : 1 < b) (hd : d ≤ k) :
    digit (b := b) d (b ^ k) = if d = k then 1 else 0 := by
  by_cases hdk : d = k
  · simp [hdk, digit_basePow_self (b := b) k hb]
  · have hlt : d < k := lt_of_le_of_ne hd hdk
    simp [hdk, digit_basePow_of_lt (b := b) k d hb hlt]

end RecursiveGridGenericBase
