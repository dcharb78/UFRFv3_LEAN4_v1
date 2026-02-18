import Recursive_Grid_Generic_Base_Theorem

/-!
# Recursive Grid: Carry Cascade at `b^k - 1`

This file formalizes the "simultaneous depth closing" event that shows up throughout the UFRF
story as:

* `13, 169, 2197, ... = 13^k` are structural node counts (index-of-indexes),
* the boundary just before a node, `13^k - 1`, is an **all-return** state on depths `< k`,
* one tick later (`+1`) the system is exactly at the node boundary `13^k`, i.e. all lower depths
  reset and the next depth increments.

We prove this generically for any base `b > 1` using the digit extractor from
`Recursive_Grid_Generic_Base_Theorem.lean`:

`digit d t := ⌊t / b^d⌋ mod b`.

Everything is exact `Nat` arithmetic; no placeholders.
-/

namespace RecursiveGridGenericBase

variable {b : Nat}

private theorem basePow_pos (k : Nat) (hb : 1 < b) : 0 < b ^ k :=
  by
    simpa using (Nat.pow_pos (base_pos (b := b) hb) : 0 < b ^ k)

private theorem basePow_one_le (k : Nat) (hb : 1 < b) : 1 ≤ b ^ k :=
  Nat.succ_le_of_lt (basePow_pos (b := b) k hb)

private theorem basePow_sub_one_add_one (k : Nat) (hb : 1 < b) : b ^ k - 1 + 1 = b ^ k :=
  Nat.sub_add_cancel (basePow_one_le (b := b) k hb)

/-!
## Boundary decomposition: `b^(k+1) - 1 = (b-1) + b*(b^k - 1)`
-/

theorem pow_succ_sub_one_eq (k : Nat) (hb : 1 < b) :
    b ^ (k + 1) - 1 = (b - 1) + b * (b ^ k - 1) := by
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt (base_pos (b := b) hb)
  have hk1 : 1 ≤ b ^ k := basePow_one_le (b := b) k hb
  have hk1' : 1 + (b ^ k - 1) = b ^ k := by
    calc
      1 + (b ^ k - 1) = (b ^ k - 1) + 1 := by simp [Nat.add_comm]
      _ = b ^ k := Nat.sub_add_cancel hk1
  have hk1_succ : 1 ≤ b ^ (k + 1) := basePow_one_le (b := b) (k + 1) hb
  -- Prove an equality with a common trailing `+1`, then cancel.
  have hsum :
      (b ^ (k + 1) - 1) + 1 = ((b - 1) + b * (b ^ k - 1)) + 1 := by
    calc
      (b ^ (k + 1) - 1) + 1 = b ^ (k + 1) := Nat.sub_add_cancel hk1_succ
      _ = ((b - 1) + b * (b ^ k - 1)) + 1 := by
        -- Show `((b-1) + b*(b^k-1)) + 1 = b^(k+1)`.
        have : ((b - 1) + b * (b ^ k - 1)) + 1 = b ^ (k + 1) := by
          calc
            ((b - 1) + b * (b ^ k - 1)) + 1
                = (b - 1 + 1) + b * (b ^ k - 1) := by
                    simp [Nat.add_assoc, Nat.add_comm]
            _ = b + b * (b ^ k - 1) := by
                    simp [Nat.sub_add_cancel hb1]
            _ = b * 1 + b * (b ^ k - 1) := by simp
            _ = b * (1 + (b ^ k - 1)) := by simp [Nat.mul_add]
            _ = b * (b ^ k) := by simp [hk1']
            _ = b ^ k * b := by simp [Nat.mul_comm]
            _ = b ^ (k + 1) := by simp [Nat.pow_succ]
        simp [this]
  exact Nat.add_right_cancel hsum

theorem pow_succ_sub_one_div (k : Nat) (hb : 1 < b) :
    (b ^ (k + 1) - 1) / b = b ^ k - 1 := by
  have hb0 : 0 < b := base_pos (b := b) hb
  have hlt : b - 1 < b := Nat.sub_lt hb0 (Nat.succ_pos 0)
  calc
    (b ^ (k + 1) - 1) / b = ((b - 1) + b * (b ^ k - 1)) / b := by
      simp [pow_succ_sub_one_eq (b := b) k hb]
    _ = (b - 1) / b + (b ^ k - 1) := by
      simpa using
        (Nat.add_mul_div_left (x := b - 1) (z := (b ^ k - 1)) (y := b) hb0)
    _ = 0 + (b ^ k - 1) := by
      simp [Nat.div_eq_of_lt hlt]
    _ = b ^ k - 1 := by simp

theorem pow_succ_sub_one_mod (k : Nat) (hb : 1 < b) :
    (b ^ (k + 1) - 1) % b = b - 1 := by
  have hb0 : 0 < b := base_pos (b := b) hb
  have hlt : b - 1 < b := Nat.sub_lt hb0 (Nat.succ_pos 0)
  calc
    (b ^ (k + 1) - 1) % b = ((b - 1) + b * (b ^ k - 1)) % b := by
      simp [pow_succ_sub_one_eq (b := b) k hb]
    _ = (b - 1) % b := by
      exact Nat.add_mul_mod_self_left (b - 1) b (b ^ k - 1)
    _ = b - 1 := by
      exact Nat.mod_eq_of_lt hlt

/-!
## All-return state at `b^k - 1` (depths `< k`)
-/

theorem digit_basePow_sub_one_of_lt (k d : Nat) (hb : 1 < b) (hd : d < k) :
    digit (b := b) d (b ^ k - 1) = b - 1 := by
  induction k generalizing d with
  | zero =>
      exact (Nat.not_lt_zero d hd).elim
  | succ k ih =>
      cases d with
      | zero =>
          -- depth 0: `digit 0 t = t % b`
          have : (b ^ (k + 1) - 1) % b = b - 1 := pow_succ_sub_one_mod (b := b) k hb
          simpa [digit] using this
      | succ d =>
          have hd' : d < k := Nat.succ_lt_succ_iff.1 hd
          -- shift depth by dividing by `b`, which lowers the exponent by one at `b^(k+1)-1`
          have hdiv : (b ^ (k + 1) - 1) / b = b ^ k - 1 := pow_succ_sub_one_div (b := b) k hb
          calc
            digit (b := b) (d + 1) (b ^ (k + 1) - 1)
                = digit (b := b) d ((b ^ (k + 1) - 1) / b) := by
                    simpa using (digit_succ (b := b) d (b ^ (k + 1) - 1))
            _ = digit (b := b) d (b ^ k - 1) := by simp [hdiv]
            _ = b - 1 := ih d hd'

theorem digit_basePow_sub_one_self (k : Nat) (hb : 1 < b) : digit (b := b) k (b ^ k - 1) = 0 := by
  unfold digit
  have hkpos : 0 < b ^ k := basePow_pos (b := b) k hb
  have hlt : b ^ k - 1 < b ^ k := Nat.sub_lt hkpos (Nat.succ_pos 0)
  have hdiv : (b ^ k - 1) / b ^ k = 0 := Nat.div_eq_of_lt hlt
  simp [hdiv]

/-!
## Carry cascade: `b^k - 1` (all return) → `b^k` (reset + next depth = 1)
-/

theorem carryCascade_at_basePow (k : Nat) (hb : 1 < b) :
    (∀ d < k, digit (b := b) d (b ^ k - 1) = b - 1)
    ∧ (∀ d < k, digit (b := b) d (b ^ k - 1 + 1) = 0)
    ∧ digit (b := b) k (b ^ k - 1 + 1) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact digit_basePow_sub_one_of_lt (b := b) k d hb hd
  · intro d hd
    have h1 : b ^ k - 1 + 1 = b ^ k := basePow_sub_one_add_one (b := b) k hb
    -- after the tick, we are exactly at `b^k`, so all lower digits are `0`
    simpa [h1] using digit_basePow_of_lt (b := b) k d hb hd
  · have h1 : b ^ k - 1 + 1 = b ^ k := basePow_sub_one_add_one (b := b) k hb
    simpa [h1] using digit_basePow_self (b := b) k hb

end RecursiveGridGenericBase
