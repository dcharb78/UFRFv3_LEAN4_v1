import Mathlib

/-!
# Observer/Cycle Periodicity Bridge (Unbounded Mechanism Lemmas)

This bridge lifts finite protocol witnesses into all-`n` / all-`d` mechanism lemmas
for the cycle-position axis (`mod 13`), while keeping observer digits as a separate lens.
-/

namespace ObserverDigitsCyclePeriodicityBridge

def digitAt (depth n : Nat) : Nat :=
  (n / (10 ^ depth)) % 10

def cyclePos (n : Nat) : Nat :=
  n % 13

theorem pow10_mod13_period6 (d : Nat) :
    (10 ^ (d + 6)) % 13 = (10 ^ d) % 13 := by
  have h6 : (10 ^ 6) % 13 = 1 := by native_decide
  calc
    (10 ^ (d + 6)) % 13 = (10 ^ d * 10 ^ 6) % 13 := by
      rw [Nat.pow_add]
    _ = (((10 ^ d) % 13) * ((10 ^ 6) % 13)) % 13 := by
      rw [Nat.mul_mod]
    _ = (((10 ^ d) % 13) * 1) % 13 := by
      rw [h6]
    _ = (10 ^ d) % 13 := by simp

theorem cyclePos_add_pow10_update (n d : Nat) :
    cyclePos (n + 10 ^ d) = (cyclePos n + ((10 ^ d) % 13)) % 13 := by
  unfold cyclePos
  rw [Nat.add_mod]

theorem cyclePos_add_pow10_period6 (n d : Nat) :
    cyclePos (n + 10 ^ (d + 6)) = cyclePos (n + 10 ^ d) := by
  unfold cyclePos
  rw [Nat.add_mod, Nat.add_mod]
  simp [pow10_mod13_period6]

theorem cyclePos_add_pow10_update_period6 (n d : Nat) :
    cyclePos (n + 10 ^ (d + 6)) = (cyclePos n + ((10 ^ d) % 13)) % 13 := by
  rw [cyclePos_add_pow10_period6, cyclePos_add_pow10_update]

theorem cyclePos_mul_tick10_6_return (n : Nat) :
    cyclePos (n * 10 ^ 6) = cyclePos n := by
  unfold cyclePos
  have h6 : (10 ^ 6) % 13 = 1 := by native_decide
  calc
    (n * 10 ^ 6) % 13 = ((n % 13) * ((10 ^ 6) % 13)) % 13 := by
      rw [Nat.mul_mod]
    _ = ((n % 13) * 1) % 13 := by
      rw [h6]
    _ = n % 13 := by simp

theorem pow10_mul6_mod13_one (q : Nat) :
    (10 ^ (6 * q)) % 13 = 1 := by
  induction q with
  | zero =>
      norm_num
  | succ q ih =>
      calc
        (10 ^ (6 * Nat.succ q)) % 13 = (10 ^ (6 * q + 6)) % 13 := by
          simp [Nat.mul_succ, Nat.add_comm]
        _ = (10 ^ (6 * q) * 10 ^ 6) % 13 := by
          rw [Nat.pow_add]
        _ = (((10 ^ (6 * q)) % 13) * ((10 ^ 6) % 13)) % 13 := by
          rw [Nat.mul_mod]
        _ = (1 * 1) % 13 := by
          simp [ih]
        _ = 1 := by
          norm_num

theorem pow10_mod13_reduce_mod6 (d : Nat) :
    (10 ^ d) % 13 = (10 ^ (d % 6)) % 13 := by
  have hd : d = d % 6 + 6 * (d / 6) := by
    exact (Nat.mod_add_div d 6).symm
  rw [hd, Nat.pow_add, Nat.mul_mod]
  rw [pow10_mul6_mod13_one]
  simp

theorem cyclePos_add_pow10_residue_normal_form (n d : Nat) :
    cyclePos (n + 10 ^ d) = (cyclePos n + ((10 ^ (d % 6)) % 13)) % 13 := by
  rw [cyclePos_add_pow10_update, pow10_mod13_reduce_mod6]

theorem cyclePos_add_pow10_same_residue (n d e : Nat) (hde : d % 6 = e % 6) :
    cyclePos (n + 10 ^ d) = cyclePos (n + 10 ^ e) := by
  rw [cyclePos_add_pow10_residue_normal_form, cyclePos_add_pow10_residue_normal_form]
  simp [hde]

end ObserverDigitsCyclePeriodicityBridge
