import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Cycle-Step Orbit (Additive) in `ZMod m`

This file formalizes a general “orbit size” fact:

If you repeatedly add a step `s` in the cycle `ZMod m`, the orbit closes after

`m / gcd(m,s)`

steps (at the latest).

This is the abstract version of concrete “chord” / “sub-orbit” patterns like:
- mod 12 with step 3: `{0,3,6,9}` (a 4-cycle).

No placeholders; exact arithmetic only.
-/

namespace CycleStepOrbit

/-- The additive orbit-size bound for stepping by `s` in `ZMod m`. -/
def orbitSize (m s : Nat) : Nat := m / Nat.gcd m s

/-!
## Scale invariance (ratio-only)

If we scale both the modulus and the step by the same positive factor `k`,
the orbit size is unchanged:

`orbitSize (k*m) (k*s) = orbitSize m s`.

This is the exact arithmetic version of "structure depends on ratios, not absolute units".
-/

theorem orbitSize_scale_invariant {k m s : Nat} (hk : 0 < k) :
    orbitSize (k * m) (k * s) = orbitSize m s := by
  unfold orbitSize
  -- `gcd(k*m, k*s) = k*gcd(m,s)`, then cancel `k` from numerator/denominator.
  simpa [Nat.gcd_mul_left, Nat.mul_assoc] using
    (Nat.mul_div_mul_left (n := m) (k := Nat.gcd m s) hk)

theorem orbitSize_eq_modulus_of_coprime {m s : Nat} (h : Nat.Coprime m s) :
    orbitSize m s = m := by
  unfold orbitSize
  have hg : Nat.gcd m s = 1 := (Nat.coprime_iff_gcd_eq_one).1 h
  simp [hg]

theorem orbitSize_eq_modulus_of_prime {p s : Nat} (hp : Nat.Prime p) (hs : ¬ p ∣ s) :
    orbitSize p s = p := by
  apply orbitSize_eq_modulus_of_coprime
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hs

theorem orbitSize_nsmul_step_returns (m s : Nat) :
    orbitSize m s • (s : ZMod m) = 0 := by
  unfold orbitSize
  -- Let `g = gcd m s`.
  set g : Nat := Nat.gcd m s
  have hgM : g ∣ m := by
    simpa [g] using (Nat.gcd_dvd_left m s)
  have hgS : g ∣ s := by
    simpa [g] using (Nat.gcd_dvd_right m s)
  have hs : g * (s / g) = s := Nat.mul_div_cancel' hgS
  have hm : m / g * g = m := Nat.div_mul_cancel hgM
  -- Work in the ring structure: `n • a = (n : ZMod m) * a`.
  simp [nsmul_eq_mul]
  calc
    ((m / g : Nat) : ZMod m) * (s : ZMod m)
        = ((m / g : Nat) : ZMod m) * ((g * (s / g) : Nat) : ZMod m) := by
            simp [hs]
    _ = ((m / g : Nat) : ZMod m) * ((g : Nat) : ZMod m) * ((s / g : Nat) : ZMod m) := by
            simp [Nat.cast_mul, mul_assoc]
    _ = ((m / g * g : Nat) : ZMod m) * ((s / g : Nat) : ZMod m) := by
            -- Combine the first two factors into a single `Nat` product cast.
            rw [← Nat.cast_mul (m / g) g]
    _ = (m : ZMod m) * ((s / g : Nat) : ZMod m) := by
            simp [hm]
    _ = 0 := by
            -- `m = 0` in `ZMod m`.
            simp

theorem orbitSize_mul_step_dvd (m s : Nat) : m ∣ orbitSize m s * s := by
  -- Convert the `ZMod m` return statement into a divisibility statement on `Nat`.
  have hz : orbitSize m s • (s : ZMod m) = 0 := orbitSize_nsmul_step_returns m s
  have hz' : ((orbitSize m s : Nat) : ZMod m) * ((s : Nat) : ZMod m) = 0 := by
    simpa [nsmul_eq_mul] using hz
  have hz'' : ((orbitSize m s * s : Nat) : ZMod m) = 0 := by
    -- Rewrite `↑(orbitSize) * ↑s` as `↑(orbitSize*s)`.
    have h := hz'
    rw [← Nat.cast_mul (orbitSize m s) s] at h
    exact h
  exact (ZMod.natCast_eq_zero_iff (orbitSize m s * s) m).1 hz''

/-!
## Converting `nsmul` closure into a divisibility condition
-/

/--
`n • (s : ZMod m) = 0` iff `m ∣ n*s`.

This is the exact arithmetic bridge between:
- cycle closure in the additive group `ZMod m`, and
- divisibility on `Nat`.
-/
theorem nsmul_eq_zero_iff_modulus_dvd_mul (m s n : Nat) :
    n • (s : ZMod m) = 0 ↔ m ∣ n * s := by
  constructor
  · intro hn
    have hnMul : ((n : Nat) : ZMod m) * ((s : Nat) : ZMod m) = 0 := by
      simpa [nsmul_eq_mul] using hn
    have hnCast : ((n * s : Nat) : ZMod m) = 0 := by
      have h' := hnMul
      rw [← Nat.cast_mul n s] at h'
      simpa using h'
    exact (ZMod.natCast_eq_zero_iff (n * s) m).1 hnCast
  · intro hdiv
    have hnCast : ((n * s : Nat) : ZMod m) = 0 :=
      (ZMod.natCast_eq_zero_iff (n * s) m).2 hdiv
    have hnMul : ((n : Nat) : ZMod m) * ((s : Nat) : ZMod m) = 0 := by
      simpa [Nat.cast_mul] using hnCast
    simpa [nsmul_eq_mul] using hnMul

/-!
## Minimality / exact order

`orbitSize m s = m / gcd(m,s)` is not just a return bound: it is the **exact** additive order of
`(s : ZMod m)` (for positive moduli).

Concretely: if `n • s = 0`, then `orbitSize m s ∣ n`, and conversely if `orbitSize m s ∣ n`
then `n • s = 0`.
-/

/--
If stepping by `+s` in `ZMod m` returns after `n` steps, then `orbitSize m s` divides `n`.

Assumption `0 < m` excludes the degenerate modulus `m = 0` case (`ZMod 0 = ℤ`), where the
`m / gcd(m,s)` formula is not an order.
-/
theorem orbitSize_dvd_of_nsmul_eq_zero {m s n : Nat} (hm : 0 < m)
    (hn : n • (s : ZMod m) = 0) : orbitSize m s ∣ n := by
  unfold orbitSize
  set g : Nat := Nat.gcd m s
  have hgpos : 0 < g := by
    simpa [g] using Nat.gcd_pos_of_pos_left s hm
  have hgM : g ∣ m := by
    simpa [g] using (Nat.gcd_dvd_left m s)
  have hgS : g ∣ s := by
    simpa [g] using (Nat.gcd_dvd_right m s)

  -- Convert the return statement into `m ∣ n*s`.
  have hnMul : ((n : Nat) : ZMod m) * ((s : Nat) : ZMod m) = 0 := by
    simpa [nsmul_eq_mul] using hn
  have hnCast : ((n * s : Nat) : ZMod m) = 0 := by
    have h' := hnMul
    rw [← Nat.cast_mul n s] at h'
    simpa using h'
  have hdiv : m ∣ n * s := (ZMod.natCast_eq_zero_iff (n * s) m).1 hnCast

  -- Cancel the gcd factor to get `(m/g) ∣ n*(s/g)`.
  have hm' : m = (m / g) * g := (Nat.div_mul_cancel hgM).symm
  have hs' : s = (s / g) * g := (Nat.div_mul_cancel hgS).symm
  have hns' : n * s = (n * (s / g)) * g := by
    calc
      n * s = n * ((s / g) * g) := by
            simpa using congrArg (fun t => n * t) hs'
      _ = (n * (s / g)) * g := by
            rw [Nat.mul_assoc]
  have hdiv' : (m / g) * g ∣ (n * (s / g)) * g := by
    have h := hdiv
    rw [hm'] at h
    rw [hns'] at h
    exact h
  have hdiv'' : m / g ∣ n * (s / g) :=
    Nat.dvd_of_mul_dvd_mul_right hgpos hdiv'

  -- Since `g = gcd(m,s)`, the reduced parts are coprime, so cancel `(s/g)`.
  have hcop : Nat.Coprime (m / g) (s / g) := by
    have : 0 < Nat.gcd m s := Nat.gcd_pos_of_pos_left s hm
    simpa [g] using (Nat.coprime_div_gcd_div_gcd (m := m) (n := s) this)
  exact hcop.dvd_of_dvd_mul_right hdiv''

/-- If `orbitSize m s ∣ n`, then stepping by `+s` in `ZMod m` returns after `n` steps. -/
theorem nsmul_eq_zero_of_orbitSize_dvd {m s n : Nat} (hn : orbitSize m s ∣ n) :
    n • (s : ZMod m) = 0 := by
  rcases hn with ⟨k, rfl⟩
  have hret : orbitSize m s • (s : ZMod m) = 0 := orbitSize_nsmul_step_returns m s
  -- `(orbitSize*k)•s = k•(orbitSize•s) = 0`.
  rw [mul_nsmul]
  simp [hret]

/-- Exact return criterion (positive moduli): `n • s = 0 ↔ orbitSize m s ∣ n`. -/
theorem nsmul_eq_zero_iff_orbitSize_dvd {m s n : Nat} (hm : 0 < m) :
    n • (s : ZMod m) = 0 ↔ orbitSize m s ∣ n := by
  constructor
  · intro hn
    exact orbitSize_dvd_of_nsmul_eq_zero (m := m) (s := s) (n := n) hm hn
  · intro hn
    exact nsmul_eq_zero_of_orbitSize_dvd (m := m) (s := s) (n := n) hn

/--
Two-axis **exact orbit size** (coprime moduli):

If `m₁ ⟂ m₂` and both are positive, then the orbit size of step `+s` in the product node
`ZMod (m₁*m₂)` is exactly the `lcm` of the per-axis orbit sizes.
-/
theorem orbitSize_mul_eq_lcm_orbitSize {m₁ m₂ s : Nat}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hcop : Nat.Coprime m₁ m₂) :
    orbitSize (m₁ * m₂) s = Nat.lcm (orbitSize m₁ s) (orbitSize m₂ s) := by
  -- Two naturals are equal iff they define the same "set of multiples".
  apply (Nat.dvd_right_iff_eq).1
  intro n
  have hm : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  -- Rewrite both sides using the "exact order" characterization.
  constructor
  · intro hn
    have hnsProd : n • (s : ZMod (m₁ * m₂)) = 0 :=
      nsmul_eq_zero_of_orbitSize_dvd (m := m₁ * m₂) (s := s) (n := n) hn
    have hdivProd : m₁ * m₂ ∣ n * s :=
      (nsmul_eq_zero_iff_modulus_dvd_mul (m₁ * m₂) s n).1 hnsProd
    have hdiv₁ : m₁ ∣ n * s := Nat.dvd_trans (Nat.dvd_mul_right m₁ m₂) hdivProd
    have hdiv₂ : m₂ ∣ n * s := Nat.dvd_trans (Nat.dvd_mul_left m₂ m₁) hdivProd
    have hns₁ : n • (s : ZMod m₁) = 0 :=
      (nsmul_eq_zero_iff_modulus_dvd_mul m₁ s n).2 hdiv₁
    have hns₂ : n • (s : ZMod m₂) = 0 :=
      (nsmul_eq_zero_iff_modulus_dvd_mul m₂ s n).2 hdiv₂
    have hd₁ : orbitSize m₁ s ∣ n :=
      (nsmul_eq_zero_iff_orbitSize_dvd (m := m₁) (s := s) (n := n) hm₁).1 hns₁
    have hd₂ : orbitSize m₂ s ∣ n :=
      (nsmul_eq_zero_iff_orbitSize_dvd (m := m₂) (s := s) (n := n) hm₂).1 hns₂
    exact (Nat.lcm_dvd_iff).2 ⟨hd₁, hd₂⟩
  · intro hn
    have hd : orbitSize m₁ s ∣ n ∧ orbitSize m₂ s ∣ n := (Nat.lcm_dvd_iff).1 hn
    have hns₁ : n • (s : ZMod m₁) = 0 :=
      nsmul_eq_zero_of_orbitSize_dvd (m := m₁) (s := s) (n := n) hd.1
    have hns₂ : n • (s : ZMod m₂) = 0 :=
      nsmul_eq_zero_of_orbitSize_dvd (m := m₂) (s := s) (n := n) hd.2
    have hdiv₁ : m₁ ∣ n * s :=
      (nsmul_eq_zero_iff_modulus_dvd_mul m₁ s n).1 hns₁
    have hdiv₂ : m₂ ∣ n * s :=
      (nsmul_eq_zero_iff_modulus_dvd_mul m₂ s n).1 hns₂
    have hdivProd : m₁ * m₂ ∣ n * s := hcop.mul_dvd_of_dvd_of_dvd hdiv₁ hdiv₂
    have hnsProd : n • (s : ZMod (m₁ * m₂)) = 0 :=
      (nsmul_eq_zero_iff_modulus_dvd_mul (m₁ * m₂) s n).2 hdivProd
    exact (nsmul_eq_zero_iff_orbitSize_dvd (m := m₁ * m₂) (s := s) (n := n) hm).1 hnsProd

/--
Two-axis concurrency (coprime moduli):

If `m₁` and `m₂` are coprime, then stepping by `+s` closes simultaneously on both axes after
`lcm(orbitSize m₁ s, orbitSize m₂ s)` steps, hence it also closes in `ZMod (m₁*m₂)`.
-/
theorem lcm_orbitSize_two_axes_returns (m₁ m₂ s : Nat) (hcop : Nat.Coprime m₁ m₂) :
    Nat.lcm (orbitSize m₁ s) (orbitSize m₂ s) • (s : ZMod (m₁ * m₂)) = 0 := by
  set k : Nat := Nat.lcm (orbitSize m₁ s) (orbitSize m₂ s)
  -- Show `m₁*m₂ ∣ k*s` by combining the two axis divisibility facts.
  have hm₁ : m₁ ∣ k * s := by
    have h₁ : m₁ ∣ orbitSize m₁ s * s := orbitSize_mul_step_dvd m₁ s
    have hk : orbitSize m₁ s ∣ k := by
      simpa [k] using (Nat.dvd_lcm_left (orbitSize m₁ s) (orbitSize m₂ s))
    exact Nat.dvd_trans h₁ (Nat.mul_dvd_mul_right hk s)
  have hm₂ : m₂ ∣ k * s := by
    have h₂ : m₂ ∣ orbitSize m₂ s * s := orbitSize_mul_step_dvd m₂ s
    have hk : orbitSize m₂ s ∣ k := by
      simpa [k] using (Nat.dvd_lcm_right (orbitSize m₁ s) (orbitSize m₂ s))
    exact Nat.dvd_trans h₂ (Nat.mul_dvd_mul_right hk s)
  have hprod : m₁ * m₂ ∣ k * s := hcop.mul_dvd_of_dvd_of_dvd hm₁ hm₂
  -- Convert divisibility back to a `ZMod` equality via `natCast_zmod_eq_zero_iff_dvd`.
  simp [k, nsmul_eq_mul]
  -- Goal is `(↑k : ZMod (m₁*m₂)) * ↑s = 0`; rewrite as `↑(k*s) = 0` and apply divisibility.
  have : ((k * s : Nat) : ZMod (m₁ * m₂)) = 0 :=
    (ZMod.natCast_eq_zero_iff (k * s) (m₁ * m₂)).2 hprod
  -- Rewrite the goal into the `natCast` form.
  simpa [Nat.cast_mul] using this

end CycleStepOrbit
