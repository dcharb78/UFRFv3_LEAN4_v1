import Tn_Truncated_Engine

namespace TnExact

/-!
# Exact `Tₙ` Definition (All `n`) + Scale Invariance

The low-order file `Tn_Recurrence_Universality_Theorem.lean` defines `TnFromGen`
only for `n ≤ 4` (and returns `0` for larger `n`) because it is specialized to a
degree-`4` truncation.

This module defines the *exact* `Tₙ` for **all** `n` using the generalized truncated
engine `Tn_Truncated_Engine.lean`:

* Let `A(t) = ∏ (exp(d*t) - 1) / (d*t)`.
* The coefficient of `tⁿ` depends only on truncation degree `N = n`.
* Define `Tₙ = n! * [tⁿ]A(t)` by extracting that coefficient from `aCoeffs n`.

We also prove the fundamental **scale invariance** law:
scaling every generator by `k` scales `Tₙ` by `kⁿ`.

This file contains no placeholders.
-/

noncomputable section

open scoped BigOperators

open Polynomial
open Finset (antidiagonal mem_antidiagonal)
open TnTruncated

/-- Index for extracting the degree-`n` coefficient from `Fin (n+1)`. -/
def degIndex (n : Nat) : Fin (n + 1) :=
  ⟨n, Nat.lt_succ_self n⟩

@[simp] theorem degIndex_val (n : Nat) : (degIndex n : Nat) = n := rfl

/--
Exact `Tₙ` for a generator *list*.

Definition: `Tₙ = n! * [tⁿ] A(t)` where `A(t) = ∏ (exp(d*t)-1)/(d*t)`.
We compute `[tⁿ]A(t)` using truncation degree `N = n`, which is exact at degree `n`.
-/
def TnFromGen (gens : List Nat) (n : Nat) : ℚ :=
  (Nat.factorial n : ℚ) * (aCoeffs n gens) (degIndex n)

/--
Exact `Tₙ` for a generator *multiset* (order-free / concurrent form).
-/
def TnFromMS (s : Multiset Nat) (n : Nat) : ℚ :=
  (Nat.factorial n : ℚ) * (aCoeffsMS n s) (degIndex n)

theorem TnFromGen_scale (k : Nat) (gens : List Nat) (n : Nat) :
    TnFromGen (gens.map (fun d => k * d)) n = (k : ℚ) ^ n * TnFromGen gens n := by
  -- Use coefficient-level scaling from the truncated engine at `N = n`.
  have hcoeff :
      (aCoeffs n (gens.map (fun d => k * d))) (degIndex n) =
        (scaleCoeffs n k (aCoeffs n gens)) (degIndex n) := by
    simpa using congrArg (fun c => c (degIndex n)) (aCoeffs_scale n k gens)
  -- Rewrite with the coefficient identity, then unfold `scaleCoeffs` at degree `n`.
  unfold TnFromGen
  rw [hcoeff]
  simp [scaleCoeffs, degIndex, mul_left_comm]

theorem TnFromMS_scale (k : Nat) (s : Multiset Nat) (n : Nat) :
    TnFromMS (s.map (fun d => k * d)) n = (k : ℚ) ^ n * TnFromMS s n := by
  have hcoeff :
      (aCoeffsMS n (s.map (fun d => k * d))) (degIndex n) =
        (scaleCoeffs n k (aCoeffsMS n s)) (degIndex n) := by
    simpa using congrArg (fun c => c (degIndex n)) (aCoeffsMS_scale n k s)
  unfold TnFromMS
  rw [hcoeff]
  simp [scaleCoeffs, degIndex, mul_left_comm]

/-- Embed a degree `m` (with `m ≤ N`) as an index in `Fin (N+1)`. -/
def idxOfLe (N m : Nat) (h : m ≤ N) : Fin (N + 1) :=
  ⟨m, Nat.lt_succ_of_le h⟩

/--
`Tₙ` computed from truncation degree `N`.

When `n ≤ N`, this is the exact factorial-weighted coefficient:
`n! * [tⁿ] A(t)` computed from `aCoeffsMS N`.
When `n > N`, it is defined as `0`.
-/
def TnTrunc (N : Nat) (s : Multiset Nat) (n : Nat) : ℚ :=
  if h : n ≤ N then
    (Nat.factorial n : ℚ) * (aCoeffsMS N s) (idxOfLe N n h)
  else 0

theorem TnTrunc_add (N : Nat) (s t : Multiset Nat) (n : Nat) (hn : n ≤ N) :
    TnTrunc N (s + t) n =
      ∑ x ∈ antidiagonal n,
        (Nat.choose n x.1 : ℚ) * TnTrunc N s x.1 * TnTrunc N t x.2 := by
  have hn' : n ≤ N := hn
  have hadd :
      aCoeffsMS N (s + t) (idxOfLe N n hn') =
        mulCoeffs N (aCoeffsMS N s) (aCoeffsMS N t) (idxOfLe N n hn') := by
    simpa using congrArg (fun c => c (idxOfLe N n hn')) (aCoeffsMS_add N s t)

  -- Expand the LHS to a polynomial coefficient.
  simp [TnTrunc, hn']
  rw [hadd]
  simp [mulCoeffs, ofPoly, idxOfLe]

  -- Expand the coefficient of the product polynomial.
  simp [Polynomial.coeff_mul]

  -- Push `n!` inside the sum (via `Finset.mul_sum` on the underlying `Finset.sum`).
  have hmul :
      (↑n.factorial : ℚ) *
          (∑ x ∈ antidiagonal n,
              (toPoly N (aCoeffsMS N s)).coeff x.1 * (toPoly N (aCoeffsMS N t)).coeff x.2) =
        ∑ x ∈ antidiagonal n,
          (↑n.factorial : ℚ) *
              ((toPoly N (aCoeffsMS N s)).coeff x.1 * (toPoly N (aCoeffsMS N t)).coeff x.2) := by
    simpa using
      (Finset.mul_sum (antidiagonal n)
        (fun x : Nat × Nat =>
          (toPoly N (aCoeffsMS N s)).coeff x.1 * (toPoly N (aCoeffsMS N t)).coeff x.2)
        (↑n.factorial : ℚ))
  rw [hmul]

  -- Prove summand-wise equality.
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxsum : x.1 + x.2 = n := mem_antidiagonal.mp hx
  have hx1_le_n : x.1 ≤ n := Finset.antidiagonal.fst_le hx
  have hx2_le_n : x.2 ≤ n := Finset.antidiagonal.snd_le hx
  have hx1_le_N : x.1 ≤ N := hx1_le_n.trans hn'
  have hx2_le_N : x.2 ≤ N := hx2_le_n.trans hn'

  have hA : (toPoly N (aCoeffsMS N s)).coeff x.1 = (aCoeffsMS N s) (idxOfLe N x.1 hx1_le_N) := by
    simpa [idxOfLe] using (coeff_toPoly_of_le N (aCoeffsMS N s) hx1_le_N)
  have hB : (toPoly N (aCoeffsMS N t)).coeff x.2 = (aCoeffsMS N t) (idxOfLe N x.2 hx2_le_N) := by
    simpa [idxOfLe] using (coeff_toPoly_of_le N (aCoeffsMS N t) hx2_le_N)

  have hsub : n - x.1 = x.2 := by
    calc
      n - x.1 = (x.1 + x.2) - x.1 := by simp [hxsum]
      _ = x.2 := Nat.add_sub_cancel_left x.1 x.2

  have hfact :
      (Nat.choose n x.1 : ℚ) * (Nat.factorial x.1 : ℚ) * (Nat.factorial x.2 : ℚ) =
        (Nat.factorial n : ℚ) := by
    have :
        (Nat.choose n x.1 : ℚ) * (Nat.factorial x.1 : ℚ) * (Nat.factorial (n - x.1) : ℚ) =
          (Nat.factorial n : ℚ) := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hx1_le_n)
    simpa [hsub] using this

  -- Finish: rewrite coefficients and simplify the `TnTrunc` branches (the `if` conditions are true).
  simp [hA, hB]
  rw [hfact.symm]
  simp [hx1_le_N, hx2_le_N, idxOfLe, mul_assoc, mul_left_comm]

end
