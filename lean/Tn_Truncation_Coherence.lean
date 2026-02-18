import Tn_Exact_Definition

namespace TnTruncated

/-!
# Truncation Coherence (Degree Stability)

This module connects truncation levels:

* Restricting degree-`(N+1)` coefficient data down to degree `N`.
* Showing this restriction commutes with `mulCoeffs`.
* Showing `aCoeffs` / `aCoeffsMS` are coherent under this restriction.

These lemmas let us upgrade the `TnExact.TnTrunc_add` convolution law into a
clean exact statement about `TnExact.TnFromMS`.
-/

noncomputable section

open scoped BigOperators

open Polynomial

/-- Restrict degree-`(N+1)` coefficient data to degree `N` by dropping the top slot. -/
def restrictCoeffs (N : Nat) (c : Coeffs (N + 1)) : Coeffs N :=
  fun i => c i.castSucc

@[simp] theorem restrictCoeffs_apply (N : Nat) (c : Coeffs (N + 1)) (i : Fin (N + 1)) :
    restrictCoeffs N c i = c i.castSucc := rfl

theorem restrictCoeffs_ofPoly (N : Nat) (p : Polynomial ℚ) :
    restrictCoeffs N (ofPoly (N + 1) p) = ofPoly N p := by
  funext i
  simp [restrictCoeffs, ofPoly]

theorem ofPoly_toPoly_succ (N : Nat) (c : Coeffs (N + 1)) :
    ofPoly N (toPoly (N + 1) c) = restrictCoeffs N c := by
  funext i
  have hiN : (i : Nat) ≤ N := Nat.le_of_lt_succ i.isLt
  have hi : (i : Nat) ≤ N + 1 := Nat.le_trans hiN (Nat.le_succ N)
  have hcoeff := (coeff_toPoly_of_le (N + 1) c (m := (i : Nat)) hi)
  have hidx : (⟨(i : Nat), Nat.lt_succ_of_le hi⟩ : Fin (N + 2)) = i.castSucc := by
    apply Fin.ext
    rfl
  simpa [ofPoly, restrictCoeffs, hidx] using hcoeff

theorem truncPoly_toPoly_succ (N : Nat) (c : Coeffs (N + 1)) :
    truncPoly N (toPoly (N + 1) c) = toPoly N (restrictCoeffs N c) := by
  -- `truncPoly` is defined via `ofPoly`, and `ofPoly` of the larger `toPoly` is exactly restriction.
  unfold truncPoly
  simpa using congrArg (toPoly N) (ofPoly_toPoly_succ N c)

theorem restrictCoeffs_mulCoeffs (N : Nat) (a b : Coeffs (N + 1)) :
    restrictCoeffs N (mulCoeffs (N + 1) a b) =
      mulCoeffs N (restrictCoeffs N a) (restrictCoeffs N b) := by
  -- Both sides are equal to `ofPoly N (toPoly (N+1) a * toPoly (N+1) b)`.
  have hL :
      restrictCoeffs N (mulCoeffs (N + 1) a b) =
        ofPoly N (toPoly (N + 1) a * toPoly (N + 1) b) := by
    calc
      restrictCoeffs N (mulCoeffs (N + 1) a b)
          = restrictCoeffs N (ofPoly (N + 1) (toPoly (N + 1) a * toPoly (N + 1) b)) := by
              rfl
      _ = ofPoly N (toPoly (N + 1) a * toPoly (N + 1) b) := by
            simpa using restrictCoeffs_ofPoly N (toPoly (N + 1) a * toPoly (N + 1) b)

  have hR :
      mulCoeffs N (restrictCoeffs N a) (restrictCoeffs N b) =
        ofPoly N (toPoly (N + 1) a * toPoly (N + 1) b) := by
    calc
      mulCoeffs N (restrictCoeffs N a) (restrictCoeffs N b)
          = ofPoly N (toPoly N (restrictCoeffs N a) * toPoly N (restrictCoeffs N b)) := by
              rfl
      _ = ofPoly N ((truncPoly N (toPoly (N + 1) a)) * (truncPoly N (toPoly (N + 1) b))) := by
            -- Rewrite each `toPoly N (restrictCoeffs ...)` as a truncation of the `N+1` polynomial.
            simp [truncPoly_toPoly_succ]
      _ = ofPoly N ((toPoly (N + 1) a) * (toPoly (N + 1) b)) := by
            -- Truncations do not affect coefficients in degrees `≤ N`.
            calc
              ofPoly N ((truncPoly N (toPoly (N + 1) a)) * (truncPoly N (toPoly (N + 1) b)))
                  = ofPoly N ((toPoly (N + 1) a) * (truncPoly N (toPoly (N + 1) b))) := by
                      simpa using
                        (ofPoly_mul_left_trunc N (toPoly (N + 1) a) (truncPoly N (toPoly (N + 1) b)))
              _ = ofPoly N ((toPoly (N + 1) a) * (toPoly (N + 1) b)) := by
                      simpa using (ofPoly_mul_right_trunc N (toPoly (N + 1) a) (toPoly (N + 1) b))
      _ = ofPoly N (toPoly (N + 1) a * toPoly (N + 1) b) := by
            rfl

  calc
    restrictCoeffs N (mulCoeffs (N + 1) a b)
        = ofPoly N (toPoly (N + 1) a * toPoly (N + 1) b) := hL
    _ = mulCoeffs N (restrictCoeffs N a) (restrictCoeffs N b) := by
          symm
          exact hR

theorem restrictCoeffs_coeffsOne (N : Nat) :
    restrictCoeffs N (coeffsOne (N + 1)) = coeffsOne N := by
  funext i
  simp [restrictCoeffs, coeffsOne]

theorem restrictCoeffs_factorCoeffs (N d : Nat) :
    restrictCoeffs N (factorCoeffs (N + 1) d) = factorCoeffs N d := by
  funext i
  simp [restrictCoeffs, factorCoeffs, factorCoeff]

theorem restrictCoeffs_aCoeffs (N : Nat) (gens : List Nat) :
    restrictCoeffs N (aCoeffs (N + 1) gens) = aCoeffs N gens := by
  induction gens with
  | nil =>
      simpa [aCoeffs] using restrictCoeffs_coeffsOne N
  | cons d ds ih =>
      simp [aCoeffs, ih, restrictCoeffs_mulCoeffs, restrictCoeffs_factorCoeffs]

theorem restrictCoeffs_aCoeffsMS (N : Nat) (s : Multiset Nat) :
    restrictCoeffs N (aCoeffsMS (N + 1) s) = aCoeffsMS N s := by
  refine Quotient.inductionOn s (fun xs => ?_)
  simpa using (restrictCoeffs_aCoeffs N xs)

end

end TnTruncated

namespace TnExact

/-!
## Exact Concurrency (No Truncation Parameter)

Using truncation coherence, we can:

1. Show `TnTrunc N` agrees with the exact `TnFromMS` for all degrees `≤ N`.
2. Specialize `TnTrunc_add` at `N = n` and rewrite every term into `TnFromMS`.
-/

noncomputable section

open scoped BigOperators

open Finset (antidiagonal)

open TnTruncated

theorem aCoeffsMS_degree_stable (m N : Nat) (s : Multiset Nat) (hm : m ≤ N) :
    (aCoeffsMS N s) (idxOfLe N m hm) = (aCoeffsMS m s) (degIndex m) := by
  -- Induct `N` upward from `m`, using `restrictCoeffs_aCoeffsMS` to relate `N+1` to `N`.
  refine Nat.le_induction (m := m)
    (P := fun n hmn => (aCoeffsMS n s) (idxOfLe n m hmn) = (aCoeffsMS m s) (degIndex m))
    ?base ?succ N hm
  · -- Base case: `n = m`.
    rfl
  · intro n hmn ih
    have hmn_succ : m ≤ n + 1 := Nat.le_trans hmn (Nat.le_succ n)
    have hrestrict :
        (aCoeffsMS n s) (idxOfLe n m hmn) =
          (aCoeffsMS (n + 1) s) ((idxOfLe n m hmn).castSucc) := by
      have := congrArg (fun c => c (idxOfLe n m hmn)) (TnTruncated.restrictCoeffs_aCoeffsMS n s)
      -- `restrictCoeffs` is `castSucc` on indices.
      simpa [TnTruncated.restrictCoeffs] using this.symm
    have hidx :
        ((idxOfLe n m hmn).castSucc : Fin (n + 2)) = idxOfLe (n + 1) m hmn_succ := by
      apply Fin.ext
      rfl
    -- Combine the restriction step with the induction hypothesis.
    calc
      (aCoeffsMS (n + 1) s) (idxOfLe (n + 1) m hmn_succ)
          = (aCoeffsMS (n + 1) s) ((idxOfLe n m hmn).castSucc) := by
              simp [hidx]
      _ = (aCoeffsMS n s) (idxOfLe n m hmn) := by
              simpa using hrestrict.symm
      _ = (aCoeffsMS m s) (degIndex m) := ih

theorem TnTrunc_eq_TnFromMS (N : Nat) (s : Multiset Nat) (n : Nat) (hn : n ≤ N) :
    TnTrunc N s n = TnFromMS s n := by
  unfold TnTrunc TnFromMS
  simp [hn, aCoeffsMS_degree_stable n N s hn]

theorem TnFromMS_add (s t : Multiset Nat) (n : Nat) :
    TnFromMS (s + t) n =
      ∑ x ∈ antidiagonal n,
        (Nat.choose n x.1 : ℚ) * TnFromMS s x.1 * TnFromMS t x.2 := by
  -- Start from the truncated convolution at `N = n`, then rewrite each `TnTrunc` term to `TnFromMS`.
  have htrunc :=
    (TnTrunc_add (N := n) (s := s) (t := t) (n := n) (hn := (Nat.le_refl n)))
  -- Convert the outer `TnTrunc` to the exact `TnFromMS`.
  have houter : TnFromMS (s + t) n = TnTrunc n (s + t) n := by
    symm
    exact TnTrunc_eq_TnFromMS n (s + t) n (Nat.le_refl n)
  -- Rewrite each summand using degree stability (`x.1 ≤ n`, `x.2 ≤ n`).
  calc
    TnFromMS (s + t) n
        = TnTrunc n (s + t) n := houter
    _ = ∑ x ∈ antidiagonal n,
          (Nat.choose n x.1 : ℚ) * TnTrunc n s x.1 * TnTrunc n t x.2 := htrunc
    _ = ∑ x ∈ antidiagonal n,
          (Nat.choose n x.1 : ℚ) * TnFromMS s x.1 * TnFromMS t x.2 := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hx1 : x.1 ≤ n := Finset.antidiagonal.fst_le hx
          have hx2 : x.2 ≤ n := Finset.antidiagonal.snd_le hx
          -- Rewrite the two `TnTrunc` factors.
          rw [TnTrunc_eq_TnFromMS n s x.1 hx1]
          rw [TnTrunc_eq_TnFromMS n t x.2 hx2]

end

end TnExact
