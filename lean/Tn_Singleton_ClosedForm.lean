import Tn_Truncation_Coherence

namespace TnExact

/-!
# Closed Form for a Single Generator

For a single generator `d`, the generating factor is:

`(exp(d*t) - 1) / (d*t) = Σ_{n>=0} d^n * t^n / (n+1)!`.

Our exact definition `TnFromMS` is `n! * [t^n]A(t)`, so for a singleton multiset
we should have:

`Tₙ({d}) = d^n / (n+1)`.

This lemma makes that connection explicit in Lean, without introducing any axioms.
-/

noncomputable section

open TnTruncated

theorem TnFromMS_singleton (d n : Nat) :
    TnFromMS ({d} : Multiset Nat) n = (d ^ n : ℚ) / (n + 1 : ℚ) := by
  -- Reduce to the one-factor coefficient.
  unfold TnFromMS
  -- Replace the multiset singleton by its list representative (definitional).
  change (Nat.factorial n : ℚ) * (aCoeffs n [d]) (degIndex n) = (d ^ n : ℚ) / (n + 1 : ℚ)
  -- Unfold the one-element list product (`aCoeffs`) and evaluate the degree-`n` slot.
  simp [TnTruncated.aCoeffs, TnTruncated.mulCoeffs_one_left, TnTruncated.factorCoeffs,
    TnTruncated.factorCoeff, degIndex]
  -- Finish the factorial cancellation.
  have hn0 : (Nat.factorial n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  field_simp [Nat.factorial_succ, hn0]
  simp [Nat.factorial_succ, mul_assoc, mul_comm]

end
