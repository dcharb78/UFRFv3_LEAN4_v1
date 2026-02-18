import Tn_Singleton_ClosedForm

namespace TnExact

/-!
# Two-Generator Closed Form (From Concurrency + Singleton Law)

This file is a small "concurrency instantiation" lemma:

* `TnFromMS_add` says multiset union composes by binomial convolution.
* `TnFromMS_singleton` gives `Tₙ({d}) = dⁿ/(n+1)`.

Combining them yields an explicit formula for `{a,b}`.
-/

noncomputable section

open scoped BigOperators

open Finset (antidiagonal)

theorem TnFromMS_pair_singletons (a b n : Nat) :
    TnFromMS ({a} + {b} : Multiset Nat) n =
      ∑ x ∈ antidiagonal n,
        (Nat.choose n x.1 : ℚ) *
          ((a ^ x.1 : ℚ) / (x.1 + 1 : ℚ)) *
          ((b ^ x.2 : ℚ) / (x.2 + 1 : ℚ)) := by
  -- Start from exact concurrency, then rewrite each singleton with the closed form.
  simpa [TnFromMS_singleton, mul_assoc, mul_left_comm, mul_comm] using
    (TnFromMS_add (s := ({a} : Multiset Nat)) (t := ({b} : Multiset Nat)) (n := n))

end

end TnExact

