import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/-!
# Utilities: Distinct Primes imply Pairwise Coprime

This file bridges the user-facing statement "a list of distinct primes" to the
mechanism-facing hypothesis `List.Pairwise Nat.Coprime`.

No placeholders.
-/

namespace Nat

/-- Distinct primes are coprime. -/
theorem coprime_of_prime_prime_ne {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p ≠ q) :
    Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).2 h

end Nat

namespace List

/--
If every element of a list is prime and the list is `Nodup`, then the list is pairwise coprime.

This is the standard "distinct primes are pairwise coprime" reduction, packaged in list form.
-/
theorem pairwise_coprime_of_prime_nodup {ps : List Nat}
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hnodup : ps.Nodup) : ps.Pairwise Nat.Coprime := by
  induction ps with
  | nil =>
      simp
  | cons a tl ih =>
      have hnodup' := (List.nodup_cons.1 hnodup)
      have ha_not_mem : a ∉ tl := hnodup'.1
      have hnodup_tl : tl.Nodup := hnodup'.2

      have hprime_a : Nat.Prime a := hprime a (by simp)
      have hprime_tl : ∀ p ∈ tl, Nat.Prime p := by
        intro p hp
        exact hprime p (by simp [hp])

      -- Use the `pairwise_cons` characterization.
      apply pairwise_cons.2
      refine ⟨?_, ih hprime_tl hnodup_tl⟩
      intro b hb
      have hprime_b : Nat.Prime b := hprime_tl b hb
      have hab : a ≠ b := by
        intro hEq
        subst hEq
        exact ha_not_mem hb
      exact Nat.coprime_of_prime_prime_ne hprime_a hprime_b hab

end List

