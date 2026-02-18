import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Pairwise

/-!
# Utilities: Coprimality for Prime Powers

This file is intentionally small: it contains reusable lemmas that let us
reduce "pairwise coprime prime powers" hypotheses to "pairwise coprime bases".

No placeholders.
-/

namespace Nat

/-- If `a` and `b` are coprime, then any powers `a^m` and `b^n` are coprime. -/
theorem Coprime.pow_pow {a b m n : Nat} (h : Nat.Coprime a b) : Nat.Coprime (a ^ m) (b ^ n) := by
  -- `pow_left`/`pow_right` are standard Nat.Coprime transport lemmas.
  exact (h.pow_left m).pow_right n

end Nat

namespace List

/--
If a list is pairwise coprime, then raising every element to the same power
preserves pairwise coprimality.
-/
theorem Pairwise.coprime_pow {ps : List Nat} (h : ps.Pairwise Nat.Coprime) (e : Nat) :
    (ps.map (fun p => p ^ e)).Pairwise Nat.Coprime := by
  induction ps with
  | nil =>
      simp
  | cons a tl ih =>
      have ha : ∀ b ∈ tl, Nat.Coprime a b := (pairwise_cons.1 h).1
      have htl : tl.Pairwise Nat.Coprime := (pairwise_cons.1 h).2
      apply pairwise_cons.2
      refine ⟨?_, ih htl⟩
      intro b hb
      rcases mem_map.1 hb with ⟨b0, hb0, rfl⟩
      exact (ha b0 hb0).pow_pow (m := e) (n := e)

end List

