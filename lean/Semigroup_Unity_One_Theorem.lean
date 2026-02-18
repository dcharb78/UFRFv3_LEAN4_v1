import Semigroup_Standard_Semantics_Theorem

/-!
# Semigroup Unity: If `1` Is a Generator, Everything Is Reachable

In the repo's **additive semigroup** lens (`semigroupPred`), reachability is defined by
nonnegative linear combinations of a generator list.

If the generator list contains `1`, then the semigroup closure is trivial:
every `n : Nat` is reachable (take `n = n * 1`).

This file formalizes that fact. It explains why the UFRF semigroup/gap theorems do **not**
use `1` as a generator: including it collapses the emergence structure (no gaps exist).

No placeholders; proof uses the standard `AddSubmonoid.closure` semantics.
-/

namespace GapSetPrime

open scoped BigOperators

/--
If `1` is in the generator list, then every `n` is semigroup-reachable.

This captures the “unity generates everything” statement in the **additive** semigroup lens.
-/
theorem semigroupPred_of_one_mem {gens : List Nat} (h1 : (1 : Nat) ∈ gens) (n : Nat) :
    semigroupPred gens n := by
  -- Use the standard semantics for `semigroupPred`.
  have h1' : (1 : Nat) ∈ AddSubmonoid.closure (genSet gens) := by
    refine AddSubmonoid.subset_closure ?_
    -- `genSet` membership is definitionally list membership.
    change (1 : Nat) ∈ gens
    exact h1
  have hn : n ∈ AddSubmonoid.closure (genSet gens) := by
    -- `n` is `n`-fold addition of `1`, i.e. `n * 1`.
    have : n * (1 : Nat) ∈ AddSubmonoid.closure (genSet gens) := by
      simpa [Nat.nsmul_eq_mul] using
        (AddSubmonoid.nsmul_mem (AddSubmonoid.closure (genSet gens)) h1' n)
    simpa using this
  exact (semigroupPred_iff_mem_closure gens n).2 hn

/-- A convenient corollary: `1 :: gens` reaches every `n`. -/
theorem semigroupPred_cons_one (gens : List Nat) (n : Nat) : semigroupPred (1 :: gens) n := by
  exact semigroupPred_of_one_mem (gens := 1 :: gens) (by simp) n

end GapSetPrime

