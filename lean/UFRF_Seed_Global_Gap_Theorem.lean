import UFRF_Minimal_Semigroup_Seed_Theorem
import UFRF_Global_Gap_Theorem

/-!
# UFRF Seed Global Gap Theorem (Triad [3,5,7])

We already proved:

* global UFRF coverage for `ufrfGenerators = [3,5,7,11,13]`
  (`UFRF_Global_Gap_Theorem.lean`), and
* semigroup-closure redundancy: `[3,5,7]` generates the same additive closure as
  `[3,5,7,11,13]` (`UFRF_Minimal_Semigroup_Seed_Theorem.lean`).

This file composes them into the clean "triad seed" statement:

* For the seed list `ufrfSeedGenerators = [3,5,7]`, every `n ≥ 5` is reachable.
* The **positive** gap set is exactly `{1,2,4}`.

No placeholders; these are logical consequences of previously-validated theorems.
-/

namespace GapSetPrime

/--
Seed coverage: for `[3,5,7]`, every `n ≥ 5` is semigroup-reachable.
-/
theorem seed_semigroupPred_ge_5 : ∀ n : Nat, 5 ≤ n → semigroupPred ufrfSeedGenerators n := by
  intro n hn
  -- Use the already-proved UFRF coverage + the seed equivalence.
  have hufrf : semigroupPred ufrfGenerators n := ufrf_semigroupPred_ge_5 n hn
  exact (semigroupPred_ufrf_iff_seed n).1 hufrf

/--
Seed global gap set: the only positive gaps for `[3,5,7]` are `{1,2,4}`.
-/
theorem seed_positive_gaps_eq :
    {n : Nat | 0 < n ∧ ¬ semigroupPred ufrfSeedGenerators n} = ({1, 2, 4} : Set Nat) := by
  -- Start from the global UFRF gap characterization and transport via `ufrf ↔ seed`.
  ext n
  have hgapU :
      (0 < n ∧ ¬ semigroupPred ufrfGenerators n) ↔ n ∈ ({1, 2, 4} : Set Nat) := by
    -- Convert set equality into pointwise membership.
    have := congrArg (fun s => n ∈ s) ufrf_positive_gaps_eq
    simpa [Set.mem_setOf_eq] using this
  have hiff : semigroupPred ufrfGenerators n ↔ semigroupPred ufrfSeedGenerators n :=
    semigroupPred_ufrf_iff_seed n
  constructor
  · rintro ⟨hnpos, hnnotSeed⟩
    have hnnotU : ¬ semigroupPred ufrfGenerators n := by
      intro hnU
      exact hnnotSeed ((hiff).1 hnU)
    exact (hgapU).1 ⟨hnpos, hnnotU⟩
  · intro hnmem
    have hU : 0 < n ∧ ¬ semigroupPred ufrfGenerators n := (hgapU).2 hnmem
    refine ⟨hU.1, ?_⟩
    intro hnSeed
    exact hU.2 ((hiff).2 hnSeed)

end GapSetPrime

