import UFRF_Seed_Global_Gap_Theorem

/-!
# Seed Inevitability From Gap Signature `{1,2,4}`

This file reduces remaining arbitrariness in the UFRF semigroup lens.

If a semigroup (presented via `semigroupPred gens`) has **positive gaps** exactly `{1,2,4}`,
then its reachability predicate is uniquely determined:

`{0,3} ∪ {n | 5 ≤ n}`.

Since the UFRF seed list `ufrfSeedGenerators = [3,5,7]` has this signature, any generator list
with the same signature generates the same semigroup (as a predicate on `ℕ`).

We also prove a minimality statement in the list sense: each of `3,5,7` is necessary (removing it
prevents reaching that value).

No placeholders; proofs are discrete case splits + arithmetic.
-/

namespace GapSetPrime

/-! ## Canonical semigroup determined by gaps `{1,2,4}` -/

private def canonical357 (n : ℕ) : Prop :=
  n = 0 ∨ n = 3 ∨ 5 ≤ n

private lemma not_mem_124_of_ge5 {n : ℕ} (hn : 5 ≤ n) : n ∉ ({1, 2, 4} : Set ℕ) := by
  have hn1 : n ≠ 1 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 5) hn)
  have hn2 : n ≠ 2 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 5) hn)
  have hn4 : n ≠ 4 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 5) hn)
  simp [Set.mem_insert_iff, Set.mem_singleton_iff, hn1, hn2, hn4]

private lemma not_mem_124_of_eq3 : (3 : ℕ) ∉ ({1, 2, 4} : Set ℕ) := by
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]

private lemma semigroupPred_of_not_mem_positiveGaps {gens : List ℕ} {n : ℕ}
    (hGaps : {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n} = ({1, 2, 4} : Set ℕ))
    (hnpos : 0 < n) (hnnot : n ∉ ({1, 2, 4} : Set ℕ)) :
    semigroupPred gens n := by
  by_contra hnot
  have hmemLeft : n ∈ {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n} := ⟨hnpos, hnot⟩
  have hEq : (n ∈ {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n}) = (n ∈ ({1, 2, 4} : Set ℕ)) :=
    congrArg (fun s : Set ℕ => n ∈ s) hGaps
  have hmemRight : n ∈ ({1, 2, 4} : Set ℕ) := Eq.mp hEq hmemLeft
  exact hnnot hmemRight

/--
If the positive gap set of `gens` is exactly `{1,2,4}`, then `semigroupPred gens` is *forced* to be
the canonical predicate `{0,3} ∪ {n | 5 ≤ n}`.
-/
theorem semigroupPred_iff_canonical357_of_positiveGaps_eq (gens : List ℕ)
    (hGaps : {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n} = ({1, 2, 4} : Set ℕ)) (n : ℕ) :
    semigroupPred gens n ↔ canonical357 n := by
  constructor
  · intro hn
    by_cases hn0 : n = 0
    · exact Or.inl hn0
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    -- If `n ∈ {1,2,4}`, then `n` is a positive gap and hence not reachable (contradiction).
    have hnnot124 : n ∉ ({1, 2, 4} : Set ℕ) := by
      intro hmem
      have hEq : (n ∈ {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n}) = (n ∈ ({1, 2, 4} : Set ℕ)) :=
        congrArg (fun s : Set ℕ => n ∈ s) hGaps
      have hmemLeft : n ∈ {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n} := Eq.mpr hEq hmem
      exact hmemLeft.2 hn
    -- If `n ≥ 5` we're done; otherwise `n < 5` and the only remaining option is `n = 3`.
    by_cases hn5 : 5 ≤ n
    · exact Or.inr (Or.inr hn5)
    have hlt : n < 5 := lt_of_not_ge hn5
    have hn1 : n ≠ 1 := by
      intro h; apply hnnot124; subst h; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hn2 : n ≠ 2 := by
      intro h; apply hnnot124; subst h; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hn4 : n ≠ 4 := by
      intro h; apply hnnot124; subst h; simp [Set.mem_insert_iff, Set.mem_singleton_iff]
    -- Finite Nat case split: `n < 5` means `n ∈ {0,1,2,3,4}`.
    cases n with
    | zero =>
        cases hn0 rfl
    | succ n1 =>
        cases n1 with
        | zero =>
            cases hn1 rfl
        | succ n2 =>
            cases n2 with
            | zero =>
                cases hn2 rfl
            | succ n3 =>
                cases n3 with
                | zero =>
                    -- `n = 3`.
                    exact Or.inr (Or.inl rfl)
                | succ n4 =>
                    cases n4 with
                    | zero =>
                        cases hn4 rfl
                    | succ n5 =>
                        -- `n ≥ 5`, contradicting `n < 5`.
                        have hge5 :
                            5 ≤ Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n5)))) := by
                          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
                            (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n5)))))
                        exact False.elim ((not_lt_of_ge hge5) hlt)
  · intro hcanon
    rcases hcanon with rfl | rfl | hn5
    · exact semigroupPred_zero gens
    ·
      have hnpos : (0 : ℕ) < 3 := by decide
      have hnnot : (3 : ℕ) ∉ ({1, 2, 4} : Set ℕ) := not_mem_124_of_eq3
      exact semigroupPred_of_not_mem_positiveGaps (gens := gens) (n := 3) hGaps hnpos hnnot
    ·
      have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 5) hn5
      have hnnot : n ∉ ({1, 2, 4} : Set ℕ) := not_mem_124_of_ge5 hn5
      exact semigroupPred_of_not_mem_positiveGaps (gens := gens) (n := n) hGaps hnpos hnnot

/--
**Seed inevitability (semigroup lens):**

If a generator list `gens` has positive gaps exactly `{1,2,4}`, then it generates the same semigroup
predicate as the UFRF seed `[3,5,7]`.
-/
theorem semigroupPred_iff_seed_of_positiveGaps_eq (gens : List ℕ)
    (hGaps : {n : ℕ | 0 < n ∧ ¬ semigroupPred gens n} = ({1, 2, 4} : Set ℕ)) (n : ℕ) :
    semigroupPred gens n ↔ semigroupPred ufrfSeedGenerators n := by
  have hcanonG :
      semigroupPred gens n ↔ canonical357 n :=
    semigroupPred_iff_canonical357_of_positiveGaps_eq gens hGaps n
  have hcanonSeed :
      semigroupPred ufrfSeedGenerators n ↔ canonical357 n :=
    semigroupPred_iff_canonical357_of_positiveGaps_eq ufrfSeedGenerators seed_positive_gaps_eq n
  exact hcanonG.trans hcanonSeed.symm

/-! ## Minimality of the seed triad `[3,5,7]` (list sense) -/

/-- Removing `3` (leaving `[5,7]`) cannot reach `3`. -/
theorem semigroupPred_57_false_3 : ¬ semigroupPred ([5, 7] : List ℕ) 3 := by
  intro h
  have h' :
      ∃ k s,
        (∃ k₀ s₀, s₀ = 0 ∧ s = s₀ + k₀ * 5) ∧
          3 = s + k * 7 := by
    simpa [semigroupPred, List.foldl] using h
  rcases h' with ⟨k, s, hs, h3⟩
  rcases hs with ⟨k₀, s₀, hs₀, hs⟩
  subst hs₀
  have hs' : s = k₀ * 5 := by
    simpa [Nat.zero_add] using hs
  have hEq : k₀ * 5 + k * 7 = 3 := by
    simpa [hs', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h3.symm
  have hk7_le3 : k * 7 ≤ 3 := by
    have : k * 7 ≤ k₀ * 5 + k * 7 := Nat.le_add_left (k * 7) (k₀ * 5)
    simpa [hEq] using this
  cases k with
  | zero =>
      have hEq0 : k₀ * 5 = 3 := by
        simpa using hEq
      have hdiv : (5 : ℕ) ∣ 3 := by
        refine hEq0 ▸ ?_
        exact Nat.dvd_mul_left 5 k₀
      exact (by decide : ¬ (5 : ℕ) ∣ 3) hdiv
  | succ k1 =>
      have h7_le : 7 ≤ (Nat.succ k1) * 7 := by
        -- Rewrite `7` as `1*7` and use monotonicity of multiplication on the RHS.
        rw [← Nat.one_mul 7]
        exact Nat.mul_le_mul_right 7 (Nat.succ_le_succ (Nat.zero_le k1))
      have : (7 : ℕ) ≤ 3 := le_trans h7_le (by simpa using hk7_le3)
      exact (by decide : ¬ (7 : ℕ) ≤ 3) this

/-- Removing `5` (leaving `[3,7]`) cannot reach `5`. -/
theorem semigroupPred_37_false_5 : ¬ semigroupPred ([3, 7] : List ℕ) 5 := by
  intro h
  have h' :
      ∃ k s,
        (∃ k₀ s₀, s₀ = 0 ∧ s = s₀ + k₀ * 3) ∧
          5 = s + k * 7 := by
    simpa [semigroupPred, List.foldl] using h
  rcases h' with ⟨k, s, hs, h5⟩
  rcases hs with ⟨k₀, s₀, hs₀, hs⟩
  subst hs₀
  have hs' : s = k₀ * 3 := by
    simpa [Nat.zero_add] using hs
  have hEq : k₀ * 3 + k * 7 = 5 := by
    simpa [hs', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h5.symm
  have hk7_le5 : k * 7 ≤ 5 := by
    have : k * 7 ≤ k₀ * 3 + k * 7 := Nat.le_add_left (k * 7) (k₀ * 3)
    simpa [hEq] using this
  cases k with
  | zero =>
      have hEq0 : k₀ * 3 = 5 := by
        simpa using hEq
      have hdiv : (3 : ℕ) ∣ 5 := by
        refine hEq0 ▸ ?_
        exact Nat.dvd_mul_left 3 k₀
      exact (by decide : ¬ (3 : ℕ) ∣ 5) hdiv
  | succ k1 =>
      have h7_le : 7 ≤ (Nat.succ k1) * 7 := by
        rw [← Nat.one_mul 7]
        exact Nat.mul_le_mul_right 7 (Nat.succ_le_succ (Nat.zero_le k1))
      have : (7 : ℕ) ≤ 5 := le_trans h7_le (by simpa using hk7_le5)
      exact (by decide : ¬ (7 : ℕ) ≤ 5) this

/--
Minimality witness: each of the three seed generators is necessary (removing it prevents reaching it).
-/
theorem ufrfSeedGenerators_minimal :
    (¬ semigroupPred ([3, 5] : List ℕ) 7)
      ∧ (¬ semigroupPred ([3, 7] : List ℕ) 5)
      ∧ (¬ semigroupPred ([5, 7] : List ℕ) 3) := by
  refine ⟨semigroupPred_35_false_7, semigroupPred_37_false_5, semigroupPred_57_false_3⟩

end GapSetPrime
