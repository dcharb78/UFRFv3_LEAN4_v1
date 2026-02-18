import Semigroup_Standard_Semantics_Theorem

/-!
# UFRF Global Gap Theorem (Unbounded Coverage)

`GapSetPrime.gapSet` in `Gap_Set_Prime_Theorem.lean` computes **bounded** gaps via DP.
This file proves an **unbounded** structural fact about the UFRF generator semigroup:

*For the generator list* `ufrfGenerators = [3,5,7,11,13]`, *every* natural `n ≥ 5`
is reachable, i.e. lies in the numerical semigroup.

This is the emergent-closure upgrade: after finitely many base cases (`5,6,7`),
adding `3` closes all larger integers.

No placeholders; proof uses only arithmetic and the semigroup closure lemmas proved in
`Semigroup_Standard_Semantics_Theorem.lean`.
-/

namespace GapSetPrime

private theorem ufrf_semigroupPred_three : semigroupPred ufrfGenerators 3 := by
  -- `3 ∈ ufrfGenerators`.
  exact
    semigroupPred_of_mem_gens (gens := ufrfGenerators) (g := 3) (by simp [ufrfGenerators])

private theorem ufrf_semigroupPred_five : semigroupPred ufrfGenerators 5 := by
  -- `5 ∈ ufrfGenerators`.
  exact
    semigroupPred_of_mem_gens (gens := ufrfGenerators) (g := 5) (by simp [ufrfGenerators])

private theorem ufrf_semigroupPred_seven : semigroupPred ufrfGenerators 7 := by
  -- `7 ∈ ufrfGenerators`.
  exact
    semigroupPred_of_mem_gens (gens := ufrfGenerators) (g := 7) (by simp [ufrfGenerators])

private theorem ufrf_semigroupPred_six : semigroupPred ufrfGenerators 6 := by
  -- `6 = 3 + 3`.
  have h3 : semigroupPred ufrfGenerators 3 := ufrf_semigroupPred_three
  simpa using (semigroupPred_add ufrfGenerators h3 h3)

/--
Global (unbounded) coverage:

For the UFRF generators `[3,5,7,11,13]`, every `n ≥ 5` lies in the semigroup.

Proof sketch:
- Base window: `5,6,7` are reachable.
- Step: if `n ≥ 8`, then `n-3 ≥ 5`, so by induction `n-3` is reachable, hence so is `n = (n-3)+3`.
-/
theorem ufrf_semigroupPred_ge_5 : ∀ n : Nat, 5 ≤ n → semigroupPred ufrfGenerators n := by
  intro n hn
  -- Strong induction on `n` with predicate `5 ≤ n → semigroupPred ufrfGenerators n`.
  refine
    (Nat.strong_induction_on (p := fun n => 5 ≤ n → semigroupPred ufrfGenerators n) n ?_) hn
  intro n ih hn5
  by_cases hlt : n < 8
  · -- Small case: `5 ≤ n ≤ 7`, so `n = 5,6,7`.
    have hn_le7 : n ≤ 7 := by
      -- `n < 8` is `n < 7+1`, hence `n ≤ 7`.
      exact (Nat.lt_succ_iff.mp (by simpa using hlt))
    rcases Nat.exists_eq_add_of_le hn5 with ⟨t, rfl⟩
    -- Now show `t ≤ 2`, so `t = 0,1,2`.
    have ht_le2 : t ≤ 2 := by
      have : 5 + t ≤ 5 + 2 := by
        -- `5+2 = 7`.
        simpa using hn_le7
      exact Nat.le_of_add_le_add_left this
    -- Exhaust `t ∈ {0,1,2}`.
    cases t with
    | zero =>
        simpa using ufrf_semigroupPred_five
    | succ t1 =>
        cases t1 with
        | zero =>
            simpa using ufrf_semigroupPred_six
        | succ t2 =>
            cases t2 with
            | zero =>
                simpa using ufrf_semigroupPred_seven
            | succ t3 =>
                -- Contradiction: `t = 3 + t3` cannot satisfy `t ≤ 2`.
                have hle : Nat.succ (Nat.succ (Nat.succ t3)) ≤ 2 := ht_le2
                have hle1 : Nat.succ (Nat.succ t3) ≤ 1 := by
                  have : Nat.succ (Nat.succ (Nat.succ t3)) ≤ Nat.succ 1 := by
                    exact hle
                  exact Nat.succ_le_succ_iff.mp this
                have hle0 : Nat.succ t3 ≤ 0 := by
                  have : Nat.succ (Nat.succ t3) ≤ Nat.succ 0 := by
                    exact hle1
                  exact Nat.succ_le_succ_iff.mp this
                exact (Nat.not_succ_le_zero t3 hle0).elim
  · -- Large case: `n ≥ 8`, reduce to `n-3`.
    have hn8 : 8 ≤ n := Nat.le_of_not_lt hlt
    have h3 : semigroupPred ufrfGenerators 3 := ufrf_semigroupPred_three
    have hsub_ge5 : 5 ≤ n - 3 := by
      have : 8 - 3 ≤ n - 3 := Nat.sub_le_sub_right hn8 3
      simpa using this
    have hsub_lt : n - 3 < n := by
      have h3le : 3 ≤ n := le_trans (by decide : 3 ≤ 8) hn8
      exact Nat.sub_lt_self (a := 3) (b := n) (by decide) h3le
    have hpred : semigroupPred ufrfGenerators (n - 3) :=
      ih (n - 3) hsub_lt hsub_ge5
    have hadd : semigroupPred ufrfGenerators ((n - 3) + 3) :=
      semigroupPred_add ufrfGenerators hpred h3
    have h3le : 3 ≤ n := le_trans (by decide : 3 ≤ 8) hn8
    simpa [Nat.sub_add_cancel h3le] using hadd

-- ============================================================
-- Global gap set: only {1,2,4} are missing
-- ============================================================

private theorem ufrfGenerators_pos : ∀ g ∈ ufrfGenerators, 0 < g := by
  intro g hg
  simp [ufrfGenerators] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem ufrf_not_semigroupPred_of_table_false (n : Nat) (hn : n ≤ 10)
    (hget : (reachableTable ufrfGenerators 10).getD n false = false) : ¬ semigroupPred ufrfGenerators n := by
  intro hsem
  have hiff :=
    (reachableTable_getD_iff_semigroupPred (gens := ufrfGenerators) (upTo := 10) (n := n)
      hn ufrfGenerators_pos)
  have htrue : (reachableTable ufrfGenerators 10).getD n false = true := (hiff).2 hsem
  rw [hget] at htrue
  cases htrue

theorem ufrf_not_semigroupPred_one : ¬ semigroupPred ufrfGenerators 1 := by
  refine ufrf_not_semigroupPred_of_table_false 1 (by decide) ?_
  native_decide

theorem ufrf_not_semigroupPred_two : ¬ semigroupPred ufrfGenerators 2 := by
  refine ufrf_not_semigroupPred_of_table_false 2 (by decide) ?_
  native_decide

theorem ufrf_not_semigroupPred_four : ¬ semigroupPred ufrfGenerators 4 := by
  refine ufrf_not_semigroupPred_of_table_false 4 (by decide) ?_
  native_decide

/--
Global characterization of the **positive gaps** of the UFRF semigroup:

`n` is a positive gap iff `n ∈ {1,2,4}`.
-/
theorem ufrf_positive_gaps_eq :
    {n : Nat | 0 < n ∧ ¬ semigroupPred ufrfGenerators n} = ({1, 2, 4} : Set Nat) := by
  ext n
  constructor
  · rintro ⟨hnpos, hnnot⟩
    -- If `n ≥ 5` then it is reachable, contradiction. So `n ≤ 4`.
    have hnlt5 : n < 5 := by
      refine Nat.lt_of_not_ge ?_
      intro hnge
      exact hnnot (ufrf_semigroupPred_ge_5 n hnge)
    have hnle4 : n ≤ 4 := by
      exact (Nat.lt_succ_iff.mp (by simpa using hnlt5))
    -- Enumerate `n = 1,2,3,4`; exclude `3` because it is reachable.
    have hnne0 : n ≠ 0 := Nat.ne_of_gt hnpos
    rcases Nat.exists_eq_succ_of_ne_zero hnne0 with ⟨k, rfl⟩
    have hk_le3 : k ≤ 3 := by
      have : Nat.succ k ≤ Nat.succ 3 := by
        simpa using hnle4
      exact Nat.succ_le_succ_iff.mp this
    cases k with
    | zero =>
        -- n = 1
        simp
    | succ k1 =>
        cases k1 with
        | zero =>
            -- n = 2
            simp
        | succ k2 =>
            cases k2 with
            | zero =>
                -- n = 3 is reachable: contradiction.
                exfalso
                exact hnnot ufrf_semigroupPred_three
            | succ k3 =>
                cases k3 with
                | zero =>
                    -- n = 4
                    simp
                | succ k4 =>
                    -- Contradiction: `k = 4 + k4` cannot satisfy `k ≤ 3`.
                    have : Nat.succ (Nat.succ (Nat.succ (Nat.succ k4))) ≤ 3 := hk_le3
                    have h2 : Nat.succ (Nat.succ (Nat.succ k4)) ≤ 2 :=
                      Nat.succ_le_succ_iff.mp this
                    have h1 : Nat.succ (Nat.succ k4) ≤ 1 :=
                      Nat.succ_le_succ_iff.mp h2
                    have h0 : Nat.succ k4 ≤ 0 :=
                      Nat.succ_le_succ_iff.mp h1
                    exact (Nat.not_succ_le_zero k4 h0).elim
  · intro hnmem
    -- Membership in `{1,2,4}` gives the three cases.
    have hnpos : 0 < n := by
      -- All three elements are positive.
      rcases hnmem with (rfl | rfl | rfl) <;> decide
    refine ⟨hnpos, ?_⟩
    rcases hnmem with (rfl | rfl | rfl)
    · exact ufrf_not_semigroupPred_one
    · exact ufrf_not_semigroupPred_two
    · exact ufrf_not_semigroupPred_four

end GapSetPrime
