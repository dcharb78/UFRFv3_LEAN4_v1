import Semigroup_Standard_Semantics_Theorem

/-!
# UFRF Minimal Semigroup Seed (Closure Redundancy)

The repo's UFRF semigroup is usually presented with generators:

`[3, 5, 7, 11, 13]`.

However, **as a numerical semigroup (additive closure)** the last two generators are redundant:

* `11 = 5 + 3 + 3`
* `13 = 7 + 3 + 3`

So the semigroup closure is already determined by the smaller seed list `[3,5,7]`.

This is a precise “minimal seed” statement *for the semigroup lens only*:
it does **not** claim that `11` and `13` are irrelevant elsewhere (they are essential in the
Frobenius-emergence story and other UFRF structures). It only says that, for reachability as
nonnegative linear combinations, `[3,5,7]` generates the same set as `[3,5,7,11,13]`.

No placeholders; the proof uses `AddSubmonoid.closure` semantics.
-/

namespace GapSetPrime

/-- A minimal seed list that generates the same *semigroup closure* as `ufrfGenerators`. -/
def ufrfSeedGenerators : List ℕ := [3, 5, 7]

private abbrev seedClosure : AddSubmonoid ℕ :=
  AddSubmonoid.closure (genSet ufrfSeedGenerators)

private theorem three_mem_seedClosure : (3 : ℕ) ∈ seedClosure := by
  refine AddSubmonoid.subset_closure ?_
  -- `genSet` membership is definitionally list membership.
  change (3 : ℕ) ∈ ufrfSeedGenerators
  simp [ufrfSeedGenerators]

private theorem five_mem_seedClosure : (5 : ℕ) ∈ seedClosure := by
  refine AddSubmonoid.subset_closure ?_
  change (5 : ℕ) ∈ ufrfSeedGenerators
  simp [ufrfSeedGenerators]

private theorem seven_mem_seedClosure : (7 : ℕ) ∈ seedClosure := by
  refine AddSubmonoid.subset_closure ?_
  change (7 : ℕ) ∈ ufrfSeedGenerators
  simp [ufrfSeedGenerators]

private theorem eleven_mem_seedClosure : (11 : ℕ) ∈ seedClosure := by
  -- `11 = 5 + 3 + 3`.
  have h53 : (5 + 3 : ℕ) ∈ seedClosure :=
    seedClosure.add_mem five_mem_seedClosure three_mem_seedClosure
  have h533 : (5 + 3 + 3 : ℕ) ∈ seedClosure :=
    seedClosure.add_mem h53 three_mem_seedClosure
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h533

private theorem thirteen_mem_seedClosure : (13 : ℕ) ∈ seedClosure := by
  -- `13 = 7 + 3 + 3`.
  have h73 : (7 + 3 : ℕ) ∈ seedClosure :=
    seedClosure.add_mem seven_mem_seedClosure three_mem_seedClosure
  have h733 : (7 + 3 + 3 : ℕ) ∈ seedClosure :=
    seedClosure.add_mem h73 three_mem_seedClosure
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h733

private theorem genSet_ufrf_subset_seedClosure :
    genSet ufrfGenerators ⊆ seedClosure := by
  intro g hg
  -- Enumerate the 5 cases for `g ∈ [3,5,7,11,13]`.
  change g ∈ ufrfGenerators at hg
  have hg' : g = 3 ∨ g = 5 ∨ g = 7 ∨ g = 11 ∨ g = 13 := by
    simpa [ufrfGenerators] using hg
  rcases hg' with rfl | rfl | rfl | rfl | rfl
  · exact three_mem_seedClosure
  · exact five_mem_seedClosure
  · exact seven_mem_seedClosure
  · exact eleven_mem_seedClosure
  · exact thirteen_mem_seedClosure

private theorem seedClosure_le_ufrfClosure :
    seedClosure ≤ AddSubmonoid.closure (genSet ufrfGenerators) := by
  -- It suffices to show the seed generators themselves are in the UFRF closure.
  refine AddSubmonoid.closure_le.2 ?_
  intro g hg
  -- `g ∈ [3,5,7]` implies `g ∈ [3,5,7,11,13]`.
  change g ∈ ufrfSeedGenerators at hg
  have hg' : g = 3 ∨ g = 5 ∨ g = 7 := by
    simpa [ufrfSeedGenerators] using hg
  have : g ∈ ufrfGenerators := by
    rcases hg' with rfl | rfl | rfl <;> simp [ufrfGenerators]
  exact AddSubmonoid.subset_closure (by
    -- `genSet` membership is definitionally list membership.
    change g ∈ ufrfGenerators
    exact this)

private theorem ufrfClosure_le_seedClosure :
    AddSubmonoid.closure (genSet ufrfGenerators) ≤ seedClosure := by
  -- If all generators are already in `seedClosure`, then the full closure is contained in it.
  exact AddSubmonoid.closure_le.2 genSet_ufrf_subset_seedClosure

/--
**Minimal seed (semigroup lens):**

`semigroupPred [3,5,7,11,13] n` is equivalent to `semigroupPred [3,5,7] n` for all `n`.
-/
theorem semigroupPred_ufrf_iff_seed (n : ℕ) :
    semigroupPred ufrfGenerators n ↔ semigroupPred ufrfSeedGenerators n := by
  -- Move to the standard closure semantics.
  have hufrf : semigroupPred ufrfGenerators n ↔ n ∈ AddSubmonoid.closure (genSet ufrfGenerators) :=
    semigroupPred_iff_mem_closure ufrfGenerators n
  have hseed : semigroupPred ufrfSeedGenerators n ↔ n ∈ AddSubmonoid.closure (genSet ufrfSeedGenerators) :=
    semigroupPred_iff_mem_closure ufrfSeedGenerators n
  constructor
  · intro hn
    have hn' : n ∈ AddSubmonoid.closure (genSet ufrfGenerators) := (hufrf.1 hn)
    have : n ∈ seedClosure := ufrfClosure_le_seedClosure hn'
    exact hseed.2 this
  · intro hn
    have hn' : n ∈ seedClosure := (hseed.1 hn)
    have : n ∈ AddSubmonoid.closure (genSet ufrfGenerators) := seedClosure_le_ufrfClosure hn'
    exact hufrf.2 this

/-- Concrete redundancy: the seed already reaches `11`. -/
theorem semigroupPred_seed_11 : semigroupPred ufrfSeedGenerators 11 := by
  -- By closure semantics (and the explicit witness in `eleven_mem_seedClosure`).
  have : (11 : ℕ) ∈ seedClosure := eleven_mem_seedClosure
  exact (semigroupPred_iff_mem_closure ufrfSeedGenerators 11).2 this

/-- Concrete redundancy: the seed already reaches `13`. -/
theorem semigroupPred_seed_13 : semigroupPred ufrfSeedGenerators 13 := by
  have : (13 : ℕ) ∈ seedClosure := thirteen_mem_seedClosure
  exact (semigroupPred_iff_mem_closure ufrfSeedGenerators 13).2 this

/--
Nontriviality: removing `7` changes the semigroup.

`7` is not reachable from `[3,5]`, so `[3,5,7]` is a genuinely stronger seed than `[3,5]`.
-/
theorem semigroupPred_35_false_7 : ¬ semigroupPred ([3, 5] : List ℕ) 7 := by
  intro h
  -- Unfold the fold-closure semantics for the concrete list `[3,5]`.
  have h' :
      ∃ k s,
        (∃ k₀ s₀, s₀ = 0 ∧ s = s₀ + k₀ * 3) ∧
          7 = s + k * 5 := by
    simpa [semigroupPred, List.foldl] using h
  rcases h' with ⟨k, s, hs, h7⟩
  rcases hs with ⟨k₀, s₀, hs₀, hs⟩
  subst hs₀
  have hs' : s = k₀ * 3 := by
    simpa [Nat.zero_add] using hs
  have hEq : k₀ * 3 + k * 5 = 7 := by
    -- rewrite the `s` term and flip sides to have a convenient normal form.
    simpa [hs', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h7.symm
  have hk5_le7 : k * 5 ≤ 7 := by
    have : k * 5 ≤ k₀ * 3 + k * 5 := Nat.le_add_left (k * 5) (k₀ * 3)
    simpa [hEq] using this
  cases k with
  | zero =>
      have hEq0 : k₀ * 3 = 7 := by
        simpa using hEq
      have hdiv : (3 : ℕ) ∣ 7 := by
        -- `3 ∣ k₀*3 = 7`.
        refine hEq0 ▸ ?_
        exact Nat.dvd_mul_left 3 k₀
      exact (by decide : ¬ (3 : ℕ) ∣ 7) hdiv
  | succ k1 =>
      cases k1 with
      | zero =>
          -- `k = 1`: `k₀*3 + 5 = 7`, so `k₀*3 = 2`.
          have hEq1 : k₀ * 3 + 5 = 7 := by
            simpa using hEq
          have h7eq : (7 : ℕ) = 2 + 5 := by decide
          have hk0 : k₀ * 3 = 2 := by
            have : k₀ * 3 + 5 = 2 + 5 := by
              simpa [h7eq] using hEq1
            exact Nat.add_right_cancel this
          have hdiv : (3 : ℕ) ∣ 2 := by
            refine hk0 ▸ ?_
            exact Nat.dvd_mul_left 3 k₀
          exact (by decide : ¬ (3 : ℕ) ∣ 2) hdiv
      | succ k2 =>
          -- `k ≥ 2`: then `k*5 ≥ 10`, contradicting `k*5 ≤ 7`.
          have hk2 : 2 ≤ Nat.succ (Nat.succ k2) := by
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k2))
          have h10_le : 10 ≤ (Nat.succ (Nat.succ k2)) * 5 := by
            simpa using (Nat.mul_le_mul_right 5 hk2)
          have : (10 : ℕ) ≤ 7 := le_trans h10_le (by simpa using hk5_le7)
          exact (by decide : ¬ (10 : ℕ) ≤ 7) this

end GapSetPrime
