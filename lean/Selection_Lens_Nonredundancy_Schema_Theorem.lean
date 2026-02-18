import Gap_Set_Prime_Theorem
import Seed_To_Frobenius_Emergence_Bridge_Theorem

/-!
# Emergence Selection Lens Schema (Semigroup vs Pair-Based Nonredundancy)

Goal: make reusable the bridge fact established concretely in
`Seed_To_Frobenius_Emergence_Bridge_Theorem`:

* In the **semigroup lens** (`GapSetPrime.semigroupPred`), a generator can be *redundant*
  because it is already reachable as a nonnegative combination of a smaller seed.

* In an **emergence / selection lens** that acts on **explicit generator pairs**
  (here: Frobenius Level-2 values built by `SeedToFrobeniusBridge.L2Of`), the same generator
  can be *nonredundant*: omitting it removes the relevant explicit pairs, so downstream
  selections can fail.

This file defines a small, parameterized interface for selection rules on Level-2 lists,
proves generic nonredundancy lemmas, and instantiates them on concrete UFRF data.

No placeholders: all results are exact.
-/

namespace SelectionLensNonredundancy

open GapSetPrime
open SeedToFrobeniusBridge

abbrev L2Builder := List Nat → List Nat
abbrev SelectionRule := List Nat → Prop

/-- Run a selection rule on the Level-2 list derived from an explicit generator list. -/
def run (L2 : L2Builder) (sel : SelectionRule) (xs : List Nat) : Prop :=
  sel (L2 xs)

/-- Selection-lens redundancy: adding `g` does not change the selected property. -/
def selectionRedundant (L2 : L2Builder) (sel : SelectionRule) (xs : List Nat) (g : Nat) : Prop :=
  run L2 sel xs ↔ run L2 sel (xs ++ [g])

/-- Minimal constraint used to force explicit generator inclusion: `sel` implies a witness element is present. -/
def requiresElem (sel : SelectionRule) (v : Nat) : Prop :=
  ∀ L2, sel L2 → v ∈ L2

/-- If a selection rule requires witness `v`, and `v` is not present, the rule cannot hold. -/
theorem run_false_of_requiresElem_of_not_mem
    (L2 : L2Builder) (sel : SelectionRule) (v : Nat) (xs : List Nat) :
    requiresElem sel v → v ∉ L2 xs → ¬ run L2 sel xs := by
  intro hreq hnot hrun
  exact hnot (hreq (L2 xs) hrun)

/-- Generic schema: if `sel` is false before adding `g` but true after, then `g` is nonredundant. -/
theorem nonredundant_of_run_true_false
    (L2 : L2Builder) (sel : SelectionRule) (xs : List Nat) (g : Nat) :
    run L2 sel (xs ++ [g]) → ¬ run L2 sel xs → ¬ selectionRedundant L2 sel xs g := by
  intro h1 h0 hred
  exact h0 (hred.2 h1)

/-- Selection rule: "the Level-2 list contains `v`". -/
def has (v : Nat) : SelectionRule := fun L2 => v ∈ L2

theorem requiresElem_has (v : Nat) : requiresElem (has v) v := by
  intro L2 hv
  exact hv

-- --------------------------------------------------------------------
-- Pattern selection rules (beyond membership): AP(12) witness
-- --------------------------------------------------------------------

/--
Order-independent AP(12) selection rule on a Level-2 list.

This treats the Level-2 list as a finite set and checks whether it contains
some 3-term arithmetic progression with common difference `12`.

This is intentionally weaker than “the unique Monster triple”, but it is the
right shape to plug into the same nonredundancy schema as membership rules.
-/
def hasAP12b (L2 : List Nat) : Bool :=
  let xs := L2.eraseDups
  -- Search over the (deduplicated) list itself; order is irrelevant for membership checks.
  xs.any (fun a => decide ((a + 12) ∈ xs) && decide ((a + 24) ∈ xs))

/-- AP(12) selection rule, expressed as a decidable proposition via `hasAP12b`. -/
def hasAP12 : SelectionRule := fun L2 => hasAP12b L2 = true

-- --------------------------------------------------------------------
-- Semigroup redundancy witnesses for the seed `[3,5,7]`
-- --------------------------------------------------------------------

/-- Helper: unfold `semigroupPred` for one-step extension by an appended generator. -/
theorem semigroupPred_append_singleton_iff (xs : List Nat) (g n : Nat) :
    semigroupPred (xs ++ [g]) n ↔ ∃ k s, semigroupPred xs s ∧ n = s + k * g := by
  -- `semigroupPred` is a `foldl` closure; appending `[g]` adds one closure step.
  unfold semigroupPred
  -- Reassociate the fold along append.
  -- After rewriting, `[g]` runs one step of the closure operator.
  simp [List.foldl_append, List.foldl]

/-- Semigroup reachability: `11 = 2*3 + 1*5` (so `11` is redundant w.r.t. the seed). -/
theorem semigroupPred_seed_11 : semigroupPred seed 11 := by
  -- Seed is `[3,5,7]`.
  have hstep7 : semigroupPred (seed.dropLast) 11 := by
    -- `seed.dropLast = [3,5]`.
    -- `11 = 6 + 1*5`, and `6 = 0 + 2*3`.
    -- Expand `[3,5]` as append-singleton of `[3]`.
    -- First show `semigroupPred [3] 6`.
    have h3 : semigroupPred ([3] : List Nat) 6 := by
      -- `semigroupPred [3] 6` means `6 = 0 + 2*3`.
      -- Expand via append-singleton.
      have : semigroupPred ([] : List Nat) 0 := by
        -- Base predicate is `{0}`.
        simp [semigroupPred]
      -- Use the append-singleton characterization.
      -- `[3] = [] ++ [3]`.
      have h : ∃ k s, semigroupPred ([] : List Nat) s ∧ 6 = s + k * 3 := by
        refine ⟨2, 0, ?_, by native_decide⟩
        simpa using this
      -- Rewrite goal using the iff lemma.
      have := (semigroupPred_append_singleton_iff ([] : List Nat) 3 6).2 h
      simpa using this
    -- Now lift to `[3,5]`: `11 = 6 + 1*5`.
    have h : ∃ k s, semigroupPred ([3] : List Nat) s ∧ 11 = s + k * 5 := by
      refine ⟨1, 6, h3, by native_decide⟩
    have := (semigroupPred_append_singleton_iff ([3] : List Nat) 5 11).2 h
    -- `[3] ++ [5]` is `[3,5]`.
    simpa using this
  -- Finally lift to `[3,5,7]` by taking `k=0` at the last step.
  have h : ∃ k s, semigroupPred (seed.dropLast) s ∧ 11 = s + k * 7 := by
    refine ⟨0, 11, ?_, by native_decide⟩
    simpa using hstep7
  have := (semigroupPred_append_singleton_iff (seed.dropLast) 7 11).2 h
  -- `seed.dropLast ++ [7] = seed`.
  simpa [seed] using this

/-- Semigroup reachability: `13 = 6 + 1*7` (so `13` is redundant w.r.t. the seed). -/
theorem semigroupPred_seed_13 : semigroupPred seed 13 := by
  -- We only need reachability of `6` under `[3,5]` and then add `7`.
  have h35 : semigroupPred (seed.dropLast) 6 := by
    -- `6 = 0 + 2*3`.
    have h3 : semigroupPred ([3] : List Nat) 6 := by
      have : semigroupPred ([] : List Nat) 0 := by
        simp [semigroupPred]
      have h : ∃ k s, semigroupPred ([] : List Nat) s ∧ 6 = s + k * 3 := by
        refine ⟨2, 0, ?_, by native_decide⟩
        simpa using this
      have := (semigroupPred_append_singleton_iff ([] : List Nat) 3 6).2 h
      simpa using this
    -- Now lift to `[3,5]` with `k=0`.
    have h : ∃ k s, semigroupPred ([3] : List Nat) s ∧ 6 = s + k * 5 := by
      refine ⟨0, 6, h3, by native_decide⟩
    have := (semigroupPred_append_singleton_iff ([3] : List Nat) 5 6).2 h
    simpa using this
  -- Final lift to `[3,5,7]`: `13 = 6 + 1*7`.
  have h : ∃ k s, semigroupPred (seed.dropLast) s ∧ 13 = s + k * 7 := by
    refine ⟨1, 6, h35, by native_decide⟩
  have := (semigroupPred_append_singleton_iff (seed.dropLast) 7 13).2 h
  simpa [seed] using this

-- --------------------------------------------------------------------
-- Concrete instantiation: Frobenius Level-2 builder `L2Of`
-- --------------------------------------------------------------------

/-- Level-2 builder for the emergence lens used throughout the repo. -/
def L2 : L2Builder := L2Of

/-- `59` appears in Level-2 exactly when the explicit generator `11` is present. -/
theorem mem59_L2_seed11_13 : 59 ∈ L2 seed11_13 := by
  native_decide

theorem not_mem59_L2_seed13 : 59 ∉ L2 seed13 := by
  native_decide

/-- `47` and `71` appear in Level-2 exactly when the explicit generator `13` is present. -/
theorem mem47_L2_seed11_13 : 47 ∈ L2 seed11_13 := by
  native_decide

theorem not_mem47_L2_seed11 : 47 ∉ L2 seed11 := by
  native_decide

theorem mem71_L2_seed11_13 : 71 ∈ L2 seed11_13 := by
  native_decide

theorem not_mem71_L2_seed11 : 71 ∉ L2 seed11 := by
  native_decide

/-- Summary: semigroup redundancy does not imply emergence-selection redundancy (membership rules). -/
def selection_lens_nonredundancy_summary : Prop :=
    semigroupPred seed 11
  ∧ semigroupPred seed 13
  ∧ (run L2 (has 59) seed11_13 ∧ ¬ run L2 (has 59) seed13)
  ∧ (run L2 (has 47) seed11_13 ∧ ¬ run L2 (has 47) seed11)
  ∧ (run L2 (has 71) seed11_13 ∧ ¬ run L2 (has 71) seed11)
  ∧ (run L2 hasAP12 seed11_13 ∧ ¬ run L2 hasAP12 seed11 ∧ ¬ run L2 hasAP12 seed13)
  ∧ (¬ selectionRedundant L2 hasAP12 seed13 11)
  ∧ (¬ selectionRedundant L2 hasAP12 seed11 13)

theorem selection_lens_nonredundancy_summary_proof : selection_lens_nonredundancy_summary := by
  -- Semigroup lens: `11` and `13` are redundant.
  refine And.intro semigroupPred_seed_11 ?_
  refine And.intro semigroupPred_seed_13 ?_
  -- Emergence lens: membership witnesses show `11` and `13` are nonredundant.
  refine And.intro ?_ ?_
  · refine ⟨mem59_L2_seed11_13, not_mem59_L2_seed13⟩
  refine And.intro ?_ ?_
  · refine ⟨mem47_L2_seed11_13, not_mem47_L2_seed11⟩
  refine And.intro ?_ ?_
  · refine ⟨mem71_L2_seed11_13, not_mem71_L2_seed11⟩
  -- Pattern witness: AP(12) exists iff both `11` and `13` are present (order-independent).
  refine And.intro ?_ ?_
  · refine ⟨?_, ?_⟩
    · dsimp [run, hasAP12, hasAP12b]
      native_decide
    · refine ⟨?_, ?_⟩
      · dsimp [run, hasAP12, hasAP12b]
        native_decide
      · dsimp [run, hasAP12, hasAP12b]
        native_decide
  refine And.intro ?_ ?_
  · -- Adding `11` to a `13`-seed changes AP(12) from false to true.
    refine nonredundant_of_run_true_false (L2 := L2) (sel := hasAP12) (xs := seed13) (g := 11) ?_ ?_
    · dsimp [run, hasAP12, hasAP12b]
      native_decide
    · dsimp [run, hasAP12, hasAP12b]
      native_decide
  · -- Adding `13` to an `11`-seed changes AP(12) from false to true.
    refine nonredundant_of_run_true_false (L2 := L2) (sel := hasAP12) (xs := seed11) (g := 13) ?_ ?_
    · dsimp [run, hasAP12, hasAP12b]
      native_decide
    · dsimp [run, hasAP12, hasAP12b]
      native_decide

end SelectionLensNonredundancy
