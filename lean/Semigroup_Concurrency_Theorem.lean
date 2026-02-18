import Gap_Set_Prime_Theorem

/-!
# Semigroup Concurrency Theorem

This file adds an "order-free" concurrency fact that was previously only implicit:

* The fold-closure semigroup semantics `semigroupPred` is invariant under `List.Perm`.
* Therefore the bounded DP semigroup computation `reachableTable` is also invariant (within the bound),
  because `reachableTable_getD_iff_semigroupPred` connects the algorithm to `semigroupPred`.

This is a foundational statement of *concurrency*: generator processing order does not change
the emergent semigroup set.
-/

namespace GapSetPrime

/-- One generator-step closure on predicates: `n` is reachable if `n = s + k*g` for some prior `s`. -/
def stepPred (S : ℕ → Prop) (g : ℕ) : ℕ → Prop :=
  fun n => ∃ k s, S s ∧ n = s + k * g

private theorem stepPred_congr {S₁ S₂ : ℕ → Prop} (h : ∀ n, S₁ n ↔ S₂ n) (g n : ℕ) :
    stepPred S₁ g n ↔ stepPred S₂ g n := by
  constructor
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, (h s).1 hs, rfl⟩
  · rintro ⟨k, s, hs, rfl⟩
    exact ⟨k, s, (h s).2 hs, rfl⟩

/--
Two generator-step closures commute:
closing under `g₁` then `g₂` is the same as closing under `g₂` then `g₁`.

This is the core commutativity fact that makes the fold-closure semantics order-free.
-/
theorem stepPred_comm (S : ℕ → Prop) (g₁ g₂ n : ℕ) :
    stepPred (stepPred S g₁) g₂ n ↔ stepPred (stepPred S g₂) g₁ n := by
  constructor
  · rintro ⟨k₂, s₂, hs₂, hn⟩
    rcases hs₂ with ⟨k₁, s₁, hs₁, hs₂⟩
    refine ⟨k₁, s₁ + k₂ * g₂, ?_, ?_⟩
    · exact ⟨k₂, s₁, hs₁, rfl⟩
    · -- Rearrange `s₁ + k₁*g₁ + k₂*g₂` into `s₁ + k₂*g₂ + k₁*g₁`.
      have : n = (s₁ + k₁ * g₁) + k₂ * g₂ := by
        simpa [hs₂] using hn
      calc
        n = (s₁ + k₁ * g₁) + k₂ * g₂ := this
        _ = s₁ + (k₁ * g₁ + k₂ * g₂) := by
          simp [Nat.add_assoc]
        _ = s₁ + (k₂ * g₂ + k₁ * g₁) := by
          simp [Nat.add_comm]
        _ = (s₁ + k₂ * g₂) + k₁ * g₁ := by
          simp [Nat.add_assoc]
  · rintro ⟨k₁, s₁, hs₁, hn⟩
    rcases hs₁ with ⟨k₂, s₂, hs₂, hs₁⟩
    refine ⟨k₂, s₂ + k₁ * g₁, ?_, ?_⟩
    · exact ⟨k₁, s₂, hs₂, rfl⟩
    · have : n = (s₂ + k₂ * g₂) + k₁ * g₁ := by
        simpa [hs₁] using hn
      calc
        n = (s₂ + k₂ * g₂) + k₁ * g₁ := this
        _ = s₂ + (k₂ * g₂ + k₁ * g₁) := by
          simp [Nat.add_assoc]
        _ = s₂ + (k₁ * g₁ + k₂ * g₂) := by
          simp [Nat.add_comm]
        _ = (s₂ + k₁ * g₁) + k₂ * g₂ := by
          simp [Nat.add_assoc]

private theorem foldl_stepPred_congr (gs : List ℕ) {S₁ S₂ : ℕ → Prop} (h : ∀ n, S₁ n ↔ S₂ n) :
    ∀ n : ℕ, (gs.foldl stepPred S₁) n ↔ (gs.foldl stepPred S₂) n := by
  induction gs generalizing S₁ S₂ with
  | nil =>
      intro n
      simpa using h n
  | cons g gs ih =>
      intro n
      -- Fold step: rewrite to tail foldl with updated accumulators.
      simpa [List.foldl] using
        ih (S₁ := stepPred S₁ g) (S₂ := stepPred S₂ g) (fun x => stepPred_congr h g x) n

/--
Order-free fold closure: if two generator lists are permutations, folding `stepPred` over them yields
extensionally equivalent predicates.
-/
theorem foldl_stepPred_perm {xs ys : List ℕ} (hperm : List.Perm xs ys) (S : ℕ → Prop) :
    ∀ n : ℕ, (xs.foldl stepPred S) n ↔ (ys.foldl stepPred S) n := by
  induction hperm generalizing S with
  | nil =>
      intro n
      simp
  | cons a h ih =>
      intro n
      simpa [List.foldl] using ih (S := stepPred S a) n
  | swap a b l =>
      intro n
      -- Expand the first two steps of the fold, then use commutativity + congruence on the tail fold.
      have hacc : ∀ m : ℕ, stepPred (stepPred S b) a m ↔ stepPred (stepPred S a) b m := by
        intro m
        simpa using (stepPred_comm (S := S) (g₁ := b) (g₂ := a) (n := m))
      simpa [List.foldl] using (foldl_stepPred_congr (gs := l) hacc n)
  | trans h₁ h₂ ih₁ ih₂ =>
      intro n
      exact Iff.trans (ih₁ (S := S) n) (ih₂ (S := S) n)

/-- `semigroupPred` does not depend on generator order (concurrency / commutativity). -/
theorem semigroupPred_perm {xs ys : List ℕ} (hperm : List.Perm xs ys) (n : ℕ) :
    semigroupPred xs n ↔ semigroupPred ys n := by
  -- `semigroupPred` is exactly `foldl stepPred (fun n => n=0)`.
  simpa [semigroupPred, stepPred] using (foldl_stepPred_perm (S := fun x => x = 0) hperm n)

/--
Bounded DP reachability (`reachableTable`) is permutation-invariant within the bound.

This is a corollary of:
* DP correctness: `reachableTable_getD_iff_semigroupPred`
* Order-free semantics: `semigroupPred_perm`
-/
theorem reachableTable_getD_perm_iff {xs ys : List ℕ} (hperm : List.Perm xs ys)
    (upTo n : ℕ) (hn : n ≤ upTo)
    (hposx : ∀ g ∈ xs, 0 < g) (hposy : ∀ g ∈ ys, 0 < g) :
    (reachableTable xs upTo).getD n false = true ↔ (reachableTable ys upTo).getD n false = true := by
  have hx : (reachableTable xs upTo).getD n false = true ↔ semigroupPred xs n :=
    reachableTable_getD_iff_semigroupPred xs upTo n hn hposx
  have hy : (reachableTable ys upTo).getD n false = true ↔ semigroupPred ys n :=
    reachableTable_getD_iff_semigroupPred ys upTo n hn hposy
  exact hx.trans ((semigroupPred_perm (hperm := hperm) (n := n)).trans hy.symm)

end GapSetPrime
