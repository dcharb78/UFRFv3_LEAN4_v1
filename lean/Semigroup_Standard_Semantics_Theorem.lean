import Semigroup_Concurrency_Theorem

/-!
# Semigroup Standard Semantics Theorem

This file connects the repo's fold-closure semigroup semantics (`semigroupPred`) to the
standard Mathlib notion: `AddSubmonoid.closure` of the generator set.

Why this matters:
- `semigroupPred` was defined to match the DP scan order and avoid set-subtlety.
- `AddSubmonoid.closure` is the canonical, order-free mathematical object.

We prove they coincide, so:
- the DP semantics are *standard*,
- concurrency/order-invariance can be understood as a corollary of standard closure.
-/

namespace GapSetPrime

open scoped BigOperators

/-- The step-closure operator used by `semigroupPred` (written explicitly for reuse in proofs). -/
private def stepFn (S : ℕ → Prop) (g : ℕ) : ℕ → Prop :=
  fun n => ∃ k s, S s ∧ n = s + k * g

/-- The generator set associated to a list of generators (order-free view). -/
def genSet (gens : List ℕ) : Set ℕ :=
  fun g => g ∈ gens

private theorem foldl_stepFn_of_mem (gs : List ℕ) {S : ℕ → Prop} {n : ℕ} (hn : S n) :
    (gs.foldl stepFn S) n := by
  induction gs generalizing S with
  | nil =>
      simpa using hn
  | cons g gs ih =>
      -- Every step is an extension: take `k = 0`, `s = n`.
      have hstep : stepFn S g n := by
        refine ⟨0, n, hn, ?_⟩
        simp
      simpa [List.foldl] using ih (S := stepFn S g) hstep

theorem semigroupPred_zero (gens : List ℕ) : semigroupPred gens 0 := by
  -- Base predicate holds at `0`, and the fold only adds reachability.
  simpa [semigroupPred, stepFn] using
    (foldl_stepFn_of_mem (gs := gens) (S := fun n => n = 0) (n := 0) rfl)

private theorem semigroupPred_head (g : ℕ) (rest : List ℕ) : semigroupPred (g :: rest) g := by
  -- After the first generator-step, reachability is exactly "is a multiple of `g`".
  let S₁ : ℕ → Prop := fun n => ∃ k, n = k * g
  have hS₁ : S₁ g := by
    refine ⟨1, ?_⟩
    simp
  have hfold : (rest.foldl stepFn S₁) g :=
    foldl_stepFn_of_mem (gs := rest) (S := S₁) (n := g) hS₁
  -- Unfold `semigroupPred` for the cons case and simplify the first-step accumulator.
  simpa [semigroupPred, stepFn, List.foldl, S₁] using hfold

private theorem mem_split_of_mem {g : ℕ} {gens : List ℕ} (hg : g ∈ gens) :
    ∃ l₁ l₂, gens = l₁ ++ g :: l₂ := by
  induction gens with
  | nil =>
      cases hg
  | cons x xs ih =>
      simp at hg
      cases hg with
      | inl hx =>
          subst hx
          exact ⟨[], xs, by simp⟩
      | inr hmem =>
          rcases ih hmem with ⟨l₁, l₂, rfl⟩
          refine ⟨x :: l₁, l₂, ?_⟩
          simp

theorem semigroupPred_of_mem_gens {gens : List ℕ} {g : ℕ} (hg : g ∈ gens) : semigroupPred gens g := by
  rcases mem_split_of_mem (g := g) (gens := gens) hg with ⟨l₁, l₂, rfl⟩
  -- Move `g` to the front (a single canonical permutation lemma).
  have hperm : (l₁ ++ g :: l₂).Perm (g :: (l₁ ++ l₂)) := List.perm_middle
  have hhead : semigroupPred (g :: (l₁ ++ l₂)) g := semigroupPred_head g (l₁ ++ l₂)
  exact (semigroupPred_perm (hperm := hperm) (n := g)).2 hhead

private theorem stepPred_add_closed {S : ℕ → Prop} (hadd : ∀ a b, S a → S b → S (a + b)) (g a b : ℕ) :
    stepFn S g a → stepFn S g b → stepFn S g (a + b) := by
  rintro ⟨k₁, s₁, hs₁, rfl⟩ ⟨k₂, s₂, hs₂, rfl⟩
  refine ⟨k₁ + k₂, s₁ + s₂, hadd s₁ s₂ hs₁ hs₂, ?_⟩
  -- (s₁ + k₁*g) + (s₂ + k₂*g) = (s₁+s₂) + (k₁+k₂)*g
  -- The only nontrivial step is rewriting `(k₁+k₂)*g`.
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_mul]

private theorem foldl_stepFn_add_closed (gs : List ℕ) {S : ℕ → Prop}
    (hadd : ∀ a b, S a → S b → S (a + b)) :
    ∀ a b, (gs.foldl stepFn S) a → (gs.foldl stepFn S) b → (gs.foldl stepFn S) (a + b) := by
  induction gs generalizing S with
  | nil =>
      intro a b ha hb
      simpa using hadd a b ha hb
  | cons g gs ih =>
      intro a b ha hb
      -- Fold step: move to the tail fold with accumulator `stepPred S g`,
      -- and use that `stepPred` preserves addition-closure when `S` does.
      have hadd' : ∀ x y, stepFn S g x → stepFn S g y → stepFn S g (x + y) :=
        fun x y => stepPred_add_closed (S := S) hadd g x y
      simpa [List.foldl] using
        ih (S := stepFn S g) (hadd := hadd') a b ha hb

theorem semigroupPred_add (gens : List ℕ) {a b : ℕ} :
    semigroupPred gens a → semigroupPred gens b → semigroupPred gens (a + b) := by
  -- `semigroupPred` is a fold of `stepPred` starting from `{0}`.
  have hadd0 : ∀ x y : ℕ, x = 0 → y = 0 → x + y = 0 := by
    intro x y hx hy
    simp [hx, hy]
  intro ha hb
  simpa [semigroupPred, stepFn] using
    (foldl_stepFn_add_closed (gs := gens) (S := fun n => n = 0) (hadd := hadd0) a b ha hb)

private theorem stepPred_subset_addSubmonoid (M : AddSubmonoid ℕ) {S : ℕ → Prop}
    (hS : ∀ n, S n → n ∈ M) {g : ℕ} (hg : g ∈ M) :
    ∀ n, stepFn S g n → n ∈ M := by
  intro n
  rintro ⟨k, s, hs, rfl⟩
  have hsM : s ∈ M := hS s hs
  have hkgM : k * g ∈ M := by
    -- `k*g` is `k`-fold addition of `g`.
    simpa [Nat.nsmul_eq_mul] using (AddSubmonoid.nsmul_mem M hg k)
  exact M.add_mem hsM hkgM

private theorem foldl_stepFn_subset_addSubmonoid (gs : List ℕ) (M : AddSubmonoid ℕ) {S : ℕ → Prop}
    (hS : ∀ n, S n → n ∈ M) (hgs : ∀ g ∈ gs, g ∈ M) :
    ∀ n, (gs.foldl stepFn S) n → n ∈ M := by
  induction gs generalizing S with
  | nil =>
      intro n hn
      exact hS n hn
  | cons g gs ih =>
      intro n hn
      have hgM : g ∈ M := hgs g (by simp)
      have hS' : ∀ x, stepFn S g x → x ∈ M :=
        stepPred_subset_addSubmonoid (M := M) (S := S) hS hgM
      have hgs' : ∀ g' ∈ gs, g' ∈ M := by
        intro g' hg'
        exact hgs g' (by simp [hg'])
      simpa [List.foldl] using ih (S := stepFn S g) (hS := hS') (hgs := hgs') n hn

/--
Standard semantics: `semigroupPred gens n` iff `n` lies in the additive submonoid closure of the generator set.
-/
theorem semigroupPred_iff_mem_closure (gens : List ℕ) (n : ℕ) :
    semigroupPred gens n ↔ n ∈ AddSubmonoid.closure (genSet gens) := by
  let s : Set ℕ := genSet gens
  constructor
  · -- Fold-closure semantics are contained in the standard closure.
    intro hn
    have hbase : ∀ x, (fun t : ℕ => t = 0) x → x ∈ AddSubmonoid.closure s := by
      intro x hx
      subst hx
      exact (AddSubmonoid.closure s).zero_mem
    have hgens : ∀ g ∈ gens, g ∈ AddSubmonoid.closure s := by
      intro g hg
      exact (AddSubmonoid.subset_closure (s := s) hg)
    -- Apply the general "fold subset" lemma.
    simpa [semigroupPred, stepFn, s] using
      (foldl_stepFn_subset_addSubmonoid (gs := gens) (M := AddSubmonoid.closure s) (S := fun t => t = 0)
        (hS := hbase) (hgs := hgens) n hn)
  · -- Standard closure is contained in the fold-closure predicate (since it is a submonoid containing the generators).
    intro hn
    -- Use the closure induction principle with constant motive.
    refine AddSubmonoid.closure_induction (s := s)
      (motive := fun x _ => semigroupPred gens x)
      (mem := ?_) (zero := ?_) (add := ?_) hn
    · intro x hx
      -- `hx : x ∈ s` is exactly list membership by definition of `genSet`.
      exact semigroupPred_of_mem_gens (gens := gens) (g := x) hx
    · exact semigroupPred_zero gens
    · intro x y _ _ hx hy
      exact semigroupPred_add gens hx hy

end GapSetPrime
