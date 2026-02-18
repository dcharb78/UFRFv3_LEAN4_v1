import Semigroup_Standard_Semantics_Theorem

/-!
# Semigroup Coefficient Witness Theorem

This module adds an explicit *coefficient witness* semantics for `semigroupPred`.

Informally, it turns the fold-closure / DP-aligned semantics into a single algebraic normal form:

`semigroupPred gens n` iff there exists a coefficient list `ks` (aligned with `gens`) such that

`n = Σᵢ ks[i] * gens[i]`.

Why this matters for the UFRF proof spine:
- it connects the "emergence by repeated closure" view to a concrete finite witness,
  which is easier to transport across bridges and to use in downstream algebraic reasoning.
- it keeps the semantics order-free while staying explicit (no hidden `AddSubmonoid` machinery).
-/

namespace GapSetPrime

open scoped BigOperators

/-- Linear combination of generators with coefficient list aligned to `gens` (via `zipWith`). -/
def lincomb (ks gens : List ℕ) : ℕ :=
  (List.zipWith (fun k g => k * g) ks gens).sum

/-- Coefficient-witness semantics: `n` is a sum of multiples of the listed generators. -/
def coeffWitness (gens : List ℕ) (n : ℕ) : Prop :=
  ∃ ks : List ℕ, ks.length = gens.length ∧ n = lincomb ks gens

private lemma lincomb_cons (k g : ℕ) (ks gs : List ℕ) :
    lincomb (k :: ks) (g :: gs) = k * g + lincomb ks gs := by
  simp [lincomb]

private lemma lincomb_replicate_zero (gs : List ℕ) :
    lincomb (List.replicate gs.length 0) gs = 0 := by
  induction gs with
  | nil => simp [lincomb]
  | cons g gs ih =>
      have ih' : (List.zipWith (fun k g => k * g) (List.replicate gs.length 0) gs).sum = 0 := by
        simpa [lincomb] using ih
      simp [lincomb, List.replicate_succ, ih']

private lemma lincomb_singleton_in_split (l1 l2 : List ℕ) (g : ℕ) :
    lincomb (List.replicate l1.length 0 ++ 1 :: List.replicate l2.length 0) (l1 ++ g :: l2) = g := by
  have hlen : (List.replicate l1.length 0).length = l1.length := by
    simp
  have h1 : (List.zipWith (fun k g => k * g) (List.replicate l1.length 0) l1).sum = 0 := by
    simpa [lincomb] using (lincomb_replicate_zero l1)
  have h2 : (List.zipWith (fun k g => k * g) (List.replicate l2.length 0) l2).sum = 0 := by
    simpa [lincomb] using (lincomb_replicate_zero l2)
  simp [lincomb, List.zipWith_append hlen, List.sum_append, h1, h2]

private lemma lincomb_add_zipWith (gens ks1 ks2 : List ℕ)
    (h1 : ks1.length = gens.length) (h2 : ks2.length = gens.length) :
    lincomb (List.zipWith (·+·) ks1 ks2) gens = lincomb ks1 gens + lincomb ks2 gens := by
  induction gens generalizing ks1 ks2 with
  | nil =>
      simp [lincomb]
  | cons g gs ih =>
      cases ks1 with
      | nil =>
          simp at h1
      | cons k1 ks1 =>
          cases ks2 with
          | nil =>
              simp at h2
          | cons k2 ks2 =>
              have h1' : ks1.length = gs.length := by
                simpa using Nat.succ.inj h1
              have h2' : ks2.length = gs.length := by
                simpa using Nat.succ.inj h2
              have htail : lincomb (List.zipWith (·+·) ks1 ks2) gs = lincomb ks1 gs + lincomb ks2 gs :=
                ih (ks1 := ks1) (ks2 := ks2) h1' h2'
              simp [lincomb_cons, htail, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma coeffWitness_zero (gens : List ℕ) : coeffWitness gens 0 := by
  refine ⟨List.replicate gens.length 0, by simp, ?_⟩
  exact (lincomb_replicate_zero gens).symm

private lemma mem_split_of_mem {g : ℕ} {gens : List ℕ} (hg : g ∈ gens) :
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

private lemma coeffWitness_of_mem_gens {gens : List ℕ} {g : ℕ} (hg : g ∈ gens) :
    coeffWitness gens g := by
  rcases mem_split_of_mem (g := g) (gens := gens) hg with ⟨l1, l2, rfl⟩
  refine ⟨List.replicate l1.length 0 ++ 1 :: List.replicate l2.length 0, ?_, ?_⟩
  · simp
  · exact (lincomb_singleton_in_split l1 l2 g).symm

private lemma coeffWitness_add {gens : List ℕ} {a b : ℕ} :
    coeffWitness gens a → coeffWitness gens b → coeffWitness gens (a + b) := by
  rintro ⟨ks1, hlen1, rfl⟩ ⟨ks2, hlen2, rfl⟩
  refine ⟨List.zipWith (·+·) ks1 ks2, ?_, ?_⟩
  · simp [List.length_zipWith, hlen1, hlen2]
  · exact (lincomb_add_zipWith (gens := gens) (ks1 := ks1) (ks2 := ks2) hlen1 hlen2).symm

/-- Membership in the standard additive closure is equivalent to coefficient-witness semantics. -/
theorem mem_closure_iff_coeffWitness (gens : List ℕ) (n : ℕ) :
    n ∈ AddSubmonoid.closure (genSet gens) ↔ coeffWitness gens n := by
  constructor
  · intro hn
    refine AddSubmonoid.closure_induction (s := genSet gens)
      (motive := fun x _ => coeffWitness gens x)
      (mem := ?_) (zero := ?_) (add := ?_) hn
    · intro x hx
      exact coeffWitness_of_mem_gens (gens := gens) (g := x) hx
    · exact coeffWitness_zero gens
    · intro x y _ _ hx hy
      exact coeffWitness_add (gens := gens) hx hy
  · rintro ⟨ks, hlen, rfl⟩
    revert ks
    induction gens with
    | nil =>
        intro ks hlen
        have : ks = [] := by
          cases ks with
          | nil => rfl
          | cons k ks =>
              simp at hlen
        subst this
        simp [lincomb]
    | cons g gs ih =>
        intro ks hlen
        cases ks with
        | nil =>
            simp at hlen
        | cons k ks =>
            have hlen' : ks.length = gs.length := by
              simpa using Nat.succ.inj hlen
            have hsubset : genSet gs ⊆ genSet (g :: gs) := by
              intro x hx
              unfold genSet at hx ⊢
              exact List.mem_cons_of_mem g hx
            have htail_mem : lincomb ks gs ∈ AddSubmonoid.closure (genSet (g :: gs)) := by
              have : lincomb ks gs ∈ AddSubmonoid.closure (genSet gs) := ih (ks := ks) hlen'
              exact (AddSubmonoid.closure_mono hsubset) this
            have hg_mem : g ∈ AddSubmonoid.closure (genSet (g :: gs)) := by
              apply AddSubmonoid.subset_closure
              unfold genSet
              exact (List.mem_cons_self : g ∈ g :: gs)
            have hkg_mem : k * g ∈ AddSubmonoid.closure (genSet (g :: gs)) := by
              simpa [Nat.nsmul_eq_mul] using
                (AddSubmonoid.nsmul_mem (AddSubmonoid.closure (genSet (g :: gs))) hg_mem k)
            simpa [lincomb_cons, Nat.add_assoc] using
              (AddSubmonoid.add_mem (AddSubmonoid.closure (genSet (g :: gs))) hkg_mem htail_mem)

/-- `semigroupPred` has an explicit coefficient-witness normal form. -/
theorem semigroupPred_iff_coeffWitness (gens : List ℕ) (n : ℕ) :
    semigroupPred gens n ↔ coeffWitness gens n := by
  simpa [semigroupPred_iff_mem_closure] using
    (mem_closure_iff_coeffWitness (gens := gens) (n := n))

end GapSetPrime

