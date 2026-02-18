import Mathlib

/-!
# Discrete Angular Embedding Quotient (Antipodal Observer Identification)

This is a **discrete proxy** for the "angular embedding" narrative:

- model 4 quadrants as `Fin 4`,
- identify the antipodal observer positions (`0` and `2`),
- show the resulting quotient has exactly **3** equivalence classes.

The construction is finite and exact, and is intended as a stable Lean anchor that:
- avoids continuous geometry assumptions (`S¹` embedding), and
- matches the repo-wide discrete-first policy.

No placeholders.
-/

namespace AngularEmbeddingDiscreteQuotient

abbrev Quadrant : Type := Fin 4
abbrev Manifold : Type := Fin 3

/--
Collapse the two observer quadrants `0` and `2` into one class.

Intuition (coarse proxy):
- `0` = observer start (0°),
- `2` = observer flip (180°),
- `1` and `3` remain distinct pole-side quadrants.
-/
def toManifold (q : Quadrant) : Manifold :=
  match q.val with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | _ => 2

theorem toManifold_surjective : Function.Surjective toManifold := by
  intro y
  fin_cases y
  · refine ⟨(0 : Quadrant), ?_⟩
    native_decide
  · refine ⟨(1 : Quadrant), ?_⟩
    native_decide
  · refine ⟨(3 : Quadrant), ?_⟩
    native_decide

/-! ## Kernel Relation and Quotient -/

/-- Identification relation: two quadrants are equivalent iff they map to the same manifold. -/
def rel (a b : Quadrant) : Prop := toManifold a = toManifold b

theorem rel_refl (a : Quadrant) : rel a a := by
  rfl

theorem rel_symm {a b : Quadrant} : rel a b → rel b a := by
  intro h
  exact h.symm

theorem rel_trans {a b c : Quadrant} : rel a b → rel b c → rel a c := by
  intro hab hbc
  exact hab.trans hbc

def relSetoid : Setoid Quadrant :=
  { r := rel
    iseqv := ⟨rel_refl, @rel_symm, @rel_trans⟩ }

abbrev Quot : Type := Quotient relSetoid

/-- The canonical map from the quotient to the 3-manifold index set. -/
def quotToManifold : Quot → Manifold :=
  Quotient.lift toManifold (by
    intro a b hab
    exact hab)

theorem quotToManifold_bijective : Function.Bijective quotToManifold := by
  refine ⟨?_, ?_⟩
  · -- injective
    intro x y hxy
    have hinj :
        quotToManifold x = quotToManifold y → x = y :=
      Quotient.inductionOn₂ x y (fun a b => by
        intro hab
        apply Quotient.sound
        -- `hab` is exactly the kernel relation.
        simpa [quotToManifold, rel] using hab)
    exact hinj hxy
  · -- surjective
    intro y
    rcases toManifold_surjective y with ⟨q, hq⟩
    refine ⟨Quotient.mk _ q, ?_⟩
    simp [quotToManifold, hq]

noncomputable def quotEquivManifold : Quot ≃ Manifold :=
  Equiv.ofBijective quotToManifold quotToManifold_bijective

noncomputable instance : Fintype Quot :=
  Fintype.ofEquiv Manifold quotEquivManifold.symm

theorem quotient_card_three : Fintype.card Quot = 3 := by
  classical
  simpa using (Fintype.card_congr quotEquivManifold)

/-- One stable conjunct for the unified bundle. -/
def angular_embedding_discrete_summary : Prop :=
  Fintype.card Quot = 3

theorem angular_embedding_discrete_summary_proof : angular_embedding_discrete_summary := by
  simpa [angular_embedding_discrete_summary] using quotient_card_three

end AngularEmbeddingDiscreteQuotient
