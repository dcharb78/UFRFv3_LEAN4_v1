import Mathlib.Algebra.Order.Group.Abs

/-!
# Nearest-Point Distance Monotonicity (Interpretation Guard)

This file proves a small, foundational fact used when interpreting "nearest lattice distance"
computations such as `lean/Riemann_Zero_Exclusion_Theorem.lean`:

Adding more candidate points cannot increase the nearest-point distance.

We state this for the absolute-difference distance in any linear ordered additive group.
No placeholders.
-/

namespace LatticeDistanceMonotonicity

variable {α : Type*} [LinearOrder α] [AddGroup α]

/-- Absolute-difference distance. -/
def dist (x y : α) : α := |x - y|

/--
Fold a list of points into a "nearest distance" value by repeated `min`.

`init` plays the role of an initial "upper bound" (in computations this is often a large number).
The monotonicity theorems below hold for any `init`.
-/
def nearestDist (x : α) (points : List α) (init : α) : α :=
  points.foldr (fun p md => min md (dist x p)) init

theorem nearestDist_cons_le (x p : α) (points : List α) (init : α) :
    nearestDist x (p :: points) init ≤ nearestDist x points init := by
  -- `min a b ≤ a`
  simp [nearestDist, dist]

/--
Prepending more points (i.e. giving the observer more lattice candidates) cannot increase the
nearest distance.
-/
theorem nearestDist_prepend_le (x : α) (more points : List α) (init : α) :
    nearestDist x (more ++ points) init ≤ nearestDist x points init := by
  induction more with
  | nil =>
      simp [nearestDist]
  | cons p more ih =>
      have h1 :
          nearestDist x (p :: (more ++ points)) init ≤ nearestDist x (more ++ points) init := by
        simpa using (nearestDist_cons_le (x := x) (p := p) (points := more ++ points) (init := init))
      exact le_trans h1 ih

end LatticeDistanceMonotonicity
