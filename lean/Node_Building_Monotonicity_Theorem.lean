import CycleStep_Orbit_NAxes_Theorem

/-!
# Node-Building Monotonicity (LCM Closure)

UFRF interpretation:

* A modular axis is a "subsystem" (a clock / cycle / constraint).
* A node is a product of axes (CRT glue).
* The closure time of a step `+s` across axes is an `lcm` of per-axis orbit sizes.
* When we **add axes** (build a larger node), the closure time cannot get smaller:
  the old closure time always divides the new one.
* Reordering axes does not matter: closure time is invariant under `List.Perm`.

All statements here are exact, discrete `Nat` facts (no floats, no axioms).
-/

namespace CycleStepOrbit

/-!
## `lcmList` monotonicity and commutativity lens
-/

theorem lcmList_dvd_of_subset {xs ys : List Nat} (hsub : xs ⊆ ys) : lcmList xs ∣ lcmList ys := by
  refine (lcmList_dvd_iff (xs := xs) (n := lcmList ys)).2 ?_
  intro x hx
  exact dvd_lcmList_of_mem (xs := ys) (hsub hx)

theorem lcmList_dvd_lcmList_append_left (xs ys : List Nat) : lcmList xs ∣ lcmList (xs ++ ys) :=
  lcmList_dvd_of_subset (xs := xs) (ys := xs ++ ys) (by
    intro x hx
    exact List.mem_append.2 (Or.inl hx))

theorem lcmList_dvd_lcmList_append_right (xs ys : List Nat) : lcmList ys ∣ lcmList (xs ++ ys) :=
  lcmList_dvd_of_subset (xs := ys) (ys := xs ++ ys) (by
    intro y hy
    exact List.mem_append.2 (Or.inr hy))

theorem lcmList_perm {xs ys : List Nat} (hperm : xs.Perm ys) : lcmList xs = lcmList ys := by
  apply Nat.dvd_antisymm
  · exact lcmList_dvd_of_subset (xs := xs) (ys := ys) hperm.subset
  · exact lcmList_dvd_of_subset (xs := ys) (ys := xs) hperm.symm.subset

/-!
## `orbitLcm` monotonicity: adding axes builds larger closure periods
-/

theorem orbitLcm_dvd_of_subset {ms ns : List Nat} (hsub : ms ⊆ ns) (s : Nat) :
    orbitLcm ms s ∣ orbitLcm ns s := by
  refine (orbitLcm_dvd_iff (ms := ms) (s := s) (n := orbitLcm ns s)).2 ?_
  intro m hm
  exact orbitSize_dvd_orbitLcm (ms := ns) (s := s) (hsub hm)

theorem orbitLcm_dvd_orbitLcm_append_left (ms more : List Nat) (s : Nat) :
    orbitLcm ms s ∣ orbitLcm (ms ++ more) s :=
  orbitLcm_dvd_of_subset (ms := ms) (ns := ms ++ more)
    (by
      intro m hm
      exact List.mem_append.2 (Or.inl hm))
    s

theorem orbitLcm_dvd_orbitLcm_append_right (ms more : List Nat) (s : Nat) :
    orbitLcm more s ∣ orbitLcm (ms ++ more) s :=
  orbitLcm_dvd_of_subset (ms := more) (ns := ms ++ more)
    (by
      intro m hm
      exact List.mem_append.2 (Or.inr hm))
    s

theorem orbitLcm_perm {ms ns : List Nat} (s : Nat) (hperm : ms.Perm ns) :
    orbitLcm ms s = orbitLcm ns s := by
  unfold orbitLcm
  -- `Perm` respects `map`, and `lcmList` is permutation invariant.
  exact lcmList_perm (hperm := hperm.map (fun m => orbitSize m s))

/-!
## Structural bound: closure time divides the node size

This is the discrete "no overflow beyond the node" statement:
`orbitSize m s ∣ m` for each axis, hence their `lcm` divides the product of moduli.
-/

private theorem dvd_prod_of_mem {m : Nat} {ms : List Nat} (hm : m ∈ ms) : m ∣ ms.prod := by
  induction ms with
  | nil =>
      cases hm
  | cons a ms ih =>
      rcases (List.mem_cons).1 hm with rfl | hm'
      · -- `a ∣ a * ms.prod`.
        simp [List.prod_cons]
      · -- If `m ∣ ms.prod`, then `m ∣ a * ms.prod`.
        have h : m ∣ ms.prod := ih hm'
        have hmul : ms.prod ∣ (a :: ms).prod := by
          simp [List.prod_cons]
        exact Nat.dvd_trans h hmul

theorem orbitLcm_dvd_prod (ms : List Nat) (s : Nat) : orbitLcm ms s ∣ ms.prod := by
  refine (orbitLcm_dvd_iff (ms := ms) (s := s) (n := ms.prod)).2 ?_
  intro m hm
  have h1 : orbitSize m s ∣ m := orbitSize_dvd_modulus m s
  have h2 : m ∣ ms.prod := dvd_prod_of_mem (ms := ms) hm
  exact Nat.dvd_trans h1 h2

end CycleStepOrbit
