import REST_Seam_Generic_Canonical_Equiv_Theorem

/-!
# REST Seam Transport Core

Canonical seam transport lemmas (state transport only, no classification predicates).
-/

namespace RESTSeamOverlap

theorem state_parent_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    state g (seamTick g r) = 10 + r := by
  have hlt : rest + r < cycle := by
    have hr4 : r < 4 := Nat.lt_of_le_of_lt hr (by decide : 3 < 4)
    have hlt14 : 10 + r < 14 := Nat.add_lt_add_left hr4 10
    simpa [rest, cycle] using hlt14
  rw [state_parent_at_seamTick_mod_via_generic]
  rw [Nat.mod_eq_of_lt hlt]
  simp [rest]

theorem state_child_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    state (g + 1) (seamTick g r) = r := by
  have hlt : r < cycle := by
    have hr4 : r < 4 := Nat.lt_of_le_of_lt hr (by decide : 3 < 4)
    have h4leCycle : 4 ≤ cycle := by
      simp [cycle]
    exact lt_of_lt_of_le hr4 h4leCycle
  rw [state_child_at_seamTick_mod_via_generic]
  exact Nat.mod_eq_of_lt hlt

theorem state_descendant_at_seamTickN (g j r : Nat) :
    state (g + j) (seamTickN g j r) = r % cycle := by
  exact state_descendant_at_seamTickN_mod_via_generic g j r

theorem state_descendant_at_seamTickN_of_le3 (g j r : Nat) (hr : r ≤ 3) :
    state (g + j) (seamTickN g j r) = r := by
  have hlt : r < cycle := by
    have hr4 : r < 4 := Nat.lt_of_le_of_lt hr (by decide : 3 < 4)
    have h4leCycle : 4 ≤ cycle := by
      simp [cycle]
    exact lt_of_lt_of_le hr4 h4leCycle
  simpa [Nat.mod_eq_of_lt hlt] using state_descendant_at_seamTickN g j r

theorem parent_state_eq_rest_add_child_state_at_seamTick (g r : Nat) (hr : r ≤ 3) :
    state g (seamTick g r) = rest + state (g + 1) (seamTick g r) := by
  rw [state_parent_at_seamTick g r hr, state_child_at_seamTick g r hr]
  simp [rest]

theorem parentRest_childVoid_at_seamTick_zero_via_generic (g : Nat) :
    state g (seamTick g 0) = rest ∧ state (g + 1) (seamTick g 0) = 0 := by
  constructor
  · simpa [rest] using state_parent_at_seamTick_mod_via_generic g 0
  · simpa [cycle] using state_child_at_seamTick_mod_via_generic g 0

theorem parentRest_childVoid_at_seamTick_zero (g : Nat) :
    state g (seamTick g 0) = rest ∧ state (g + 1) (seamTick g 0) = 0 := by
  exact parentRest_childVoid_at_seamTick_zero_via_generic g

end RESTSeamOverlap
