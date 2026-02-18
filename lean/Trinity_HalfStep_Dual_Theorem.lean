import System_Node_ModProd_Theorem

/-!
# Trinity Half-Step Dual (0.5, 0, -0.5) as a Concurrent Axis

This file is intentionally small and algebraic.

It formalizes one concrete way to model the "half-step" / "dual" viewpoint:

* A 13-cycle with a half-step refinement is a 26-cycle (`2 * 13`).
* The 26-cycle is a *concurrent product system* of:
  - the mod-13 phase (cycle axis), and
  - the mod-2 parity (half-step axis).

This matches the narrative that a system has multiple simultaneous coordinates (concurrent axes).
Here the extra axis is exactly the "±0.5" refinement over the integer phase positions.

No placeholders: everything here is exact arithmetic / CRT.
-/

namespace TrinityHalfStepDual

open scoped Function -- for `on` in the imported CRT helper

def baseCycle : Nat := 13
def halfCycle : Nat := 2 * baseCycle -- 26

/-- The half-step index for an integer position `k`: `k + 0.5` corresponds to `2k+1` in the 26-cycle. -/
def halfIndex (k : Nat) : Nat := 2 * k + 1

theorem halfCycle_eq : halfCycle = 26 := by
  simp [halfCycle, baseCycle]

theorem halfIndex_flip : halfIndex 6 = 13 := by
  native_decide

theorem halfIndex_is_odd (k : Nat) : halfIndex k % 2 = 1 := by
  -- `(2k+1) % 2 = 1`.
  have hmul : (2 * k) % 2 = 0 := by
    calc
      (2 * k) % 2 = ((2 % 2) * (k % 2)) % 2 := by
        simp
      _ = 0 := by simp
  calc
    (2 * k + 1) % 2 = ((2 * k) % 2 + 1 % 2) % 2 := by
      simp [Nat.add_mod]
    _ = (0 + 1) % 2 := by
      simp [hmul]
    _ = 1 := by simp

/--
CRT concurrency for the half-step refinement:

Congruence mod `26` is equivalent to congruence mod `13` AND congruence mod `2`.
-/
theorem modEq_26_iff_modEq_13_and_modEq_2 (a b : Nat) :
    a ≡ b [MOD 26] ↔ (a ≡ b [MOD 13] ∧ a ≡ b [MOD 2]) := by
  have hcop : ([13, 2] : List Nat).Pairwise Nat.Coprime := by decide
  have h :=
    SystemNodeModProd.modEq_prod_iff_forall_mem (a := a) (b := b) (ms := ([13, 2] : List Nat)) hcop
  -- Unpack the list-quantified statement into a conjunction over the two axes.
  constructor
  · intro hab
    have hall : ∀ m ∈ ([13, 2] : List Nat), a ≡ b [MOD m] := (h).1 (by simpa using hab)
    exact ⟨hall 13 (by simp), hall 2 (by simp)⟩
  · rintro ⟨h13, h2⟩
    have hall : ∀ m ∈ ([13, 2] : List Nat), a ≡ b [MOD m] := by
      intro m hm
      have : m = 13 ∨ m = 2 := by simpa using hm
      rcases this with rfl | rfl
      · exact h13
      · exact h2
    -- Repack to the product modulus.
    have : a ≡ b [MOD ([13, 2] : List Nat).prod] := (h).2 hall
    simpa using this

/--
The "flip" element `13` is exactly:
- source on the mod-13 axis, and
- half-step (`1`) on the mod-2 axis.

So it is the unique nontrivial element in the kernel of the `mod 13` projection, carrying the dual parity bit.
-/
theorem flip_axis_signature :
    (13 ≡ 0 [MOD 13]) ∧ (13 ≡ 1 [MOD 2]) := by
  constructor <;> native_decide

end TrinityHalfStepDual
