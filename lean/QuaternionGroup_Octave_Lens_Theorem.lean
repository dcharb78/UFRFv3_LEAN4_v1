import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Quaternion Group "Octave" Lens (Q8)

This file is a small, **exact** anchor around quaternions that we can reuse in UFRF discussions:

* `QuaternionGroup 2` is a finite group of order `8` (an "octave" of signed units).
* It is **noncommutative** (order matters), while still being associative (it's a group).
* It contains a canonical element of order `4` (a 4-step return), matching the recurring 4-cycle
  motifs we also see in modular / music-theory lenses (e.g. the diminished-chord orbit).

No placeholders.
-/

namespace QuaternionOctaveLens

open QuaternionGroup

-- A packaged statement so we can safely include it in the unified spine.
abbrev q8_card_statement : Prop :=
  Fintype.card (QuaternionGroup 2) = 8

theorem q8_card : q8_card_statement := by
  classical
  haveI : NeZero (2 : Nat) := ⟨by decide⟩
  -- `QuaternionGroup.card` gives `4*n`.
  simpa [q8_card_statement] using (QuaternionGroup.card (n := 2))

abbrev q8_noncomm_statement : Prop :=
  (QuaternionGroup.a (n := 2) 1) * (QuaternionGroup.xa (n := 2) 0) ≠
    (QuaternionGroup.xa (n := 2) 0) * (QuaternionGroup.a (n := 2) 1)

theorem q8_noncomm : q8_noncomm_statement := by
  -- Reduce directly by computation (multiplication is a definition-by-cases).
  native_decide

abbrev q8_order4_statement : Prop :=
  orderOf (QuaternionGroup.xa (n := 2) 0) = 4

theorem q8_order4 : q8_order4_statement := by
  classical
  haveI : NeZero (2 : Nat) := ⟨by decide⟩
  simp [q8_order4_statement]

end QuaternionOctaveLens
