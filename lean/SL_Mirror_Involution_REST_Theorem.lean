import Mathlib

/-!
# SL Mirror Involution + REST Hub Theorem

Formal kernel model for `CC-0040`:

- mirror pairs: `SL5 ↔ SL6`, `SL4 ↔ SL7`, `SL3 ↔ SL8`
- REST hub: `SL9` is fixed (non-mirrored)
- mirror map is involutive.
-/

namespace SLMirrorREST

/-- Discrete 13-level index space `SL0..SL12`. -/
abbrev SL := Fin 13

def SL3  : SL := ⟨3, by decide⟩
def SL4  : SL := ⟨4, by decide⟩
def SL5  : SL := ⟨5, by decide⟩
def SL6  : SL := ⟨6, by decide⟩
def SL7  : SL := ⟨7, by decide⟩
def SL8  : SL := ⟨8, by decide⟩
def SL9  : SL := ⟨9, by decide⟩

/--
Mirror operator on levels:
- swap the three asserted mirror pairs `(3,8)`, `(4,7)`, `(5,6)`,
- leave all other levels unchanged (in particular, `SL9`).
-/
def mirror (i : SL) : SL :=
  if i = SL3 then SL8 else
  if i = SL8 then SL3 else
  if i = SL4 then SL7 else
  if i = SL7 then SL4 else
  if i = SL5 then SL6 else
  if i = SL6 then SL5 else
  i

theorem mirror_pairings :
    (mirror SL5 = SL6)
  ∧ (mirror SL6 = SL5)
  ∧ (mirror SL4 = SL7)
  ∧ (mirror SL7 = SL4)
  ∧ (mirror SL3 = SL8)
  ∧ (mirror SL8 = SL3) := by
  native_decide

theorem mirror_rest_fixed : mirror SL9 = SL9 := by
  native_decide

/-- The mirror operator is an involution (`mirror ∘ mirror = id`). -/
theorem mirror_involutive : Function.Involutive mirror := by
  intro i
  fin_cases i <;> native_decide

/--
On the core active band plus REST (`SL3..SL9`), the only fixed point is `SL9`.
This formalizes the "non-mirrored REST hub" statement.
-/
def coreBandWithREST : List SL := [SL3, SL4, SL5, SL6, SL7, SL8, SL9]

theorem mirror_fixed_only_rest_on_coreBand :
    ∀ i : SL, i ∈ coreBandWithREST → (mirror i = i ↔ i = SL9) := by
  intro i hi
  fin_cases i <;>
    simp [coreBandWithREST, mirror, SL3, SL4, SL5, SL6, SL7, SL8, SL9] at hi ⊢

/-- Bundled statement for direct reuse in higher-level proof spines. -/
theorem cc0040_bundle :
    Function.Involutive mirror
  ∧ (mirror SL5 = SL6 ∧ mirror SL6 = SL5)
  ∧ (mirror SL4 = SL7 ∧ mirror SL7 = SL4)
  ∧ (mirror SL3 = SL8 ∧ mirror SL8 = SL3)
  ∧ (mirror SL9 = SL9)
  ∧ (∀ i : SL, i ∈ coreBandWithREST → (mirror i = i ↔ i = SL9)) := by
  constructor
  · exact mirror_involutive
  constructor
  · exact ⟨mirror_pairings.1, mirror_pairings.2.1⟩
  constructor
  · exact ⟨mirror_pairings.2.2.1, mirror_pairings.2.2.2.1⟩
  constructor
  · exact ⟨mirror_pairings.2.2.2.2.1, mirror_pairings.2.2.2.2.2⟩
  constructor
  · exact mirror_rest_fixed
  · exact mirror_fixed_only_rest_on_coreBand

end SLMirrorREST
