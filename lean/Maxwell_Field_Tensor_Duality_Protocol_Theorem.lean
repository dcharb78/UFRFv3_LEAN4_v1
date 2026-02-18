import Mathlib

/-!
# Maxwell Field-Tensor Encoding + Duality Protocol (Finite, Algebraic Scaffold)

Lean companion to:
- `maxwell_field_tensor_duality_protocol.py` -> `maxwell_field_tensor_duality_results.json`

We encode an EM state by 6 components (E,B) in natural units (`c=1`) and build:
- an explicit antisymmetric `4×4` field tensor `F`,
- an explicit “duality” operator `⋆` on the 6D (E,B) space: `⋆(E,B) = (B, -E)`,
  with `⋆⋆ = -1` (a 2-step dual rotation giving a sign flip).

This is an algebraic anchor for the E/B dual-plane structure (no PDEs, no analysis).

No placeholders.
-/

namespace MaxwellFieldTensorDualityProtocol

structure EM6 (α : Type) where
  ex : α
  ey : α
  ez : α
  bx : α
  by : α
  bz : α

namespace EM6

variable {α : Type}

def dual [Ring α] (em : EM6 α) : EM6 α :=
  { ex := em.bx
    ey := em.by
    ez := em.bz
    bx := -em.ex
    by := -em.ey
    bz := -em.ez }

def neg [Neg α] (em : EM6 α) : EM6 α :=
  { ex := -em.ex
    ey := -em.ey
    ez := -em.ez
    bx := -em.bx
    by := -em.by
    bz := -em.bz }

theorem dual_dual [Ring α] (em : EM6 α) : dual (dual em) = neg em := by
  cases em <;> simp [dual, neg]

end EM6

open EM6

-- Explicit field tensor encoding (one fixed convention):
-- Electric components in row/col `0i`, magnetic components on spatial bivectors.
def toF {α : Type} [Ring α] (em : EM6 α) : Matrix (Fin 4) (Fin 4) α :=
  fun i j =>
    match i.1, j.1 with
    | 0, 1 => em.ex
    | 1, 0 => -em.ex
    | 0, 2 => em.ey
    | 2, 0 => -em.ey
    | 0, 3 => em.ez
    | 3, 0 => -em.ez
    | 2, 3 => em.bx
    | 3, 2 => -em.bx
    | 3, 1 => em.by
    | 1, 3 => -em.by
    | 1, 2 => em.bz
    | 2, 1 => -em.bz
    | _, _ => 0

theorem toF_antisymm {α : Type} [Ring α] (em : EM6 α) :
    ∀ i j : Fin 4, toF em i j = -toF em j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [toF]

end MaxwellFieldTensorDualityProtocol

