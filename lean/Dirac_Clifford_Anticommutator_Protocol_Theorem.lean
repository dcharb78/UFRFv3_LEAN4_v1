import Mathlib

/-!
# Dirac Clifford Anticommutator Protocol (Finite, Exact)

Lean companion to:
- `dirac_clifford_anticommutator_protocol.py` -> `dirac_clifford_anticommutator_results.json`

We define the standard Dirac gamma matrices using Pauli blocks, but over **Gaussian integers**
`ℤ[i]` so the verification is exact and fully decidable.

Claim (Clifford algebra with metric diag(1,-1,-1,-1)):
`γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} I`.

This is a *finite algebraic* physics-bridge anchor: no PDEs, no analysis, no floating arithmetic.
-/

namespace DiracCliffordAnticommutatorProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

noncomputable section

def gi : ℤ[i] := ⟨0, 1⟩  -- i

def I2 : Matrix (Fin 2) (Fin 2) ℤ[i] := 1
def Z2 : Matrix (Fin 2) (Fin 2) ℤ[i] := 0

def σx : Matrix (Fin 2) (Fin 2) ℤ[i] :=
  fun i j =>
    if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0

def σy : Matrix (Fin 2) (Fin 2) ℤ[i] :=
  fun i j =>
    if i = 0 ∧ j = 1 then -gi
    else if i = 1 ∧ j = 0 then gi
    else 0

def σz : Matrix (Fin 2) (Fin 2) ℤ[i] :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1
    else if i = 1 ∧ j = 1 then -1
    else 0

abbrev Idx : Type := Fin 2 ⊕ Fin 2

def γ0 : Matrix Idx Idx ℤ[i] :=
  Matrix.fromBlocks I2 Z2 Z2 (-I2)

def γ1 : Matrix Idx Idx ℤ[i] :=
  Matrix.fromBlocks Z2 σx (-σx) Z2

def γ2 : Matrix Idx Idx ℤ[i] :=
  Matrix.fromBlocks Z2 σy (-σy) Z2

def γ3 : Matrix Idx Idx ℤ[i] :=
  Matrix.fromBlocks Z2 σz (-σz) Z2

def γ (μ : Fin 4) : Matrix Idx Idx ℤ[i] :=
  match μ.1 with
  | 0 => γ0
  | 1 => γ1
  | 2 => γ2
  | _ => γ3

def η (μ ν : Fin 4) : ℤ[i] :=
  if h : μ = ν then
    if μ = 0 then 1 else -1
  else
    0

def cliffordEq (μ ν : Fin 4) : Prop :=
  γ μ * γ ν + γ ν * γ μ = (2 * η μ ν) • (1 : Matrix Idx Idx ℤ[i])

theorem dirac_clifford_anticommutator_ok :
    (∀ μ ν : Fin 4, cliffordEq μ ν) := by
  native_decide

end

end DiracCliffordAnticommutatorProtocol

