import Pauli_Quaternion_Q8_Closure_Protocol_Theorem
import Noether_Symmetry_Conservation_Lens_Theorem

/-!
# Pauli→Quaternion Q8 Gauge-Invariance Scaffold (Finite, Exact)

Lean companion to:
- `pauli_quaternion_q8_gauge_invariance_protocol.py` -> `pauli_quaternion_q8_gauge_invariance_results.json`

We work with the discrete quaternion subgroup:
`Q8 := {±I, ±qi, ±qj, ±qk}` realized as `2×2` matrices over `ℤ[i]`.

Define a concrete `2×2` trace:
`tr2(A) := A₀₀ + A₁₁`.

Gauge-invariance scaffold (finite Wilson-loop analogue):
`tr2(g * P * g⁻¹) = tr2(P)`.

We certify this exactly for all `g,P` in the 8-element enumeration, using an explicit inverse map.

No placeholders.
-/

namespace PauliQuaternionQ8GaugeInvarianceProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

open DiracCliffordAnticommutatorProtocol
open PauliQuaternionBridgeProtocol
open PauliQuaternionQ8ClosureProtocol

noncomputable section

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℤ[i]

def tr2 (A : Mat2) : ℤ[i] := A 0 0 + A 1 1

lemma tr2_eq_trace (A : Mat2) : tr2 A = Matrix.trace A := by
  classical
  -- `Matrix.trace` is the sum of diagonal entries; for `Fin 2` it is `A00 + A11`.
  simp [tr2, Matrix.trace]

-- Explicit inverse on the 8 signed units (matches the Q8 group inverse).
def q8Inv : Fin 8 → Fin 8
  | ⟨0, h⟩ => ⟨0, by decide⟩
  | ⟨1, h⟩ => ⟨1, by decide⟩
  | ⟨2, h⟩ => ⟨3, by decide⟩
  | ⟨3, h⟩ => ⟨2, by decide⟩
  | ⟨4, h⟩ => ⟨5, by decide⟩
  | ⟨5, h⟩ => ⟨4, by decide⟩
  | ⟨6, h⟩ => ⟨7, by decide⟩
  | ⟨7, h⟩ => ⟨6, by decide⟩

theorem q8_inv_ok :
    (∀ i : Fin 8, q8Elem i * q8Elem (q8Inv i) = I2 ∧ q8Elem (q8Inv i) * q8Elem i = I2) := by
  fin_cases i <;> native_decide

theorem q8_tr2_conj_invariant :
    (∀ g P : Fin 8, tr2 (q8Elem g * q8Elem P * q8Elem (q8Inv g)) = tr2 (q8Elem P)) := by
  fin_cases g <;> fin_cases P <;> native_decide

-- Strengthening: the same conjugation-invariance holds for *any* `2×2` matrix `P`
-- once we know the explicit inverse law `g⁻¹*g = I`.
theorem q8_tr2_conj_invariant_all (g : Fin 8) (P : Mat2) :
    tr2 (q8Elem g * P * q8Elem (q8Inv g)) = tr2 P := by
  classical
  have hpair := q8_inv_ok (i := g)
  have hinv : q8Elem (q8Inv g) * q8Elem g = I2 := hpair.2
  -- Convert to `Matrix.trace` and use cyclicity of trace.
  have htrace :
      Matrix.trace (q8Elem g * P * q8Elem (q8Inv g)) = Matrix.trace P := by
    calc
      Matrix.trace (q8Elem g * P * q8Elem (q8Inv g))
          = Matrix.trace ((q8Elem g * P) * q8Elem (q8Inv g)) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace (q8Elem (q8Inv g) * (q8Elem g * P)) := by
              simpa [Matrix.mul_assoc] using
                (Matrix.trace_mul_comm (A := (q8Elem g * P)) (B := q8Elem (q8Inv g)))
      _ = Matrix.trace ((q8Elem (q8Inv g) * q8Elem g) * P) := by
              simp [Matrix.mul_assoc]
      _ = Matrix.trace (I2 * P) := by
              simp [hinv]
      _ = Matrix.trace P := by simp
  -- Translate the `trace` statement back to our concrete `tr2`.
  simpa [tr2_eq_trace] using htrace

def conjBy (g : Fin 8) (P : Mat2) : Mat2 :=
  q8Elem g * P * q8Elem (q8Inv g)

theorem q8_tr2_conj_conserved_iterate (g : Fin 8) (P : Mat2) (n : Nat) :
    tr2 ((conjBy g)^[n] P) = tr2 P := by
  -- Noether lens: one-step invariance implies invariance at every iterate.
  have h : NoetherDiscrete.ConservedUnder (conjBy g) tr2 := by
    intro x
    simpa [conjBy] using q8_tr2_conj_invariant_all (g := g) (P := x)
  simpa using (NoetherDiscrete.conserved_iterate (step := conjBy g) (obs := tr2) h n P)

end

end PauliQuaternionQ8GaugeInvarianceProtocol
