import Pauli_Quaternion_Q8_Gauge_Invariance_Protocol_Theorem

/-!
# Q8 Plaquette Wilson-Loop Gauge Invariance (Finite, Algebraic Scaffold)

Lean companion to:
- `q8_plaquette_wilson_loop_gauge_invariance_protocol.py`
  -> `q8_plaquette_wilson_loop_gauge_invariance_results.json`

We model a single oriented square plaquette with four edge variables
`U01, U12, U23, U30` as `2×2` matrices over `ℤ[i]`.

Given vertex gauge elements `g0,g1,g2,g3 ∈ Q8`, define the usual lattice-gauge
edge update:

`U(st) ↦ g(s) * U(st) * g(t)⁻¹`.

Then the plaquette holonomy transforms by basepoint conjugation:

`U_p' = g0 * U_p * g0⁻¹`.

Therefore the Wilson-loop observable (trace) is invariant:

`tr2(U_p') = tr2(U_p)`.

This is the standard finite algebraic skeleton behind lattice Yang–Mills
gauge invariance, instantiated on the discrete quaternion subgroup `Q8`
already used elsewhere in this repo.

No PDEs. No placeholders.
-/

namespace Q8PlaquetteWilsonLoopGaugeInvarianceProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

open DiracCliffordAnticommutatorProtocol
open PauliQuaternionBridgeProtocol
open PauliQuaternionQ8ClosureProtocol
open PauliQuaternionQ8GaugeInvarianceProtocol

noncomputable section

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℤ[i]

-- Gauge-transform a single oriented edge `s → t`.
def edgeGauge (gSrc gTgt : Fin 8) (U : Mat2) : Mat2 :=
  q8Elem gSrc * U * q8Elem (q8Inv gTgt)

-- An explicit left-associated 4-fold product (so rewriting is predictable).
def plaquette (U01 U12 U23 U30 : Mat2) : Mat2 :=
  (((U01 * U12) * U23) * U30)

theorem plaquette_gauge_eq_conj
    (g0 g1 g2 g3 : Fin 8) (U01 U12 U23 U30 : Mat2) :
    plaquette (edgeGauge g0 g1 U01) (edgeGauge g1 g2 U12) (edgeGauge g2 g3 U23) (edgeGauge g3 g0 U30)
      = conjBy g0 (plaquette U01 U12 U23 U30) := by
  classical
  -- Cancellation identities `g⁻¹ * g = I`.
  have hinv1 : q8Elem (q8Inv g1) * q8Elem g1 = I2 := (q8_inv_ok (i := g1)).2
  have hinv2 : q8Elem (q8Inv g2) * q8Elem g2 = I2 := (q8_inv_ok (i := g2)).2
  have hinv3 : q8Elem (q8Inv g3) * q8Elem g3 = I2 := (q8_inv_ok (i := g3)).2

  -- Step 1: multiply the first two edges and cancel the internal gauge factors.
  have h01 :
      (edgeGauge g0 g1 U01) * (edgeGauge g1 g2 U12)
        = q8Elem g0 * U01 * U12 * q8Elem (q8Inv g2) := by
    unfold edgeGauge
    -- Reassociate to expose `(g1⁻¹ * g1)`.
    -- `(A*B*C) * (D*E*F)` -> `A*B*(C*D)*E*F`.
    calc
      (q8Elem g0 * U01 * q8Elem (q8Inv g1)) * (q8Elem g1 * U12 * q8Elem (q8Inv g2))
          = (q8Elem g0 * U01) * (q8Elem (q8Inv g1) * (q8Elem g1 * U12 * q8Elem (q8Inv g2))) := by
              simp [mul_assoc]
      _ = (q8Elem g0 * U01) * (((q8Elem (q8Inv g1) * q8Elem g1) * U12) * q8Elem (q8Inv g2)) := by
              simp [mul_assoc]
      _ = (q8Elem g0 * U01) * ((I2 * U12) * q8Elem (q8Inv g2)) := by
              simp [hinv1]
      _ = q8Elem g0 * U01 * U12 * q8Elem (q8Inv g2) := by
              simp [mul_assoc]

  -- Step 2: multiply with the third edge and cancel the next internal factor.
  have h012 :
      (q8Elem g0 * U01 * U12 * q8Elem (q8Inv g2)) * (edgeGauge g2 g3 U23)
        = q8Elem g0 * U01 * U12 * U23 * q8Elem (q8Inv g3) := by
    unfold edgeGauge
    calc
      (q8Elem g0 * U01 * U12 * q8Elem (q8Inv g2)) * (q8Elem g2 * U23 * q8Elem (q8Inv g3))
          = (q8Elem g0 * U01 * U12) *
              (q8Elem (q8Inv g2) * (q8Elem g2 * U23 * q8Elem (q8Inv g3))) := by
                simp [mul_assoc]
      _ = (q8Elem g0 * U01 * U12) * (((q8Elem (q8Inv g2) * q8Elem g2) * U23) * q8Elem (q8Inv g3)) := by
                simp [mul_assoc]
      _ = (q8Elem g0 * U01 * U12) * ((I2 * U23) * q8Elem (q8Inv g3)) := by
                simp [hinv2]
      _ = q8Elem g0 * U01 * U12 * U23 * q8Elem (q8Inv g3) := by
                simp [mul_assoc]

  -- Step 3: multiply with the last edge and cancel the final internal factor.
  have h0123 :
      (q8Elem g0 * U01 * U12 * U23 * q8Elem (q8Inv g3)) * (edgeGauge g3 g0 U30)
        = q8Elem g0 * U01 * U12 * U23 * U30 * q8Elem (q8Inv g0) := by
    unfold edgeGauge
    calc
      (q8Elem g0 * U01 * U12 * U23 * q8Elem (q8Inv g3)) * (q8Elem g3 * U30 * q8Elem (q8Inv g0))
          = (q8Elem g0 * U01 * U12 * U23) *
              (q8Elem (q8Inv g3) * (q8Elem g3 * U30 * q8Elem (q8Inv g0))) := by
                simp [mul_assoc]
      _ = (q8Elem g0 * U01 * U12 * U23) * (((q8Elem (q8Inv g3) * q8Elem g3) * U30) * q8Elem (q8Inv g0)) := by
                simp [mul_assoc]
      _ = (q8Elem g0 * U01 * U12 * U23) * ((I2 * U30) * q8Elem (q8Inv g0)) := by
                simp [hinv3]
      _ = q8Elem g0 * U01 * U12 * U23 * U30 * q8Elem (q8Inv g0) := by
                simp [mul_assoc]

  -- Assemble the plaquette identity.
  unfold plaquette
  -- Expand the left-hand side into the same multiplication spine as `h01/h012/h0123`.
  -- Then rewrite by the cancellation lemmas.
  calc
    (((edgeGauge g0 g1 U01 * edgeGauge g1 g2 U12) * edgeGauge g2 g3 U23) * edgeGauge g3 g0 U30)
        = (((q8Elem g0 * U01 * U12 * q8Elem (q8Inv g2)) * edgeGauge g2 g3 U23) * edgeGauge g3 g0 U30) := by
            simp [h01]
    _ = (((q8Elem g0 * U01 * U12 * U23 * q8Elem (q8Inv g3)) * edgeGauge g3 g0 U30)) := by
            simp [h012]
    _ = (q8Elem g0 * U01 * U12 * U23 * U30 * q8Elem (q8Inv g0)) := by
            simp [h0123]
    _ = q8Elem g0 * plaquette U01 U12 U23 U30 * q8Elem (q8Inv g0) := by
            simp [plaquette, mul_assoc]

theorem plaquette_trace_gauge_invariant
    (g0 g1 g2 g3 : Fin 8) (U01 U12 U23 U30 : Mat2) :
    tr2 (plaquette (edgeGauge g0 g1 U01) (edgeGauge g1 g2 U12) (edgeGauge g2 g3 U23) (edgeGauge g3 g0 U30))
      = tr2 (plaquette U01 U12 U23 U30) := by
  -- Reduce to conjugation invariance of the trace at the basepoint.
  have h := plaquette_gauge_eq_conj (g0 := g0) (g1 := g1) (g2 := g2) (g3 := g3)
    (U01 := U01) (U12 := U12) (U23 := U23) (U30 := U30)
  -- Use the already-certified trace invariance under `conjBy g0`.
  -- `q8_tr2_conj_invariant_all` is the key finite Noether-style invariant.
  simpa [h] using (q8_tr2_conj_invariant_all (g := g0) (P := plaquette U01 U12 U23 U30))

end

end Q8PlaquetteWilsonLoopGaugeInvarianceProtocol

