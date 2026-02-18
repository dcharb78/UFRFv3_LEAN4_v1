import Pauli_Quaternion_Q8_Gauge_Invariance_Protocol_Theorem

/-!
# Q8 Closed-Loop Wilson Observable Gauge Invariance (List-Based, Exact)

Lean companion to:
- `q8_wilson_loop_gauge_invariance_protocol.py`
  -> `q8_wilson_loop_gauge_invariance_results.json`

This generalizes the single-plaquette (length-4) Wilson-loop scaffold to *any*
closed loop given as a list of edge variables with a matching list of vertex
gauge elements.

Edge gauge update (oriented source→target):
`U ↦ g_src * U * g_tgt⁻¹`.

For a closed loop, internal gauge factors cancel, yielding basepoint conjugation
of the loop holonomy; therefore `tr2` is invariant.

No PDEs. No placeholders.
-/

namespace Q8WilsonLoopGaugeInvarianceProtocol

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

-- Total last gauge element of the gauge-path representation `(g0, gs)`.
-- If `gs=[]` the last gauge is the start `g0`; otherwise it is the last element of `gs`.
def lastOfCons (g0 : Fin 8) (gs : List (Fin 8)) : Fin 8 :=
  match gs.getLast? with
  | some x => x
  | none => g0

lemma lastOfCons_nil (g0 : Fin 8) : lastOfCons g0 [] = g0 := by
  rfl

lemma lastOfCons_cons (g0 g1 : Fin 8) (gs : List (Fin 8)) :
    lastOfCons g0 (g1 :: gs) = lastOfCons g1 gs := by
  cases gs <;> rfl

-- Left-associated holonomy of a path (list of edge variables).
def holonomy : List Mat2 → Mat2
  | [] => I2
  | U :: Us => U * holonomy Us

-- Gauge-transformed holonomy for a path, represented by:
-- - start gauge `g0`,
-- - list of successive vertex gauges `gs` (targets for each edge),
-- - list of edge variables `Us`.
--
-- Under the length constraint `gs.length = Us.length`, this corresponds to the gauge
-- sequence `g0,g1,...,g_n` where `gs=[g1,...,g_n]`.
def gaugedHolonomy : Fin 8 → List (Fin 8) → List Mat2 → Mat2
  | g0, g1 :: gs, U :: Us => edgeGauge g0 g1 U * gaugedHolonomy g1 gs Us
  | _, _, _ => I2

theorem gaugedHolonomy_eq_open
    (g0 : Fin 8) (gs : List (Fin 8)) (Us : List Mat2)
    (hlen : gs.length = Us.length) :
    gaugedHolonomy g0 gs Us =
      q8Elem g0 * holonomy Us * q8Elem (q8Inv (lastOfCons g0 gs)) := by
  induction Us generalizing g0 gs with
  | nil =>
      -- Then `gs=[]` by the length constraint.
      cases gs with
      | nil =>
          have hinv : q8Elem g0 * q8Elem (q8Inv g0) = I2 := (q8_inv_ok (i := g0)).1
          -- `gaugedHolonomy` defaults to `I2` on empty data; the RHS collapses by `g*g⁻¹=I`.
          simp [gaugedHolonomy, holonomy, edgeGauge, lastOfCons, hinv, mul_assoc]
      | cons g1 gs' =>
          -- Contradiction: `Nat.succ _ = 0`.
          cases hlen
  | cons U Us ih =>
      -- Then `gs = g1::gs'` by the length constraint.
      cases gs with
      | nil =>
          cases hlen
      | cons g1 gs' =>
          have hlen' : gs'.length = Us.length := Nat.succ.inj hlen
          have hinv : q8Elem (q8Inv g1) * q8Elem g1 = I2 := (q8_inv_ok (i := g1)).2
          have htail := ih (g0 := g1) (gs := gs') (hlen := hlen')
          -- One-step cancellation of the internal gauge factors.
          calc
            gaugedHolonomy g0 (g1 :: gs') (U :: Us)
                = edgeGauge g0 g1 U * gaugedHolonomy g1 gs' Us := by
                    simp [gaugedHolonomy, edgeGauge]
            _ = (q8Elem g0 * U * q8Elem (q8Inv g1)) *
                  (q8Elem g1 * holonomy Us * q8Elem (q8Inv (lastOfCons g1 gs'))) := by
                    simp [edgeGauge, htail, mul_assoc]
            _ = q8Elem g0 * U * holonomy Us * q8Elem (q8Inv (lastOfCons g1 gs')) := by
                    -- Reassociate to expose `(g1⁻¹ * g1)`.
                    calc
                      (q8Elem g0 * U * q8Elem (q8Inv g1)) *
                          (q8Elem g1 * holonomy Us * q8Elem (q8Inv (lastOfCons g1 gs')))
                          = q8Elem g0 * U * ((q8Elem (q8Inv g1) * q8Elem g1) * holonomy Us) *
                              q8Elem (q8Inv (lastOfCons g1 gs')) := by
                                simp [mul_assoc]
                      _ = q8Elem g0 * U * ((I2 * holonomy Us)) * q8Elem (q8Inv (lastOfCons g1 gs')) := by
                                simp [hinv]
                      _ = q8Elem g0 * U * holonomy Us * q8Elem (q8Inv (lastOfCons g1 gs')) := by
                                simp [mul_assoc]
            _ = q8Elem g0 * holonomy (U :: Us) * q8Elem (q8Inv (lastOfCons g0 (g1 :: gs'))) := by
                    simp [holonomy, lastOfCons_cons, mul_assoc]

theorem loop_gauge_eq_conj
    (g0 : Fin 8) (gs : List (Fin 8)) (Us : List Mat2)
    (hlen : gs.length = Us.length)
    (hclosed : lastOfCons g0 gs = g0) :
    gaugedHolonomy g0 gs Us = conjBy g0 (holonomy Us) := by
  have hopen := gaugedHolonomy_eq_open (g0 := g0) (gs := gs) (Us := Us) (hlen := hlen)
  -- Closed-loop means the end gauge equals the basepoint gauge.
  simpa [conjBy, hopen, hclosed, mul_assoc]

theorem loop_trace_gauge_invariant
    (g0 : Fin 8) (gs : List (Fin 8)) (Us : List Mat2)
    (hlen : gs.length = Us.length)
    (hclosed : lastOfCons g0 gs = g0) :
    tr2 (gaugedHolonomy g0 gs Us) = tr2 (holonomy Us) := by
  have h := loop_gauge_eq_conj (g0 := g0) (gs := gs) (Us := Us) (hlen := hlen) (hclosed := hclosed)
  -- Reduce to conjugation-invariance of the trace at the basepoint.
  -- `q8_tr2_conj_invariant_all` is the finite Noether-style invariant used throughout this lane.
  simpa [h] using (q8_tr2_conj_invariant_all (g := g0) (P := holonomy Us))

end

end Q8WilsonLoopGaugeInvarianceProtocol

