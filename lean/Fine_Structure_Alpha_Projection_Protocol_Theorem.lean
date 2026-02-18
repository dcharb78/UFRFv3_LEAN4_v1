import Fine_Structure_Alpha_Intrinsic_Protocol_Theorem
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.NormNum

/-!
# Fine-Structure Projection Correction Protocol (Ratio-First)

Lean companion to:
- `fine_structure_alpha_projection_protocol.py` -> `fine_structure_alpha_projection_results.json`

This is a *protocol scaffold*:
- take the intrinsic candidate `α⁻¹_candidate := 4π^3 + π^2 + π`,
- apply a documented correction factor `c` (ratio-first; √φ is represented by the repo's
  exact rational anchor `159/125`),
- show the projected value lands within a tight epsilon around the fixed measured reference
  used in this repo.

This is not a claim about first-principles physics axioms; it is a deterministic, auditable
numeric bridge consistent with the UFRF projection-law narrative.
-/

namespace FineStructureAlphaProjectionProtocol

open FineStructureCandidate
open FineStructureAlphaIntrinsicProtocol

noncomputable section

-- √φ anchor used elsewhere in this repo (see Tc sqrt(phi) protocol).
def sqrtPhiApprox : ℝ := (159 : ℝ) / 125

-- Document-literal correction factor candidate (ratio-first).
def correctionFactor : ℝ :=
  (9 * 311 : ℝ) /
    (312 * (13 : ℝ) ^ 2 * sqrtPhiApprox * (137 : ℝ) ^ 2)

def alphaProjCandidate : ℝ := alphaInvCandidate * (1 - correctionFactor)

-- Target epsilon for the scaffold claim.
def epsProj : ℝ := (1 : ℝ) / 100000000  -- 1e-8

lemma correctionFactor_pos : 0 < correctionFactor := by
  norm_num [correctionFactor, sqrtPhiApprox]

lemma correctionFactor_lt_one : correctionFactor < 1 := by
  norm_num [correctionFactor, sqrtPhiApprox]

lemma k_nonneg : 0 ≤ (1 - correctionFactor) := by
  have : correctionFactor ≤ 1 := le_of_lt correctionFactor_lt_one
  linarith

theorem alphaProjCandidate_between_proj_bounds :
    (alphaLo * (1 - correctionFactor)) ≤ alphaProjCandidate ∧
      alphaProjCandidate ≤ (alphaHi * (1 - correctionFactor)) := by
  have hb := alphaInvCandidate_between_alphaLo_alphaHi
  have hk : 0 ≤ (1 - correctionFactor) := k_nonneg
  constructor
  · -- lower: alphaLo*(1-c) ≤ alphaInvCandidate*(1-c)
    have hmul : alphaLo * (1 - correctionFactor) ≤ alphaInvCandidate * (1 - correctionFactor) := by
      exact mul_le_mul_of_nonneg_right hb.1 hk
    simpa [alphaProjCandidate] using hmul
  · -- upper
    have hmul : alphaInvCandidate * (1 - correctionFactor) ≤ alphaHi * (1 - correctionFactor) := by
      exact mul_le_mul_of_nonneg_right hb.2 hk
    simpa [alphaProjCandidate] using hmul

theorem alphaProjCandidate_within_eps_of_measuredRef :
    alphaInvMeasuredRef - epsProj < alphaProjCandidate ∧
      alphaProjCandidate < alphaInvMeasuredRef + epsProj := by
  have hb := alphaProjCandidate_between_proj_bounds
  have h_lo : alphaInvMeasuredRef - epsProj < alphaLo * (1 - correctionFactor) := by
    -- All constants are rational (alphaLo is f(piLo20)), so this is decidable by arithmetic.
    norm_num [alphaInvMeasuredRef, epsProj, alphaLo, piLo20, f, correctionFactor, sqrtPhiApprox]
  have h_hi : alphaHi * (1 - correctionFactor) < alphaInvMeasuredRef + epsProj := by
    norm_num [alphaInvMeasuredRef, epsProj, alphaHi, piHi20, f, correctionFactor, sqrtPhiApprox]
  constructor
  · exact lt_of_lt_of_le h_lo hb.1
  · exact lt_of_le_of_lt hb.2 h_hi

end

end FineStructureAlphaProjectionProtocol

