import Fine_Structure_Internal_Consistency_Theorem
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Nlinarith
import Mathlib.Tactic.NormNum

/-!
# Fine-Structure (π-Polynomial) Intrinsic Anchor Protocol

This module is the Lean companion to:
- `fine_structure_alpha_intrinsic_protocol.py` -> `fine_structure_alpha_intrinsic_results.json`

It upgrades the coarse `d6`-based bracketing in the internal-consistency layer to a
very tight, mathlib-certified `d20` π-bracket, and derives a stable 9-decimal rounding
anchor for the candidate expression:

`α⁻¹_candidate := 4π^3 + π^2 + π`.

This remains a *protocol anchor*: a deterministic numeric consequence of a closed-form
expression, not a physical derivation from PDE-level axioms.
-/

namespace FineStructureAlphaIntrinsicProtocol

open FineStructureCandidate

noncomputable section

-- These match mathlib's `Real.pi_gt_d20` / `Real.pi_lt_d20` bounds.
def piLo20 : ℝ := 3.14159265358979323846
def piHi20 : ℝ := 3.14159265358979323847

def f (x : ℝ) : ℝ := 4 * x ^ 3 + x ^ 2 + x

lemma f_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : f x ≤ f y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hdiff :
      f y - f x =
        (y - x) * (4 * (y ^ 2 + x * y + x ^ 2) + (y + x) + 1) := by
    unfold f
    ring
  have hnonneg :
      0 ≤ (y - x) * (4 * (y ^ 2 + x * y + x ^ 2) + (y + x) + 1) := by
    apply mul_nonneg
    · linarith
    · have hsum : 0 ≤ (y ^ 2 + x * y + x ^ 2) := by nlinarith
      have hlin : 0 ≤ (y + x) := by linarith
      nlinarith
  have : 0 ≤ f y - f x := by
    simpa [hdiff] using hnonneg
  linarith

lemma pi_bounds_d20 : piLo20 < Real.pi ∧ Real.pi < piHi20 := by
  constructor
  · simpa [piLo20] using Real.pi_gt_d20
  · simpa [piHi20] using Real.pi_lt_d20

def alphaLo : ℝ := f piLo20
def alphaHi : ℝ := f piHi20

lemma alphaInvCandidate_eq_f_pi : alphaInvCandidate = f Real.pi := by
  unfold alphaInvCandidate f
  ring

theorem alphaInvCandidate_between_alphaLo_alphaHi :
    alphaLo ≤ alphaInvCandidate ∧ alphaInvCandidate ≤ alphaHi := by
  have hpi : piLo20 < Real.pi := pi_bounds_d20.1
  have hpi' : Real.pi < piHi20 := pi_bounds_d20.2
  have hlo : piLo20 ≤ Real.pi := le_of_lt hpi
  have hhi : Real.pi ≤ piHi20 := le_of_lt hpi'
  have h0 : (0 : ℝ) ≤ piLo20 := by
    norm_num [piLo20]
  have hl : alphaLo ≤ f Real.pi := by
    -- alphaLo = f(piLo20) ≤ f(pi) using monotonicity
    exact f_mono h0 hlo
  have hh : f Real.pi ≤ alphaHi := by
    -- f(pi) ≤ f(piHi20) using monotonicity
    have h0pi : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    exact f_mono h0pi hhi
  constructor
  · -- alphaLo ≤ alphaInvCandidate
    simpa [alphaLo, alphaInvCandidate_eq_f_pi] using hl
  · -- alphaInvCandidate ≤ alphaHi
    simpa [alphaHi, alphaInvCandidate_eq_f_pi] using hh

-- 9-decimal rounding anchor used in the UFRF docs.
def alphaRound9 : ℝ := (137036303776 : ℝ) / 1000000000

-- Half-ulp for 9-decimal rounding: 0.5e-9 = 1 / 2_000_000_000.
def epsRound9 : ℝ := (1 : ℝ) / 2000000000

lemma alphaRound9_def : alphaRound9 = (137.036303776 : ℝ) := by
  -- `137.036303776` is rational; prove equality by normalization.
  norm_num [alphaRound9]

lemma epsRound9_def : epsRound9 = (5e-10 : ℝ) := by
  norm_num [epsRound9]

theorem alpha_interval_within_eps_of_alphaRound9 :
    alphaRound9 - epsRound9 < alphaLo ∧ alphaHi < alphaRound9 + epsRound9 := by
  constructor
  · -- pure rational inequality
    -- (alphaRound9 - epsRound9) < f(piLo20)
    -- Note: all constants here are rational, so `norm_num` can close it.
    norm_num [alphaLo, alphaRound9, epsRound9, piLo20, f]
  · -- alphaHi < (alphaRound9 + epsRound9)
    norm_num [alphaHi, alphaRound9, epsRound9, piHi20, f]

theorem alphaInvCandidate_within_round9_half_ulp :
    (alphaRound9 - epsRound9) < alphaInvCandidate ∧ alphaInvCandidate < (alphaRound9 + epsRound9) := by
  have hb := alphaInvCandidate_between_alphaLo_alphaHi
  have hwin := alpha_interval_within_eps_of_alphaRound9
  constructor
  · exact lt_of_lt_of_le hwin.1 hb.1
  · exact lt_of_le_of_lt hb.2 hwin.2

end

end FineStructureAlphaIntrinsicProtocol

