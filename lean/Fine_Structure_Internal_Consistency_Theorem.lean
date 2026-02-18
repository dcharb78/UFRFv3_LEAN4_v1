import Mathlib

/-!
# Fine-Structure Candidate (Internal Consistency Only)

This file formalizes the *candidate* inverse fine-structure expression

`α⁻¹_candidate = 4π^3 + π^2 + π`

as an exact real expression and proves internal-consistency facts:
- exact algebraic rewrites,
- positivity,
- numeric bracketing (`137 < α⁻¹_candidate < 138`),
- integer floor anchor (`⌊α⁻¹_candidate⌋ = 137`).

This is intentionally a math-only layer. It does **not yet** derive the candidate
from the UFRF core first principles (E×B dual trinity).
-/

namespace FineStructureCandidate

noncomputable section

/-- UFRF candidate for the inverse fine-structure constant. -/
def alphaInvCandidate : ℝ := 4 * Real.pi ^ 3 + Real.pi ^ 2 + Real.pi

/-- Reference measured value used as a fixed comparison constant. -/
def alphaInvMeasuredRef : ℝ := 137.035999084

/-- Structural split used in UFRF prose: `4π^3 = 2π^3 + 2π^3`. -/
theorem dual_bfield_split :
    4 * Real.pi ^ 3 = 2 * Real.pi ^ 3 + 2 * Real.pi ^ 3 := by
  ring

/-- Candidate expression rewritten to emphasize the dual `2π^3` contribution. -/
theorem candidate_rewrite_dual_bfield :
    alphaInvCandidate = (2 * Real.pi ^ 3 + 2 * Real.pi ^ 3) + Real.pi ^ 2 + Real.pi := by
  unfold alphaInvCandidate
  ring

/-- Basic positivity of the candidate expression. -/
theorem candidate_pos : 0 < alphaInvCandidate := by
  unfold alphaInvCandidate
  nlinarith [Real.pi_pos]

/-- Tight decimal bracket from mathlib's `π` bounds at 6 decimals. -/
theorem candidate_between_137_and_138 :
    (137 : ℝ) < alphaInvCandidate ∧ alphaInvCandidate < (138 : ℝ) := by
  unfold alphaInvCandidate
  have hpi_low : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hpi_high : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  constructor
  · nlinarith [hpi_low]
  · nlinarith [hpi_high]

/-- Integer anchor implied by the bracket: `⌊α⁻¹_candidate⌋ = 137`. -/
theorem floor_candidate_eq_137 : Int.floor alphaInvCandidate = 137 := by
  refine (Int.floor_eq_iff).2 ?_
  constructor
  · change ((137 : ℤ) : ℝ) ≤ alphaInvCandidate
    exact le_of_lt candidate_between_137_and_138.1
  · have h : alphaInvCandidate < (138 : ℝ) := candidate_between_137_and_138.2
    have hcast : (((137 : ℤ) : ℝ) + 1) = (138 : ℝ) := by norm_num
    exact hcast ▸ h

/-- Difference between the candidate and the fixed comparison value. -/
def measuredOffset : ℝ := alphaInvCandidate - alphaInvMeasuredRef

/-- The fixed reference value lies below the candidate. -/
theorem measuredOffset_pos : 0 < measuredOffset := by
  unfold measuredOffset alphaInvCandidate alphaInvMeasuredRef
  have hpi_low : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  nlinarith [hpi_low]

theorem measuredRef_lt_candidate : alphaInvMeasuredRef < alphaInvCandidate := by
  simpa [measuredOffset] using measuredOffset_pos

end

end FineStructureCandidate
