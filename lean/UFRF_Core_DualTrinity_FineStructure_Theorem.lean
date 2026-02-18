import Trinity_HalfStep_Dual_Theorem
import Fine_Structure_Internal_Consistency_Theorem

/-!
# UFRF Core (E×B Dual Trinity) -> Fine-Structure Bridge

This file adds an explicit *bridge layer* between:

1. the discrete dual-trinity witness already formalized in this repo
   (`mod 26` as concurrent `(mod 13, mod 2)`), and
2. the fine-structure candidate internal-consistency layer.

The goal is to keep the chain non-placeholder and modular:
- duality witness (discrete),
- geometric decomposition (`4π^3 + π^2 + π`) from named core terms,
- transport to existing numeric anchors (`137 < · < 138`, floor `= 137`).

This is still a formal bridge, not a full continuous E/B field dynamics derivation.
-/

namespace UFRFCoreDualTrinityFineStructure

open TrinityHalfStepDual
open FineStructureCandidate

noncomputable section

/-- Dual-trinity count of concurrent B-planes. -/
def dualPlaneCount : Nat := 2

/-- Angular sweep per B-plane. -/
def bPlaneAngularSpan : ℝ := 2 * Real.pi

/-- Cross-sectional factor per B-plane. -/
def bPlaneCrossSection : ℝ := Real.pi ^ 2

/-- Per-plane geometric contribution. -/
def bPlaneTerm : ℝ := bPlaneAngularSpan * bPlaneCrossSection

/-- Interface contribution in the core decomposition. -/
def interfaceTerm : ℝ := Real.pi ^ 2

/-- Axial contribution in the core decomposition. -/
def axialTerm : ℝ := Real.pi

/-- Core decomposition candidate for `α⁻¹`. -/
def alphaInvFromCore : ℝ :=
  (dualPlaneCount : ℝ) * bPlaneTerm + interfaceTerm + axialTerm

theorem bPlaneTerm_eq : bPlaneTerm = 2 * Real.pi ^ 3 := by
  unfold bPlaneTerm bPlaneAngularSpan bPlaneCrossSection
  ring

theorem dual_trinity_volume_term :
    (dualPlaneCount : ℝ) * bPlaneTerm = 4 * Real.pi ^ 3 := by
  unfold dualPlaneCount
  rw [bPlaneTerm_eq]
  ring

/-- Same cubic term written with an explicit duality-dependent coefficient. -/
theorem cubic_term_from_duality_count :
    (dualPlaneCount : ℝ) * bPlaneTerm = ((dualPlaneCount : ℝ) * 2) * Real.pi ^ 3 := by
  rw [bPlaneTerm_eq]
  ring

theorem cubic_coefficient_eval : ((dualPlaneCount : ℝ) * 2) = (4 : ℝ) := by
  norm_num [dualPlaneCount]

theorem alphaInvFromCore_closed_form :
    alphaInvFromCore = 4 * Real.pi ^ 3 + Real.pi ^ 2 + Real.pi := by
  unfold alphaInvFromCore interfaceTerm axialTerm
  rw [dual_trinity_volume_term]

/--
Coefficient-form version: the cubic coefficient is explicitly the
duality count contribution `dualPlaneCount * 2`.
-/
theorem alphaInvFromCore_coeff_form :
    alphaInvFromCore =
      (((dualPlaneCount : ℝ) * 2) * Real.pi ^ 3) + Real.pi ^ 2 + Real.pi := by
  unfold alphaInvFromCore interfaceTerm axialTerm
  rw [cubic_term_from_duality_count]

theorem alphaInvFromCore_coeff_form_eval :
    alphaInvFromCore =
      (4 : ℝ) * Real.pi ^ 3 + (1 : ℝ) * Real.pi ^ 2 + (1 : ℝ) * Real.pi := by
  calc
    alphaInvFromCore
        = (((dualPlaneCount : ℝ) * 2) * Real.pi ^ 3) + Real.pi ^ 2 + Real.pi :=
          alphaInvFromCore_coeff_form
    _ = (4 : ℝ) * Real.pi ^ 3 + (1 : ℝ) * Real.pi ^ 2 + (1 : ℝ) * Real.pi := by
          simp [cubic_coefficient_eval]

theorem alphaInvFromCore_eq_candidate :
    alphaInvFromCore = alphaInvCandidate := by
  simpa [alphaInvCandidate] using alphaInvFromCore_closed_form

theorem alphaInvFromCore_between_137_and_138 :
    (137 : ℝ) < alphaInvFromCore ∧ alphaInvFromCore < (138 : ℝ) := by
  rw [alphaInvFromCore_eq_candidate]
  exact candidate_between_137_and_138

theorem alphaInvFromCore_floor_eq_137 :
    Int.floor alphaInvFromCore = 137 := by
  rw [alphaInvFromCore_eq_candidate]
  exact floor_candidate_eq_137

theorem alphaInvFromCore_measuredRef_lt :
    alphaInvMeasuredRef < alphaInvFromCore := by
  rw [alphaInvFromCore_eq_candidate]
  exact measuredRef_lt_candidate

/-- Reuse the canonical dual-axis concurrency witness as a core duality anchor. -/
theorem dual_axis_concurrency_witness (a b : Nat) :
    a ≡ b [MOD 26] ↔ (a ≡ b [MOD 13] ∧ a ≡ b [MOD 2]) := by
  simpa using TrinityHalfStepDual.modEq_26_iff_modEq_13_and_modEq_2 a b

/--
End-to-end bridge in one statement:
- duality witness on the discrete side,
- exact equality to the fine-structure candidate,
- numeric anchor and floor anchor.
-/
theorem core_to_finestructure_bridge :
    (∀ a b : Nat, a ≡ b [MOD 26] ↔ (a ≡ b [MOD 13] ∧ a ≡ b [MOD 2]))
    ∧ alphaInvFromCore = alphaInvCandidate
    ∧ (137 : ℝ) < alphaInvFromCore
    ∧ alphaInvFromCore < (138 : ℝ)
    ∧ Int.floor alphaInvFromCore = 137 := by
  constructor
  · intro a b
    exact dual_axis_concurrency_witness a b
  constructor
  · exact alphaInvFromCore_eq_candidate
  constructor
  · exact alphaInvFromCore_between_137_and_138.1
  constructor
  · exact alphaInvFromCore_between_137_and_138.2
  · exact alphaInvFromCore_floor_eq_137

end

end UFRFCoreDualTrinityFineStructure
