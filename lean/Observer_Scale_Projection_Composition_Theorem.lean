import Mathlib

/-!
# Observer/Scale Projection - Discrete Composition Core

This file formalizes a discrete projection layer that is compatible with the
existing UFRF tick/index work:

- scales live on an integer ladder (`SL : Nat`),
- observer distance is integer difference on that ladder,
- projection is affine in that distance,
- composition across intermediate observers is exact.

No analytic/physical assumptions are introduced.
-/

namespace ObserverScaleProjection

/-- The repository's discrete scale ladder anchor. -/
def scaleM (sl : Nat) : Nat := 144 * 10 ^ sl

/-- Integer observer-distance on the scale ladder. -/
def deltaSL (obs tgt : Nat) : Int := (obs : Int) - (tgt : Int)

/-- Affine projection in a log-like chart (discrete-first core). -/
def project (alpha : Rat) (x : Rat) (d : Int) : Rat := x + alpha * (d : Rat)

/-- Projection using observer/target scale levels. -/
def projectSL (alpha : Rat) (x : Rat) (obs tgt : Nat) : Rat :=
  project alpha x (deltaSL obs tgt)

@[simp] theorem deltaSL_self (s : Nat) : deltaSL s s = 0 := by
  simp [deltaSL]

theorem deltaSL_compose (a b c : Nat) :
    deltaSL a c = deltaSL a b + deltaSL b c := by
  unfold deltaSL
  ring

theorem project_compose (alpha : Rat) (x : Rat) (d1 d2 : Int) :
    project alpha (project alpha x d1) d2 = project alpha x (d1 + d2) := by
  unfold project
  simp [Int.cast_add, mul_add, add_assoc]

theorem projectSL_compose (alpha : Rat) (x : Rat) (obs mid tgt : Nat) :
    projectSL alpha (projectSL alpha x obs mid) mid tgt = projectSL alpha x obs tgt := by
  unfold projectSL
  rw [project_compose]
  rw [← deltaSL_compose obs mid tgt]

@[simp] theorem projectSL_id (alpha : Rat) (x : Rat) (s : Nat) :
    projectSL alpha x s s = x := by
  simp [projectSL, project]

/-- Scale-ladder multiplicative step (discrete analogue of ratio chaining). -/
theorem scaleM_mul_pow_of_le {a b : Nat} (h : a ≤ b) :
    scaleM b = scaleM a * 10 ^ (b - a) := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  simp [scaleM, Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- On the discrete scale ladder, relative ratio is exact power-of-10 shift. -/
theorem scaleM_div_of_le {a b : Nat} (h : a ≤ b) :
    scaleM b / scaleM a = 10 ^ (b - a) := by
  have hmul : scaleM b = scaleM a * 10 ^ (b - a) := scaleM_mul_pow_of_le h
  have hpos : 0 < scaleM a := by
    dsimp [scaleM]
    positivity
  rw [hmul]
  simpa [Nat.mul_comm] using (Nat.mul_div_right (10 ^ (b - a)) hpos)

/-- Ratio chaining across three observer scales is exact on the `scaleM` ladder. -/
theorem scaleM_div_chain_of_le {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    scaleM c / scaleM a = (scaleM c / scaleM b) * (scaleM b / scaleM a) := by
  have hac : a ≤ c := le_trans hab hbc
  rw [scaleM_div_of_le hac, scaleM_div_of_le hbc, scaleM_div_of_le hab]
  have hsub : c - a = (c - b) + (b - a) := by omega
  rw [hsub, Nat.pow_add]

/--
Projection over scale levels decomposes into a base leg plus a correction leg.
This is the affine counterpart of `deltaSL_compose`.
-/
theorem projectSL_split (alpha : Rat) (x : Rat) (obs mid tgt : Nat) :
    projectSL alpha x obs tgt =
      projectSL alpha x obs mid + alpha * (deltaSL mid tgt : Rat) := by
  unfold projectSL project deltaSL
  have hObsTgt :
      ((((obs : Int) - (tgt : Int)) : Int) : Rat) = (obs : Rat) - (tgt : Rat) := by norm_num
  have hObsMid :
      ((((obs : Int) - (mid : Int)) : Int) : Rat) = (obs : Rat) - (mid : Rat) := by norm_num
  have hMidTgt :
      ((((mid : Int) - (tgt : Int)) : Int) : Rat) = (mid : Rat) - (tgt : Rat) := by norm_num
  rw [hObsTgt, hObsMid, hMidTgt]
  ring

/-- Projection offset from base chart is exactly `alpha * deltaSL`. -/
theorem projectSL_sub_base (alpha : Rat) (x : Rat) (obs tgt : Nat) :
    projectSL alpha x obs tgt - x = alpha * (deltaSL obs tgt : Rat) := by
  unfold projectSL project
  ring

/--
For fixed target, observer-to-observer projection difference is independent of `x`
and equals the observer ladder delta scaled by `alpha`.
-/
theorem projectSL_obs_diff (alpha : Rat) (x : Rat) (obs₁ obs₂ tgt : Nat) :
    projectSL alpha x obs₁ tgt - projectSL alpha x obs₂ tgt
      = alpha * (deltaSL obs₁ obs₂ : Rat) := by
  unfold projectSL project deltaSL
  have hObs1Tgt :
      ((((obs₁ : Int) - (tgt : Int)) : Int) : Rat) = (obs₁ : Rat) - (tgt : Rat) := by norm_num
  have hObs2Tgt :
      ((((obs₂ : Int) - (tgt : Int)) : Int) : Rat) = (obs₂ : Rat) - (tgt : Rat) := by norm_num
  have hObs1Obs2 :
      ((((obs₁ : Int) - (obs₂ : Int)) : Int) : Rat) = (obs₁ : Rat) - (obs₂ : Rat) := by norm_num
  rw [hObs1Tgt, hObs2Tgt, hObs1Obs2]
  ring

/--
For fixed observer, target-to-target projection difference is independent of `x`
and equals `alpha` times the negated target ladder delta.
-/
theorem projectSL_tgt_diff (alpha : Rat) (x : Rat) (obs tgt₁ tgt₂ : Nat) :
    projectSL alpha x obs tgt₁ - projectSL alpha x obs tgt₂
      = -alpha * (deltaSL tgt₁ tgt₂ : Rat) := by
  unfold projectSL project deltaSL
  have hObsTgt1 :
      ((((obs : Int) - (tgt₁ : Int)) : Int) : Rat) = (obs : Rat) - (tgt₁ : Rat) := by norm_num
  have hObsTgt2 :
      ((((obs : Int) - (tgt₂ : Int)) : Int) : Rat) = (obs : Rat) - (tgt₂ : Rat) := by norm_num
  have hTgt1Tgt2 :
      ((((tgt₁ : Int) - (tgt₂ : Int)) : Int) : Rat) = (tgt₁ : Rat) - (tgt₂ : Rat) := by norm_num
  rw [hObsTgt1, hObsTgt2, hTgt1Tgt2]
  ring

/-- Translating the base chart translates projected coordinates by the same amount. -/
theorem projectSL_add_base (alpha : Rat) (x c : Rat) (obs tgt : Nat) :
    projectSL alpha (x + c) obs tgt = projectSL alpha x obs tgt + c := by
  unfold projectSL project
  ring

/--
High-level affine package: base offset, observer delta, target delta, and base-translation
are exposed together as one reusable theorem.
-/
theorem projectSL_affine_suite
    (alpha : Rat) (x c : Rat) (obs₁ obs₂ tgt₁ tgt₂ : Nat) :
    (projectSL alpha x obs₁ tgt₁ - x = alpha * (deltaSL obs₁ tgt₁ : Rat))
    ∧ (projectSL alpha x obs₁ tgt₁ - projectSL alpha x obs₂ tgt₁
        = alpha * (deltaSL obs₁ obs₂ : Rat))
    ∧ (projectSL alpha x obs₁ tgt₁ - projectSL alpha x obs₁ tgt₂
        = -alpha * (deltaSL tgt₁ tgt₂ : Rat))
    ∧ (projectSL alpha (x + c) obs₁ tgt₁ = projectSL alpha x obs₁ tgt₁ + c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact projectSL_sub_base alpha x obs₁ tgt₁
  · exact projectSL_obs_diff alpha x obs₁ obs₂ tgt₁
  · exact projectSL_tgt_diff alpha x obs₁ tgt₁ tgt₂
  · exact projectSL_add_base alpha x c obs₁ tgt₁

/--
Observer-difference is translation-invariant in the base chart.
-/
theorem projectSL_obs_diff_add_base
    (alpha : Rat) (x c : Rat) (obs₁ obs₂ tgt : Nat) :
    projectSL alpha (x + c) obs₁ tgt - projectSL alpha (x + c) obs₂ tgt
      = alpha * (deltaSL obs₁ obs₂ : Rat) := by
  exact projectSL_obs_diff alpha (x + c) obs₁ obs₂ tgt

end ObserverScaleProjection
