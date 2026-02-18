import Mathlib

/-!
# Noether Lens (Discrete): Symmetry = Conservation

This file is a *discrete* formalization of the slogan:

> symmetry and conservation are the same statement, viewed in two directions

We avoid analytic/PDE assumptions. Instead:
- a "symmetry" is modeled as a deterministic state-update map `step : X → X`,
- a "conserved quantity" is an observation `obs : X → Y` that is invariant under `step`.

Then invariance at one step implies invariance at every iterate.

This is the right bridge vocabulary for multiple lanes in this repo:
- tick/axis closure invariance (`Nat/ZMod` orbit closure),
- gauge conjugation invariance (trace/Wilson-loop analogues),
- involution/flip symmetries (expansion↔contraction lenses).

No placeholders.
-/

namespace NoetherDiscrete

/-! ## Step-Invariance as a Conserved Quantity -/

def ConservedUnder {X Y : Type} (step : X → X) (obs : X → Y) : Prop :=
  ∀ x : X, obs (step x) = obs x

theorem conserved_iterate {X Y : Type} (step : X → X) (obs : X → Y)
    (h : ConservedUnder step obs) :
    ∀ (n : Nat) (x : X), obs ((step^[n]) x) = obs x := by
  intro n x
  induction n generalizing x with
  | zero =>
      simp
  | succ n ih =>
      -- `(step^[n+1]) x = (step^[n]) (step x)`; one-step invariance + IH.
      simpa [Function.iterate_succ_apply, h x] using ih (x := step x)

/-! ## Involutions (Flip Symmetries) -/

def IsInvolution {X : Type} (flip : X → X) : Prop :=
  ∀ x : X, flip (flip x) = x

theorem flip_conserved_of_involution {X Y : Type} (flip : X → X) (obs : X → Y)
    (hflip : IsInvolution flip)
    (h : ConservedUnder flip obs) :
    ∀ x : X, obs (flip x) = obs x ∧ obs x = obs (flip x) := by
  intro x
  refine And.intro (h x) ?_
  -- Apply conservation at `flip x` and simplify using involution.
  have := h (flip x)
  simpa [hflip x] using this

end NoetherDiscrete

