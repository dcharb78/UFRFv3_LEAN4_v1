import Mathlib

/-!
# Wallis Product (π/2) Anchor

This file adds one fully formal, non-empirical "infinite series / convergence" anchor
that matches the narrative in the UFRF synthesis notes:

* the classical Wallis product partial products `Real.Wallis.W k` converge to `π/2`.

Nothing here is claimed to be uniquely "UFRF"; it is a standard Mathlib theorem.
We keep it as a clean convergence certificate that can be referenced when discussing
"exact local bracketing factors accumulating to a global constant".
-/

namespace WallisProduct

open scoped Topology
open Filter

/-- Wallis' product formula: the partial products converge to `π/2`. -/
theorem wallis_tendsto_pi_div_two : Tendsto Real.Wallis.W atTop (𝓝 (Real.pi / 2)) := by
  -- `Real.Wallis.tendsto_W_nhds_pi_div_two` is the Mathlib proof.
  simpa using (Real.Wallis.tendsto_W_nhds_pi_div_two)

end WallisProduct

