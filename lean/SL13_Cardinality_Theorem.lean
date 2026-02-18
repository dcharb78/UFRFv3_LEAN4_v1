import Mathlib

/-!
# SL13 Cardinality Theorem

Minimal kernel statement that the level index space has exactly 13 states.
This formalizes the "there are 13 SLs" invariant as a finite object.
-/

namespace UFRF

/-- Discrete SL index set (`SL0..SL12`). -/
abbrev SL := Fin 13

theorem sl_cardinality : Fintype.card SL = 13 := by
  native_decide

theorem sl_indices_finRange_length : (List.finRange 13).length = 13 := by
  native_decide

theorem sl_values_bounded (i : SL) : i.1 ≤ 12 := by
  exact Nat.le_pred_of_lt i.2

end UFRF
