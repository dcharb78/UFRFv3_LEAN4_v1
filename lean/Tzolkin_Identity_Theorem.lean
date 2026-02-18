import Mathlib

/-!
# Tzolkin Identity Theorem

Kernel arithmetic identity used in the cycle inventory:
`260 = 13 * 20`.
-/

namespace UFRF

theorem tzolkin_identity_nat : (260 : Nat) = 13 * 20 := by
  native_decide

theorem tzolkin_identity_int : (260 : Int) = 13 * 20 := by
  norm_num

end UFRF
