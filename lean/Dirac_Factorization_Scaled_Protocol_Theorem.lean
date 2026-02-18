import Dirac_Clifford_Anticommutator_Protocol_Theorem

/-!
# Dirac Factorization (Scaled) Protocol (Finite, Exact)

Lean companion to:
- `dirac_factorization_scaled_protocol.py` -> `dirac_factorization_scaled_results.json`

This is the exact (denominator-cleared) version of the standard identity:
`(γ·p - m)(γ·p + m) = (p^2 - m^2) I`.

We use the same seeded test vector as the AllGreen package:
`p = [2.0, 0.3, -0.1, 0.2]`, `m = 1.0`, but multiply through by `d=10` to avoid rationals.
Then the exact identity over `ℤ[i]` becomes:

Let `p' = [20, 3, -1, 2]`, `m' = 10`, and
`M = 20γ0 - 3γ1 + 1γ2 - 2γ3`.

Then:
`(M - 10I)(M + 10I) = 286 I`.
-/

namespace DiracFactorizationScaledProtocol

open Matrix

local notation "ℤ[i]" => GaussianInt

open DiracCliffordAnticommutatorProtocol

noncomputable section

def M : Matrix Idx Idx ℤ[i] :=
  (20 : ℤ[i]) • γ0 - (3 : ℤ[i]) • γ1 + (1 : ℤ[i]) • γ2 - (2 : ℤ[i]) • γ3

def mScaled : ℤ[i] := 10
def scalarScaled : ℤ[i] := 286

theorem dirac_factorization_scaled_ok :
    (M - mScaled • (1 : Matrix Idx Idx ℤ[i])) *
        (M + mScaled • (1 : Matrix Idx Idx ℤ[i])) =
      scalarScaled • (1 : Matrix Idx Idx ℤ[i]) := by
  native_decide

end

end DiracFactorizationScaledProtocol

