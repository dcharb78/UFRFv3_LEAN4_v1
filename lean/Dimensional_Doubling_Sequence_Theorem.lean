import Mathlib

/-!
# Dimensional Doubling Sequence Theorem

Kernel formalization of `CC-0010`:

`D(n) = 13 * 2^(n-1)` for `n ≥ 1`, with witness values
`D(1..5) = [13,26,52,104,208]`.
-/

namespace UFRF

/-- Dimensional doubling law with base seed `13`. -/
def dimensionalDoubling (n : Nat) : Nat :=
  13 * 2 ^ (n - 1)

theorem dimensionalDoubling_n1 : dimensionalDoubling 1 = 13 := by
  native_decide

theorem dimensionalDoubling_n2 : dimensionalDoubling 2 = 26 := by
  native_decide

theorem dimensionalDoubling_n3 : dimensionalDoubling 3 = 52 := by
  native_decide

theorem dimensionalDoubling_n4 : dimensionalDoubling 4 = 104 := by
  native_decide

theorem dimensionalDoubling_n5 : dimensionalDoubling 5 = 208 := by
  native_decide

theorem dimensionalDoubling_first_five :
    [dimensionalDoubling 1,
     dimensionalDoubling 2,
     dimensionalDoubling 3,
     dimensionalDoubling 4,
     dimensionalDoubling 5] = [13, 26, 52, 104, 208] := by
  native_decide

end UFRF
