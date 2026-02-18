import Mathlib.Combinatorics.Enumerative.Catalan

namespace UnityCatalan

open scoped BigOperators

/-
Screenshot anchor: "Catalan = 42 architectures".

In Mathlib, `catalan n` is the nth Catalan number. We certify the concrete value:

  catalan 5 = 42
-/

/-!
The "fractal / nesting" recurrence (self-similar functional equation):

`catalan (n+1)` is an antidiagonal convolution of smaller Catalan numbers.
-/
theorem catalan_fractal_recurrence (n : Nat) :
    catalan (n + 1) = ∑ ij ∈ Finset.antidiagonal n, catalan ij.1 * catalan ij.2 := by
  simpa using catalan_succ' n

theorem catalan_five_eq_42 : catalan 5 = 42 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

end UnityCatalan
