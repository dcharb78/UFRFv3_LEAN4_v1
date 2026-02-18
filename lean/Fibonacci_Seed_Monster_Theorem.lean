/-
# Fibonacci Seed (Monster Identities)

This file captures the **purely arithmetic** part of the "Fibonacci seed" narrative:
the Monster primes `47,59,71` can be written as `(a-1)(b-1)-1` where the factors
`(a-1)` and `(b-1)` are themselves simple linear combinations of Fibonacci numbers.

Nothing here claims any primality mechanism; these are exact equalities.
-/

import Mathlib

namespace FibonacciSeed

/-- Fibonacci numbers with the standard Lean indexing (`fib 0 = 0`, `fib 1 = 1`). -/
abbrev F (n : Nat) : Nat := Nat.fib n

-- Small concrete Fibonacci values (anchors).
theorem F2 : F 2 = 1 := by native_decide
theorem F3 : F 3 = 2 := by native_decide
theorem F4 : F 4 = 3 := by native_decide
theorem F5 : F 5 = 5 := by native_decide
theorem F6 : F 6 = 8 := by native_decide
theorem F7 : F 7 = 13 := by native_decide

-- "Expansion terms" used in the UFRF Frobenius presentation.
theorem term4_eq : F 4 + F 2 = 4 := by native_decide
theorem term6_eq : F 5 + F 2 = 6 := by native_decide
theorem term10_eq : F 6 + F 3 = 10 := by native_decide
theorem term12_eq : F 7 - F 2 = 12 := by native_decide

/--
Monster identity (Seed): `47 = 4 * 12 - 1`, with `4 = F₄ + F₂` and `12 = F₇ - F₂`.
-/
theorem monster47_fib :
    (F 4 + F 2) * (F 7 - F 2) - 1 = 47 := by
  native_decide

/--
Monster identity (Amplify): `59 = 6 * 10 - 1`, with `6 = F₅ + F₂` and `10 = F₆ + F₃`.
-/
theorem monster59_fib :
    (F 5 + F 2) * (F 6 + F 3) - 1 = 59 := by
  native_decide

/--
Monster identity (Harmonize): `71 = 6 * 12 - 1`, with `6 = F₅ + F₂` and `12 = F₇ - F₂`.
-/
theorem monster71_fib :
    (F 5 + F 2) * (F 7 - F 2) - 1 = 71 := by
  native_decide

/--
The same identities in the `(a-1)(b-1)-1` form for the UFRF pairs:
`(5,13) ↦ 47`, `(7,11) ↦ 59`, `(7,13) ↦ 71`.
-/
theorem monster47_pair : (5 - 1) * (13 - 1) - 1 = 47 := by native_decide
theorem monster59_pair : (7 - 1) * (11 - 1) - 1 = 59 := by native_decide
theorem monster71_pair : (7 - 1) * (13 - 1) - 1 = 71 := by native_decide

end FibonacciSeed

