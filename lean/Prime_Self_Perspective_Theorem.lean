import Mathlib

/-!
# Prime Self-Perspective Theorem

Discrete "local viewpoint" invariant:
for any positive modulus `n`, self-residue is zero (`n % n = 0`).
Specialized to primes: every prime is in the `0`-state in its own mod-`p` chart.
-/

namespace UFRF

theorem self_mod_zero {n : Nat} (_hn : 0 < n) : n % n = 0 := by
  exact Nat.mod_eq_zero_of_dvd (dvd_refl n)

theorem prime_self_mod_zero {p : Nat} (hp : Nat.Prime p) : p % p = 0 := by
  exact self_mod_zero hp.pos

theorem one_mod_prime_is_one {p : Nat} (hp : Nat.Prime p) : 1 % p = 1 := by
  exact Nat.mod_eq_of_lt hp.one_lt

end UFRF
