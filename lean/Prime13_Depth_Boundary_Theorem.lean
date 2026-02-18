import Mathlib

/-!
# Prime 13 Depth Boundary (Self-Referential Prime at 13^k)

Several repo narratives describe `13, 13^2, 13^3, ...` as *depth boundaries* of a recursive
13-cycle ("index of indexes", simultaneous closings at `13^k`, etc.).

A small but structurally important discrete fact is:

> If a prime divides `13^k`, then that prime must be `13`.

This encodes the sense in which the cycle length being prime makes `13` the unique
"self-recognizing" prime at every depth boundary.

No placeholders.
-/

namespace Prime13DepthBoundary

theorem prime_dvd_13_pow_eq_13 (p k : Nat) (hp : Nat.Prime p) (hk : p ∣ 13 ^ k) : p = 13 := by
  have hdiv : p ∣ 13 := hp.dvd_of_dvd_pow hk
  have h13 : Nat.Prime 13 := by decide
  rcases (Nat.dvd_prime h13).1 hdiv with hp1 | hp13
  · exact (hp.ne_one hp1).elim
  · exact hp13

end Prime13DepthBoundary
