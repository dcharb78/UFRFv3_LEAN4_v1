import CycleStep_Orbit_Theorem

/-!
# Observer Tick = Axis Choice (Discrete, Ratio-Only)

This file packages a core "observer axis-choice" principle in pure `Nat/ZMod` terms:

- return/closure of a tick action is determined by `orbitSize = m / gcd(m,s)`,
- so two axis charts with the same orbit size induce the same closure predicate
  `n • step = 0`,
- scaling both modulus and step by a common factor does not change that predicate.

Interpretation:
- chart coordinates may change (`m, s`),
- but the closure event seen by an observer at tick `n` is invariant under
  ratio-preserving chart changes.

No placeholders.
-/

namespace CycleStepOrbit

/--
General axis-choice equivalence:

If two axis charts `(m₁,s₁)` and `(m₂,s₂)` have the same orbit size, then for every tick count `n`,
closure is equivalent:

`n • (s₁ : ZMod m₁) = 0 ↔ n • (s₂ : ZMod m₂) = 0`.
-/
theorem nsmul_eq_zero_iff_of_orbitSize_eq
    {m₁ s₁ m₂ s₂ n : Nat}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (horb : orbitSize m₁ s₁ = orbitSize m₂ s₂) :
    (n • (s₁ : ZMod m₁) = 0 ↔ n • (s₂ : ZMod m₂) = 0) := by
  constructor
  · intro h1
    have hd1 : orbitSize m₁ s₁ ∣ n :=
      (nsmul_eq_zero_iff_orbitSize_dvd (m := m₁) (s := s₁) (n := n) hm₁).1 h1
    have hd2 : orbitSize m₂ s₂ ∣ n := by
      simpa [horb] using hd1
    exact (nsmul_eq_zero_iff_orbitSize_dvd (m := m₂) (s := s₂) (n := n) hm₂).2 hd2
  · intro h2
    have hd2 : orbitSize m₂ s₂ ∣ n :=
      (nsmul_eq_zero_iff_orbitSize_dvd (m := m₂) (s := s₂) (n := n) hm₂).1 h2
    have hd1 : orbitSize m₁ s₁ ∣ n := by
      simpa [horb] using hd2
    exact (nsmul_eq_zero_iff_orbitSize_dvd (m := m₁) (s := s₁) (n := n) hm₁).2 hd1

/--
Ratio-only restatement:

The same equivalence as `nsmul_eq_zero_iff_of_orbitSize_eq`, written directly with
the normalized ratio formula `m / gcd(m,s)`.
-/
theorem nsmul_eq_zero_iff_of_ratio_eq
    {m₁ s₁ m₂ s₂ n : Nat}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hratio : m₁ / Nat.gcd m₁ s₁ = m₂ / Nat.gcd m₂ s₂) :
    (n • (s₁ : ZMod m₁) = 0 ↔ n • (s₂ : ZMod m₂) = 0) := by
  exact nsmul_eq_zero_iff_of_orbitSize_eq hm₁ hm₂ (by simpa [orbitSize] using hratio)

/--
Scale-preserving chart change:

If we scale both modulus and step by the same positive factor `k`,
the closure predicate is unchanged for every `n`.
-/
theorem nsmul_eq_zero_iff_scaled_axis
    {k m s n : Nat}
    (hk : 0 < k) (hm : 0 < m) :
    (n • ((k * s : Nat) : ZMod (k * m)) = 0 ↔ n • (s : ZMod m) = 0) := by
  have hkm : 0 < k * m := Nat.mul_pos hk hm
  have horb : orbitSize (k * m) (k * s) = orbitSize m s :=
    orbitSize_scale_invariant (k := k) (m := m) (s := s) hk
  exact nsmul_eq_zero_iff_of_orbitSize_eq (m₁ := k * m) (s₁ := k * s) (m₂ := m) (s₂ := s)
    hkm hm horb

end CycleStepOrbit

