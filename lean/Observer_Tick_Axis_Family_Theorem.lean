import Observer_Tick_Axis_Choice_Theorem
import CycleStep_Orbit_NAxes_Theorem

/-!
# Observer Tick = Axis Choice (Finite Family / Subsystem Node)

This file lifts single-axis chart-change invariance to a finite subsystem list.

Core idea:
- if each axis `m` sees the same orbit size under two observer-step charts `s₁, s₂`,
- then the composite node `ZMod ms.prod` has the same closure events at every tick `n`.

No placeholders.
-/

namespace CycleStepOrbit

/--
If two observer-step charts `s₁, s₂` induce the same per-axis orbit size across a finite axis list,
their synchronizing `orbitLcm` values are equal.
-/
theorem orbitLcm_eq_of_forall_mem_orbitSize_eq
    (ms : List Nat) {s₁ s₂ : Nat}
    (hEq : ∀ m ∈ ms, orbitSize m s₁ = orbitSize m s₂) :
    orbitLcm ms s₁ = orbitLcm ms s₂ := by
  apply Nat.dvd_antisymm
  · refine (orbitLcm_dvd_iff (ms := ms) (s := s₁) (n := orbitLcm ms s₂)).2 ?_
    intro m hm
    have h2 : orbitSize m s₂ ∣ orbitLcm ms s₂ :=
      orbitSize_dvd_orbitLcm (ms := ms) (s := s₂) hm
    simpa [hEq m hm] using h2
  · refine (orbitLcm_dvd_iff (ms := ms) (s := s₂) (n := orbitLcm ms s₁)).2 ?_
    intro m hm
    have h1 : orbitSize m s₁ ∣ orbitLcm ms s₁ :=
      orbitSize_dvd_orbitLcm (ms := ms) (s := s₁) hm
    simpa [hEq m hm] using h1

/--
Finite-family chart-change invariance on the subsystem node:

Assume:
- pairwise-coprime axes `ms` (CRT node),
- positive moduli,
- pointwise orbit-size equality under two step charts `s₁, s₂`.

Then for every tick count `n`, closure is equivalent on the node chart:
`n • (s₁ : ZMod ms.prod) = 0 ↔ n • (s₂ : ZMod ms.prod) = 0`.
-/
theorem nsmul_eq_zero_iff_prod_of_forall_mem_orbitSize_eq
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hEq : ∀ m ∈ ms, orbitSize m s₁ = orbitSize m s₂) :
    (n • (s₁ : ZMod ms.prod) = 0 ↔ n • (s₂ : ZMod ms.prod) = 0) := by
  have hmprod : 0 < ms.prod := prod_pos_of_forall_mem_pos ms hpos
  have hOrbEq : orbitSize ms.prod s₁ = orbitSize ms.prod s₂ := by
    calc
      orbitSize ms.prod s₁ = orbitLcm ms s₁ := by
        simpa using (orbitSize_prod_eq_orbitLcm_of_pairwise_coprime ms hcop s₁ hpos)
      _ = orbitLcm ms s₂ := orbitLcm_eq_of_forall_mem_orbitSize_eq ms hEq
      _ = orbitSize ms.prod s₂ := by
        simpa using (orbitSize_prod_eq_orbitLcm_of_pairwise_coprime ms hcop s₂ hpos).symm
  exact nsmul_eq_zero_iff_of_orbitSize_eq
    (m₁ := ms.prod) (s₁ := s₁) (m₂ := ms.prod) (s₂ := s₂) (n := n)
    hmprod hmprod hOrbEq

/--
Ratio-only version of finite-family chart-change invariance:
pointwise equality of `m / gcd(m,s)` across axes is enough.
-/
theorem nsmul_eq_zero_iff_prod_of_forall_mem_ratio_eq
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hRatio : ∀ m ∈ ms, m / Nat.gcd m s₁ = m / Nat.gcd m s₂) :
    (n • (s₁ : ZMod ms.prod) = 0 ↔ n • (s₂ : ZMod ms.prod) = 0) := by
  refine nsmul_eq_zero_iff_prod_of_forall_mem_orbitSize_eq ms hcop hpos ?_
  intro m hm
  simpa [orbitSize] using hRatio m hm

/--
Common practical specialization:
if both step charts are coprime to every axis, both orbit profiles are exactly the modulus profile,
so the node-level closure predicates coincide.
-/
theorem nsmul_eq_zero_iff_prod_of_forall_mem_coprime
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hcop₁ : ∀ m ∈ ms, Nat.Coprime m s₁)
    (hcop₂ : ∀ m ∈ ms, Nat.Coprime m s₂) :
    (n • (s₁ : ZMod ms.prod) = 0 ↔ n • (s₂ : ZMod ms.prod) = 0) := by
  refine nsmul_eq_zero_iff_prod_of_forall_mem_orbitSize_eq ms hcop hpos ?_
  intro m hm
  have h1 : orbitSize m s₁ = m := orbitSize_eq_modulus_of_coprime (hcop₁ m hm)
  have h2 : orbitSize m s₂ = m := orbitSize_eq_modulus_of_coprime (hcop₂ m hm)
  simp [h1, h2]

/-- A reusable node-closure predicate for a subsystem list. -/
def nodeClosure (ms : List Nat) (s n : Nat) : Prop :=
  n • (s : ZMod ms.prod) = 0

/--
Product-node closure is equivalent to axiswise closure for pairwise-coprime subsystem axes.

This is the finite-list CRT bridge from the packed node predicate `nodeClosure ms s n`
to the concrete per-axis predicate `n • (s : ZMod m) = 0` for each `m ∈ ms`.
-/
theorem nodeClosure_iff_forall_mem_nsmul_eq_zero
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) {s n : Nat} :
    nodeClosure ms s n ↔ ∀ m ∈ ms, n • (s : ZMod m) = 0 := by
  constructor
  · intro hnode
    have hdivProd : ms.prod ∣ n * s :=
      (nsmul_eq_zero_iff_modulus_dvd_mul ms.prod s n).1 (by simpa [nodeClosure] using hnode)
    have hmodProd : n * s ≡ 0 [MOD ms.prod] := (Nat.modEq_zero_iff_dvd).2 hdivProd
    have hmodAxes : ∀ m ∈ ms, n * s ≡ 0 [MOD m] :=
      SystemNodeModProd.modEq_mem_of_modEq_prod (a := n * s) (b := 0) hcop hmodProd
    intro m hm
    have hdiv : m ∣ n * s := (Nat.modEq_zero_iff_dvd).1 (hmodAxes m hm)
    exact (nsmul_eq_zero_iff_modulus_dvd_mul m s n).2 hdiv
  · intro hall
    have hmodAxes : ∀ m ∈ ms, n * s ≡ 0 [MOD m] := by
      intro m hm
      have hdiv : m ∣ n * s :=
        (nsmul_eq_zero_iff_modulus_dvd_mul m s n).1 (hall m hm)
      exact (Nat.modEq_zero_iff_dvd).2 hdiv
    have hmodProd : n * s ≡ 0 [MOD ms.prod] :=
      SystemNodeModProd.modEq_prod_of_forall_mem (a := n * s) (b := 0) hcop hmodAxes
    have hdivProd : ms.prod ∣ n * s := (Nat.modEq_zero_iff_dvd).1 hmodProd
    have hnode : n • (s : ZMod ms.prod) = 0 :=
      (nsmul_eq_zero_iff_modulus_dvd_mul ms.prod s n).2 hdivProd
    simpa [nodeClosure] using hnode

/--
Compositional closure packaging:
closure on an appended subsystem list is equivalent to closure on each subsystem,
provided the appended list is pairwise coprime.
-/
theorem nodeClosure_append_iff
    (ms₁ ms₂ : List Nat)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) {s n : Nat} :
    nodeClosure (ms₁ ++ ms₂) s n ↔ nodeClosure ms₁ s n ∧ nodeClosure ms₂ s n := by
  rcases (List.pairwise_append.1 hcop) with ⟨hcop₁, hcop₂, _hcross⟩
  constructor
  · intro happend
    have hallAppend : ∀ m ∈ ms₁ ++ ms₂, n • (s : ZMod m) = 0 :=
      (nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms₁ ++ ms₂) (hcop := hcop)).1 happend
    have hall₁ : ∀ m ∈ ms₁, n • (s : ZMod m) = 0 := by
      intro m hm
      exact hallAppend m (List.mem_append.2 (Or.inl hm))
    have hall₂ : ∀ m ∈ ms₂, n • (s : ZMod m) = 0 := by
      intro m hm
      exact hallAppend m (List.mem_append.2 (Or.inr hm))
    refine And.intro ?_ ?_
    · exact (nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms₁) (hcop := hcop₁)).2 hall₁
    · exact (nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms₂) (hcop := hcop₂)).2 hall₂
  · intro hparts
    rcases hparts with ⟨h₁, h₂⟩
    have hall₁ : ∀ m ∈ ms₁, n • (s : ZMod m) = 0 :=
      (nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms₁) (hcop := hcop₁)).1 h₁
    have hall₂ : ∀ m ∈ ms₂, n • (s : ZMod m) = 0 :=
      (nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms₂) (hcop := hcop₂)).1 h₂
    have hallAppend : ∀ m ∈ ms₁ ++ ms₂, n • (s : ZMod m) = 0 := by
      intro m hm
      rcases List.mem_append.1 hm with hm₁ | hm₂
      · exact hall₁ m hm₁
      · exact hall₂ m hm₂
    exact (nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms₁ ++ ms₂) (hcop := hcop)).2 hallAppend

/--
Node-closure chart invariance from pointwise orbit-size equality.
-/
theorem nodeClosure_iff_of_forall_mem_orbitSize_eq
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hEq : ∀ m ∈ ms, orbitSize m s₁ = orbitSize m s₂) :
    nodeClosure ms s₁ n ↔ nodeClosure ms s₂ n := by
  simpa [nodeClosure] using
    (nsmul_eq_zero_iff_prod_of_forall_mem_orbitSize_eq
      (ms := ms) (hcop := hcop) (hpos := hpos) (s₁ := s₁) (s₂ := s₂) (n := n) hEq)

/--
Node-closure chart invariance from pointwise ratio equality (`m / gcd(m,s)`).
-/
theorem nodeClosure_iff_of_forall_mem_ratio_eq
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hRatio : ∀ m ∈ ms, m / Nat.gcd m s₁ = m / Nat.gcd m s₂) :
    nodeClosure ms s₁ n ↔ nodeClosure ms s₂ n := by
  simpa [nodeClosure] using
    (nsmul_eq_zero_iff_prod_of_forall_mem_ratio_eq
      (ms := ms) (hcop := hcop) (hpos := hpos) (s₁ := s₁) (s₂ := s₂) (n := n) hRatio)

/--
Node-closure chart invariance when both observer-step charts are axiswise coprime.
-/
theorem nodeClosure_iff_of_forall_mem_coprime
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hcop₁ : ∀ m ∈ ms, Nat.Coprime m s₁)
    (hcop₂ : ∀ m ∈ ms, Nat.Coprime m s₂) :
    nodeClosure ms s₁ n ↔ nodeClosure ms s₂ n := by
  simpa [nodeClosure] using
    (nsmul_eq_zero_iff_prod_of_forall_mem_coprime
      (ms := ms) (hcop := hcop) (hpos := hpos)
      (s₁ := s₁) (s₂ := s₂) (n := n) hcop₁ hcop₂)

/--
One-call chart-change package at subsystem-node level:
bundles orbit-size, ratio, and coprime variants into one theorem payload.
-/
theorem nodeClosure_chart_change_package
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s₁ s₂ n : Nat}
    (hEq : ∀ m ∈ ms, orbitSize m s₁ = orbitSize m s₂)
    (hRatio : ∀ m ∈ ms, m / Nat.gcd m s₁ = m / Nat.gcd m s₂)
    (hcop₁ : ∀ m ∈ ms, Nat.Coprime m s₁)
    (hcop₂ : ∀ m ∈ ms, Nat.Coprime m s₂) :
    (nodeClosure ms s₁ n ↔ nodeClosure ms s₂ n)
    ∧ (nodeClosure ms s₁ n ↔ nodeClosure ms s₂ n)
    ∧ (nodeClosure ms s₁ n ↔ nodeClosure ms s₂ n) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nodeClosure_iff_of_forall_mem_orbitSize_eq ms hcop hpos hEq
  · exact nodeClosure_iff_of_forall_mem_ratio_eq ms hcop hpos hRatio
  · exact nodeClosure_iff_of_forall_mem_coprime ms hcop hpos hcop₁ hcop₂

/-- Fixed-parameter smoke theorem for chart-change package on `[3,11,13]`. -/
theorem nodeClosure_chart_change_package_smoke_3_11_13 :
    (nodeClosure ([3, 11, 13] : List Nat) 1 1 ↔ nodeClosure ([3, 11, 13] : List Nat) 1 1)
    ∧ (nodeClosure ([3, 11, 13] : List Nat) 1 1 ↔ nodeClosure ([3, 11, 13] : List Nat) 1 1)
    ∧ (nodeClosure ([3, 11, 13] : List Nat) 1 1 ↔ nodeClosure ([3, 11, 13] : List Nat) 1 1) := by
  exact nodeClosure_chart_change_package
    ([3, 11, 13] : List Nat)
    (by decide)
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)
    (s₁ := 1) (s₂ := 1) (n := 1)
    (by
      intro m hm
      rfl)
    (by
      intro m hm
      rfl)
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)
    (by
      intro m hm
      simp at hm
      rcases hm with rfl | rfl | rfl <;> decide)

end CycleStepOrbit
