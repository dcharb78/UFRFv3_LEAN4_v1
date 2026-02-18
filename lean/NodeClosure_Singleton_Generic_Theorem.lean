import Observer_Tick_Axis_Family_Theorem

/-!
# NodeClosure Singleton Generic Witness

Generic singleton-axis closure witnesses, reusable across seam moduli.
-/

namespace CycleStepOrbit

theorem nodeClosure_singleton_iff (m s n : Nat) :
    nodeClosure ([m] : List Nat) s n ↔ m ∣ n * s := by
  unfold nodeClosure
  simpa [List.prod_cons, Nat.mul_one] using
    (nsmul_eq_zero_iff_modulus_dvd_mul (m := m * 1) s n)

theorem nodeClosure_singleton_step1_iff (m n : Nat) :
    nodeClosure ([m] : List Nat) 1 n ↔ m ∣ n := by
  simpa [Nat.mul_one] using (nodeClosure_singleton_iff m 1 n)

theorem nodeClosure_singleton_step1_iff_zero_of_lt
    (m n : Nat) (hn : n < m) :
    nodeClosure ([m] : List Nat) 1 n ↔ n = 0 := by
  constructor
  · intro hnode
    have hdiv : m ∣ n := (nodeClosure_singleton_step1_iff m n).1 hnode
    exact Nat.eq_zero_of_dvd_of_lt hdiv hn
  · intro hn0
    have hdiv : m ∣ n := by simp [hn0]
    exact (nodeClosure_singleton_step1_iff m n).2 hdiv

end CycleStepOrbit
