import CycleStep_Orbit_Theorem
import System_Node_ModProd_Theorem
import Mathlib.Data.Nat.ModEq

/-!
# Cycle-Step Orbit Concurrency (N Axes)

This file generalizes the two-axis orbit-closure lemma from `CycleStep_Orbit_Theorem.lean`
to an arbitrary finite family of **pairwise coprime** modular axes.

Interpretation (UFRF language):
- Each modulus `m` is an axis (a subsystem).
- A step `+s` has an intrinsic orbit size `m / gcd(m,s)` on that axis.
- Concurrency happens when many axes return at once; the synchronizing time is an `lcm`.
- Pairwise coprimality is the exact condition for “axes glue into a node” via CRT.

No placeholders; exact arithmetic only.
-/

namespace CycleStepOrbit

/-- LCM over a list (recursive form, so we can reason by induction). -/
def lcmList : List Nat → Nat
  | [] => 1
  | x :: xs => Nat.lcm x (lcmList xs)

/-!
## Basic list facts: `lcmList` divides a number iff every member divides it
-/

theorem lcmList_dvd_iff {xs : List Nat} {n : Nat} : lcmList xs ∣ n ↔ ∀ x ∈ xs, x ∣ n := by
  induction xs with
  | nil =>
      simp [lcmList]
  | cons x xs ih =>
      constructor
      · intro h
        have hx : x ∣ n := Nat.dvd_trans (Nat.dvd_lcm_left x (lcmList xs)) h
        have hxs : lcmList xs ∣ n := Nat.dvd_trans (Nat.dvd_lcm_right x (lcmList xs)) h
        refine ?_
        intro y hy
        rcases (List.mem_cons).1 hy with rfl | hy'
        · exact hx
        · exact (ih.1 hxs) y hy'
      · intro hall
        -- Use `lcm_dvd_iff` and recurse.
        have hx : x ∣ n := hall x (by simp)
        have hxs : lcmList xs ∣ n := (ih.2 fun y hy => hall y (by simp [hy]))
        exact (Nat.lcm_dvd_iff).2 ⟨hx, hxs⟩

theorem lcmList_eq_prod_of_pairwise_coprime (xs : List Nat) (hcop : xs.Pairwise Nat.Coprime) :
    lcmList xs = xs.prod := by
  induction xs with
  | nil =>
      simp [lcmList]
  | cons x xs ih =>
      have hx : ∀ n ∈ xs, Nat.Coprime x n := (List.pairwise_cons.mp hcop).1
      have hxs : xs.Pairwise Nat.Coprime := List.Pairwise.of_cons hcop
      have hcop_prod : Nat.Coprime x xs.prod := (Nat.coprime_list_prod_right_iff).2 hx
      -- `lcmList (x::xs) = lcm x (lcmList xs) = lcm x xs.prod = x*xs.prod`.
      simp [lcmList, ih hxs, List.prod_cons, Nat.Coprime.lcm_eq_mul hcop_prod]

theorem dvd_lcmList_of_mem {a : Nat} {xs : List Nat} (ha : a ∈ xs) : a ∣ lcmList xs := by
  induction xs with
  | nil =>
      cases ha
  | cons x xs ih =>
      -- `a = x` or `a ∈ xs`.
      have : a = x ∨ a ∈ xs := by
        simpa using ha
      rcases this with rfl | ha'
      · -- `x ∣ lcm x (lcmList xs)`.
        simp [lcmList, Nat.dvd_lcm_left]
      · -- `a ∣ lcmList xs`, hence `a ∣ lcm x (lcmList xs)`.
        have hd : a ∣ lcmList xs := ih ha'
        exact Nat.dvd_trans hd (by simp [lcmList, Nat.dvd_lcm_right])

theorem prod_pos_of_forall_mem_pos (ms : List Nat) (hpos : ∀ m ∈ ms, 0 < m) : 0 < ms.prod := by
  induction ms with
  | nil =>
      simp
  | cons a ms ih =>
      have ha : 0 < a := hpos a (by simp)
      have hms : ∀ m ∈ ms, 0 < m := by
        intro m hm
        exact hpos m (by simp [hm])
      simpa [List.prod_cons] using Nat.mul_pos ha (ih hms)

/-- The synchronizing step count for a family of axes `ms` under step `+s`. -/
def orbitLcm (ms : List Nat) (s : Nat) : Nat :=
  lcmList (ms.map (fun m => orbitSize m s))

theorem orbitLcm_dvd_iff {ms : List Nat} {s n : Nat} :
    orbitLcm ms s ∣ n ↔ ∀ m ∈ ms, orbitSize m s ∣ n := by
  unfold orbitLcm
  -- Reduce to `lcmList_dvd_iff` on the mapped list.
  simpa [List.forall_mem_map] using
    (lcmList_dvd_iff (xs := ms.map (fun m => orbitSize m s)) (n := n))

theorem orbitSize_dvd_modulus (m s : Nat) : orbitSize m s ∣ m := by
  -- `m = (m / gcd(m,s)) * gcd(m,s)`.
  refine ⟨Nat.gcd m s, ?_⟩
  unfold orbitSize
  simpa using (Nat.div_mul_cancel (Nat.gcd_dvd_left m s)).symm

theorem orbitSize_coprime_of_coprime {m n s : Nat} (hcop : Nat.Coprime m n) :
    Nat.Coprime (orbitSize m s) (orbitSize n s) := by
  have hn : orbitSize n s ∣ n := orbitSize_dvd_modulus n s
  have hm : orbitSize m s ∣ m := orbitSize_dvd_modulus m s
  have hmn : Nat.Coprime m (orbitSize n s) := Nat.Coprime.coprime_dvd_right hn hcop
  exact Nat.Coprime.coprime_dvd_left hm hmn

theorem orbitSize_map_pairwise_coprime (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (s : Nat) :
    (ms.map (fun m => orbitSize m s)).Pairwise Nat.Coprime := by
  induction ms with
  | nil =>
      simp
  | cons m ms ih =>
      have hm : ∀ n ∈ ms, Nat.Coprime m n := (List.pairwise_cons.mp hcop).1
      have hms : ms.Pairwise Nat.Coprime := List.Pairwise.of_cons hcop
      have h1 : ∀ x ∈ ms.map (fun n => orbitSize n s), Nat.Coprime (orbitSize m s) x := by
        intro x hx
        rcases List.mem_map.1 hx with ⟨n, hn, rfl⟩
        exact orbitSize_coprime_of_coprime (m := m) (n := n) (s := s) (hm n hn)
      have h2 : (ms.map (fun n => orbitSize n s)).Pairwise Nat.Coprime := ih hms
      exact (List.pairwise_cons.2 ⟨h1, h2⟩)

theorem orbitLcm_eq_prod_of_pairwise_coprime (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (s : Nat) :
    orbitLcm ms s = (ms.map (fun m => orbitSize m s)).prod := by
  unfold orbitLcm
  exact lcmList_eq_prod_of_pairwise_coprime (xs := ms.map (fun m => orbitSize m s))
    (orbitSize_map_pairwise_coprime ms hcop s)

theorem map_orbitSize_eq_self_of_forall_coprime (ms : List Nat) (s : Nat)
    (hs : ∀ m ∈ ms, Nat.Coprime m s) :
    ms.map (fun m => orbitSize m s) = ms := by
  induction ms with
  | nil =>
      simp
  | cons m ms ih =>
      have hm : Nat.Coprime m s := hs m (by simp)
      have hs' : ∀ n ∈ ms, Nat.Coprime n s := by
        intro n hn
        exact hs n (by simp [hn])
      simp [orbitSize_eq_modulus_of_coprime hm, ih hs']

/--
If:
- the axes `ms` are pairwise coprime, and
- the step `s` is coprime to every axis,

then the synchronizing orbit length is the full product modulus:
`orbitLcm ms s = ms.prod`.

This is a precise, discrete form of: "when the observer step is compatible with every axis,
the composite system closes exactly at the structural node count."
-/
theorem orbitLcm_eq_prod_moduli_of_pairwise_coprime_of_forall_coprime
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (s : Nat)
    (hs : ∀ m ∈ ms, Nat.Coprime m s) :
    orbitLcm ms s = ms.prod := by
  unfold orbitLcm
  have hmap : ms.map (fun m => orbitSize m s) = ms := map_orbitSize_eq_self_of_forall_coprime ms s hs
  simpa [hmap] using (lcmList_eq_prod_of_pairwise_coprime (xs := ms) hcop)

theorem orbitSize_dvd_orbitLcm {ms : List Nat} {s m : Nat} (hm : m ∈ ms) :
    orbitSize m s ∣ orbitLcm ms s := by
  unfold orbitLcm
  apply dvd_lcmList_of_mem
  exact List.mem_map.2 ⟨m, hm, rfl⟩

theorem axis_dvd_orbitLcm_mul (ms : List Nat) (s : Nat) {m : Nat} (hm : m ∈ ms) :
    m ∣ orbitLcm ms s * s := by
  have h1 : m ∣ orbitSize m s * s := orbitSize_mul_step_dvd m s
  have h2 : orbitSize m s ∣ orbitLcm ms s := orbitSize_dvd_orbitLcm (ms := ms) (s := s) hm
  have h3 : orbitSize m s * s ∣ orbitLcm ms s * s := Nat.mul_dvd_mul_right h2 s
  exact Nat.dvd_trans h1 h3

theorem prod_dvd_orbitLcm_mul (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (s : Nat) :
    ms.prod ∣ orbitLcm ms s * s := by
  -- Prove `orbitLcm* s ≡ 0 (mod m)` for every axis `m`.
  have hall : ∀ m ∈ ms, orbitLcm ms s * s ≡ 0 [MOD m] := by
    intro m hm
    exact (Nat.modEq_zero_iff_dvd).2 (axis_dvd_orbitLcm_mul ms s hm)
  -- Glue the per-axis congruences into a congruence modulo the product modulus.
  have hprod :
      orbitLcm ms s * s ≡ 0 [MOD ms.prod] :=
    SystemNodeModProd.modEq_prod_of_forall_mem (a := orbitLcm ms s * s) (b := 0) (ms := ms) hcop hall
  -- Convert congruence-to-zero into divisibility.
  exact (Nat.modEq_zero_iff_dvd).1 hprod

/--
**N-axis closure:**

If the moduli are pairwise coprime, then stepping by `+s` returns in `ZMod (ms.prod)` after
`orbitLcm ms s` steps.
-/
theorem orbitLcm_nsmul_step_returns (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (s : Nat) :
    orbitLcm ms s • (s : ZMod ms.prod) = 0 := by
  -- Reduce `nsmul` to multiplication and use divisibility of the `Nat` product.
  have hdiv : ms.prod ∣ orbitLcm ms s * s := prod_dvd_orbitLcm_mul ms hcop s
  have hz : ((orbitLcm ms s * s : Nat) : ZMod ms.prod) = 0 :=
    (ZMod.natCast_eq_zero_iff (orbitLcm ms s * s) (ms.prod)).2 hdiv
  -- Turn the cast equality into the desired `nsmul` statement.
  simpa [nsmul_eq_mul, Nat.cast_mul] using hz

/--
**N-axis exact orbit size** (pairwise coprime axes, positive moduli):

If the axis moduli `ms` are pairwise coprime and all positive, then the orbit size of step `+s`
in the composite node `ZMod ms.prod` is exactly `orbitLcm ms s` (the `lcm` of the per-axis orbit
sizes).
-/
theorem orbitSize_prod_eq_orbitLcm_of_pairwise_coprime
    (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime) (s : Nat) (hpos : ∀ m ∈ ms, 0 < m) :
    orbitSize ms.prod s = orbitLcm ms s := by
  have hmprod : 0 < ms.prod := prod_pos_of_forall_mem_pos ms hpos
  -- Two naturals are equal iff they define the same "set of multiples".
  apply (Nat.dvd_right_iff_eq).1
  intro n
  constructor
  · intro hn
    -- `orbitSize ∣ n` -> closure in the composite node.
    have hnsProd : n • (s : ZMod ms.prod) = 0 :=
      nsmul_eq_zero_of_orbitSize_dvd (m := ms.prod) (s := s) (n := n) hn
    have hdivProd : ms.prod ∣ n * s :=
      (nsmul_eq_zero_iff_modulus_dvd_mul ms.prod s n).1 hnsProd
    -- Glue divisibility into per-axis divisibility via CRT (`ModEq` view).
    have hall : ∀ m ∈ ms, m ∣ n * s := by
      -- Convert divisibility to `ModEq` and project to axes.
      have hmodProd : n * s ≡ 0 [MOD ms.prod] := (Nat.modEq_zero_iff_dvd).2 hdivProd
      have hallMod : ∀ m ∈ ms, n * s ≡ 0 [MOD m] :=
        SystemNodeModProd.modEq_mem_of_modEq_prod (a := n * s) (b := 0) hcop hmodProd
      intro m hm
      exact (Nat.modEq_zero_iff_dvd).1 (hallMod m hm)
    -- Each axis gives `orbitSize m s ∣ n` (exact order on that axis).
    have hallOrbit : ∀ m ∈ ms, orbitSize m s ∣ n := by
      intro m hm
      have hmpos : 0 < m := hpos m hm
      have hns : n • (s : ZMod m) = 0 :=
        (nsmul_eq_zero_iff_modulus_dvd_mul m s n).2 (hall m hm)
      exact (nsmul_eq_zero_iff_orbitSize_dvd (m := m) (s := s) (n := n) hmpos).1 hns
    exact (orbitLcm_dvd_iff (ms := ms) (s := s) (n := n)).2 hallOrbit
  · intro hn
    -- `orbitLcm ∣ n` -> per-axis closure -> composite closure -> `orbitSize ∣ n`.
    have hallOrbit : ∀ m ∈ ms, orbitSize m s ∣ n :=
      (orbitLcm_dvd_iff (ms := ms) (s := s) (n := n)).1 hn
    have hallDiv : ∀ m ∈ ms, m ∣ n * s := by
      intro m hm
      have hns : n • (s : ZMod m) = 0 :=
        nsmul_eq_zero_of_orbitSize_dvd (m := m) (s := s) (n := n) (hallOrbit m hm)
      exact (nsmul_eq_zero_iff_modulus_dvd_mul m s n).1 hns
    -- Glue per-axis divisibility into product divisibility.
    have hallMod : ∀ m ∈ ms, n * s ≡ 0 [MOD m] := by
      intro m hm
      exact (Nat.modEq_zero_iff_dvd).2 (hallDiv m hm)
    have hmodProd : n * s ≡ 0 [MOD ms.prod] :=
      SystemNodeModProd.modEq_prod_of_forall_mem (a := n * s) (b := 0) hcop hallMod
    have hdivProd : ms.prod ∣ n * s := (Nat.modEq_zero_iff_dvd).1 hmodProd
    have hnsProd : n • (s : ZMod ms.prod) = 0 :=
      (nsmul_eq_zero_iff_modulus_dvd_mul ms.prod s n).2 hdivProd
    exact (nsmul_eq_zero_iff_orbitSize_dvd (m := ms.prod) (s := s) (n := n) hmprod).1 hnsProd

end CycleStepOrbit
