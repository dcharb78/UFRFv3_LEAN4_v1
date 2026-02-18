/-
# Multidimensional Ticks (Base-10 + Modular Coordinates)

This file formalizes a clean "pattern-of-patterns" statement for the **decimal tick** action
`n ↦ n * 10^k`:

* **Scale axis (base 10)**:
  - `decade (n * 10^k) = decade n + k`  (for `n ≠ 0`)
  - `leadingBlock (n * 10^k) = leadingBlock n`  (for `n ≠ 0`)

* **Cycle axes (mod m)**:
  - `(n * 10^k) % m = ((n % m) * (10^k % m)) % m`
  - If `10^k ≡ 1 (mod m)`, then the residue is invariant ("return").
  - If `10^k ≡ 0 (mod m)`, then the residue collapses to 0 at that tick-scale ("absorption").

This is intentionally discrete and exact: no real logarithms, no probabilistic claims.
-/

import Mathlib

import Universal_Ticks_Theorem
import Decimal_Mod13_Concurrency_Theorem
import Observer_Tick_Axis_Family_Theorem

namespace MultidimensionalTicks

/-- Base-10 tick action: scale by `10^k`. -/
def tick10 (k n : Nat) : Nat :=
  n * 10 ^ k

theorem tick10_add (k₁ k₂ n : Nat) : tick10 k₁ (tick10 k₂ n) = tick10 (k₁ + k₂) n := by
  unfold tick10
  calc
    (n * 10 ^ k₂) * 10 ^ k₁ = n * (10 ^ k₂ * 10 ^ k₁) := by ac_rfl
    _ = n * (10 ^ (k₂ + k₁)) := by simp [Nat.pow_add]
    _ = n * (10 ^ (k₁ + k₂)) := by simp [Nat.add_comm]

theorem tick10_ne_zero (k n : Nat) (hn : n ≠ 0) : tick10 k n ≠ 0 := by
  unfold tick10
  exact Nat.mul_ne_zero hn (pow_ne_zero _ (by decide : (10 : Nat) ≠ 0))

theorem tick10_decompose_base10 (n k : Nat) (hn : n ≠ 0) :
    UniversalTicks.decade (tick10 k n) = UniversalTicks.decade n + k
    ∧ UniversalTicks.leadingBlock (tick10 k n) = UniversalTicks.leadingBlock n := by
  constructor
  · simpa [tick10] using UniversalTicks.decade_mul_pow10 n k hn
  · simpa [tick10] using UniversalTicks.leadingBlock_mul_pow10 n k hn

theorem tick10_mod (n k m : Nat) :
    (tick10 k n) % m = ((n % m) * ((10 ^ k) % m)) % m := by
  simp [tick10, Nat.mul_mod]

theorem tick10_mod_invariant (n k m : Nat) (hm : m ≠ 0) (hk : (10 ^ k : Nat) % m = 1) :
    (tick10 k n) % m = n % m := by
  have hlt : n % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero hm)
  calc
    (tick10 k n) % m = ((n % m) * ((10 ^ k) % m)) % m := tick10_mod n k m
    _ = ((n % m) * 1) % m := by simp [hk]
    _ = (n % m) % m := by simp
    _ = n % m := by simp [Nat.mod_eq_of_lt hlt]

theorem tick10_mod_absorb (n k m : Nat) (hk : (10 ^ k : Nat) % m = 0) :
    (tick10 k n) % m = 0 := by
  calc
    (tick10 k n) % m = ((n % m) * ((10 ^ k) % m)) % m := tick10_mod n k m
    _ = ((n % m) * 0) % m := by simp [hk]
    _ = 0 := by simp

theorem tick10_mod_invariant_of_nsmul_sub_one
    (n k m : Nat)
    (hns : n • ((10 ^ k - 1 : Nat) : ZMod m) = 0) :
    (tick10 k n) % m = n % m := by
  have hdiv : m ∣ n * (10 ^ k - 1) :=
    (CycleStepOrbit.nsmul_eq_zero_iff_modulus_dvd_mul m (10 ^ k - 1) n).1 hns
  have hmod0 : n * (10 ^ k - 1) ≡ 0 [MOD m] :=
    (Nat.modEq_zero_iff_dvd).2 hdiv
  have hmod1 : n * (10 ^ k - 1) + n ≡ n [MOD m] :=
    by simpa using (Nat.ModEq.add_right n hmod0)
  have hpow : 1 ≤ 10 ^ k := Nat.succ_le_of_lt (Nat.pow_pos (n := k) (by decide : 0 < (10 : Nat)))
  have hcalc : n * (10 ^ k - 1) + n = tick10 k n := by
    calc
      n * (10 ^ k - 1) + n = n * (10 ^ k - 1) + n * 1 := by simp
      _ = n * ((10 ^ k - 1) + 1) := by rw [← Nat.mul_add]
      _ = n * (10 ^ k) := by simp [Nat.sub_add_cancel hpow]
      _ = tick10 k n := by simp [tick10]
  have hmodTick : tick10 k n ≡ n [MOD m] := by
    simpa [hcalc] using hmod1
  simpa [Nat.ModEq] using hmodTick

-- ------------------------------------------------------------
-- Observer-scale view: coprime axes are permutations (no information loss)
-- ------------------------------------------------------------

/--
If `gcd(10,m)=1`, then *for every tick-length `k`*, multiplication by `10^k`
is a permutation of the residue space `ZMod m`.

This captures the “internal observer” viewpoint: on an invertible axis, a base-10 tick
does not destroy information; it only relabels states.
-/
theorem tick10_zmod_bijective (m k : Nat) (hcop : Nat.Coprime 10 m) :
    Function.Bijective (fun x : ZMod m => ((10 : ZMod m) ^ k) * x) := by
  -- Package `10` as a unit in `ZMod m`.
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime 10 hcop
  -- Left multiplication by a unit is a bijection, and `u` coerces to `10`.
  simpa [u, ZMod.coe_unitOfCoprime] using (Units.mulLeft_bijective (u ^ k))

-- ------------------------------------------------------------
-- General periodicity when `m` is coprime to 10 (Euler totient)
-- ------------------------------------------------------------

/--
If `gcd(10,m)=1` (i.e. `10` is invertible mod `m`), then decimal ticks are periodic:
`10^φ(m) ≡ 1 (mod m)`, hence scaling by `10^φ(m)` preserves residues mod `m`.

This is a general (non-tight) return-period lemma; for some moduli the true period is smaller.
-/
theorem ten_pow_totient_mod_eq_one (m : Nat) (hm : 1 < m) (hcop : (10 : Nat).Coprime m) :
    (10 ^ Nat.totient m : Nat) % m = 1 := by
  -- `Nat.pow_totient_mod_eq_one` is Euler's theorem in modular exponentiation form.
  simpa using (Nat.pow_totient_mod_eq_one (x := 10) (n := m) hm hcop)

theorem tick10_mod_invariant_totient (n m : Nat) (hm : 1 < m) (hcop : (10 : Nat).Coprime m) :
    (tick10 (Nat.totient m) n) % m = n % m := by
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt (lt_trans (Nat.zero_lt_one) hm)
  exact tick10_mod_invariant n (Nat.totient m) m hm0 (ten_pow_totient_mod_eq_one m hm hcop)

theorem ten_pow_mul_mod_eq_one (m k t : Nat) (hm : 1 < m) (hk : (10 ^ k : Nat) % m = 1) :
    (10 ^ (k * t) : Nat) % m = 1 := by
  calc
    (10 ^ (k * t) : Nat) % m = ((10 ^ k) ^ t) % m := by
      simp [pow_mul]
    _ = (((10 ^ k) % m) ^ t) % m := by
      simp [Nat.pow_mod]
    _ = (1 ^ t) % m := by
      simp [hk]
    _ = 1 := by
      have : (1 : Nat) < m := hm
      simp [Nat.mod_eq_of_lt this]

theorem tick10_mod_invariant_mul (n m k t : Nat) (hm : 1 < m) (hk : (10 ^ k : Nat) % m = 1) :
    (tick10 (k * t) n) % m = n % m := by
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt (lt_trans (Nat.zero_lt_one) hm)
  exact tick10_mod_invariant n (k * t) m hm0 (ten_pow_mul_mod_eq_one m k t hm hk)

theorem tick10_mod_invariant_of_dvd (n m k₀ k : Nat) (hm : 1 < m) (hk₀ : (10 ^ k₀ : Nat) % m = 1)
    (hdiv : k₀ ∣ k) :
    (tick10 k n) % m = n % m := by
  rcases hdiv with ⟨t, rfl⟩
  simpa [Nat.mul_assoc] using tick10_mod_invariant_mul n m k₀ t hm hk₀

theorem tick10_mod_invariant_lcm_left (n m k₁ k₂ : Nat) (hm : 1 < m) (hk₁ : (10 ^ k₁ : Nat) % m = 1) :
    (tick10 (Nat.lcm k₁ k₂) n) % m = n % m := by
  exact tick10_mod_invariant_of_dvd n m k₁ (Nat.lcm k₁ k₂) hm hk₁ (Nat.dvd_lcm_left k₁ k₂)

theorem tick10_mod_invariant_lcm_right (n m k₁ k₂ : Nat) (hm : 1 < m) (hk₂ : (10 ^ k₂ : Nat) % m = 1) :
    (tick10 (Nat.lcm k₁ k₂) n) % m = n % m := by
  exact tick10_mod_invariant_of_dvd n m k₂ (Nat.lcm k₁ k₂) hm hk₂ (Nat.dvd_lcm_right k₁ k₂)

-- ------------------------------------------------------------
-- Combined coordinates: decimal "log-axis" + modular axes
-- ------------------------------------------------------------

/--
One tick length can return **simultaneously** on multiple modular axes:

Take `K = lcm(φ(m₁), φ(m₂))`. Since `K` is a multiple of each totient period, `10^K ≡ 1 (mod mᵢ)`
for `i=1,2`, so decimal ticks return on both axes at the same time.
-/
theorem tick10_mod_invariant_lcm_totients (n m₁ m₂ : Nat)
    (hm₁ : 1 < m₁) (hm₂ : 1 < m₂)
    (hcop₁ : (10 : Nat).Coprime m₁) (hcop₂ : (10 : Nat).Coprime m₂) :
    (tick10 (Nat.lcm (Nat.totient m₁) (Nat.totient m₂)) n) % m₁ = n % m₁
      ∧ (tick10 (Nat.lcm (Nat.totient m₁) (Nat.totient m₂)) n) % m₂ = n % m₂ := by
  constructor
  ·
    exact
      tick10_mod_invariant_lcm_left n m₁ (Nat.totient m₁) (Nat.totient m₂) hm₁
        (ten_pow_totient_mod_eq_one m₁ hm₁ hcop₁)
  ·
    exact
      tick10_mod_invariant_lcm_right n m₂ (Nat.totient m₁) (Nat.totient m₂) hm₂
        (ten_pow_totient_mod_eq_one m₂ hm₂ hcop₂)

/--
Combined coordinate invariance (discrete counterpart of “nested logs + mods”):

At tick `k = φ(m)`, the base-10 *leading block* is unchanged (scale invariance) and the residue mod `m`
returns (cycle invariance), provided `gcd(10,m)=1`.

This is a precise, Lean-checkable version of:
“`log100` is `log1` in the cycle, while modular coordinates also return at their own periods.”
-/
theorem tick10_totient_invariant_leadingBlock_and_mod (n m : Nat) (hn : n ≠ 0)
    (hm : 1 < m) (hcop : (10 : Nat).Coprime m) :
    UniversalTicks.leadingBlock (tick10 (Nat.totient m) n) = UniversalTicks.leadingBlock n
      ∧ (tick10 (Nat.totient m) n) % m = n % m := by
  constructor
  ·
    simpa [tick10] using
      (UniversalTicks.leadingBlock_mul_pow10 n (Nat.totient m) hn)
  ·
    exact tick10_mod_invariant_totient n m hm hcop

-- ------------------------------------------------------------
-- Finite families of axes (concurrent nesting)
-- ------------------------------------------------------------

/--
`totientLCM ms` is a conservative "global return tick" for a finite list of moduli:
it is the LCM of their totients.

At tick `k = totientLCM ms`, decimal scaling by `10^k` returns simultaneously on every axis
`mod m` for `m ∈ ms` (assuming `gcd(10,m)=1`).
-/
def totientLCM : List Nat → Nat
  | [] => 1
  | m :: ms => Nat.lcm (Nat.totient m) (totientLCM ms)

/--
`globalTick ms a₂ a₅` is a conservative *single* tick length that:

* is a multiple of `totientLCM ms` (so every coprime axis in `ms` returns), and
* is at least `max a₂ a₅` (so `2^a₂` and `5^a₅` are absorbed to 0).
-/
def globalTick (ms : List Nat) (a₂ a₅ : Nat) : Nat :=
  totientLCM ms * (Nat.max a₂ a₅ + 1)

theorem totientLCM_append (ms₁ ms₂ : List Nat) :
    totientLCM (ms₁ ++ ms₂) = Nat.lcm (totientLCM ms₁) (totientLCM ms₂) := by
  induction ms₁ with
  | nil =>
      simp [totientLCM]
  | cons a ms₁ ih =>
      -- Reassociate the nested `lcm` structure.
      simp [totientLCM, ih, Nat.lcm_assoc]

theorem totient_dvd_totientLCM_of_mem (m : Nat) :
    ∀ ms : List Nat, m ∈ ms → Nat.totient m ∣ totientLCM ms := by
  intro ms hm
  induction ms with
  | nil =>
      cases hm
  | cons a ms ih =>
      have : m = a ∨ m ∈ ms := by
        simpa using (List.mem_cons.1 hm)
      cases this with
      | inl h =>
          subst h
          simp [totientLCM, Nat.dvd_lcm_left]
      | inr h =>
          have ih' : Nat.totient m ∣ totientLCM ms := ih h
          have hdiv : totientLCM ms ∣ totientLCM (a :: ms) := by
            simp [totientLCM, Nat.dvd_lcm_right]
          exact dvd_trans ih' hdiv

/--
Multi-axis concurrency for a *finite* family of moduli:
if every modulus in `ms` is coprime to `10`, then one global tick returns all residues at once.
-/
theorem tick10_mod_invariant_totientLCM (n : Nat) (ms : List Nat)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    ∀ m ∈ ms, (tick10 (totientLCM ms) n) % m = n % m := by
  intro m hm
  have hm1 : 1 < m := hgt m hm
  have hc : (10 : Nat).Coprime m := hcop m hm
  have hk0 : (10 ^ Nat.totient m : Nat) % m = 1 := ten_pow_totient_mod_eq_one m hm1 hc
  have hdiv : Nat.totient m ∣ totientLCM ms := totient_dvd_totientLCM_of_mem m ms hm
  exact tick10_mod_invariant_of_dvd n m (Nat.totient m) (totientLCM ms) hm1 hk0 hdiv

/--
Combined coordinate invariance for a finite family of moduli:

- the base-10 leading block is unchanged (scale axis),
- every residue mod `m ∈ ms` returns (cycle axes),

at the single tick `k = totientLCM ms`.
-/
theorem tick10_totientLCM_invariant_leadingBlock_and_mods (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    UniversalTicks.leadingBlock (tick10 (totientLCM ms) n) = UniversalTicks.leadingBlock n
      ∧ (∀ m ∈ ms, (tick10 (totientLCM ms) n) % m = n % m) := by
  constructor
  ·
    simpa [tick10] using UniversalTicks.leadingBlock_mul_pow10 n (totientLCM ms) hn
  ·
    exact tick10_mod_invariant_totientLCM n ms hgt hcop

theorem tick10_totientLCM_leadingBlock_invariant
    (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    UniversalTicks.leadingBlock (tick10 (totientLCM ms) n) = UniversalTicks.leadingBlock n := by
  exact (tick10_totientLCM_invariant_leadingBlock_and_mods n ms hn hgt hcop).1

theorem tick10_totientLCM_mod_invariant
    (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    ∀ m ∈ ms, (tick10 (totientLCM ms) n) % m = n % m := by
  exact (tick10_totientLCM_invariant_leadingBlock_and_mods n ms hn hgt hcop).2

/--
A concrete “system node” view: package a finite family of axes into one coordinate map.

We use the list order of `ms` to produce a canonical vector of residues.
-/
def systemCoord (ms : List Nat) (n : Nat) : Nat × List Nat :=
  (UniversalTicks.leadingBlock n, ms.map (fun m => n % m))

theorem systemCoord_mods_invariant_of_axis_nsmul_sub_one
    (n k : Nat) (ms : List Nat)
    (hall : ∀ m ∈ ms, n • ((10 ^ k - 1 : Nat) : ZMod m) = 0) :
    ms.map (fun m => (tick10 k n) % m) = ms.map (fun m => n % m) := by
  induction ms with
  | nil =>
      simp
  | cons a ms ih =>
      have ha : (tick10 k n) % a = n % a :=
        tick10_mod_invariant_of_nsmul_sub_one n k a (hall a (by simp))
      have htail : ∀ m ∈ ms, n • ((10 ^ k - 1 : Nat) : ZMod m) = 0 := by
        intro m hm
        exact hall m (by simp [hm])
      simpa [ha] using ih htail

theorem systemCoord_mods_invariant_of_nodeClosure
    (n k : Nat) (ms : List Nat) (hcop : ms.Pairwise Nat.Coprime)
    (hnode : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n) :
    ms.map (fun m => (tick10 k n) % m) = ms.map (fun m => n % m) := by
  have hall : ∀ m ∈ ms, n • ((10 ^ k - 1 : Nat) : ZMod m) = 0 :=
    (CycleStepOrbit.nodeClosure_iff_forall_mem_nsmul_eq_zero (ms := ms) (hcop := hcop)).1 hnode
  exact systemCoord_mods_invariant_of_axis_nsmul_sub_one n k ms hall

theorem systemCoord_invariant_of_nodeClosure
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime)
    (hnode : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n) :
    systemCoord ms (tick10 k n) = systemCoord ms n := by
  unfold systemCoord
  apply Prod.ext
  · simpa [tick10] using UniversalTicks.leadingBlock_mul_pow10 n k hn
  · simpa using systemCoord_mods_invariant_of_nodeClosure n k ms hcop hnode

theorem systemCoord_invariant_of_nodeClosure_chart_change
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s : Nat}
    (hEq : ∀ m ∈ ms, CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure ms s n) :
    systemCoord ms (tick10 k n) = systemCoord ms n := by
  have hnodeTick : CycleStepOrbit.nodeClosure ms (10 ^ k - 1) n := by
    exact
      (CycleStepOrbit.nodeClosure_iff_of_forall_mem_orbitSize_eq
        (ms := ms) (hcop := hcop) (hpos := hpos)
        (s₁ := s) (s₂ := 10 ^ k - 1) (n := n) hEq).1 hnode
  exact systemCoord_invariant_of_nodeClosure n k ms hn hcop hnodeTick

theorem systemCoord_invariant_of_nodeClosure_chart_change_ratio
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s : Nat}
    (hRatio : ∀ m ∈ ms, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure ms s n) :
    systemCoord ms (tick10 k n) = systemCoord ms n := by
  have hEq : ∀ m ∈ ms,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    simpa [CycleStepOrbit.orbitSize] using hRatio m hm
  exact systemCoord_invariant_of_nodeClosure_chart_change n k ms hn hcop hpos hEq hnode

theorem systemCoord_invariant_of_nodeClosure_chart_change_coprime
    (n k : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hcop : ms.Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms, 0 < m)
    {s : Nat}
    (hcopS : ∀ m ∈ ms, Nat.Coprime m s)
    (hcopTick : ∀ m ∈ ms, Nat.Coprime m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure ms s n) :
    systemCoord ms (tick10 k n) = systemCoord ms n := by
  have hEq : ∀ m ∈ ms,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    have hs : CycleStepOrbit.orbitSize m s = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopS m hm)
    have ht : CycleStepOrbit.orbitSize m (10 ^ k - 1) = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopTick m hm)
    simp [hs, ht]
  exact systemCoord_invariant_of_nodeClosure_chart_change n k ms hn hcop hpos hEq hnode

theorem systemCoord_invariant_of_nodeClosure_append
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime)
    (h₁ : CycleStepOrbit.nodeClosure ms₁ (10 ^ k - 1) n)
    (h₂ : CycleStepOrbit.nodeClosure ms₂ (10 ^ k - 1) n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  have happ : CycleStepOrbit.nodeClosure (ms₁ ++ ms₂) (10 ^ k - 1) n := by
    exact
      (CycleStepOrbit.nodeClosure_append_iff (ms₁ := ms₁) (ms₂ := ms₂)
        (hcop := hcop) (s := 10 ^ k - 1) (n := n)).2 ⟨h₁, h₂⟩
  exact systemCoord_invariant_of_nodeClosure n k (ms₁ ++ ms₂) hn hcop happ

theorem systemCoord_invariant_of_nodeClosure_chart_change_append
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hEq : ∀ m ∈ ms₁ ++ ms₂,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure (ms₁ ++ ms₂) s n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  exact
    systemCoord_invariant_of_nodeClosure_chart_change n k (ms₁ ++ ms₂) hn hcop hpos hEq hnode

theorem systemCoord_invariant_of_nodeClosure_chart_change_append_ratio
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hRatio : ∀ m ∈ ms₁ ++ ms₂, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure (ms₁ ++ ms₂) s n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  have hEq : ∀ m ∈ ms₁ ++ ms₂,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    simpa [CycleStepOrbit.orbitSize] using hRatio m hm
  exact
    systemCoord_invariant_of_nodeClosure_chart_change_append
      n k ms₁ ms₂ hn hcop hpos hEq hnode

theorem systemCoord_invariant_of_nodeClosure_chart_change_append_coprime
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hcopS : ∀ m ∈ ms₁ ++ ms₂, Nat.Coprime m s)
    (hcopTick : ∀ m ∈ ms₁ ++ ms₂, Nat.Coprime m (10 ^ k - 1))
    (hnode : CycleStepOrbit.nodeClosure (ms₁ ++ ms₂) s n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  have hEq : ∀ m ∈ ms₁ ++ ms₂,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    have hs : CycleStepOrbit.orbitSize m s = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopS m hm)
    have ht : CycleStepOrbit.orbitSize m (10 ^ k - 1) = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopTick m hm)
    simp [hs, ht]
  exact
    systemCoord_invariant_of_nodeClosure_chart_change_append
      n k ms₁ ms₂ hn hcop hpos hEq hnode

theorem systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hEq₁ : ∀ m ∈ ms₁, CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1))
    (hEq₂ : ∀ m ∈ ms₂, CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1))
    (h₁ : CycleStepOrbit.nodeClosure ms₁ s n)
    (h₂ : CycleStepOrbit.nodeClosure ms₂ s n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  rcases (List.pairwise_append.1 hcop) with ⟨hcop₁, hcop₂, _hcross⟩
  have hpos₁ : ∀ m ∈ ms₁, 0 < m := by
    intro m hm
    exact hpos m (List.mem_append.2 (Or.inl hm))
  have hpos₂ : ∀ m ∈ ms₂, 0 < m := by
    intro m hm
    exact hpos m (List.mem_append.2 (Or.inr hm))
  have h₁tick : CycleStepOrbit.nodeClosure ms₁ (10 ^ k - 1) n := by
    exact
      (CycleStepOrbit.nodeClosure_iff_of_forall_mem_orbitSize_eq
        (ms := ms₁) (hcop := hcop₁) (hpos := hpos₁)
        (s₁ := s) (s₂ := 10 ^ k - 1) (n := n) hEq₁).1 h₁
  have h₂tick : CycleStepOrbit.nodeClosure ms₂ (10 ^ k - 1) n := by
    exact
      (CycleStepOrbit.nodeClosure_iff_of_forall_mem_orbitSize_eq
        (ms := ms₂) (hcop := hcop₂) (hpos := hpos₂)
        (s₁ := s) (s₂ := 10 ^ k - 1) (n := n) hEq₂).1 h₂
  exact systemCoord_invariant_of_nodeClosure_append n k ms₁ ms₂ hn hcop h₁tick h₂tick

theorem systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts_ratio
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hRatio₁ : ∀ m ∈ ms₁, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (hRatio₂ : ∀ m ∈ ms₂, m / Nat.gcd m s = m / Nat.gcd m (10 ^ k - 1))
    (h₁ : CycleStepOrbit.nodeClosure ms₁ s n)
    (h₂ : CycleStepOrbit.nodeClosure ms₂ s n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  have hEq₁ : ∀ m ∈ ms₁,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    simpa [CycleStepOrbit.orbitSize] using hRatio₁ m hm
  have hEq₂ : ∀ m ∈ ms₂,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    simpa [CycleStepOrbit.orbitSize] using hRatio₂ m hm
  exact
    systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts
      n k ms₁ ms₂ hn hcop hpos hEq₁ hEq₂ h₁ h₂

theorem systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts_coprime
    (n k : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hcop : (ms₁ ++ ms₂).Pairwise Nat.Coprime) (hpos : ∀ m ∈ ms₁ ++ ms₂, 0 < m)
    {s : Nat}
    (hcopS₁ : ∀ m ∈ ms₁, Nat.Coprime m s)
    (hcopS₂ : ∀ m ∈ ms₂, Nat.Coprime m s)
    (hcopTick₁ : ∀ m ∈ ms₁, Nat.Coprime m (10 ^ k - 1))
    (hcopTick₂ : ∀ m ∈ ms₂, Nat.Coprime m (10 ^ k - 1))
    (h₁ : CycleStepOrbit.nodeClosure ms₁ s n)
    (h₂ : CycleStepOrbit.nodeClosure ms₂ s n) :
    systemCoord (ms₁ ++ ms₂) (tick10 k n) = systemCoord (ms₁ ++ ms₂) n := by
  have hEq₁ : ∀ m ∈ ms₁,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    have hs : CycleStepOrbit.orbitSize m s = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopS₁ m hm)
    have ht : CycleStepOrbit.orbitSize m (10 ^ k - 1) = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopTick₁ m hm)
    simp [hs, ht]
  have hEq₂ : ∀ m ∈ ms₂,
      CycleStepOrbit.orbitSize m s = CycleStepOrbit.orbitSize m (10 ^ k - 1) := by
    intro m hm
    have hs : CycleStepOrbit.orbitSize m s = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopS₂ m hm)
    have ht : CycleStepOrbit.orbitSize m (10 ^ k - 1) = m :=
      CycleStepOrbit.orbitSize_eq_modulus_of_coprime (hcopTick₂ m hm)
    simp [hs, ht]
  exact
    systemCoord_invariant_of_nodeClosure_chart_change_append_of_parts
      n k ms₁ ms₂ hn hcop hpos hEq₁ hEq₂ h₁ h₂

theorem systemCoord_append (ms₁ ms₂ : List Nat) (n : Nat) :
    systemCoord (ms₁ ++ ms₂) n =
      (UniversalTicks.leadingBlock n,
        (ms₁.map (fun m => n % m)) ++ (ms₂.map (fun m => n % m))) := by
  simp [systemCoord, List.map_append]

/--
At the global return tick `totientLCM ms`, the `systemCoord ms` is invariant (for `n ≠ 0`),
provided all axes are valid (`1 < m`) and coprime to `10`.

This makes “systems become nodes of other systems” precise:
the whole finite system state is a stable, composable label under the tick action.
-/
theorem systemCoord_invariant_at_totientLCM (n : Nat) (ms : List Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoord ms (tick10 (totientLCM ms) n) = systemCoord ms n := by
  have hblock := tick10_totientLCM_leadingBlock_invariant n ms hn hgt hcop
  have hmods := tick10_totientLCM_mod_invariant n ms hn hgt hcop
  unfold systemCoord
  -- First coordinate: leading block.
  apply Prod.ext
  · exact hblock
  · -- Second coordinate: residue vector (from pointwise invariance).
    -- Keep the tick length constant, and use a small induction to lift pointwise equalities to `map`.
    let K := totientLCM ms
    have hmap :
        ∀ ms' : List Nat,
          (∀ m ∈ ms', (tick10 K n) % m = n % m) →
            ms'.map (fun m => (tick10 K n) % m) = ms'.map (fun m => n % m) := by
      intro ms' hmods'
      induction ms' with
      | nil =>
          simp
      | cons a ms' ih =>
          have ha : (tick10 K n) % a = n % a := hmods' a (by simp)
          have ht : ∀ m ∈ ms', (tick10 K n) % m = n % m := by
            intro m hm
            exact hmods' m (by simp [hm])
          simp [ha, ih ht]
    -- `hmods` is exactly the pointwise hypothesis for `ms` at tick `K = totientLCM ms`.
    have : ms.map (fun m => (tick10 K n) % m) = ms.map (fun m => n % m) := by
      -- Rewrite `hmods` using the definitional equality `K = totientLCM ms`.
      simpa [K] using (hmap ms hmods)
    simpa [systemCoord, K, tick10] using this

theorem systemCoord_invariant_at_globalTick (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoord ms (tick10 (globalTick ms a₂ a₅) n) = systemCoord ms n := by
  have hblock :
      UniversalTicks.leadingBlock (tick10 (globalTick ms a₂ a₅) n) = UniversalTicks.leadingBlock n := by
    simpa [tick10] using UniversalTicks.leadingBlock_mul_pow10 n (globalTick ms a₂ a₅) hn
  have hmods : ∀ m ∈ ms, (tick10 (globalTick ms a₂ a₅) n) % m = n % m := by
    intro m hm
    have hm1 : 1 < m := hgt m hm
    have hc : (10 : Nat).Coprime m := hcop m hm
    have hk0 : (10 ^ Nat.totient m : Nat) % m = 1 := ten_pow_totient_mod_eq_one m hm1 hc
    have hdivTot : Nat.totient m ∣ totientLCM ms := totient_dvd_totientLCM_of_mem m ms hm
    have hdivK : Nat.totient m ∣ globalTick ms a₂ a₅ := by
      unfold globalTick
      exact dvd_mul_of_dvd_left hdivTot (Nat.max a₂ a₅ + 1)
    exact tick10_mod_invariant_of_dvd n m (Nat.totient m) (globalTick ms a₂ a₅) hm1 hk0 hdivK
  unfold systemCoord
  apply Prod.ext
  · exact hblock
  ·
    let K := globalTick ms a₂ a₅
    have hmap :
        ∀ ms' : List Nat,
          (∀ m ∈ ms', (tick10 K n) % m = n % m) →
            ms'.map (fun m => (tick10 K n) % m) = ms'.map (fun m => n % m) := by
      intro ms' hmods'
      induction ms' with
      | nil =>
          simp
      | cons a ms' ih =>
          have ha : (tick10 K n) % a = n % a := hmods' a (by simp)
          have ht : ∀ m ∈ ms', (tick10 K n) % m = n % m := by
            intro m hm
            exact hmods' m (by simp [hm])
          simp [ha, ih ht]
    have : ms.map (fun m => (tick10 K n) % m) = ms.map (fun m => n % m) := by
      simpa [K] using (hmap ms hmods)
    simpa [systemCoord, K, tick10] using this

theorem systemCoord_invariant_at_globalTick_add
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoord ms (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      systemCoord ms n := by
  have hB :=
    systemCoord_invariant_at_globalTick
      (n := n) (ms := ms) (a₂ := b₂) (a₅ := b₅) hn hgt hcop
  have hnB : tick10 (globalTick ms b₂ b₅) n ≠ 0 :=
    tick10_ne_zero (globalTick ms b₂ b₅) n hn
  have hA :=
    systemCoord_invariant_at_globalTick
      (n := tick10 (globalTick ms b₂ b₅) n)
      (ms := ms) (a₂ := a₂) (a₅ := a₅) hnB hgt hcop
  rw [← tick10_add (globalTick ms a₂ a₅) (globalTick ms b₂ b₅) n]
  exact hA.trans hB

theorem systemCoord_invariant_at_lcm_subsystems (n : Nat) (ms₁ ms₂ : List Nat) (hn : n ≠ 0)
    (hgt₁ : ∀ m ∈ ms₁, 1 < m) (hgt₂ : ∀ m ∈ ms₂, 1 < m)
    (hcop₁ : ∀ m ∈ ms₁, (10 : Nat).Coprime m) (hcop₂ : ∀ m ∈ ms₂, (10 : Nat).Coprime m) :
    systemCoord (ms₁ ++ ms₂) (tick10 (Nat.lcm (totientLCM ms₁) (totientLCM ms₂)) n) =
      systemCoord (ms₁ ++ ms₂) n := by
  -- Lift the per-subsystem conditions to the concatenated family.
  have hgt : ∀ m ∈ ms₁ ++ ms₂, 1 < m := by
    intro m hm
    have : m ∈ ms₁ ∨ m ∈ ms₂ := by
      simpa using (List.mem_append.1 hm)
    cases this with
    | inl h => exact hgt₁ m h
    | inr h => exact hgt₂ m h
  have hcop : ∀ m ∈ ms₁ ++ ms₂, (10 : Nat).Coprime m := by
    intro m hm
    have : m ∈ ms₁ ∨ m ∈ ms₂ := by
      simpa using (List.mem_append.1 hm)
    cases this with
    | inl h => exact hcop₁ m h
    | inr h => exact hcop₂ m h
  -- Apply the general finite-family invariance, then rewrite the tick length by `totientLCM_append`.
  simpa [totientLCM_append] using
    (systemCoord_invariant_at_totientLCM n (ms₁ ++ ms₂) hn hgt hcop)

-- ------------------------------------------------------------
-- Worked example: build a system from subsystems (nodes of nodes)
-- ------------------------------------------------------------

theorem totientLCM_3_11 : totientLCM ([3, 11] : List Nat) = 10 := by
  native_decide

theorem totientLCM_13 : totientLCM ([13] : List Nat) = 12 := by
  native_decide

theorem totientLCM_3_11_13 : totientLCM ([3, 11, 13] : List Nat) = 60 := by
  native_decide

theorem systemCoord_example_3_11_13 (n : Nat) (hn : n ≠ 0) :
    systemCoord ([3, 11, 13] : List Nat) (tick10 60 n) =
      systemCoord ([3, 11, 13] : List Nat) n := by
  have hgt : ∀ m ∈ ([3, 11, 13] : List Nat), 1 < m := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl | rfl <;> decide
  have hcop : ∀ m ∈ ([3, 11, 13] : List Nat), (10 : Nat).Coprime m := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl | rfl <;> decide
  -- Use the general finite-family system-node invariance, then rewrite the tick length to `60`.
  simpa [totientLCM_3_11_13] using
    (systemCoord_invariant_at_totientLCM n ([3, 11, 13] : List Nat) hn hgt hcop)

theorem systemCoord_example_build_from_subsystems (n : Nat) (hn : n ≠ 0) :
    systemCoord (([3, 11] : List Nat) ++ ([13] : List Nat))
        (tick10 (Nat.lcm 10 12) n) =
      systemCoord (([3, 11] : List Nat) ++ ([13] : List Nat)) n := by
  have hgt₁ : ∀ m ∈ ([3, 11] : List Nat), 1 < m := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl <;> decide
  have hgt₂ : ∀ m ∈ ([13] : List Nat), 1 < m := by
    intro m hm
    simp at hm
    rcases hm with rfl
    decide
  have hcop₁ : ∀ m ∈ ([3, 11] : List Nat), (10 : Nat).Coprime m := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl <;> decide
  have hcop₂ : ∀ m ∈ ([13] : List Nat), (10 : Nat).Coprime m := by
    intro m hm
    simp at hm
    rcases hm with rfl
    decide
  -- Use the subsystem composition theorem, then rewrite the subsystem ticks to `10` and `12`.
  simpa [totientLCM_3_11, totientLCM_13] using
    (systemCoord_invariant_at_lcm_subsystems n ([3, 11] : List Nat) ([13] : List Nat) hn hgt₁ hgt₂ hcop₁ hcop₂)

-- ------------------------------------------------------------
-- Concrete axis examples (small moduli)
-- ------------------------------------------------------------

theorem ten_pow_one_mod3 : (10 ^ 1 : Nat) % 3 = 1 := by
  native_decide

theorem tick10_mod3_return_every_decade (n : Nat) : (tick10 1 n) % 3 = n % 3 := by
  exact tick10_mod_invariant n 1 3 (by decide) ten_pow_one_mod3

-- ------------------------------------------------------------
-- Absorption thresholds on 2^a and 5^a (base-10 carries these factors)
-- ------------------------------------------------------------

theorem ten_pow_mod_pow2_eq_zero (a k : Nat) (hak : a ≤ k) :
    (10 ^ k : Nat) % (2 ^ a) = 0 := by
  have h1 : (2 : Nat) ^ a ∣ (2 : Nat) ^ k := pow_dvd_pow (a := (2 : Nat)) hak
  have h2 : (2 : Nat) ^ k ∣ (10 : Nat) ^ k := by
    exact pow_dvd_pow_of_dvd (by decide : (2 : Nat) ∣ 10) k
  exact Nat.mod_eq_zero_of_dvd (dvd_trans h1 h2)

theorem tick10_mod_pow2_absorbs (n a k : Nat) (hak : a ≤ k) :
    (tick10 k n) % (2 ^ a) = 0 := by
  exact tick10_mod_absorb n k (2 ^ a) (ten_pow_mod_pow2_eq_zero a k hak)

theorem ten_pow_mod_pow5_eq_zero (a k : Nat) (hak : a ≤ k) :
    (10 ^ k : Nat) % (5 ^ a) = 0 := by
  have h1 : (5 : Nat) ^ a ∣ (5 : Nat) ^ k := pow_dvd_pow (a := (5 : Nat)) hak
  have h2 : (5 : Nat) ^ k ∣ (10 : Nat) ^ k := by
    exact pow_dvd_pow_of_dvd (by decide : (5 : Nat) ∣ 10) k
  exact Nat.mod_eq_zero_of_dvd (dvd_trans h1 h2)

theorem tick10_mod_pow5_absorbs (n a k : Nat) (hak : a ≤ k) :
    (tick10 k n) % (5 ^ a) = 0 := by
  exact tick10_mod_absorb n k (5 ^ a) (ten_pow_mod_pow5_eq_zero a k hak)

-- ------------------------------------------------------------
-- One global tick: return on coprime axes + absorb on 2/5 axes
-- ------------------------------------------------------------

--
-- This packages the idea that base-10 ticks simultaneously drive:
-- * cycle returns on invertible axes (odd moduli coprime to 10),
-- * convergence/absorption on the 2/5 axes inherent in decimal scaling.
--

theorem totientLCM_dvd_globalTick (ms : List Nat) (a₂ a₅ : Nat) :
    totientLCM ms ∣ globalTick ms a₂ a₅ := by
  simp [globalTick]

theorem totientLCM_pos_of_gt (ms : List Nat) (hgt : ∀ m ∈ ms, 1 < m) :
    0 < totientLCM ms := by
  induction ms with
  | nil =>
      simp [totientLCM]
  | cons a ms ih =>
      have ha : 1 < a := hgt a (by simp)
      have ha0 : 0 < a := lt_trans Nat.zero_lt_one ha
      have ht : 0 < Nat.totient a := (Nat.totient_pos.2 ha0)
      have hgt' : ∀ m ∈ ms, 1 < m := by
        intro m hm
        exact hgt m (by simp [hm])
      have ih' : 0 < totientLCM ms := ih hgt'
      -- `lcm` of positive numbers is positive.
      simpa [totientLCM] using (Nat.lcm_pos ht ih')

theorem max_le_globalTick_of_gt (ms : List Nat) (a₂ a₅ : Nat) (hgt : ∀ m ∈ ms, 1 < m) :
    Nat.max a₂ a₅ ≤ globalTick ms a₂ a₅ := by
  have h1 : Nat.max a₂ a₅ ≤ Nat.max a₂ a₅ + 1 := Nat.le_succ _
  have hpos : 0 < totientLCM ms := totientLCM_pos_of_gt ms hgt
  have h2 : Nat.max a₂ a₅ + 1 ≤ globalTick ms a₂ a₅ := by
    -- `x ≤ (totientLCM ms) * x` when `totientLCM ms > 0`.
    simpa [globalTick] using (Nat.le_mul_of_pos_left (Nat.max a₂ a₅ + 1) hpos)
  exact le_trans h1 h2

/--
At the single tick `globalTick ms a₂ a₅`, we get the combined behavior:

* the **leading block** (base-10 scale axis) is invariant (for `n ≠ 0`),
* every axis `m ∈ ms` with `gcd(10,m)=1` returns to the same residue, and
* the absorption axes `2^a₂` and `5^a₅` collapse to `0`.
-/
theorem tick10_globalTick_return_and_absorb (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    UniversalTicks.leadingBlock (tick10 (globalTick ms a₂ a₅) n) = UniversalTicks.leadingBlock n
      ∧ (∀ m ∈ ms, (tick10 (globalTick ms a₂ a₅) n) % m = n % m)
      ∧ (tick10 (globalTick ms a₂ a₅) n) % (2 ^ a₂) = 0
      ∧ (tick10 (globalTick ms a₂ a₅) n) % (5 ^ a₅) = 0 := by
  constructor
  ·
    simpa [tick10] using UniversalTicks.leadingBlock_mul_pow10 n (globalTick ms a₂ a₅) hn
  constructor
  ·
    intro m hm
    have hm1 : 1 < m := hgt m hm
    have hc : (10 : Nat).Coprime m := hcop m hm
    have hk0 : (10 ^ Nat.totient m : Nat) % m = 1 := ten_pow_totient_mod_eq_one m hm1 hc
    have hdivTot : Nat.totient m ∣ totientLCM ms := totient_dvd_totientLCM_of_mem m ms hm
    have hdivK : Nat.totient m ∣ globalTick ms a₂ a₅ :=
      dvd_trans hdivTot (totientLCM_dvd_globalTick ms a₂ a₅)
    exact tick10_mod_invariant_of_dvd n m (Nat.totient m) (globalTick ms a₂ a₅) hm1 hk0 hdivK
  constructor
  ·
    have ha : a₂ ≤ globalTick ms a₂ a₅ :=
      le_trans (Nat.le_max_left _ _) (max_le_globalTick_of_gt ms a₂ a₅ hgt)
    exact tick10_mod_pow2_absorbs n a₂ (globalTick ms a₂ a₅) ha
  ·
    have ha : a₅ ≤ globalTick ms a₂ a₅ :=
      le_trans (Nat.le_max_right _ _) (max_le_globalTick_of_gt ms a₂ a₅ hgt)
    exact tick10_mod_pow5_absorbs n a₅ (globalTick ms a₂ a₅) ha

theorem tick10_globalTick_leadingBlock_invariant
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    UniversalTicks.leadingBlock (tick10 (globalTick ms a₂ a₅) n) = UniversalTicks.leadingBlock n := by
  exact (tick10_globalTick_return_and_absorb n ms a₂ a₅ hn hgt hcop).1

theorem tick10_globalTick_mod_invariant
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    ∀ m ∈ ms, (tick10 (globalTick ms a₂ a₅) n) % m = n % m := by
  exact (tick10_globalTick_return_and_absorb n ms a₂ a₅ hn hgt hcop).2.1

theorem tick10_globalTick_mod_pow2_absorb
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (tick10 (globalTick ms a₂ a₅) n) % (2 ^ a₂) = 0 := by
  exact (tick10_globalTick_return_and_absorb n ms a₂ a₅ hn hgt hcop).2.2.1

theorem tick10_globalTick_mod_pow5_absorb
    (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    (tick10 (globalTick ms a₂ a₅) n) % (5 ^ a₅) = 0 := by
  exact (tick10_globalTick_return_and_absorb n ms a₂ a₅ hn hgt hcop).2.2.2

/--
Package a mixed “observer state”:

- `leadingBlock n` (scale axis),
- residues mod a finite coprime family `ms` (cycle-return axes),
- residues mod `2^a₂` and `5^a₅` (absorption axes).

This is a concrete, composable “node label” for a multidimensional system.
-/
def systemCoordMixed (ms : List Nat) (a₂ a₅ : Nat) (n : Nat) : Nat × List Nat × Nat × Nat :=
  (UniversalTicks.leadingBlock n, ms.map (fun m => n % m), n % (2 ^ a₂), n % (5 ^ a₅))

/--
At the single tick `globalTick ms a₂ a₅`, the mixed observer-state `systemCoordMixed` is invariant
for its cycle-return axes, and absorbed to `0` on the 2/5 axes.

This is the discrete “projection law” skeleton: some coordinates return (permutation/identity),
others converge (projection to a fixed value), under the same tick.
-/
theorem systemCoordMixed_invariant_at_globalTick (n : Nat) (ms : List Nat) (a₂ a₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅) n) =
      (UniversalTicks.leadingBlock n, ms.map (fun m => n % m), 0, 0) := by
  have hblock :=
    tick10_globalTick_leadingBlock_invariant n ms a₂ a₅ hn hgt hcop
  have hmods :=
    tick10_globalTick_mod_invariant n ms a₂ a₅ hn hgt hcop
  have h2 :=
    tick10_globalTick_mod_pow2_absorb n ms a₂ a₅ hn hgt hcop
  have h5 :=
    tick10_globalTick_mod_pow5_absorb n ms a₂ a₅ hn hgt hcop
  unfold systemCoordMixed
  -- Reduce to componentwise equalities.
  apply Prod.ext
  · -- leadingBlock
    exact hblock
  · -- rest of the tuple: (residue vector, mod 2^a₂, mod 5^a₅)
    -- Turn the `∀ m ∈ ms` pointwise invariance into equality of `map`.
    let K := globalTick ms a₂ a₅
    have hmap :
        ∀ ms' : List Nat,
          (∀ m ∈ ms', (tick10 K n) % m = n % m) →
            ms'.map (fun m => (tick10 K n) % m) = ms'.map (fun m => n % m) := by
      intro ms' hmods'
      induction ms' with
      | nil =>
          simp
      | cons a ms' ih =>
          have ha : (tick10 K n) % a = n % a := hmods' a (by simp)
          have ht : ∀ m ∈ ms', (tick10 K n) % m = n % m := by
            intro m hm
            exact hmods' m (by simp [hm])
          simp [ha, ih ht]
    have : ms.map (fun m => (tick10 K n) % m) = ms.map (fun m => n % m) := by
      simpa [K] using (hmap ms hmods)
    -- Assemble the nested products.
    -- Second component: residue vector; third/fourth: absorbed to 0.
    -- `Prod.ext` on the nested pair `List Nat × Nat × Nat`.
    apply Prod.ext
    · -- residue vector
      simpa [K] using this
    · -- (mod 2^a₂, mod 5^a₅)
      apply Prod.ext
      · simpa using h2
      · simpa using h5

theorem systemCoordMixed_invariant_at_globalTick_add
    (n : Nat) (ms : List Nat) (a₂ a₅ b₂ b₅ : Nat) (hn : n ≠ 0)
    (hgt : ∀ m ∈ ms, 1 < m) (hcop : ∀ m ∈ ms, (10 : Nat).Coprime m) :
    systemCoordMixed ms a₂ a₅ (tick10 (globalTick ms a₂ a₅ + globalTick ms b₂ b₅) n) =
      (UniversalTicks.leadingBlock n, ms.map (fun m => n % m), 0, 0) := by
  let Ka := globalTick ms a₂ a₅
  let Kb := globalTick ms b₂ b₅
  have hnB : tick10 Kb n ≠ 0 := tick10_ne_zero Kb n hn
  have hA :=
    systemCoordMixed_invariant_at_globalTick
      (n := tick10 Kb n) (ms := ms) (a₂ := a₂) (a₅ := a₅) hnB hgt hcop
  have hBsys :=
    systemCoord_invariant_at_globalTick
      (n := n) (ms := ms) (a₂ := b₂) (a₅ := b₅) hn hgt hcop
  have hBblock : UniversalTicks.leadingBlock (tick10 Kb n) = UniversalTicks.leadingBlock n := by
    have hfst := congrArg Prod.fst hBsys
    simpa [systemCoord] using hfst
  have hBmods : ms.map (fun m => (tick10 Kb n) % m) = ms.map (fun m => n % m) := by
    have hsnd := congrArg Prod.snd hBsys
    simpa [systemCoord] using hsnd
  have hA' :
      systemCoordMixed ms a₂ a₅ (tick10 (Ka + Kb) n) =
        (UniversalTicks.leadingBlock (tick10 Kb n), ms.map (fun m => (tick10 Kb n) % m), 0, 0) := by
    simpa [Ka, Kb, tick10_add] using hA
  calc
    systemCoordMixed ms a₂ a₅ (tick10 (Ka + Kb) n)
      = (UniversalTicks.leadingBlock (tick10 Kb n), ms.map (fun m => (tick10 Kb n) % m), 0, 0) := hA'
    _ = (UniversalTicks.leadingBlock n, ms.map (fun m => n % m), 0, 0) := by
      simp [hBblock, hBmods]

theorem ten_pow_one_mod2 : (10 ^ 1 : Nat) % 2 = 0 := by
  native_decide

theorem tick10_mod2_absorbs_after_one_decade (n : Nat) : (tick10 1 n) % 2 = 0 := by
  exact tick10_mod_absorb n 1 2 ten_pow_one_mod2

theorem ten_pow_one_mod5 : (10 ^ 1 : Nat) % 5 = 0 := by
  native_decide

theorem tick10_mod5_absorbs_after_one_decade (n : Nat) : (tick10 1 n) % 5 = 0 := by
  exact tick10_mod_absorb n 1 5 ten_pow_one_mod5

theorem ten_pow_two_mod11 : (10 ^ 2 : Nat) % 11 = 1 := by
  native_decide

theorem tick10_mod11_return_every_two_decades (n : Nat) : (tick10 2 n) % 11 = n % 11 := by
  exact tick10_mod_invariant n 2 11 (by decide) ten_pow_two_mod11

theorem tick10_mod13_return_every_six_decades (n : Nat) : (tick10 6 n) % 13 = n % 13 := by
  -- Reuse the dedicated mod-13 lemma.
  simpa [tick10, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    DecimalMod13.mul_ten_pow_six_mod13 n

theorem ten_pow_two_mod4 : (10 ^ 2 : Nat) % 4 = 0 := by
  native_decide

theorem tick10_mod4_absorbs_after_two_decades (n : Nat) : (tick10 2 n) % 4 = 0 := by
  exact tick10_mod_absorb n 2 4 ten_pow_two_mod4

end MultidimensionalTicks
