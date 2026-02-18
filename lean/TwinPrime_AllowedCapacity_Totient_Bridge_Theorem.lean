import Mathlib
import TwinPrime_AllowedCapacity_Density_Theorem

/-!
# Twin-Prime Allowed-Capacity vs Euler Totient (φ) Bridge

This file adds a **structural comparison** between:

- the certified **allowed-channel capacity** for the twin-prime predicate `x ≠ 0, -2` on each axis, and
- the classical **unit density** given by Euler's totient function `φ`.

For a prime-power axis `p^(k+1)` with `p > 2`:

- allowed channels: `(p-2)·p^k`
- units (coprime residues): `φ(p^(k+1)) = p^k·(p-1)`

So the **density ratio** is exponent-independent:

`((p-2)·p^k)/(p^k·(p-1)) = (p-2)/(p-1)`.

We keep this as a mechanism theorem only: it compares channel *counts/densities*.
No claim about prime occupancy.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityTotientBridge

open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityCRTList

/-! ## Totient multiplicativity on pairwise-coprime lists -/

theorem totient_prod_of_pairwise_coprime :
    ∀ (l : List Nat), l.Pairwise Nat.Coprime → Nat.totient l.prod = (l.map Nat.totient).prod := by
  intro l hl
  induction l with
  | nil =>
      simp
  | cons n ns ih =>
      have hhead : ∀ m ∈ ns, Nat.Coprime n m := (List.pairwise_cons.mp hl).1
      have htail : ns.Pairwise Nat.Coprime := (List.pairwise_cons.mp hl).2
      have hcop : Nat.Coprime n ns.prod := Nat.coprime_list_prod_right_iff.mpr hhead
      -- Use `φ(n*Π) = φ(n)*φ(Π)` and fold the tail by IH.
      simpa [List.prod_cons, List.map_cons, Nat.totient_mul hcop] using
        congrArg (fun t => Nat.totient n * t) (ih htail)

/-! ## Per-axis totient density for prime powers -/

namespace PrimePow

theorem totientDensity_formula (pp : PrimePow) (hp : Nat.Prime pp.p) :
    ((Nat.totient pp.modulus : Nat) : ℚ) / (pp.modulus : ℚ) = ((pp.p - 1 : ℚ) / (pp.p : ℚ)) := by
  have hp0_nat : pp.p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two pp.hp)
  have hp0 : (pp.p : ℚ) ≠ 0 := by exact_mod_cast hp0_nat
  have hk0 : ((pp.p : ℚ) ^ pp.k) ≠ 0 := pow_ne_zero _ hp0
  have hp1 : (1 : Nat) ≤ pp.p := Nat.succ_le_of_lt (lt_trans Nat.zero_lt_two pp.hp)

  calc
    ((Nat.totient pp.modulus : Nat) : ℚ) / (pp.modulus : ℚ)
        = ((pp.p ^ pp.k * (pp.p - 1) : Nat) : ℚ) / (pp.modulus : ℚ) := by
            have : Nat.totient (pp.p ^ (pp.k + 1)) = pp.p ^ pp.k * (pp.p - 1) := by
              simpa using (Nat.totient_prime_pow_succ hp pp.k)
            simp [PrimePow.modulus, this]
    _ = ((pp.p ^ pp.k * (pp.p - 1) : Nat) : ℚ) / ((pp.p ^ (pp.k + 1) : Nat) : ℚ) := by
          simp [PrimePow.modulus]
    _ = ((pp.p : ℚ) ^ pp.k * (pp.p - 1 : ℚ)) / ((pp.p : ℚ) ^ pp.k * (pp.p : ℚ)) := by
          simp [pow_succ, Nat.cast_sub hp1]
    _ = ((pp.p - 1 : ℚ) / (pp.p : ℚ)) := by
          simpa using (mul_div_mul_left (pp.p - 1 : ℚ) (pp.p : ℚ) hk0)

end PrimePow

/-! ## Product identity: totient density and density-ratio bridge -/

theorem prod_div_prod_eq_prod_div {ι : Type*} (l : List ι) (f g : ι → ℚ) :
    (l.map f).prod / (l.map g).prod = (l.map (fun i => f i / g i)).prod := by
  induction l with
  | nil =>
      simp
  | cons a as ih =>
      simp [List.prod_cons, ih, mul_div_mul_comm]

/--
Pure algebra: for each axis `p` we have

`((p-2)/p) / ((p-1)/p) = (p-2)/(p-1)`,

so the ratio of products is the product of ratios.

This is intentionally **mechanism-only**: it is an identity in `ℚ`, independent of primality
or CRT assumptions.
-/
theorem prod_allowed_over_totient_simplify (pps : List PrimePow) :
    (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod /
        (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod =
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod := by
  -- First rewrite as a product of pointwise ratios, then simplify each axis.
  calc
    (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod /
        (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod =
      (pps.map (fun pp =>
          (((pp.p - 2 : ℚ) / (pp.p : ℚ)) / ((pp.p - 1 : ℚ) / (pp.p : ℚ))))).prod := by
        simpa using
          (prod_div_prod_eq_prod_div (l := pps)
            (f := fun pp : PrimePow => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))
            (g := fun pp : PrimePow => ((pp.p - 1 : ℚ) / (pp.p : ℚ))))
    _ = (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod := by
          induction pps with
          | nil =>
              simp
          | cons pp ps ih =>
              have hp0_nat : pp.p ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_two pp.hp)
              have hp0 : (pp.p : ℚ) ≠ 0 := by exact_mod_cast hp0_nat
              have hhead :
                  (((pp.p - 2 : ℚ) / (pp.p : ℚ)) / ((pp.p - 1 : ℚ) / (pp.p : ℚ))) =
                    ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)) := by
                field_simp [hp0]
              -- Expand the list products; then rewrite head and tail explicitly.
              -- Using `simp` to cancel common factors introduces `Or` goals via `mul_eq_mul_left_iff`.
              simp [List.prod_cons]
              rw [hhead, ih]

/--
List-level rewrite for the unit-density ratios:

`∏ (φ(m_i)/m_i) = ∏ ((p_i-1)/p_i)` for prime-power moduli `m_i = p_i^(k_i+1)`.

This lemma depends only on the per-axis prime hypothesis (not on CRT coprimality).
-/
theorem totientDensity_ratio_list_eq (pps : List PrimePow)
    (hprime : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p) :
    (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ) / (n : ℚ)) (mods pps)).prod =
      (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod := by
  induction pps with
  | nil =>
      simp [mods]
  | cons pp ps ih =>
      have hp_head : Nat.Prime pp.p := hprime pp.p (by simp)
      have hprime_tail : ∀ p ∈ (ps.map PrimePow.p), Nat.Prime p := by
        intro p hp
        exact hprime p (by simp [hp])
      -- Avoid `simp` cancellation (`mul_eq_mul_left_iff`) which introduces spurious `Or` goals.
      let f : Nat → ℚ := fun n : Nat => ((Nat.totient n : Nat) : ℚ) / (n : ℚ)
      let g : PrimePow → ℚ := fun pp : PrimePow => ((pp.p - 1 : ℚ) / (pp.p : ℚ))
      have htail : (List.map f (mods ps)).prod = (List.map g ps).prod := ih hprime_tail
      calc
        (List.map f (mods (pp :: ps))).prod
            = f pp.modulus * (List.map f (mods ps)).prod := by
                simp [mods, f]
        _ = f pp.modulus * (List.map g ps).prod := by
              simp [htail]
        _ = g pp * (List.map g ps).prod := by
              -- rewrite the head factor by the per-axis prime-power identity
              simp [f, g, PrimePow.totientDensity_formula (pp := pp) hp_head]
        _ = (List.map g (pp :: ps)).prod := by
              simp

/--
Totient density on a prime-power product modulus (distinct primes):

`φ(∏ p^(k+1)) / (∏ p^(k+1)) = ∏ ((p-1)/p)`.

This is the unit-density analogue of `TwinPrimeAllowedCapacityDensity.globalDensity_eq_of_prime_nodup`.
-/
theorem totientDensity_eq_of_prime_nodup (pps : List PrimePow)
    (hprime : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p) (hnodup : (pps.map PrimePow.p).Nodup) :
    ((Nat.totient (mods pps).prod : Nat) : ℚ) / ((mods pps).prod : ℚ) =
      (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod := by
  classical
  -- Distinct primes ⇒ pairwise-coprime bases ⇒ pairwise-coprime prime-power moduli.
  have hpPairs : (pps.map PrimePow.p).Pairwise Nat.Coprime :=
    List.pairwise_coprime_of_prime_nodup hprime hnodup
  have coMods : (mods pps).Pairwise Nat.Coprime :=
    mods_pairwise_coprime_of_p_pairwise_coprime pps hpPairs

  have htotNat : Nat.totient (mods pps).prod = ((mods pps).map Nat.totient).prod :=
    totient_prod_of_pairwise_coprime (l := mods pps) coMods
  have htotQ : ((Nat.totient (mods pps).prod : Nat) : ℚ) = (((mods pps).map Nat.totient).prod : ℚ) := by
    exact_mod_cast htotNat

  -- Push `Nat` casts inside the list products, so we can use `prod_div_prod_eq_prod_div`.
  have hcastNum :
      (((mods pps).map Nat.totient).prod : ℚ) =
        (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ)) (mods pps)).prod := by
    -- Avoid simp-driven coercion rewriting (`List.map` ↔ monadic bind). Prove the list-level
    -- rewrite first, then take `List.prod`.
    have hlist :
        (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ)) (mods pps)) =
          (List.map (fun t : Nat => (t : ℚ)) ((mods pps).map Nat.totient)) := by
      simp [mods, List.map_map, Function.comp]
    have hR :
        (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ)) (mods pps)).prod =
          (List.map (fun t : Nat => (t : ℚ)) ((mods pps).map Nat.totient)).prod := by
      exact congrArg List.prod hlist
    have h := (List.prod_hom (l := (mods pps).map Nat.totient) (f := Nat.castRingHom ℚ))
    calc
      (((mods pps).map Nat.totient).prod : ℚ) =
          (List.map (fun t : Nat => (t : ℚ)) ((mods pps).map Nat.totient)).prod := by
            exact h.symm
      _ =
          (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ)) (mods pps)).prod := by
            exact hR.symm

  have hcastDen : ((mods pps).prod : ℚ) = (List.map (fun n : Nat => (n : ℚ)) (mods pps)).prod := by
    exact (List.prod_hom (l := mods pps) (f := Nat.castRingHom ℚ)).symm

  -- Convert `(∏ φ(n)) / (∏ n)` into `∏ (φ(n)/n)`.
  have hprodRatio :
      (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ)) (mods pps)).prod /
          (List.map (fun n : Nat => (n : ℚ)) (mods pps)).prod =
        (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ) / (n : ℚ)) (mods pps)).prod := by
    -- `/` on `ℚ` is defined; use the general list lemma.
    simpa [div_eq_mul_inv] using
      (prod_div_prod_eq_prod_div (l := mods pps) (f := fun n : Nat => ((Nat.totient n : Nat) : ℚ))
        (g := fun n : Nat => (n : ℚ)))

  have hperAxis :
      (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ) / (n : ℚ)) (mods pps)).prod =
        (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod :=
    totientDensity_ratio_list_eq (pps := pps) hprime

  -- Assemble the final statement.
  calc
    ((Nat.totient (mods pps).prod : Nat) : ℚ) / ((mods pps).prod : ℚ)
        = (((mods pps).map Nat.totient).prod : ℚ) / ((mods pps).prod : ℚ) := by
            simp [htotQ]
    _ = (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ)) (mods pps)).prod /
            (List.map (fun n : Nat => (n : ℚ)) (mods pps)).prod := by
            -- Rewrite both numerator and denominator casts.
            simp [hcastNum, hcastDen]
    _ = (List.map (fun n : Nat => ((Nat.totient n : Nat) : ℚ) / (n : ℚ)) (mods pps)).prod := by
            simpa using hprodRatio
    _ = (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod := by
            simpa using hperAxis

/-
Bridge: allowed-channel density vs unit density.

Combines:
- `TwinPrimeAllowedCapacityDensity.globalDensity_eq_of_prime_nodup` (allowed density `∏ (p-2)/p`)
- `totientDensity_eq_of_prime_nodup` (unit density `∏ (p-1)/p`)

to obtain the ratio `∏ (p-2)/(p-1)`.
-/
theorem allowedDensity_over_totientDensity_eq_of_prime_nodup (pps : List PrimePow)
    (hprime : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p) (hnodup : (pps.map PrimePow.p).Nodup) :
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      ((Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps)
                    (mods_pairwise_coprime_of_p_pairwise_coprime pps
                      (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
          : ℚ) /
          (Nat.totient (mods pps).prod : ℚ)) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod) := by
  classical
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩

  have hAllowed :
      ((Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps)
                    (mods_pairwise_coprime_of_p_pairwise_coprime pps
                      (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
          : ℚ) /
          ((mods pps).prod : ℚ)) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod := by
    simpa using
      (TwinPrimeAllowedCapacityDensity.globalDensity_eq_of_prime_nodup (pps := pps) hprime hnodup)

  have hTot : ((Nat.totient (mods pps).prod : Nat) : ℚ) / ((mods pps).prod : ℚ) =
      (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod :=
    totientDensity_eq_of_prime_nodup (pps := pps) hprime hnodup

  -- Divide the two density identities.
  -- `allowed/totient = (∏ (p-2)/p) / (∏ (p-1)/p) = ∏ (p-2)/(p-1)`.
  -- We keep it as a pure `ℚ` equality.
  --
  -- Note: `/` is `(*)` with inverse, so this is valid even without additional nonzero side-lemmas.
  have hN0 : ((mods pps).prod : ℚ) ≠ 0 := by
    exact_mod_cast (NeZero.ne (mods pps).prod)

  -- Step 1: convert `a/φ(N)` into `(a/N) / (φ(N)/N)` using `N ≠ 0`.
  have hNormalize :
      ((Fintype.card
              ({x : ZMod (mods pps).prod //
                  allowedAxisPow pps
                    (axisEquiv (mods pps)
                      (mods_pairwise_coprime_of_p_pairwise_coprime pps
                        (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
            : ℚ) /
            (Nat.totient (mods pps).prod : ℚ)) =
        (((Fintype.card
                ({x : ZMod (mods pps).prod //
                    allowedAxisPow pps
                      (axisEquiv (mods pps)
                        (mods_pairwise_coprime_of_p_pairwise_coprime pps
                          (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
              : ℚ) /
            ((mods pps).prod : ℚ)) /
          ((((Nat.totient (mods pps).prod : Nat) : ℚ) / ((mods pps).prod : ℚ)))) := by
    -- This is a pure field identity: `a/φ = (a/N)/(φ/N)` when `N ≠ 0`.
    field_simp [hN0]

  -- Step 2: substitute the two density identities.
  have hDensities :
      (((Fintype.card
              ({x : ZMod (mods pps).prod //
                  allowedAxisPow pps
                    (axisEquiv (mods pps)
                      (mods_pairwise_coprime_of_p_pairwise_coprime pps
                        (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
            : ℚ) /
            ((mods pps).prod : ℚ)) /
          ((((Nat.totient (mods pps).prod : Nat) : ℚ) / ((mods pps).prod : ℚ)))) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod /
          (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod := by
    -- Avoid `simp` here: it rewrites `↑(mods pps).prod` into `List.map Nat.cast ...` and then
    -- `hAllowed` / `hTot` no longer match syntactically. Direct rewriting is stable.
    rw [hAllowed, hTot]

  -- Step 3: simplify the ratio of products (pure algebra, no CRT/primality assumptions needed).
  have hProdQuot :
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod /
          (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod :=
    prod_allowed_over_totient_simplify (pps := pps)

  -- Assemble the proof.
  calc
    ((Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps)
                    (mods_pairwise_coprime_of_p_pairwise_coprime pps
                      (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
          : ℚ) /
          (Nat.totient (mods pps).prod : ℚ)
        =
          (((Fintype.card
                ({x : ZMod (mods pps).prod //
                    allowedAxisPow pps
                      (axisEquiv (mods pps)
                        (mods_pairwise_coprime_of_p_pairwise_coprime pps
                          (List.pairwise_coprime_of_prime_nodup hprime hnodup)) x)} : Type)
              : ℚ) /
            ((mods pps).prod : ℚ)) /
          ((((Nat.totient (mods pps).prod : Nat) : ℚ) / ((mods pps).prod : ℚ))))) := by
            simpa using hNormalize
    _ =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod /
          (pps.map (fun pp => ((pp.p - 1 : ℚ) / (pp.p : ℚ)))).prod := by
          simpa using hDensities
    _ = (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod := by
          simpa using hProdQuot

end TwinPrimeAllowedCapacityTotientBridge
