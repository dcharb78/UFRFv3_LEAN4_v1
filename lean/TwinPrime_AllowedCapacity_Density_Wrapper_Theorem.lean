import TwinPrime_AllowedCapacity_Density_Theorem

/-!
# Twin-Prime Allowed-Capacity: User-Facing Prime/Exponent Wrappers

The mechanism layer works with the bundled structure `PrimePow(p,k,hp:2<p)`.
This file provides wrappers that accept:
- `ps : List Nat` of (distinct) primes,
- `ks : List Nat` exponents (same length),
and constructs the `PrimePow` list internally.

This is an API layer: it does not add new mechanism, it just reduces caller burden.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityWrappers

open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityDensity
open TwinPrimeAllowedCapacityCRTList

/--
Zip a list of primes `ps` with a list of exponents `ks` into the bundled axis structure `PrimePow`.

Inputs:
- primality for each `p ∈ ps`,
- exclusion of `p = 2` (so `2 < p` is derivable),
- a length guard `ps.length = ks.length` (to avoid silent truncation).
-/
def zipPrimePow :
    (ps ks : List Nat) →
    (hprime : ∀ p ∈ ps, Nat.Prime p) →
    (hne2 : ∀ p ∈ ps, p ≠ 2) →
    (hlen : ps.length = ks.length) →
    List PrimePow
  | [], [], _, _, _ => []
  | p :: ps, k :: ks, hprime, hne2, hlen =>
      have hp_le : 2 ≤ p := (hprime p (by simp)).two_le
      have hp_ne : (2 : Nat) ≠ p := Ne.symm (hne2 p (by simp))
      have hp : 2 < p := lt_of_le_of_ne hp_le hp_ne
      have hprime' : ∀ q ∈ ps, Nat.Prime q := by
        intro q hq
        exact hprime q (by simp [hq])
      have hne2' : ∀ q ∈ ps, q ≠ 2 := by
        intro q hq
        exact hne2 q (by simp [hq])
      have hlen' : ps.length = ks.length := by
        -- `length (p::ps) = length (k::ks)` implies `length ps = length ks`.
        simpa using Nat.succ.inj (by simpa using hlen)
      ⟨p, k, hp⟩ :: zipPrimePow ps ks hprime' hne2' hlen'
  | [], _ :: _, _, _, hlen => by
      cases hlen
  | _ :: _, [], _, _, hlen => by
      cases hlen

theorem zipPrimePow_map_p :
    ∀ (ps ks : List Nat) (hprime : ∀ p ∈ ps, Nat.Prime p) (hne2 : ∀ p ∈ ps, p ≠ 2)
      (hlen : ps.length = ks.length),
      (zipPrimePow ps ks hprime hne2 hlen).map PrimePow.p = ps := by
  intro ps ks hprime hne2 hlen
  induction ps generalizing ks with
  | nil =>
      cases ks with
      | nil => simp [zipPrimePow]
      | cons k ks =>
          cases hlen
  | cons p ps ih =>
      cases ks with
      | nil =>
          cases hlen
      | cons k ks =>
          have hprime' : ∀ q ∈ ps, Nat.Prime q := by
            intro q hq
            exact hprime q (by simp [hq])
          have hne2' : ∀ q ∈ ps, q ≠ 2 := by
            intro q hq
            exact hne2 q (by simp [hq])
          have hlen' : ps.length = ks.length := by
            simpa using Nat.succ.inj (by simpa using hlen)
          simp [zipPrimePow, ih (ks := ks) (hprime := hprime') (hne2 := hne2') (hlen := hlen')]

/-!
## Capacity wrapper (distinct primes + exponents)

This is the Step-224 capacity count, but callable from `ps,ks` rather than `PrimePow`.
-/
theorem card_allowedPrimePowerProduct_of_prime_lists (ps ks : List Nat)
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hne2 : ∀ p ∈ ps, p ≠ 2) (hnodup : ps.Nodup)
    (hlen : ps.length = ks.length) :
    let pps := zipPrimePow ps ks hprime hne2 hlen
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps)
                  (mods_pairwise_coprime_of_p_pairwise_coprime pps
                    (List.pairwise_coprime_of_prime_nodup
                      (by
                        intro p hp
                        have : p ∈ ps := by
                          simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hp
                        exact hprime p this)
                      (by
                        simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hnodup))) x)}) =
        (pps.map (fun pp => (pp.p - 2) * pp.p ^ pp.k)).prod) := by
  classical
  let pps := zipPrimePow ps ks hprime hne2 hlen
  have hprimePps : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p := by
    intro p hp
    have : p ∈ ps := by
      simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hp
    exact hprime p this
  have hnodupPps : (pps.map PrimePow.p).Nodup := by
    simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hnodup
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩
  simpa [pps] using
    (card_allowedPrimePowerProduct_of_prime_nodup (pps := pps) hprimePps hnodupPps)

/-!
## Density wrapper (distinct primes + exponents)

This is the Step-226 density identity, callable from `ps,ks`.
Note the RHS depends only on `ps` (scale invariance; exponents drop out).
-/
theorem globalDensity_eq_of_prime_lists (ps ks : List Nat)
    (hprime : ∀ p ∈ ps, Nat.Prime p) (hne2 : ∀ p ∈ ps, p ≠ 2) (hnodup : ps.Nodup)
    (hlen : ps.length = ks.length) :
    let pps := zipPrimePow ps ks hprime hne2 hlen
    (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
      (Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps)
                    (mods_pairwise_coprime_of_p_pairwise_coprime pps
                      (List.pairwise_coprime_of_prime_nodup
                        (by
                          intro p hp
                          have : p ∈ ps := by
                            simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hp
                          exact hprime p this)
                        (by
                          simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hnodup))) x)})
          : ℚ) / ((mods pps).prod : ℚ) =
        (ps.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod) := by
  classical
  let pps := zipPrimePow ps ks hprime hne2 hlen
  have hprimePps : ∀ p ∈ (pps.map PrimePow.p), Nat.Prime p := by
    intro p hp
    have : p ∈ ps := by
      simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hp
    exact hprime p this
  have hnodupPps : (pps.map PrimePow.p).Nodup := by
    simpa [pps, zipPrimePow_map_p ps ks hprime hne2 hlen] using hnodup
  letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩

  have hbase :
      (Fintype.card
            ({x : ZMod (mods pps).prod //
                allowedAxisPow pps
                  (axisEquiv (mods pps)
                    (mods_pairwise_coprime_of_p_pairwise_coprime pps
                      (List.pairwise_coprime_of_prime_nodup hprimePps hnodupPps)) x)})
          : ℚ) / ((mods pps).prod : ℚ) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod := by
    simpa using (globalDensity_eq_of_prime_nodup (pps := pps) hprimePps hnodupPps)

  -- Rewrite the RHS: it depends only on the base prime list.
  have hrhs :
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod =
        (ps.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod := by
    have hmap : pps.map PrimePow.p = ps := by
      simpa [pps] using zipPrimePow_map_p ps ks hprime hne2 hlen
    have hmap2 :
        pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ))) =
          (pps.map PrimePow.p).map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ))) := by
      -- Avoid `simp`: in some contexts it rewrites `map` through the monad structure (`flatMap`),
      -- making this basic functor identity harder to match. We use `change` + `exact`.
      let g : Nat → ℚ := fun p => ((p - 2 : ℚ) / (p : ℚ))
      -- LHS is definitionally `map (g ∘ PrimePow.p) pps`; RHS is `map g (map PrimePow.p pps)`.
      change List.map (g ∘ PrimePow.p) pps = List.map g (List.map PrimePow.p pps)
      exact (List.comp_map g PrimePow.p pps)
    calc
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p : ℚ)))).prod =
          ((pps.map PrimePow.p).map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod := by
            simpa using congrArg List.prod hmap2
      _ = (ps.map (fun p : Nat => ((p - 2 : ℚ) / (p : ℚ)))).prod := by
            -- Use `rw` to avoid simp rewriting the casted expression into `flatMap` form.
            rw [hmap]
  simpa [hrhs] using hbase

end TwinPrimeAllowedCapacityWrappers
