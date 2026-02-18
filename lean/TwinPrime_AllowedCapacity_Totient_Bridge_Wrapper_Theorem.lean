import TwinPrime_AllowedCapacity_Totient_Bridge_Theorem
import TwinPrime_AllowedCapacity_Density_Wrapper_Theorem

/-!
# Twin-Prime Allowed-Capacity vs Totient: User-Facing Prime/Exponent Wrappers

The mechanism layer for the totient bridge works with the bundled structure
`PrimePow(p,k,hp : 2 < p)`. This file provides wrappers that accept:

- `ps : List Nat` of distinct primes,
- `ks : List Nat` exponents (same length),

and constructs the `PrimePow` list internally via `zipPrimePow`.

This is an API layer: it does not add new mechanism; it just reduces caller burden.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityTotientWrappers

open TwinPrimeAllowedCapacityTotientBridge
open TwinPrimeAllowedCapacityWrappers
open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityCRTList

/-!
## Totient bridge wrapper (distinct primes + exponents)

This is the Step-230 totient lens identity, callable from `ps,ks`.
Note the RHS depends only on `ps` (exponents drop out).
-/
theorem allowedOverTotient_eq_of_prime_lists (ps ks : List Nat)
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
          : ℚ) / (Nat.totient (mods pps).prod : ℚ) =
        (ps.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod) := by
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
          : ℚ) / (Nat.totient (mods pps).prod : ℚ) =
        (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod := by
    simpa using
      (allowedDensity_over_totientDensity_eq_of_prime_nodup (pps := pps) hprimePps hnodupPps)

  -- Rewrite the RHS: it depends only on the base prime list.
  have hrhs :
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod =
        (ps.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod := by
    have hmap : pps.map PrimePow.p = ps := by
      simpa [pps] using zipPrimePow_map_p ps ks hprime hne2 hlen
    let g : Nat → ℚ := fun p => ((p - 2 : ℚ) / (p - 1 : ℚ))
    have hmap2 :
        pps.map (fun pp => g pp.p) = (pps.map PrimePow.p).map g := by
      change List.map (g ∘ PrimePow.p) pps = List.map g (List.map PrimePow.p pps)
      exact (List.comp_map g PrimePow.p pps)
    calc
      (pps.map (fun pp => ((pp.p - 2 : ℚ) / (pp.p - 1 : ℚ)))).prod =
          ((pps.map PrimePow.p).map g).prod := by
            simpa [g] using congrArg List.prod hmap2
      _ = (ps.map g).prod := by
            rw [hmap]
      _ = (ps.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod := by
            rfl

  simpa [pps, hrhs] using hbase

end TwinPrimeAllowedCapacityTotientWrappers
