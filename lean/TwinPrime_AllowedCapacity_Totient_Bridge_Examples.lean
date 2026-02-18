import TwinPrime_AllowedCapacity_Totient_Bridge_Wrapper_Theorem

/-!
# Examples: Twin-Prime Allowed/Totient Wrapper API

These are small, auditable instantiations that exercise the user-facing totient wrapper layer:

- the totient bridge wrapper theorem typechecks end-to-end,
- the ratio `allowed(N)/φ(N)` is independent of the exponent list `ks` (for fixed base primes `ps`),
- key composite example: `N = 7·11·13 = 1001`, giving ratio `11/16`.

No placeholders.
-/

namespace TwinPrimeAllowedCapacityTotientWrapperExamples

open TwinPrimeAllowedCapacityTotientWrappers
open TwinPrimeAllowedCapacityWrappers
open TwinPrimeAllowedCapacityPrimePowerProduct
open TwinPrimeAllowedCapacityCRTList

section PS71113

def ps71113 : List Nat := [7, 11, 13]
def ks000 : List Nat := [0, 0, 0]
def ks123 : List Nat := [1, 2, 3]

lemma ps71113_hprime : ∀ p ∈ ps71113, Nat.Prime p := by
  intro p hp
  simp [ps71113] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps71113_hne2 : ∀ p ∈ ps71113, p ≠ 2 := by
  intro p hp
  simp [ps71113] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps71113_nodup : ps71113.Nodup := by
  decide

lemma ps71113_len_ks000 : ps71113.length = ks000.length := by
  decide

lemma ps71113_len_ks123 : ps71113.length = ks123.length := by
  decide

noncomputable def ratioExpr (ks : List Nat) (hlen : ps71113.length = ks.length) : ℚ :=
  let pps := zipPrimePow ps71113 ks ps71113_hprime ps71113_hne2 hlen
  (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
    (Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps)
                  (mods_pairwise_coprime_of_p_pairwise_coprime pps
                    (List.pairwise_coprime_of_prime_nodup
                      (by
                        intro p hp
                        have : p ∈ ps71113 := by
                          simpa [pps, zipPrimePow_map_p ps71113 ks ps71113_hprime ps71113_hne2 hlen] using hp
                        exact ps71113_hprime p this)
                      (by
                        simpa [pps, zipPrimePow_map_p ps71113 ks ps71113_hprime ps71113_hne2 hlen] using
                          ps71113_nodup))) x)})
        : ℚ) / (Nat.totient (mods pps).prod : ℚ))

theorem ratio_ps71113_eq_eleven_sixteenths (ks : List Nat) (hlen : ps71113.length = ks.length) :
    ratioExpr ks hlen = (11 / 16 : ℚ) := by
  have h :=
    allowedOverTotient_eq_of_prime_lists (ps := ps71113) (ks := ks)
      ps71113_hprime ps71113_hne2 ps71113_nodup hlen
  have hform :
      ratioExpr ks hlen = (ps71113.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod := by
    dsimp [ratioExpr]
    simpa using h
  have heval :
      (ps71113.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod = (11 / 16 : ℚ) := by
    -- (5/6)*(9/10)*(11/12) = 11/16.
    simp [ps71113]
    norm_num
  exact hform.trans heval

theorem ratio_ps71113_independent_of_ks :
    ratioExpr ks000 ps71113_len_ks000 = ratioExpr ks123 ps71113_len_ks123 := by
  have h0 := ratio_ps71113_eq_eleven_sixteenths (ks := ks000) ps71113_len_ks000
  have h1 := ratio_ps71113_eq_eleven_sixteenths (ks := ks123) ps71113_len_ks123
  simp [h0, h1]

end PS71113

section PS357

def ps357 : List Nat := [3, 5, 7]
def ks000' : List Nat := [0, 0, 0]

lemma ps357_hprime : ∀ p ∈ ps357, Nat.Prime p := by
  intro p hp
  simp [ps357] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps357_hne2 : ∀ p ∈ ps357, p ≠ 2 := by
  intro p hp
  simp [ps357] at hp
  rcases hp with rfl | rfl | rfl
  · decide
  · decide
  · decide

lemma ps357_nodup : ps357.Nodup := by
  decide

lemma ps357_len_ks000 : ps357.length = ks000'.length := by
  decide

noncomputable def ratioExpr357 : ℚ :=
  let pps := zipPrimePow ps357 ks000' ps357_hprime ps357_hne2 ps357_len_ks000
  (letI : NeZero (mods pps).prod := ⟨mods_prod_ne_zero pps⟩;
    (Fintype.card
          ({x : ZMod (mods pps).prod //
              allowedAxisPow pps
                (axisEquiv (mods pps)
                  (mods_pairwise_coprime_of_p_pairwise_coprime pps
                    (List.pairwise_coprime_of_prime_nodup
                      (by
                        intro p hp
                        have : p ∈ ps357 := by
                          simpa [zipPrimePow_map_p ps357 ks000' ps357_hprime ps357_hne2 ps357_len_ks000, pps] using
                            hp
                        exact ps357_hprime p this)
                      (by
                        simpa [zipPrimePow_map_p ps357 ks000' ps357_hprime ps357_hne2 ps357_len_ks000, pps] using
                          ps357_nodup))) x)})
        : ℚ) / (Nat.totient (mods pps).prod : ℚ))

theorem ratio_ps357_eq_five_sixteenths :
    ratioExpr357 = (5 / 16 : ℚ) := by
  have h :=
    allowedOverTotient_eq_of_prime_lists (ps := ps357) (ks := ks000')
      ps357_hprime ps357_hne2 ps357_nodup ps357_len_ks000
  have hform :
      ratioExpr357 = (ps357.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod := by
    dsimp [ratioExpr357]
    exact h
  have heval :
      (ps357.map (fun p : Nat => ((p - 2 : ℚ) / (p - 1 : ℚ)))).prod = (5 / 16 : ℚ) := by
    -- (1/2)*(3/4)*(5/6) = 5/16.
    simp [ps357]
    norm_num
  exact hform.trans heval

end PS357

end TwinPrimeAllowedCapacityTotientWrapperExamples
