# Number-Theoretic Analysis: "13 as Template, Primes as Projections"

## Executive Summary

This document provides rigorous theorem formulations for the proposed framework connecting modular arithmetic, cyclic group structure, and the special role of 13 as a "template" prime.

---

## PART I: THE FLIP POINT THEOREM

### Theorem 1.1 (Flip Point Characterization for Odd Primes)

**Statement:** Let p be an odd prime. The map σ: ZMod p → ZMod p defined by σ(x) = -x (mod p) is an involution (σ² = id) with:

  (a) **Fixed point:** σ(0) = 0
  (b) **Pairing:** For x ≠ 0, σ(x) ≠ x and σ(σ(x)) = x
  (c) **Geometric center:** The "flip point" at p/2 is the unique point in [0, p) such that the distance from x to p/2 equals the distance from σ(x) to p/2

**Formal statement:** |x - p/2| = |σ(x) - p/2| for all x ∈ ZMod p (viewed in ℝ)

**Proof sketch:**
- σ(x) = p - x for x ≠ 0
- |x - p/2| = |p - x - p/2| = |p/2 - x| = |x - p/2| ∎

### Theorem 1.2 (Geometric Symmetry)

**Statement:** For odd prime p, define the expansion and contraction zones:
- E = {0, 1, ..., ⌊(p-1)/2⌋} (expansion: moving away from 0)
- C = {⌈p/2⌉, ..., p-1} (contraction: moving toward 0)

Then σ maps E bijectively to C, with:
- σ(0) = 0 (boundary)
- For x ∈ E \\{0\\}, σ(x) ∈ C
- The flip point p/2 lies strictly between E and C

---

## PART II: THE ORBIT STRUCTURE THEOREM

### Theorem 2.1 (Orbit Size Formula)

**Statement:** For any modulus n and step size s ∈ ZMod n, the orbit of 0 under repeated addition of s has size:

$$|\text{Orbit}_n(s)| = \frac{n}{\gcd(n, s)}$$

### Corollary 2.2 (Prime Orbit Property)

**Statement:** For prime p and any s ∈ {1, 2, ..., p-1}:

$$|\text{Orbit}_p(s)| = \frac{p}{\gcd(p, s)} = \frac{p}{1} = p$$

**Interpretation:** Every non-zero step size generates the FULL cycle in ZMod p.

### Theorem 2.3 (Phase Decomposition)

**Statement:** For odd prime p and step s generating the full orbit, define:
- **Phase 1 (Expansion):** Positions 0, s, 2s, ..., ks where ks ≤ p/2 < (k+1)s
- **Phase 2 (Crossing):** The step crossing p/2
- **Phase 3 (Contraction):** Remaining positions back to 0

The number of steps in each phase depends on s and p, with the flip point serving as the transition marker.

---

## PART III: THE PROJECTION THEOREM

### Theorem 3.1 (Natural Projection Homomorphism)

**Statement:** For primes p < q, the map π: ZMod q → ZMod p defined by π(x) = x mod p is a surjective ring homomorphism with:
- ker(π) = {0, p, 2p, ..., kp} where kp < q
- |ker(π)| = ⌈q/p⌉

### Theorem 3.2 (Multiplicative Group Embedding Criterion)

**Statement:** For primes p and q, there exists an embedding (injective homomorphism):

$$\iota: (\mathbb{Z}/p\mathbb{Z})^* \hookrightarrow (\mathbb{Z}/q\mathbb{Z})^*$$

**if and only if** (p-1) divides (q-1).

**Proof sketch:**
- (Z/qZ)* is cyclic of order q-1 (since q is prime)
- A cyclic group of order q-1 has a unique subgroup of order d for each d | (q-1)
- (Z/pZ)* has order p-1
- Therefore embedding exists iff (p-1) | (q-1) ∎

### Corollary 3.3 (13 as Universal Template for Small Primes)

**Statement:** For p ∈ {3, 5, 7}:

$$(p-1) \mid 12 = 13 - 1$$

Therefore, for each p ∈ {3, 5, 7}, there exists an embedding:

$$(\mathbb{Z}/p\mathbb{Z})^* \hookrightarrow (\mathbb{Z}/13\mathbb{Z})^*$$

**Explicit embeddings:**
- (Z/3Z)* ≅ {1, 12} ⊂ (Z/13Z)*
- (Z/5Z)* ≅ {1, 5, 8, 12} ⊂ (Z/13Z)*  
- (Z/7Z)* ≅ {1, 3, 4, 9, 10, 12} ⊂ (Z/13Z)*

**Note:** 11 is excluded since 10 ∤ 12.

---

## PART IV: SYNCHRONIZATION AND CONCURRENT AXES

### Theorem 4.1 (Totient LCM as Synchronization Period)

**Statement:** For distinct primes p₁, p₂, ..., pₖ, define:

$$L = \text{lcm}(\varphi(p_1), \varphi(p_2), ..., \varphi(p_k)) = \text{lcm}(p_1-1, p_2-1, ..., p_k-1)$$

Then L is the smallest positive integer such that:

$$g^L \equiv 1 \pmod{p_i}$$

for all g coprime to pᵢ, for all i = 1, ..., k.

Equivalently, L is the exponent of the group:

$$G = (\mathbb{Z}/p_1\mathbb{Z})^* \times (\mathbb{Z}/p_2\mathbb{Z})^* \times ... \times (\mathbb{Z}/p_k\mathbb{Z})^*$$

### Theorem 4.2 (Chinese Remainder Theorem Connection)

**Statement:** For distinct primes p₁, p₂, ..., pₖ, let N = p₁·p₂·...·pₖ.

By CRT:

$$\mathbb{Z}/N\mathbb{Z} \cong \mathbb{Z}/p_1\mathbb{Z} \times \mathbb{Z}/p_2\mathbb{Z} \times ... \times \mathbb{Z}/p_k\mathbb{Z}$$

Restricting to units:

$$(\mathbb{Z}/N\mathbb{Z})^* \cong (\mathbb{Z}/p_1\mathbb{Z})^* \times (\mathbb{Z}/p_2\mathbb{Z})^* \times ... \times (\mathbb{Z}/p_k\mathbb{Z})^*$$

The exponent of (Z/NZ)* equals lcm(p₁-1, p₂-1, ..., pₖ-1).

### Theorem 4.3 (Concurrent Axes Model)

**Statement:** For distinct primes p₁, p₂, ..., pₖ, consider k "axes" where axis i traces the orbit structure of ZMod pᵢ. These axes are "concurrent" in the sense that after L = lcm(p₁-1, ..., pₖ-1) steps:

- Each axis completes an integer number of full cycles
- The system returns to its initial state across all axes simultaneously
- L is the **MINIMAL** such synchronization period

---

## PART V: MINIMALITY OF 13

### Theorem 5.1 (Structural Minimality Criterion)

**Statement:** A prime q is a "template" for primes P = {p₁, p₂, ..., pₖ} if:

$$(p_i - 1) \mid (q - 1) \text{ for all } i = 1, ..., k$$

### Theorem 5.2 (13 is Minimal Template for {3, 5, 7})

**Statement:** Among all primes q such that:
- 2 | (q-1) [for p=3]
- 4 | (q-1) [for p=5]  
- 6 | (q-1) [for p=7]

The minimal q is the smallest prime with 12 | (q-1), which is q = 13.

**Proof:**
- Need: q ≡ 1 (mod 12)
- Primes ≡ 1 (mod 12): 13, 37, 61, 73, ...
- Minimum is 13. ∎

### Theorem 5.3 (General Template Construction)

**Statement:** For any finite set of primes P = {p₁, ..., pₖ}, the minimal template prime is the smallest prime q such that:

$$\text{lcm}(p_1-1, p_2-1, ..., p_k-1) \mid (q - 1)$$

**Example:** For P = {3, 5, 7, 11}:
- lcm(2, 4, 6, 10) = 60
- Smallest prime q with 60 | (q-1) is q = 61

---

## LEAN FORMALIZATION REQUIREMENTS

To formalize these theorems in Lean 4, the following would need to be established:

### 1. Basic definitions:
- ZMod n as a ring and additive group
- (ZMod n)* as the multiplicative group of units
- Order of elements and groups

### 2. For Theorem 1 (Flip Point):
- Define the involution σ(x) = -x
- Prove it has the stated properties
- Connect to geometric interpretation

### 3. For Theorem 2 (Orbit Formula):
- orbitSize n s = n / gcd(n, s)
- This is standard; follows from Lagrange's theorem for cyclic groups

### 4. For Theorem 3 (Projection):
- Natural projection homomorphisms
- Subgroup existence criterion for cyclic groups
- Explicit construction of embeddings

### 5. For Theorem 4 (Synchronization):
- Totient function and its properties
- LCM computation
- Connection to group exponent
- Chinese Remainder Theorem

### 6. For Theorem 5 (Minimality):
- Search procedure for minimal template primes
- Verification that 13 satisfies the criterion
- Proof of minimality

---

## KEY INSIGHTS

1. **The Flip Point:** The point p/2 serves as the geometric center of symmetry for the involution x ↦ -x in ZMod p.

2. **Full Cycles:** For prime p, every non-zero step generates the full orbit of size p. This is the "full cycle" claim.

3. **13 as Template:** The key structural property is that for p ∈ {3, 5, 7}, we have (p-1) | 12 = 13-1. This allows (Z/pZ)* to embed into (Z/13Z)*.

4. **Synchronization:** The LCM of totients gives the minimal period for concurrent evolution across multiple prime moduli.

5. **Minimality:** 13 is the smallest prime q such that 12 | (q-1), making it the minimal template for the primes whose totients divide 12.
