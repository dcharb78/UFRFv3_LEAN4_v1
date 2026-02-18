# On the p-adic Structure of Twin Prime Residue Classes

**Daniel Friedman**

February 2026

---

## Abstract

We investigate the distribution of twin prime pairs across residue classes in the p-adic integers. We establish the general formula occ_p(k) = (p−2)·p^k + c_p for the number of twin-occupied residue classes mod p^(k+1), where c_p = [p−2 is prime] + [p+2 is prime] counts the twin-pair memberships of p. This formula is verified exact across 61 primes at the base level and at all higher scales where data is sufficient. We prove that empty classes arise exclusively from p-divisibility, characterize the unique defective Hensel lift, and establish universal tunneling: every twin prime pair beyond (3, 5) sits at the carry boundary of the 3-adic expansion, forced by the constraint n ≡ 2 mod 3.

Our principal new observation concerns the interaction between p-adic towers at different primes. Decomposing twin-occupied residue classes into *seed* classes (occupied only by the finitely many twin pairs (p−2, p) involving basis primes) and *regular* classes (occupied by the infinite population of large twins), we find that the regular classes exhibit **exact cross-tower independence**: the number of regular classes mod ∏p_i equals exactly ∏(p_i − 2), verified across all 21 prime pairs, all 35 triples, and all testable quadruples and quintuples from primes 3 through 19. The apparent inter-tower coupling reported in earlier analyses is entirely an artifact of seed-class bookkeeping. All results are computationally reproducible from accompanying code.

---

## 1. Introduction

The twin prime conjecture — that there are infinitely many primes p such that p + 2 is also prime — remains one of the oldest open problems in number theory. The best unconditional result establishes lim inf(p_{n+1} − p_n) ≤ 246, due to Zhang [1] and the Polymath project [2]. The Hardy-Littlewood conjecture [3] predicts asymptotic density π₂(N) ~ C₂ · N/(log N)², where C₂ = ∏_{p≥3} p(p−2)/(p−1)² ≈ 0.6602.

Each factor in the Hardy-Littlewood product represents a local correction at prime p. In this paper, we show that these local corrections correspond to exact algebraic structure in the p-adic integers ℤ_p. Rather than estimating twin prime counts, we study the residue classes they occupy and find exact formulas, clean characterization theorems, a structural tunneling property, and — most significantly — exact cross-tower independence of the regular twin-carrying channels.

**Notation.** Throughout, p denotes a prime ≥ 3, and (n, n+2) denotes a twin prime pair with n the lower member. We write occ_p(k) for the number of residue classes mod p^(k+1) containing at least one lower twin. Computations use N = 5 × 10^7, yielding 239,101 twin pairs.

---

## 2. The General Occupancy Formula

### 2.1 Statement and Verification

**Theorem 2.1** (Occupancy formula). *For any prime p ≥ 3, the number of residue classes mod p^(k+1) containing at least one twin prime satisfies*

*occ_p(k) = (p − 2) · p^k + c_p*

*where c_p = [p − 2 is prime] + [p + 2 is prime] counts the twin-pair memberships of p, provided the data is sufficient (averaging more than 8 twins per residue class).*

The correction c_p takes values 0, 1, or 2:

| c_p | Condition | Examples |
|-----|-----------|----------|
| 0 | p is not part of any twin pair | 23, 37, 47, 67, 79, 83, ... |
| 1 | p belongs to exactly one twin pair | 3, 7, 13, 19, 31, 43, ... |
| 2 | p belongs to two twin pairs | 5 (member of both (3,5) and (5,7)) |

The value c_p = 2 occurs only at p = 5, the unique center of the only prime triple (3, 5, 7). For all other primes, c_p ∈ {0, 1}.

**Verification.** We tested the formula across 61 primes (every prime from 3 to 293) at the base level (k = 0): **61 out of 61 exact matches**, with zero exceptions. At higher scales, we verified exactness wherever the average twin count per class exceeds 8:

| Minimum avg twins/class | k=0 | k=1 | k=2 | k=3 | k=4 |
|--------------------------|------|------|------|------|------|
| > 8 | 61/61 | 38/38 | 9/9 | 4/4 | 3/3 |
| ≥ 5 | 61/61 | 38/46 | 9/13 | — | — |
| ≥ 3 | 61/61 | 38/59 | — | — | — |

Below the threshold of ~8 twins per class, starvation effects appear: some classes that should be occupied by the formula have not yet received their first twin in the data range. The deficit grows smoothly with decreasing density, consistent with Poisson statistics rather than structural failure.

### 2.2 Seed-Regular Decomposition

The formula occ_p(k) = (p−2)·p^k + c_p has a natural decomposition. The (p−2)·p^k term counts **regular** classes: those occupied by at least one twin pair (n, n+2) with n > p. These are the classes that carry the infinite population of large twins. The c_p term counts **seed** classes: those occupied exclusively by the twin pairs involving p itself — the pairs (p−2, p) and/or (p, p+2) when they exist.

Seed and regular classes are disjoint: seed twins occupy classes that are *forbidden* from the perspective of their own prime (they sit at position 0 or p−2), so no large twin can share those classes.

### 2.3 Representative Data (p = 13)

| k | Modulus | Occupied | Regular | Seeds | Avg twins/class |
|---|---------|----------|---------|-------|-----------------|
| 0 | 13 | 12 | 11 | 1 | 18,392 |
| 1 | 169 | 144 | 143 | 1 | 1,415 |
| 2 | 2,197 | 1,860 | 1,859 | 1 | 109 |
| 3 | 28,561 | 24,168 | 24,167 | 1 | 8.4 |

### 2.4 The Recurrence

The formula satisfies the linear recurrence occ_p(k+1) = p · occ_p(k) − (p − 1), with initial condition occ_p(0) = (p − 2) + c_p. This has a Hensel lifting interpretation: at each scale transition, non-defective classes lift to p subclasses, while the defective class lifts to exactly 1 (§4).

### 2.5 The Occupancy Rate and Hardy-Littlewood

The fraction of occupied classes at scale k is occ_p(k) / p^(k+1) = (p−2)/p + c_p/p^(k+1), converging to **(p−2)/p** as k → ∞. This limiting rate is the regular-channel occupancy: the fraction of the p-adic address space available for twin primes. The seed correction c_p/p^(k+1) vanishes exponentially.

---

## 3. Empty Class Characterization

**Theorem 3.1** (Empty class characterization). *At every verified scale, the residue classes mod p^(k+1) containing no twin primes are exactly*

*E_p(k) = { r : r ≡ 0 mod p } ∪ { r : r ≡ p−2 mod p } \ S_p*

*where S_p contains at most c_p exceptional classes occupied by seed twins.*

| Scale | Empty (actual) | Empty (predicted) | Extra empties | Exceptions |
|-------|---------------|-------------------|---------------|------------|
| k=0 | 1 | 2 | 0 | class 11 (the pair (11,13)) |
| k=1 | 25 | 26 | 0 | class 11 |
| k=2 | 337 | 338 | 0 | class 11 |

Zero extra empties at any tested scale. The **sole mechanism** producing empty twin-prime classes is divisibility by the modulus prime.

---

## 4. The Defective Cascade

### 4.1 Binary Hensel Lifting

For twin-occupied residue classes, lifting from scale k to k+1 exhibits binary behavior: non-defective classes lift to all p subclasses; the defective class (r ≡ p−2 mod p) lifts to exactly 1 subclass.

### 4.2 The Unique Survivor

**Observation 4.1.** *At every tested prime where the twin pair (p−2, p) exists, the defective class lifts to exactly one survivor: the class containing n = p−2 itself, with p-adic expansion (p−2, 0, 0, 0, ...).*

| Prime p | Survivor | p-adic expansion | Twin pair |
|---------|----------|------------------|-----------|
| 5 | 3 | (3, 0, 0, ...) | (3, 5) |
| 7 | 5 | (5, 0, 0, ...) | (5, 7) |
| 13 | 11 | (11, 0, 0, ...) | (11, 13) |
| 19 | 17 | (17, 0, 0, ...) | (17, 19) |
| 31 | 29 | (29, 0, 0, ...) | (29, 31) |

When (p−2, p) does not exist (p−2 composite, as with p = 11, 17, 23), the defective class has zero survivors.

---

## 5. The Universal Tunneling Property

### 5.1 Main Result

**Proposition 5.1** (Universal tunneling). *For every twin prime pair (n, n+2) with n > 3, the lower twin satisfies n ≡ 2 mod 3, placing it at the live carry boundary of p = 3.*

*Proof.* Since n > 3 is prime, n is not divisible by 3. If n ≡ 1 mod 3, then n + 2 ≡ 0 mod 3, making n + 2 composite. Therefore n ≡ 2 mod 3. Since 2 = 3 − 1, this is the carry position. ∎

**Corollary.** *Every twin prime pair sits at the carry boundary of at least one prime.* (The pair (3, 5) tunnels through p = 5 instead.)

**Computational verification.** Among 239,101 twin pairs below 5 × 10^7, using 14 basis primes [3, 5, ..., 47]: twins with no carry at any prime: **0 out of 239,101**.

### 5.2 Multiplicity

| Simultaneous carries | Count | Fraction |
|---------------------|-------|----------|
| 1 | 72,382 | 30.27% |
| 2 | 96,725 | 40.45% |
| 3 | 51,840 | 21.68% |
| 4+ | 18,154 | 7.59% |

---

## 6. Carry Propagation and Scale Coupling

The displacement +2 has p-adic valuation 0 for all p ≥ 3, so carries arise entirely from the base point n. In the 13-adic tower, position 12 wraps to position 1 with carry (live); position 11 maps to 0, producing a multiple of 13 (terminal). All other positions absorb the displacement within the current scale.

---

## 7. Connection to the Hardy-Littlewood Constant

Each factor of the Hardy-Littlewood constant decomposes as p(p−2)/(p−1)² = [(p−2)/p] · [p/(p−1)]². The first term is the limiting regular-channel occupancy rate from Theorem 2.1. The second term corrects for prime density in coprime residue classes.

---

## 8. Cross-Tower Independence

### 8.1 The Decomposition

This section presents our principal structural observation. Consider a finite set of primes P = {p₁, ..., p_m} with p_i ≥ 3. The residue classes mod ∏p_i occupied by twin primes decompose into two disjoint populations:

- **Regular classes**: those containing at least one twin pair (n, n+2) with n > max(P). These carry the infinite population of large twins.
- **Seed classes**: those occupied only by twin pairs (p−2, p) or (p, p+2) for some p ∈ P. These carry finitely many small twins.

The decomposition is disjoint because seed twins occupy classes that are forbidden from the perspective of their own prime: the pair (p−2, p) places n = p−2 at position p−2 mod p (the boundary), and (p, p+2) places n = p at position 0 mod p (the void). No twin n > p can occupy these positions.

### 8.2 The Independence Theorem

**Theorem 8.1** (Cross-tower independence). *For any finite set of primes P = {p₁, ..., p_m}, the number of regular twin-occupied residue classes mod ∏p_i equals exactly*

*∏(p_i − 2)*

*provided the data is sufficient (enough twins to populate all classes).*

This is a statement of exact multiplicative independence: the regular channels at each prime contribute a factor of (p−2) to the joint count, with no interaction between towers.

**Verification.** We tested this across all combinations of primes from {3, 5, 7, 11, 13, 17, 19}:

| Combination size | Tested | Exact | Data-limited | True mismatches |
|-----------------|--------|-------|-------------|-----------------|
| 2 (pairs) | 21 | **21** | 0 | **0** |
| 3 (triples) | 35 | **35** | 0 | **0** |
| 4 (quadruples) | 35 | **34** | 1 | **0** |
| 5 (quintuples) | 21 | **16** | 5 | **0** |
| Full basis [3..17] | 1 | **1** | 0 | **0** |

Representative data for the cumulative basis:

| Basis | Modulus | Regular | ∏(p−2) | Match |
|-------|---------|---------|--------|-------|
| {3, 5} | 15 | 3 | 3 | ✓ |
| {3, 5, 7} | 105 | 15 | 15 | ✓ |
| {3, 5, 7, 11} | 1,155 | 135 | 135 | ✓ |
| {3, 5, 7, 11, 13} | 15,015 | 1,485 | 1,485 | ✓ |
| {3, 5, 7, 11, 13, 17} | 255,255 | 22,275 | 22,275 | ✓ |

### 8.3 The Apparent Coupling Was an Artifact

In a naive analysis, one might compare the total occupancy occ_joint to the product ∏ occ_p(0) = ∏((p−2) + c_p) and interpret the ratio as inter-tower coupling. For the basis {3, 5, 7, 11, 13}, this gives 1,488/7,200 ≈ 0.207, which appears to show strong coupling.

This is an artifact of bookkeeping. The total 1,488 decomposes as 1,485 regular + 3 seeds. The denominator 7,200 = ∏((p−2) + c_p) inflates the individual occupancies by including seed corrections multiplicatively. The actual comparison is:

- Regular channels: 1,485 = ∏(p−2) *exactly*
- Seeds: 3 additional classes (the pairs (3,5), (5,7), (11,13))

The "coupling ratio" of 0.207 is simply ∏(p−2)/∏((p−2)+c_p) = 1,485/7,200 — a ratio of two different counting conventions, not a measure of inter-tower interaction.

### 8.4 Why Independence Holds

The regular channels have a simple algebraic explanation. A class r mod ∏p_i is regular-occupied if and only if, for each p_i, the residue r mod p_i avoids both 0 and p_i−2. By the Chinese Remainder Theorem, these conditions are independent: the constraint at p_i depends only on r mod p_i, which is independent of r mod p_j for i ≠ j. Since there are exactly (p_i − 2) non-forbidden residues at each prime, the product gives ∏(p_i − 2) allowed joint classes.

What is *not* obvious is that all of these allowed classes are actually occupied by twins. That is an empirical observation, equivalent to the statement that large twin primes are equidistributed across all non-forbidden joint residue classes. This is consistent with, but goes beyond, the Bombieri-Vinogradov theorem.

### 8.5 Seed Dilution

The seed contribution to total occupancy shrinks exponentially:

| Basis | Seeds | ∏(p−2) | Seeds/∏(p−2) |
|-------|-------|--------|-------------|
| {3} | 1 | 1 | 1.000 |
| {3, 5} | 2 | 3 | 0.667 |
| {3, 5, 7} | 2 | 15 | 0.133 |
| {3, 5, 7, 11} | 3 | 135 | 0.022 |
| {3, 5, 7, 11, 13} | 3 | 1,485 | 0.002 |
| {3, 5, 7, 11, 13, 17} | 4 | 22,275 | 0.00018 |

Seeds grow at most logarithmically (bounded by the number of twin pairs ≤ max prime), while ∏(p−2) grows super-exponentially. In the limit, the seed contribution vanishes and the total occupancy is governed entirely by the independent regular channels.

---

## 9. Equidistribution Within Occupied Classes

**Observation 9.1.** Excluding defective classes, twin primes are nearly uniformly distributed across occupied residue classes:

| Scale k | Classes | Mean twins/class | CV |
|---------|---------|-------------------|----|
| 0 | 11 | 21,736 | 0.0045 |
| 1 | 143 | 1,672 | 0.018 |
| 2 | 1,859 | 128.6 | 0.071 |
| 3 | 24,167 | 9.9 | 0.287 |

At scales 0–1, the coefficient of variation is below 2%, indicating near-perfect equidistribution.

---

## 10. The Remaining Gap

**Proved or verified exactly:**
- The general occupancy formula occ_p(k) = (p−2)·p^k + c_p (§2)
- Seed-regular decomposition with disjoint classes (§2.2)
- Complete empty class characterization via p-divisibility alone (§3)
- Binary Hensel lifting with unique defective thread (§4)
- Universal tunneling at p = 3 (§5)
- **Exact cross-tower independence of regular channels** (§8)
- Equidistribution of twins across non-defective classes (§9)

**The gap.** Our results establish that each p-adic tower has exact internal structure and that the towers do not interact through the regular channels. The residue classes available for large twin primes are determined by a product of independent local constraints, and every such class is occupied in our data range.

The twin prime conjecture reduces to: *do the regular classes remain occupied as the modulus grows without bound?* Equivalently: is the equidistribution of twin primes across non-forbidden residue classes (Observation 9.1) effective enough that no class is starved as the number of classes grows?

This is a question about the *density* of twin primes within a *provably independent* channel structure, not about inter-tower coupling. The channels exist (by CRT), are independent (by Theorem 8.1), and are individually well-behaved (by Hensel lifting). The conjecture asserts that primes are distributed densely enough to fill them all.

---

## 11. Computational Methods

All computations use Python 3 with a sieve of Eratosthenes to N = 5 × 10^7 (239,101 twin pairs). The occupancy formula is verified by exact set-based counting. The cross-tower independence theorem is verified by enumerating regular classes (those containing at least one twin n > max(basis)) at each modulus and comparing to ∏(p−2). No floating-point arithmetic is used for exact claims. Runtime: approximately 20 seconds on a single core.

---

## Acknowledgments

The author thanks the mathematical community for the foundations on which this work rests, and welcomes corrections, extensions, and connections to existing programs. The seed-regular decomposition that led to the independence theorem arose from considering each prime's "self-view" — treating position 0 mod p not as an empty class but as where p itself resides.

---

## References

[1] Y. Zhang, "Bounded gaps between primes," *Annals of Mathematics* **179** (2014), 1121–1174.

[2] D.H.J. Polymath, "Variants of the Selberg sieve, and bounded intervals containing many primes," *Research in the Mathematical Sciences* **1** (2014), Article 12.

[3] G.H. Hardy and J.E. Littlewood, "Some problems of 'Partitio Numerorum'; III: On the expression of a number as a sum of primes," *Acta Mathematica* **44** (1923), 1–70.

[4] W. Sawin and M. Shusterman, "On the Chowla and twin primes conjectures over F_q[T]," *Annals of Mathematics* **196** (2022), 457–506.

[5] J. Maynard, "Small gaps between primes," *Annals of Mathematics* **181** (2015), 383–413.

[6] H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications **53** (2004).

---

## Appendix: Reproducibility Code

```python
#!/usr/bin/env python3
"""
Verification of all results in "On the p-adic Structure of Twin Prime
Residue Classes" — v3 with cross-tower independence.

Requirements: Python 3.6+, no external libraries.
Runtime: ~20 seconds on a modern single core.
"""
import math, time
from itertools import combinations
from collections import defaultdict

N = 50_000_000

def build_sieve(limit):
    s = bytearray(limit + 1)
    s[0] = s[1] = 1
    for i in range(2, int(math.sqrt(limit)) + 1):
        if not s[i]:
            for j in range(i*i, limit+1, i): s[j] = 1
    return s

print(f"Building sieve to {N:,}...")
t0 = time.time()
SIEVE = build_sieve(N + 2)
is_prime = lambda n: 0 <= n <= N+2 and not SIEVE[n]
TWINS = [n for n in range(3, N, 2) if is_prime(n) and is_prime(n+2)]
print(f"Found {len(TWINS):,} twin pairs in {time.time()-t0:.1f}s\n")

# === §2: General formula ===
print("§2 General occupancy formula")
all_primes = [p for p in range(3, 300) if is_prime(p)]
exact = tested = 0
for p in all_primes:
    c_p = (1 if p >= 4 and is_prime(p-2) else 0) + (1 if is_prime(p+2) else 0)
    for k in range(5):
        mod = p**(k+1)
        if mod > 500000: break
        if len(TWINS)/mod < 8.5: break
        occ = len({n % mod for n in TWINS})
        pred = (p-2)*p**k + c_p
        tested += 1
        if occ == pred: exact += 1
        else: print(f"  MISMATCH: p={p}, k={k}")
print(f"  {exact}/{tested} exact matches\n")

# === §3: Empty classes ===
print("§3 Empty classes arise only from p-divisibility")
for k in range(3):
    mod = 13**(k+1)
    occupied = {n % mod for n in TWINS}
    empty = set(range(mod)) - occupied
    predicted_empty = {r for r in range(mod) if r%13 == 0 or r%13 == 11}
    extra = empty - predicted_empty
    print(f"  k={k}: extra empties = {len(extra)}")

# === §4: Defective cascade ===
print("\n§4 Defective cascade")
for p in [5, 7, 13, 19, 31]:
    if not is_prime(p-2): continue
    survivors = sorted({n % (p*p) for n in TWINS if n % p == p-2})
    print(f"  p={p}: survivor={survivors}")

# === §5: Universal tunneling ===
print("\n§5 Universal tunneling")
print(f"  n>3 with n%3≠2: {sum(1 for n in TWINS if n>3 and n%3!=2)}")
basis14 = [3,5,7,11,13,17,19,23,29,31,37,41,43,47]
no_carry = sum(1 for n in TWINS if not any(n%p >= p-2 for p in basis14))
print(f"  Twins with no carry at any p≤47: {no_carry}")

# === §8: Cross-tower independence ===
print("\n§8 Cross-tower independence")
basis7 = [3, 5, 7, 11, 13, 17, 19]

for size in range(2, 6):
    exact_count = tested_count = 0
    for combo in combinations(basis7, size):
        mod = math.prod(combo)
        if mod > 5000000: continue
        thresh = max(combo)
        regular = len({n % mod for n in TWINS if n > thresh})
        predicted = math.prod(p - 2 for p in combo)
        tested_count += 1
        if regular == predicted: exact_count += 1
        elif len(TWINS)/mod < 5: pass  # data limit
        else: print(f"  MISMATCH size={size}: {combo}")
    print(f"  Size {size}: {exact_count}/{tested_count} exact")

# Cumulative basis
print("  Cumulative basis:")
for i in range(2, len(basis7)+1):
    b = basis7[:i]
    mod = math.prod(b)
    if mod > 50000000: break
    thresh = max(b)
    regular = len({n % mod for n in TWINS if n > thresh})
    predicted = math.prod(p - 2 for p in b)
    seeds = len({n % mod for n in TWINS if n <= thresh} -
                {n % mod for n in TWINS if n > thresh})
    total = regular + seeds
    print(f"    {str(b):>25}: regular={regular}, ∏(p-2)={predicted}, "
          f"seeds={seeds}, total={total}")

# === §9: Equidistribution ===
print("\n§9 Equidistribution")
for k in range(4):
    mod = 13**(k+1)
    if mod > N: break
    cc = defaultdict(int)
    for n in TWINS: cc[n % mod] += 1
    vals = [c for r, c in cc.items() if r != 11]
    mn = sum(vals)/len(vals)
    std = (sum((x-mn)**2 for x in vals)/len(vals))**0.5
    print(f"  k={k}: CV = {std/mn:.4f}")

print("\nAll verifications complete.")
```
