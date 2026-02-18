"""
OBSERVER TRACKING: From 1, never from 0
=========================================

Each prime is 0 to itself, 1 to us.
We track from 1 (existence). The index has indexes.
What does the accumulated view look like as we add primes?
"""
import math
from collections import Counter, defaultdict

N = 50_000_000
sieve = bytearray(N + 3)
sieve[0] = sieve[1] = 1
for i in range(2, int(math.sqrt(N + 2)) + 1):
    if not sieve[i]:
        for j in range(i*i, N+3, i): sieve[j] = 1
def is_prime(n): return 0 <= n <= N+2 and not sieve[n]
twins = [n for n in range(3, N, 2) if is_prime(n) and is_prime(n+2)]

# ================================================================
# THE OBSERVER'S VIEW: we track relative to each prime's 0
# ================================================================
print("=" * 80)
print("THE OBSERVER'S ACCUMULATED INDEX")
print("=" * 80)

print("""
  When we add prime p to our tracking:
    - p sees itself as 0 (void/source)
    - We see p as existing (1)
    - A twin n has distance (n mod p) from p's void
    - This distance is the INDEX at this level
    
  As we add primes, each twin accumulates a tuple of indexes:
    (distance from 3's void, distance from 5's void, distance from 7's void, ...)
    
  This tuple IS the adelic address. But from the observer's perspective,
  it's never (0, 0, 0, ...) because the observer starts at 1.
  The only thing at (0, 0, 0, ...) would be something divisible by ALL primes.
  That's 0 itself. The void.
""")

# ================================================================
# TRACKING FROM 1: How many distinct "index paths" exist?
# ================================================================
print("=" * 80)
print("INDEX ACCUMULATION: Tracking from the observer's starting point")
print("=" * 80)

basis_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

# For each twin, build the accumulated index
# At each step, the index is the tuple of residues
# The KEY: how many distinct index paths do twins trace?

print(f"\n  Accumulating indexes as we add each prime:")
print(f"  {'Primes used':>30} {'Distinct paths':>15} {'Total classes':>15} "
      f"{'Ratio':>10} {'∏(p-2)':>10}")

for num_primes in range(1, len(basis_primes) + 1):
    basis = basis_primes[:num_primes]
    
    # Each twin's index at this level
    paths = set()
    for n in twins:
        path = tuple(n % p for p in basis)
        paths.add(path)
    
    total_classes = math.prod(basis)
    product_p_minus_2 = math.prod(p - 2 for p in basis)
    
    print(f"  {str(basis):>30} {len(paths):>15,} {total_classes:>15,} "
          f"{len(paths)/total_classes:>10.6f} {product_p_minus_2:>10,}")

# ================================================================
# THE INDEX OF INDEXES: What happens at scale 2?
# ================================================================
print("\n" + "=" * 80)
print("INDEX OF INDEXES: Scale 2 (mod p²)")  
print("=" * 80)

print("""
  At scale 1: twin n has index (n mod p) — its distance from p's void
  At scale 2: twin n has index ((n mod p), (n//p mod p))
    - First index: where it is relative to p's void
    - Second index: where THAT index sits relative to p's void at the next scale
    
  The second index is literally "the index of the index."
  And at scale 3, we get the index of the index of the index.
  This IS the p-adic expansion.
""")

# For p=13, show the index-of-index structure
p = 13
print(f"  p={p}: Index of indexes for twin primes")
print(f"  {'n':>8} {'idx_0':>6} {'idx_1':>6} {'idx_2':>6} | {'meaning':>40}")

sample = [5, 11, 17, 29, 41, 101, 1009, 10007, 100003]
for n in sample:
    if not (is_prime(n) and is_prime(n+2)):
        continue
    d0 = n % p
    d1 = (n // p) % p
    d2 = (n // (p*p)) % p
    
    # The meaning
    if d0 == 0:
        meaning = f"{p} sees {n} at its own void"
    elif d0 == p - 2:
        meaning = f"{p} sees {n} at boundary (n+2 ÷ {p})"
    else:
        meaning = f"{p} sees {n} at position {d0} (alive)"
    
    print(f"  {n:>8} {d0:>6} {d1:>6} {d2:>6} | {meaning:>40}")

# ================================================================
# THE KEY QUESTION: Does the index structure encode something 
# about how twins MUST be distributed?
# ================================================================
print("\n" + "=" * 80)
print("CONSTRAINT PROPAGATION: How indexes constrain each other")
print("=" * 80)

print("""
  When we know idx_0 (position mod p), what does it tell us about idx_1?
  
  For twins: we need BOTH n and n+2 coprime to p.
  - idx_0 ≠ 0 (n coprime to p)
  - idx_0 ≠ p-2 (n+2 coprime to p)
  
  Does idx_0 constrain idx_1? In other words: given where a twin IS
  relative to p's void, does that constrain where its INDEX is
  relative to p's void at the next scale?
""")

# For each idx_0 value, what's the distribution of idx_1?
p = 13
idx0_to_idx1 = defaultdict(Counter)
for n in twins:
    d0 = n % p
    d1 = (n // p) % p
    idx0_to_idx1[d0][d1] += 1

print(f"  p={p}: Distribution of idx_1 given idx_0")
print(f"  (If independent: each idx_1 should have ~7.7% of its idx_0 group)\n")

# Check uniformity for a few idx_0 values
for d0 in [1, 6, 12]:  # seed, pre-flip, carry
    total_d0 = sum(idx0_to_idx1[d0].values())
    print(f"  idx_0={d0:>2} (total={total_d0:,}):")
    for d1 in range(13):
        count = idx0_to_idx1[d0][d1]
        pct = count / total_d0 * 100
        expected = 100 / 13
        dev = (pct - expected) / expected * 100
        bar = "█" * max(0, int(pct / expected * 10))
        print(f"    idx_1={d1:>2}: {count:>5} ({pct:>5.2f}%, dev={dev:>+5.1f}%) {bar}")

# ================================================================
# THE ACCUMULATION: How does the number of "valid paths" grow?
# ================================================================
print("\n" + "=" * 80)
print("PATH GROWTH: The index count at each scale")
print("=" * 80)

print(f"\n  At p=13, tracking how many distinct (idx_0, idx_1, ..., idx_k) tuples")
print(f"  are occupied by twins at each depth:\n")

for depth in range(1, 5):
    mod = 13 ** depth
    if mod > N * 10:
        break
    paths = set()
    for n in twins:
        path = []
        temp = n
        for _ in range(depth):
            path.append(temp % 13)
            temp //= 13
        paths.add(tuple(path))
    
    total = 13 ** depth
    predicted = 11 * 13**(depth-1) + 1
    print(f"  Depth {depth}: {len(paths):>8,} paths / {total:>10,} total "
          f"(predicted: {predicted:>8,}, formula match: {'✓' if len(paths)==predicted else '✗'})")

# ================================================================
# NOW: The concurrent index accumulation across primes
# ================================================================
print("\n" + "=" * 80)
print("CONCURRENT ACCUMULATION: Index paths across ALL primes")
print("=" * 80)

print("""
  At each prime p, a twin has a depth-k index path.
  The FULL state of a twin is the concatenation of all these paths.
  
  Depth 1: (n mod 3, n mod 5, n mod 7, ...) — the CRT address
  Depth 2: ((n mod 3, n//3 mod 3), (n mod 5, n//5 mod 5), ...)
  
  Each added depth multiplies the index space.
  The fraction occupied should be ∏ occ_p(k) / ∏ p^(k+1)
  ... IF the primes were independent. But they're not.
""")

# Compute at depth 1: fraction of CRT space occupied
basis = [3, 5, 7, 11, 13]
mod_product = math.prod(basis)
occupied_joint = len({n % mod_product for n in twins})
predicted_independent = math.prod(len({n % p for n in twins}) for p in basis)

# Predicted from formula
formula_each = [p - 2 + (1 if p>=4 and is_prime(p-2) else 0) + (1 if is_prime(p+2) else 0) 
                for p in basis]

print(f"  Depth 1 across {basis}:")
print(f"    Total CRT space:     {mod_product:>10,}")
print(f"    Occupied (actual):   {occupied_joint:>10,}")
print(f"    ∏ occ_p(0):          {math.prod(formula_each):>10,}")
print(f"    Ratio actual/indep:  {occupied_joint / math.prod(formula_each):.6f}")

# Depth 2: use p² for each prime
mod_product_2 = math.prod(p**2 for p in basis)
if mod_product_2 <= N * 100:
    occupied_2 = len({tuple(n % (p**2) for p in basis) for n in twins})
    indep_2 = math.prod(len({n % (p**2) for n in twins}) for p in basis)
    print(f"\n  Depth 2 across {basis}:")
    print(f"    Total space:         {mod_product_2:>10,}")
    print(f"    Occupied (actual):   {occupied_2:>10,}")

# ================================================================
# What fraction of the joint space is "reachable" from the observer?
# ================================================================
print("\n" + "=" * 80)
print("THE OBSERVER'S REACHABLE SET")
print("=" * 80)

print("""
  The observer starts at 1 (existence, not void).
  Each step adds a prime, adding a new index dimension.
  The "reachable set" = all CRT addresses that contain twins.
  
  Question: as we add primes, does the reachable set shrink 
  FASTER or SLOWER than the total space grows?
""")

print(f"  {'Step':>5} {'Added p':>8} {'Reachable':>12} {'Total space':>14} "
      f"{'Rate':>12} {'Marginal factor':>16}")

prev_reachable = 1
prev_total = 1
for i, p in enumerate(basis_primes):
    basis_so_far = basis_primes[:i+1]
    mod = math.prod(basis_so_far)
    
    reachable = len({n % mod for n in twins})
    total_space = mod
    rate = reachable / total_space
    
    if prev_reachable > 0 and i > 0:
        marginal = (reachable / prev_reachable) / (total_space / prev_total)
    else:
        marginal = rate
    
    print(f"  {i+1:>5} {p:>8} {reachable:>12,} {total_space:>14,} "
          f"{rate:>12.8f} {marginal:>16.6f}")
    
    prev_reachable = reachable
    prev_total = total_space

# ================================================================
# The marginal factor at each step — does it approach something?
# ================================================================
print(f"\n  The marginal factor is how much of p's space twins actually use,")
print(f"  GIVEN the constraints from all previous primes.")
print(f"  If independent: marginal = (p-2)/p.")
print(f"  If coupled: marginal < (p-2)/p.")
print(f"\n  {'p':>4} {'marginal':>10} {'(p-2)/p':>10} {'ratio':>10} {'HL factor':>12}")

prev_r = 1; prev_t = 1
for i, p in enumerate(basis_primes):
    basis_so_far = basis_primes[:i+1]
    mod = math.prod(basis_so_far)
    r = len({n % mod for n in twins})
    t = mod
    if i > 0:
        marg = (r / prev_r) / (t / prev_t)
        indep = (p - 2) / p
        hl = p * (p - 2) / (p - 1)**2
        print(f"  {p:>4} {marg:>10.6f} {indep:>10.6f} {marg/indep:>10.6f} {hl:>12.6f}")
    prev_r = r; prev_t = t

