
"""
RIEMANN ZERO EXCLUSION THEOREM - Corrected Analysis
====================================================

Analyzing Riemann zero repulsion from UFRF and Monster A-zero lattices.
"""

import numpy as np
from math import pi, sin, sqrt
from scipy import stats
import json
from pathlib import Path

# First 100 Riemann zeros
riemann_zeros = [
    14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
    37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
    52.970321, 56.446248, 59.347044, 60.831779, 65.112544,
    67.079811, 69.546402, 72.067158, 75.704691, 77.144840,
    79.337375, 82.910381, 84.735493, 87.425275, 88.809111,
    92.491899, 94.651344, 95.870634, 98.831194, 101.317851,
    103.725538, 105.446623, 107.168611, 111.029536, 111.874659,
    114.320221, 116.226680, 118.790783, 121.370125, 122.946829,
    124.256818, 127.516684, 129.578704, 131.087688, 133.497737,
    134.756509, 138.116042, 139.736208, 141.123707, 143.111845,
    146.000982, 147.422765, 150.053520, 150.925257, 153.024693,
    156.112909, 157.597591, 158.849988, 161.188964, 163.030709,
    165.537069, 167.184439, 169.094515, 169.911977, 173.536502,
    174.754191, 176.441434, 178.377407, 179.916484, 182.207078,
    184.874468, 185.598783, 187.228922, 189.416408, 192.026656,
    193.079726, 195.265396, 196.876481, 198.015309, 201.264751,
    202.493594, 204.178642, 205.394702, 207.906258, 209.576509,
    211.690862, 213.347919, 214.547044, 216.169538, 219.067596,
    220.714918, 221.430705, 224.007000, 224.962612, 227.421444,
    229.337446, 231.249188, 233.693404, 236.524229, 237.584284
]

print("=" * 70)
print("RIEMANN ZERO EXCLUSION THEOREM - CORRECTED ANALYSIS")
print("=" * 70)

print(f"\nAnalyzing first {len(riemann_zeros)} Riemann zeros")
print(f"Range: {min(riemann_zeros):.2f} to {max(riemann_zeros):.2f}")

def compute_A_zero_lattice(generators, gamma_max=250):
    """Compute A-zero lattice points: γ = 2nπ/d for each generator d.

    Important: max_n must scale with d to cover [0, gamma_max]. A fixed max_n
    truncates the lattice badly for large generators (e.g. 47, 59, 71).
    """
    lattice_points = []
    for d in generators:
        max_n = int(np.floor(gamma_max * d / (2 * pi)))
        for n in range(1, max_n + 1):
            gamma = 2 * n * pi / d
            if gamma <= gamma_max:
                lattice_points.append(gamma)
    return sorted(set(lattice_points))

def distance_to_nearest_lattice(gamma, lattice_points):
    """Find minimum distance from gamma to any lattice point"""
    distances = [abs(gamma - gp) for gp in lattice_points]
    return min(distances) if distances else float('inf')

# ============================================================
# UFRF LATTICE
# ============================================================

print("\n" + "=" * 70)
print("UFRF LATTICE")
print("=" * 70)

ufrf_gens = [3, 5, 7, 11, 13]
lattice_ufrf = compute_A_zero_lattice(ufrf_gens, gamma_max=250)
print(f"Generators: {ufrf_gens}")
print(f"Lattice points: {len(lattice_ufrf)}")
print(f"Spacing range: {min([lattice_ufrf[i+1] - lattice_ufrf[i] for i in range(len(lattice_ufrf)-1)]):.4f} to {max([lattice_ufrf[i+1] - lattice_ufrf[i] for i in range(len(lattice_ufrf)-1)]):.4f}")

distances_ufrf = [distance_to_nearest_lattice(g, lattice_ufrf) for g in riemann_zeros]

print(f"\nDistances to nearest A-zero:")
print(f"  Mean: {np.mean(distances_ufrf):.6f}")
print(f"  Median: {np.median(distances_ufrf):.6f}")
print(f"  Std: {np.std(distances_ufrf):.6f}")

thresholds = [0.05, 0.1, 0.2, 0.5]
print(f"\nZeros within threshold:")
for t in thresholds:
    count = sum(1 for d in distances_ufrf if d < t)
    print(f"  Within {t}: {count}/{len(riemann_zeros)} ({100*count/len(riemann_zeros):.1f}%)")

# ============================================================
# MONSTER LATTICE
# ============================================================

print("\n" + "=" * 70)
print("MONSTER LATTICE")
print("=" * 70)

monster_gens = [47, 59, 71]
lattice_monster = compute_A_zero_lattice(monster_gens, gamma_max=250)
print(f"Generators: {monster_gens}")
print(f"Lattice points: {len(lattice_monster)}")

# Density comparison
lattice_ufrf_100 = [p for p in lattice_ufrf if p <= 100]
lattice_monster_100 = [p for p in lattice_monster if p <= 100]
print(f"\nDensity in [0, 100]:")
print(f"  UFRF: {len(lattice_ufrf_100)} points")
print(f"  Monster: {len(lattice_monster_100)} points")
print(f"  Ratio: {len(lattice_monster_100)/max(1,len(lattice_ufrf_100)):.2f}×")

distances_monster = [distance_to_nearest_lattice(g, lattice_monster) for g in riemann_zeros]

print(f"\nDistances to nearest A-zero:")
print(f"  Mean: {np.mean(distances_monster):.6f}")
print(f"  Median: {np.median(distances_monster):.6f}")
print(f"  Std: {np.std(distances_monster):.6f}")

print(f"\nZeros within threshold:")
for t in thresholds:
    count = sum(1 for d in distances_monster if d < t)
    print(f"  Within {t}: {count}/{len(riemann_zeros)} ({100*count/len(riemann_zeros):.1f}%)")

# ============================================================
# COMPARISON
# ============================================================

print("\n" + "=" * 70)
print("COMPARISON")
print("=" * 70)

print(f"\n{'Metric':<35} {'UFRF':<15} {'Monster':<15} {'Ratio':<10}")
print("-" * 75)

print(f"{'Mean distance':<35} {np.mean(distances_ufrf):<15.4f} {np.mean(distances_monster):<15.4f} {np.mean(distances_monster)/np.mean(distances_ufrf):<10.3f}")
print(f"{'Median distance':<35} {np.median(distances_ufrf):<15.4f} {np.median(distances_monster):<15.4f} {np.median(distances_monster)/np.median(distances_ufrf):<10.3f}")
print(f"{'Std deviation':<35} {np.std(distances_ufrf):<15.4f} {np.std(distances_monster):<15.4f} {np.std(distances_monster)/np.std(distances_ufrf):<10.3f}")

# Within thresholds
for t in [0.05, 0.1, 0.2]:
    count_ufrf = sum(1 for d in distances_ufrf if d < t)
    count_monster = sum(1 for d in distances_monster if d < t)
    pct_ufrf = 100 * count_ufrf / len(riemann_zeros)
    pct_monster = 100 * count_monster / len(riemann_zeros)
    ratio_str = f"{pct_monster/pct_ufrf:.2f}×" if pct_ufrf > 0 else "N/A"
    print(f"{'% within ' + str(t):<35} {pct_ufrf:<15.1f}% {pct_monster:<15.1f}% {ratio_str:<10}")

# ============================================================
# DISTRIBUTION ANALYSIS
# ============================================================

print("\n" + "=" * 70)
print("DISTRIBUTION ANALYSIS")
print("=" * 70)

# Percentiles
percentiles = [10, 25, 50, 75, 90, 95, 99]
print(f"\n{'Percentile':<15} {'UFRF':<15} {'Monster':<15}")
print("-" * 45)
for p in percentiles:
    ufrf_p = np.percentile(distances_ufrf, p)
    monster_p = np.percentile(distances_monster, p)
    print(f"{p}th{'':<12} {ufrf_p:<15.4f} {monster_p:<15.4f}")

# ============================================================
# STATISTICAL TESTS
# ============================================================

print("\n" + "=" * 70)
print("STATISTICAL TESTS")
print("=" * 70)

# Two-sample t-test
t_stat, p_value = stats.ttest_ind(distances_monster, distances_ufrf)
print(f"\nTwo-sample t-test:")
print(f"  t-statistic: {t_stat:.4f}")
print(f"  p-value: {p_value:.6e}")
print(f"  Significant (p < 0.05): {'✓ YES' if p_value < 0.05 else '✗ NO'}")

# Mann-Whitney U test
u_stat, p_value_mw = stats.mannwhitneyu(distances_monster, distances_ufrf, alternative='two-sided')
print(f"\nMann-Whitney U test:")
print(f"  U-statistic: {u_stat:.4f}")
print(f"  p-value: {p_value_mw:.6e}")
print(f"  Significant (p < 0.05): {'✓ YES' if p_value_mw < 0.05 else '✗ NO'}")

# Effect size (Cohen's d)
pooled_std = sqrt(((len(distances_ufrf)-1)*np.var(distances_ufrf, ddof=1) + 
                   (len(distances_monster)-1)*np.var(distances_monster, ddof=1)) / 
                  (len(distances_ufrf) + len(distances_monster) - 2))
cohens_d = (np.mean(distances_monster) - np.mean(distances_ufrf)) / pooled_std
print(f"\nEffect size (Cohen's d): {cohens_d:.4f}")
if abs(cohens_d) < 0.2:
    effect = "negligible"
elif abs(cohens_d) < 0.5:
    effect = "small"
elif abs(cohens_d) < 0.8:
    effect = "medium"
else:
    effect = "large"
print(f"  Interpretation: {effect}")

# ============================================================
# NULL HYPOTHESIS (RANDOM POINTS)
# ============================================================

print("\n" + "=" * 70)
print("NULL HYPOTHESIS TEST (Random Points)")
print("=" * 70)

np.random.seed(42)
random_points = np.random.uniform(min(riemann_zeros), max(riemann_zeros), len(riemann_zeros))

distances_random_ufrf = [distance_to_nearest_lattice(g, lattice_ufrf) for g in random_points]
distances_random_monster = [distance_to_nearest_lattice(g, lattice_monster) for g in random_points]

print(f"\nRandom points mean distance:")
print(f"  UFRF lattice: {np.mean(distances_random_ufrf):.4f}")
print(f"  Monster lattice: {np.mean(distances_random_monster):.4f}")

print(f"\nRiemann vs Random (mean distance):")
print(f"  UFRF: {np.mean(distances_ufrf):.4f} vs {np.mean(distances_random_ufrf):.4f}")
print(f"  Monster: {np.mean(distances_monster):.4f} vs {np.mean(distances_random_monster):.4f}")

# Statistical tests
_, p_ufrf = stats.ttest_ind(distances_ufrf, distances_random_ufrf)
_, p_monster = stats.ttest_ind(distances_monster, distances_random_monster)
print(f"\nDifference from random:")
print(f"  UFRF: p = {p_ufrf:.6e} {'✓ DIFFERENT' if p_ufrf < 0.05 else '✗ NOT DIFFERENT'}")
print(f"  Monster: p = {p_monster:.6e} {'✓ DIFFERENT' if p_monster < 0.05 else '✗ NOT DIFFERENT'}")

# ============================================================
# SUMMARY
# ============================================================

print("\n" + "=" * 70)
print("THEOREM SUMMARY")
print("=" * 70)

print("\n✓ KEY FINDINGS:")
print(f"  • Monster lattice is {len(lattice_monster_100)/max(1,len(lattice_ufrf_100)):.1f}× denser than UFRF")
print(f"  • Mean distance to Monster A-zero: {np.mean(distances_monster):.2f}")
print(f"  • Mean distance to UFRF A-zero: {np.mean(distances_ufrf):.2f}")
print(f"  • Ratio: {np.mean(distances_monster)/np.mean(distances_ufrf):.2f}×")

if np.mean(distances_monster) > np.mean(distances_ufrf):
    print(f"\n✓ Zeros are FARTHER from denser (Monster) lattice!")
    print(f"  This supports the EXCLUSION HYPOTHESIS.")
else:
    print(f"\n✗ Zeros are CLOSER to denser lattice")
    print(f"  This contradicts simple exclusion.")

print(f"\n✓ STATISTICAL SIGNIFICANCE:")
print(f"  p-value: {p_value:.6e}")
print(f"  Highly significant: {'YES ✓✓✓' if p_value < 0.001 else 'YES ✓' if p_value < 0.05 else 'NO'}")
print(f"  Effect size: {effect} (Cohen's d = {cohens_d:.3f})")

print(f"\n✓ IMPLICATIONS FOR RH:")
print(f"  • Zeros show different distance patterns for different lattices")
if np.mean(distances_monster) > np.mean(distances_ufrf):
    print(f"  • Denser lattice → larger mean distance (supports exclusion hypothesis)")
else:
    print(f"  • Denser lattice → smaller mean distance (consistent with density alone)")

print(f"  • Riemann-vs-random (t-test): UFRF p = {p_ufrf:.3g}, Monster p = {p_monster:.3g}")

# Save results
results = {
    "theorem": "riemann_zero_exclusion",
    "num_zeros": len(riemann_zeros),
    "ufrf": {
        "generators": ufrf_gens,
        "lattice_points": len(lattice_ufrf),
        "mean_distance": float(np.mean(distances_ufrf)),
        "median_distance": float(np.median(distances_ufrf)),
        "std": float(np.std(distances_ufrf))
    },
    "monster": {
        "generators": monster_gens,
        "lattice_points": len(lattice_monster),
        "mean_distance": float(np.mean(distances_monster)),
        "median_distance": float(np.median(distances_monster)),
        "std": float(np.std(distances_monster))
    },
    "comparison": {
        "density_ratio": len(lattice_monster_100)/max(1,len(lattice_ufrf_100)),
        "mean_ratio": float(np.mean(distances_monster) / np.mean(distances_ufrf)),
        "median_ratio": float(np.median(distances_monster) / np.median(distances_ufrf))
    },
    "statistics": {
        "t_statistic": float(t_stat),
        "p_value": float(p_value),
        "significant": bool(p_value < 0.05),
        "cohens_d": float(cohens_d),
        "effect_size": effect
    }
}

output_path = Path(__file__).resolve().parent / "riemann_zero_exclusion_results.json"
with open(output_path, "w") as f:
    json.dump(results, f, indent=2)

print("\n" + "=" * 70)
print(f"Results saved to: {output_path}")
print("=" * 70)

print("\n✓✓✓ RIEMANN ZERO EXCLUSION ANALYSIS COMPLETE ✓✓✓")
