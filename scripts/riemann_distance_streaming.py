#!/usr/bin/env python3
"""
Streaming nearest-lattice distance analysis for very large zeta-zero datasets.

Core distance definition matches the Lean model in
`lean/Riemann_Zero_Exclusion_Theorem.lean`:

  lattice_d = { 2 * n * pi / d | n >= 1 }
  distance(gamma, lattice_family) = min over all generators in family

This script avoids materializing lattice points and instead uses the closed-form
distance to the nearest positive multiple of each step size.
"""

from __future__ import annotations

import argparse
import gzip
import json
import math
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Sequence, Tuple


PI = 3.141592653589793
FAMILIES: Dict[str, List[int]] = {
    "ufrf": [3, 5, 7, 11, 13],
    "monster": [47, 59, 71],
}

# Lean's theorem currently reports this threshold explicitly.
DEFAULT_THRESHOLDS = [0.05]

# Built-in first 100 nontrivial zeta zeros used by the current Lean check.
FIRST_100_ZEROS: List[float] = [
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
    229.337446, 231.249188, 233.693404, 236.524229, 237.584284,
]


@dataclass
class RunningStats:
    n: int = 0
    mean: float = 0.0
    m2: float = 0.0
    min_value: float = math.inf
    max_value: float = -math.inf

    def update(self, x: float) -> None:
        self.n += 1
        delta = x - self.mean
        self.mean += delta / self.n
        delta2 = x - self.mean
        self.m2 += delta * delta2
        if x < self.min_value:
            self.min_value = x
        if x > self.max_value:
            self.max_value = x

    def merge(self, other: "RunningStats") -> None:
        if other.n == 0:
            return
        if self.n == 0:
            self.n = other.n
            self.mean = other.mean
            self.m2 = other.m2
            self.min_value = other.min_value
            self.max_value = other.max_value
            return
        delta = other.mean - self.mean
        total_n = self.n + other.n
        self.mean = self.mean + delta * other.n / total_n
        self.m2 = self.m2 + other.m2 + (delta * delta) * self.n * other.n / total_n
        self.n = total_n
        self.min_value = min(self.min_value, other.min_value)
        self.max_value = max(self.max_value, other.max_value)

    @property
    def variance_population(self) -> float:
        if self.n == 0:
            return float("nan")
        return self.m2 / self.n

    @property
    def std_population(self) -> float:
        v = self.variance_population
        if math.isnan(v):
            return float("nan")
        return math.sqrt(max(v, 0.0))

    def as_summary(self) -> Dict[str, float]:
        return {
            "count": self.n,
            "mean": self.mean,
            "std_population": self.std_population,
            "min": self.min_value if self.n else float("nan"),
            "max": self.max_value if self.n else float("nan"),
        }

    @staticmethod
    def from_dict(payload: Dict[str, float]) -> "RunningStats":
        return RunningStats(
            n=int(payload["n"]),
            mean=float(payload["mean"]),
            m2=float(payload["m2"]),
            min_value=float(payload["min_value"]),
            max_value=float(payload["max_value"]),
        )


@dataclass
class FamilyAccumulator:
    name: str
    generators: List[int]
    thresholds: List[float]
    stats: RunningStats
    within_counts: Dict[str, int]

    @staticmethod
    def create(name: str, generators: List[int], thresholds: List[float]) -> "FamilyAccumulator":
        return FamilyAccumulator(
            name=name,
            generators=generators,
            thresholds=thresholds,
            stats=RunningStats(),
            within_counts={threshold_key(t): 0 for t in thresholds},
        )

    def update(self, gamma: float) -> None:
        d = nearest_family_distance(gamma, self.generators)
        self.stats.update(d)
        for t in self.thresholds:
            if d < t:
                self.within_counts[threshold_key(t)] += 1

    def merge(self, other: "FamilyAccumulator") -> None:
        if self.name != other.name or self.generators != other.generators:
            raise ValueError(f"Family mismatch while merging: {self.name} vs {other.name}")
        self.stats.merge(other.stats)
        for k, v in other.within_counts.items():
            self.within_counts[k] = self.within_counts.get(k, 0) + int(v)

    def as_summary(self) -> Dict[str, object]:
        pts_per_2pi = distinct_points_per_2pi(self.generators)
        return {
            "generators": self.generators,
            "points_per_2pi": pts_per_2pi,
            "density_per_unit_gamma": pts_per_2pi / (2.0 * PI),
            "distance": self.stats.as_summary(),
            "within": self.within_counts,
        }

    def as_state(self) -> Dict[str, object]:
        return {
            "name": self.name,
            "generators": self.generators,
            "thresholds": self.thresholds,
            "stats": asdict(self.stats),
            "within_counts": self.within_counts,
        }

    @staticmethod
    def from_state(payload: Dict[str, object]) -> "FamilyAccumulator":
        return FamilyAccumulator(
            name=str(payload["name"]),
            generators=list(payload["generators"]),  # type: ignore[arg-type]
            thresholds=[float(x) for x in payload["thresholds"]],  # type: ignore[arg-type]
            stats=RunningStats.from_dict(payload["stats"]),  # type: ignore[arg-type]
            within_counts={k: int(v) for k, v in dict(payload["within_counts"]).items()},  # type: ignore[arg-type]
        )


def threshold_key(t: float) -> str:
    return format(t, ".12g")


def gcd_many(xs: Sequence[int]) -> int:
    g = 0
    for x in xs:
        g = math.gcd(g, x)
    return g


def combinations_indices(n: int, r: int) -> Iterator[Tuple[int, ...]]:
    idx = list(range(r))
    if r == 0 or r > n:
        return
    while True:
        yield tuple(idx)
        i = r - 1
        while i >= 0 and idx[i] == i + n - r:
            i -= 1
        if i < 0:
            break
        idx[i] += 1
        for j in range(i + 1, r):
            idx[j] = idx[j - 1] + 1


def distinct_points_per_2pi(generators: Sequence[int]) -> int:
    """
    Exact count of distinct lattice points in one 2π window.

    Inclusion-exclusion on divisibility classes gives:
      count = Σ (-1)^(k+1) gcd(subset)
    over all nonempty subsets.
    """
    gens = list(generators)
    total = 0
    n = len(gens)
    for r in range(1, n + 1):
        sign = 1 if (r % 2 == 1) else -1
        subtotal = 0
        for idx in combinations_indices(n, r):
            subset = [gens[i] for i in idx]
            subtotal += gcd_many(subset)
        total += sign * subtotal
    return total


def nearest_positive_multiple_distance(x: float, step: float) -> float:
    if x <= 0.0:
        return step
    if x <= step:
        return step - x
    r = math.fmod(x, step)
    if r < 0.0:
        r += step
    return min(r, step - r)


def nearest_family_distance(gamma: float, generators: Sequence[int]) -> float:
    best = float("inf")
    for d in generators:
        step = (2.0 * PI) / float(d)
        cand = nearest_positive_multiple_distance(gamma, step)
        if cand < best:
            best = cand
    return best


def open_text_maybe_gzip(path: Path):
    if str(path).endswith(".gz"):
        return gzip.open(path, "rt", encoding="utf-8", errors="replace")
    return path.open("r", encoding="utf-8", errors="replace")


def iter_gammas_from_file(path: Path, token_index: int) -> Iterator[Tuple[int, float]]:
    with open_text_maybe_gzip(path) as f:
        for line_no, line in enumerate(f, start=1):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.replace(",", " ").split()
            if len(parts) <= token_index:
                continue
            try:
                g = float(parts[token_index])
            except ValueError:
                continue
            yield line_no, g


def run_analysis(
    output_path: Path,
    thresholds: List[float],
    token_index: int,
    zeros_path: Path | None,
    builtin_first100: bool,
    max_zeros: int | None,
    progress_every: int,
) -> None:
    if not builtin_first100 and zeros_path is None:
        raise ValueError("Provide --zeros or use --builtin-first100.")
    if builtin_first100 and zeros_path is not None:
        raise ValueError("Use either --zeros or --builtin-first100, not both.")

    families = {
        name: FamilyAccumulator.create(name, gens, thresholds)
        for name, gens in FAMILIES.items()
    }

    line_count = 0
    parsed_count = 0

    if builtin_first100:
        source = "builtin:first100"
        gamma_iter: Iterable[Tuple[int, float]] = enumerate(FIRST_100_ZEROS, start=1)
    else:
        source = str(zeros_path)
        gamma_iter = iter_gammas_from_file(zeros_path, token_index)  # type: ignore[arg-type]

    for line_no, gamma in gamma_iter:
        line_count = line_no
        parsed_count += 1
        for fam in families.values():
            fam.update(gamma)
        if progress_every > 0 and parsed_count % progress_every == 0:
            print(f"[progress] parsed={parsed_count:,} line={line_no:,}", flush=True)
        if max_zeros is not None and parsed_count >= max_zeros:
            break

    result = {
        "meta": {
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "source": source,
            "line_count_seen": line_count,
            "parsed_zeros": parsed_count,
            "pi": PI,
            "thresholds": thresholds,
            "token_index": token_index,
        },
        "families": {name: fam.as_summary() for name, fam in families.items()},
        "comparison": build_comparison(families),
        "accumulator_state": {
            "families": {name: fam.as_state() for name, fam in families.items()},
            "line_count_seen": line_count,
            "parsed_zeros": parsed_count,
            "source": source,
        },
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"[ok] wrote {output_path} (parsed_zeros={parsed_count:,})")


def build_comparison(families: Dict[str, FamilyAccumulator]) -> Dict[str, float]:
    out: Dict[str, float] = {}
    if "ufrf" in families and "monster" in families:
        u = families["ufrf"].stats
        m = families["monster"].stats
        if u.n > 0 and m.n > 0 and u.mean != 0.0:
            out["monster_mean_over_ufrf_mean"] = m.mean / u.mean
        up = distinct_points_per_2pi(families["ufrf"].generators)
        mp = distinct_points_per_2pi(families["monster"].generators)
        out["monster_points_per_2pi_over_ufrf"] = mp / up
    return out


def merge_analysis(inputs: List[Path], output_path: Path) -> None:
    if not inputs:
        raise ValueError("No input files provided to merge.")

    merged_families: Dict[str, FamilyAccumulator] = {}
    total_lines = 0
    total_parsed = 0
    source_files: List[str] = []

    for p in inputs:
        payload = json.loads(p.read_text(encoding="utf-8"))
        state = payload["accumulator_state"]
        fam_states = state["families"]
        source_files.append(str(p))
        total_lines += int(state.get("line_count_seen", 0))
        total_parsed += int(state.get("parsed_zeros", 0))

        for name, fam_payload in fam_states.items():
            incoming = FamilyAccumulator.from_state(fam_payload)
            if name not in merged_families:
                merged_families[name] = incoming
            else:
                merged_families[name].merge(incoming)

    result = {
        "meta": {
            "created_utc": datetime.now(timezone.utc).isoformat(),
            "source": "merge",
            "inputs": source_files,
            "line_count_seen": total_lines,
            "parsed_zeros": total_parsed,
            "pi": PI,
        },
        "families": {name: fam.as_summary() for name, fam in merged_families.items()},
        "comparison": build_comparison(merged_families),
        "accumulator_state": {
            "families": {name: fam.as_state() for name, fam in merged_families.items()},
            "line_count_seen": total_lines,
            "parsed_zeros": total_parsed,
            "source": "merge",
        },
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"[ok] wrote merged {output_path} from {len(inputs)} files")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Streaming nearest-lattice distance analysis for large zeta-zero sets."
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    run = sub.add_parser("run", help="Run streaming analysis.")
    run.add_argument("--zeros", type=Path, default=None, help="Path to zeros text file (or .gz).")
    run.add_argument(
        "--builtin-first100",
        action="store_true",
        help="Use built-in first 100 zeros used by Lean checks.",
    )
    run.add_argument("--output", type=Path, required=True, help="Output JSON path.")
    run.add_argument(
        "--threshold",
        type=float,
        action="append",
        default=None,
        help="Distance threshold for within-count (repeatable). Default: 0.05",
    )
    run.add_argument(
        "--token-index",
        type=int,
        default=0,
        help="Token index for gamma in each row after whitespace/comma split.",
    )
    run.add_argument(
        "--max-zeros",
        type=int,
        default=None,
        help="Stop after this many parsed zeros (for smoke tests).",
    )
    run.add_argument(
        "--progress-every",
        type=int,
        default=1_000_000,
        help="Progress print interval in parsed zeros (0 disables).",
    )

    merge = sub.add_parser("merge", help="Merge JSON outputs from run step.")
    merge.add_argument("--inputs", type=Path, nargs="+", required=True, help="Run JSON files.")
    merge.add_argument("--output", type=Path, required=True, help="Merged output JSON.")

    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()

    if args.cmd == "run":
        thresholds = sorted(set(args.threshold if args.threshold is not None else DEFAULT_THRESHOLDS))
        run_analysis(
            output_path=args.output,
            thresholds=thresholds,
            token_index=args.token_index,
            zeros_path=args.zeros,
            builtin_first100=args.builtin_first100,
            max_zeros=args.max_zeros,
            progress_every=args.progress_every,
        )
        return

    if args.cmd == "merge":
        merge_analysis(inputs=args.inputs, output_path=args.output)
        return

    raise RuntimeError(f"Unsupported command: {args.cmd}")


if __name__ == "__main__":
    main()

