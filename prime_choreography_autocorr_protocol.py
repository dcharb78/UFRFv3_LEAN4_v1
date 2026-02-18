#!/usr/bin/env python3
"""
Prime-Choreography Autocorrelation Protocol (Deterministic, Rational)

This is an evidence-lane protocol extracted from `context2/longconversation.txt`:

- Define a single piecewise "breathing" waveform on the canonical 13-position cycle.
- Instantiate oscillators with prime-scaled periods (period = 13 * p).
- Form a superposition across a fixed prime set.
- Compute discrete autocorrelation peaks over a finite window.

This does NOT claim a universal law. It is a deterministic finite check whose outputs are
intended to be paired with a Lean summary theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
from pathlib import Path
from typing import Iterable, List, Tuple


BASE = 13


def frac_to_json(x: Fraction) -> dict:
    return {"num": x.numerator, "den": x.denominator}


def waveform(t: Fraction, *, sqrt_phi_approx: Fraction) -> Fraction:
    """
    Piecewise breathing envelope on [0, 13).

    Segment thresholds are rational: 3, 6, 13/2, 9, 21/2, 12.
    Outputs are rational except for sqrt(phi), which is passed as a rational approximation.
    """
    assert 0 <= t < BASE

    if t < 6:
        # Linear warmup + expansion: 0 -> 2 over [0,6)
        return t / 3
    if t < Fraction(13, 2):
        # Flip approach plateau: [6, 6.5)
        return Fraction(2, 1)
    if t < 9:
        # Contraction: 2 -> 1 over [6.5, 9)
        # 2 - (t - 13/2)/(5/2) = (23 - 2t)/5
        return Fraction(23, 5) - Fraction(2, 5) * t
    if t < Fraction(21, 2):
        # REST: sqrt(phi) enhancement over [9, 10.5)
        return sqrt_phi_approx
    if t < 12:
        # BRIDGE: sqrt(phi) -> sqrt(phi) - 1/2 over [10.5, 12)
        return sqrt_phi_approx - (t - Fraction(21, 2)) / 3
    # RETURN/VOID: [12, 13)
    return Fraction(0, 1)


def oscillator_output(t: int, p: int, *, sqrt_phi_approx: Fraction) -> Fraction:
    """
    One oscillator with period 13*p.
    Phase is mapped into [0,13) as (t mod (13*p)) / p.
    """
    period = BASE * p
    phase = Fraction(t % period, p)  # in [0, 13)
    return waveform(phase, sqrt_phi_approx=sqrt_phi_approx)


def superposition(ts: Iterable[int], primes: List[int], *, sqrt_phi_approx: Fraction) -> List[Fraction]:
    out: List[Fraction] = []
    for t in ts:
        s = Fraction(0, 1)
        for p in primes:
            s += oscillator_output(t, p, sqrt_phi_approx=sqrt_phi_approx)
        out.append(s)
    return out


def autocorr_top_lags(
    series: List[Fraction],
    *,
    min_lag: int,
    max_lag: int,
    top_k: int,
) -> List[Tuple[int, Fraction]]:
    """
    Return top-k lags by average autocorrelation:
      avg(lag) = (1/(N-lag)) * sum_{t=0..N-lag-1} s[t] * s[t+lag]

    Tie-break: smaller lag first.
    """
    n = len(series)
    assert 1 <= min_lag <= max_lag < n
    scores: List[Tuple[int, Fraction]] = []
    for lag in range(min_lag, max_lag + 1):
        acc = Fraction(0, 1)
        for t in range(0, n - lag):
            acc += series[t] * series[t + lag]
        avg = acc / (n - lag)
        scores.append((lag, avg))

    scores.sort(key=lambda lv: (-lv[1], lv[0]))
    return scores[:top_k]


def inversion_count(xs: List[int]) -> int:
    """
    Kendall-style inversion count of a list (how far from sorted ascending).

    This is a simple, deterministic "degeneracy detector":
    - perfectly monotone increasing -> 0 inversions (e.g. uniform control)
    - multi-period superpositions generally scramble ordering -> >0 inversions
    """
    inv = 0
    for i in range(len(xs)):
        for j in range(i + 1, len(xs)):
            if xs[i] > xs[j]:
                inv += 1
    return inv


@dataclass(frozen=True)
class ProtocolParams:
    primes_ufrf: List[int]
    primes_conventional: List[int]
    primes_uniform: List[int]
    primes_nonprime_swap: List[int]
    n_samples: int
    max_lag: int
    top_k: int
    sqrt_phi_approx: Fraction


def run(params: ProtocolParams) -> dict:
    ts = list(range(params.n_samples))

    s_ufrf = superposition(ts, params.primes_ufrf, sqrt_phi_approx=params.sqrt_phi_approx)
    s_conv = superposition(ts, params.primes_conventional, sqrt_phi_approx=params.sqrt_phi_approx)
    s_uniform = superposition(ts, params.primes_uniform, sqrt_phi_approx=params.sqrt_phi_approx)
    s_nonprime = superposition(ts, params.primes_nonprime_swap, sqrt_phi_approx=params.sqrt_phi_approx)

    top_ufrf_all = autocorr_top_lags(
        s_ufrf, min_lag=1, max_lag=params.max_lag, top_k=params.top_k
    )
    top_conv_all = autocorr_top_lags(
        s_conv, min_lag=1, max_lag=params.max_lag, top_k=params.top_k
    )
    top_uniform_all = autocorr_top_lags(
        s_uniform, min_lag=1, max_lag=params.max_lag, top_k=params.top_k
    )
    top_nonprime_all = autocorr_top_lags(
        s_nonprime, min_lag=1, max_lag=params.max_lag, top_k=params.top_k
    )
    top_ufrf_ge_base = autocorr_top_lags(
        s_ufrf, min_lag=BASE, max_lag=params.max_lag, top_k=params.top_k
    )
    top_conv_ge_base = autocorr_top_lags(
        s_conv, min_lag=BASE, max_lag=params.max_lag, top_k=params.top_k
    )
    top_uniform_ge_base = autocorr_top_lags(
        s_uniform, min_lag=BASE, max_lag=params.max_lag, top_k=params.top_k
    )
    top_nonprime_ge_base = autocorr_top_lags(
        s_nonprime, min_lag=BASE, max_lag=params.max_lag, top_k=params.top_k
    )

    def autocorr_score(series: List[Fraction], lag: int) -> Fraction:
        n = len(series)
        assert 1 <= lag < n
        acc = Fraction(0, 1)
        for t in range(0, n - lag):
            acc += series[t] * series[t + lag]
        return acc / (n - lag)

    def top_mult13(series: List[Fraction]) -> List[Tuple[int, Fraction]]:
        lags = [BASE * k for k in range(1, params.max_lag // BASE + 1)]
        scored = [(lag, autocorr_score(series, lag)) for lag in lags]
        scored.sort(key=lambda lv: (-lv[1], lv[0]))
        return scored

    mult13_ufrf = top_mult13(s_ufrf)
    mult13_conv = top_mult13(s_conv)
    mult13_uniform = top_mult13(s_uniform)
    mult13_nonprime = top_mult13(s_nonprime)

    def summarize(top_all: List[Tuple[int, Fraction]], top_ge_base: List[Tuple[int, Fraction]]) -> dict:
        lags_all = [lag for lag, _ in top_all]
        lags_ge_base = [lag for lag, _ in top_ge_base]
        contains_13_ge_base = (BASE in lags_ge_base)
        mult13_ge_base = [lag for lag in lags_ge_base if lag % BASE == 0]
        return {
            "top_lags_all": lags_all,
            "top_entries_all": [{"lag": lag, "avg": frac_to_json(avg)} for lag, avg in top_all],
            "top_lags_ge_base": lags_ge_base,
            "top_entries_ge_base": [{"lag": lag, "avg": frac_to_json(avg)} for lag, avg in top_ge_base],
            "contains_13_in_top_ge_base": contains_13_ge_base,
            "top_ge_base_multiple_of_13": mult13_ge_base,
            "count_top_ge_base_multiple_of_13": len(mult13_ge_base),
        }

    return {
        "theorem": "prime_choreography_autocorr_protocol_v1",
        "params": {
            "base": BASE,
            "n_samples": params.n_samples,
            "max_lag": params.max_lag,
            "top_k": params.top_k,
            "sqrt_phi_approx": frac_to_json(params.sqrt_phi_approx),
            "primes_ufrf": params.primes_ufrf,
            "primes_conventional": params.primes_conventional,
            "primes_uniform": params.primes_uniform,
            "primes_nonprime_swap": params.primes_nonprime_swap,
        },
        "results": {
            "ufrf": {
                **summarize(top_ufrf_all, top_ufrf_ge_base),
                "mult13_lags_sorted": [lag for lag, _ in mult13_ufrf],
                "mult13_entries_sorted": [{"lag": lag, "avg": frac_to_json(avg)} for lag, avg in mult13_ufrf],
                "mult13_inversion_count": inversion_count([lag for lag, _ in mult13_ufrf]),
            },
            "conventional": {
                **summarize(top_conv_all, top_conv_ge_base),
                "mult13_lags_sorted": [lag for lag, _ in mult13_conv],
                "mult13_entries_sorted": [{"lag": lag, "avg": frac_to_json(avg)} for lag, avg in mult13_conv],
                "mult13_inversion_count": inversion_count([lag for lag, _ in mult13_conv]),
            },
            "uniform": {
                **summarize(top_uniform_all, top_uniform_ge_base),
                "mult13_lags_sorted": [lag for lag, _ in mult13_uniform],
                "mult13_entries_sorted": [{"lag": lag, "avg": frac_to_json(avg)} for lag, avg in mult13_uniform],
                "mult13_inversion_count": inversion_count([lag for lag, _ in mult13_uniform]),
            },
            "nonprime_swap": {
                **summarize(top_nonprime_all, top_nonprime_ge_base),
                "mult13_lags_sorted": [lag for lag, _ in mult13_nonprime],
                "mult13_entries_sorted": [{"lag": lag, "avg": frac_to_json(avg)} for lag, avg in mult13_nonprime],
                "mult13_inversion_count": inversion_count([lag for lag, _ in mult13_nonprime]),
            },
        },
    }


def main() -> None:
    params = ProtocolParams(
        primes_ufrf=[1, 3, 5, 7, 11],
        primes_conventional=[2, 3, 5, 7, 11],
        primes_uniform=[1, 1, 1, 1, 1],
        primes_nonprime_swap=[1, 3, 5, 7, 9],
        n_samples=BASE * 11 * 5,  # 5 cycles of the largest prime period (13*11)
        max_lag=BASE * 11,
        top_k=15,
        sqrt_phi_approx=Fraction(159, 125),  # consistent with repo's sqrt(phi) proxy
    )

    out = run(params)
    out_path = Path(__file__).resolve().with_name("prime_choreography_autocorr_results.json")
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    u = out["results"]["ufrf"]
    c = out["results"]["conventional"]
    un = out["results"]["uniform"]
    np = out["results"]["nonprime_swap"]
    print("Saved prime choreography autocorr summary:", out_path)
    print("  UFRF primes:", out["params"]["primes_ufrf"])
    print("  Conventional primes:", out["params"]["primes_conventional"])
    print("  Uniform primes:", out["params"]["primes_uniform"])
    print("  Nonprime swap primes:", out["params"]["primes_nonprime_swap"])
    print("  UFRF top lags (all):", u["top_lags_all"])
    print("  Conventional top lags (all):", c["top_lags_all"])
    print("  UFRF top lags (>=13):", u["top_lags_ge_base"])
    print("  Conventional top lags (>=13):", c["top_lags_ge_base"])
    print("  UFRF contains 13 in top (>=13):", u["contains_13_in_top_ge_base"])
    print("  Conventional contains 13 in top (>=13):", c["contains_13_in_top_ge_base"])
    print("  Uniform mult13 top lag:", un["mult13_lags_sorted"][0])
    print("  Nonprime swap mult13 top lag:", np["mult13_lags_sorted"][0])


if __name__ == "__main__":
    main()
