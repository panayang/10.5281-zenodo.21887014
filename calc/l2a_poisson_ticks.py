"""L2a: does the rigidity map survive when the ticks are a Poisson sample instead of a lattice?

Stand-in for sprinkling: each worldline's elements are a unit-intensity Poisson process in its own
proper time (the elements of a sprinkled causal set along a geodesic chain are, to leading order,
uniformly spread in proper time). Rates are measured in proper time, not in tick counts.
Output: calc/out/l2a_poisson_ticks.txt
"""
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from twochain import TwoChain, poisson_ticks, static_pair, receding, frw_comoving

OUT = os.path.join(os.path.dirname(__file__), "out", "l2a_poisson_ticks.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def run(name, F, G, N, seeds, bfac, expect):
    say(f"\n== {name}   [expected: {expect}]  N = {N}")
    for seed in seeds:
        rng = np.random.default_rng(seed)
        tc = TwoChain(F, G, poisson_ticks(N, rng), poisson_ticks(int(bfac * N) + 50, rng))
        a, b = tc.extremes()
        say(f"seed {seed}: extremes {a:.4f} .. {b:.4f}  (spread {b - a:.4f})")


if __name__ == "__main__":
    seeds = [1, 2, 3]
    for N in (1000, 4000):
        run("static pair, redshift 0.8", *static_pair(1.0, 0.8, 20.0), N, seeds, 1.5, "rigid at 0.8")
        run("receding, rapidity 0.5", *receding(0.5), N, seeds, 2.0,
            f"not rigid, extremes toward {math.exp(-0.5):.4f} .. {math.exp(0.5):.4f}")
        run("FRW a = t^0.5, chi = 2", *frw_comoving(0.5, 2.0, 10.0), N, seeds, 1.5, "rigid at 1 (slowly)")
        run("FRW a = t (Milne), chi = 0.5", *frw_comoving(1.0, 0.5, 10.0), N, seeds, 2.0,
            f"not rigid, extremes toward {math.exp(-0.5):.4f} .. {math.exp(0.5):.4f}")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
