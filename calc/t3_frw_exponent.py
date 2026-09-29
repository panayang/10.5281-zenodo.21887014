"""T3: FRW a = t^p, comoving observers. Is the cosmic rate fixed by the causal order iff p < 1?

Analytic: the synchronisation window at cosmic time t (the span of B's cosmic times spacelike to A's
event at t) is W(t) = 2 chi t^p (1 + O(t^(p-1))) for p < 1, 2 t sinh(chi) for p = 1, and infinite
after a finite time for p > 1 (event horizon). So rho = W/P -> 0 iff p < 1, which is p-ZFC's
rigidity criterion. Numerically: the spread of middle rates between the extreme endpoints should
fall like N^(p-1) for p < 1 and approach 2 sinh(chi) (extremes e^-chi, e^chi) at p = 1.
Output: calc/out/t3_frw_exponent.txt
"""
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from twochain import TwoChain, unit_ticks, frw_comoving

OUT = os.path.join(os.path.dirname(__file__), "out", "t3_frw_exponent.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def window(F, t):
    """Measured W at proper time t for the symmetric pair: F(t) - F^{-1}(t)."""
    lo, hi = 0.0, t
    for _ in range(80):  # F^{-1}(t): the A-time whose ray arrives at t
        mid = 0.5 * (lo + hi)
        if F(mid) < t:
            lo = mid
        else:
            hi = mid
    return F(t) - lo


if __name__ == "__main__":
    Ns = [500, 1000, 2000, 4000, 8000]
    T0 = 10.0
    say("p      chi   W/t at t=1000,4000 | spread at N = " + ", ".join(map(str, Ns)) + " | fitted exponent vs p-1")
    for p, chi in [(0.3, 2.0), (0.5, 2.0), (0.6, 2.0), (2 / 3, 2.0), (0.8, 1.0), (0.9, 0.5), (1.0, 0.5)]:
        F, G = frw_comoving(p, chi, T0)
        wr = [window(F, t) / t for t in (1000.0, 4000.0)]
        spreads = []
        for N in Ns:
            tc = TwoChain(F, G, unit_ticks(N), unit_ticks(3 * N + 50))
            a, b = tc.extremes()
            spreads.append(b - a)
        k = np.polyfit(np.log(Ns[1:]), np.log(spreads[1:]), 1)[0]
        tail = f"2 sinh(chi) = {2 * math.sinh(chi):.4f}" if p == 1 else f"p-1 = {p - 1:+.3f}"
        say(f"{p:.3f}  {chi:.1f}  {wr[0]:.4f} {wr[1]:.4f} | " + " ".join(f"{s:.4f}" for s in spreads)
            + f" | {k:+.3f}  ({tail})")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
