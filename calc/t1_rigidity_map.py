"""T1: which pairs of worldlines have their relative clock rate fixed by the causal order alone?

For each geometry: the middle rate under the two extreme endpoints (bottom/top of the last row),
and under endpoints chosen at given rates. Rigid = the middle forgets the endpoint as N grows.
Output: calc/out/t1_rigidity_map.txt
"""
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from twochain import (TwoChain, unit_ticks, static_pair, receding, frw_comoving, de_sitter_comoving,
                      Worldline, minkowski_pair)

OUT = os.path.join(os.path.dirname(__file__), "out", "t1_rigidity_map.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def run(name, F, G, Ns, rates=(), expect=None, bfac=3.0):
    say(f"\n== {name}" + (f"   [expected: {expect}]" if expect else ""))
    for N in Ns:
        tc = TwoChain(F, G, unit_ticks(N), unit_ticks(int(bfac * N) + 10))
        m = N // 2
        f = tc.forward(m)
        lo_r = tc.middle_rate(tc.lo[N], m, f)
        hi_r = tc.middle_rate(tc.hi[N], m, f)
        row = f"N={N:5d}  extremes {lo_r:.4f} .. {hi_r:.4f}  (spread {hi_r - lo_r:.4f})"
        if rates:
            row += "  | end rate -> middle: " + ", ".join(
                f"{r:.3f}->{tc.middle_rate(tc.endpoint_for_rate(r), m, f):.4f}" for r in rates)
        say(row)


if __name__ == "__main__":
    Ns = [250, 1000, 4000]
    run("Minkowski, at rest, d = 20 (analytic F)", lambda t: t + 20, lambda s: s + 20, Ns,
        rates=(0.8, 1.0, 1.25), expect="rigid at 1")
    A = Worldline(lambda t: 0 * t, tmax=20000)
    B = Worldline(lambda t: 20 + 0 * t, tmax=20000)
    run("Minkowski, at rest, d = 20 (worldline solver, cross-check)", *minkowski_pair(A, B), [250, 1000],
        expect="same as above")
    R, w = 3.0, 0.2
    Bosc = Worldline(lambda t: 10 + R * np.sin(w * t), tmax=20000)
    th = np.linspace(0, 2 * math.pi, 200001)
    avg = float(np.mean(np.sqrt(1 - (R * w * np.cos(th)) ** 2)))
    run(f"Minkowski, B oscillates (amplitude {R}, speed amplitude {R * w:.1f})", *minkowski_pair(A, Bosc),
        [250, 1000, 2000], rates=(0.7, 0.9, 1.1), expect=f"rigid at <1/gamma> = {avg:.4f}")
    run("static pair, redshift 0.8 (lapse ratio a2/a1)", *static_pair(1.0, 0.8, 20.0), Ns,
        rates=(0.7, 0.8, 1.2), expect="rigid at 0.8")
    for eta in (0.25, 0.5, 1.0):
        run(f"receding, rapidity {eta}", *receding(eta), Ns,
            rates=(math.exp(-eta / 2), 1.0, math.exp(eta / 2)),
            expect=f"not rigid; extremes -> e^-eta = {math.exp(-eta):.4f}, e^eta = {math.exp(eta):.4f}")
    for p, chi in [(0.5, 2.0), (2 / 3, 2.0), (1.0, 0.5), (1.5, 0.05)]:
        run(f"FRW a = t^{p:.3g}, comoving, chi = {chi}", *frw_comoving(p, chi, 10.0), Ns, rates=(0.8, 1.0, 1.25),
            expect="rigid (slowly)" if p < 1 else ("critical: extremes -> e^-chi, e^chi" if p == 1 else "not rigid (horizon)"))
    H = 0.002
    chi = math.exp(-2.0) / H  # horizon at tau = 1000
    run(f"de Sitter, H = {H}, comoving, horizon at tau = 1000", *de_sitter_comoving(H, chi), [250, 1000, 4000],
        rates=(0.8, 1.0, 1.25), expect="windows grow then become infinite: not rigid")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
