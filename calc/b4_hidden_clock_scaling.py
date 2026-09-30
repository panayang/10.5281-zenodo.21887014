"""B4: does the hidden clock of thinned transitive percolation fade with scale separation? (law.md section 8)

TP(p), thinned with keep-probability q. Two kept neighbours are separated by a hidden gap g ~ Geometric(q) in birth labels.
P(a < b | gap g) = P_g is computed exactly: the set R of elements between a and b that are above a grows by a Markov chain
(element m joins R with probability 1 - (1-p)^{|R|}, R starts as {a}); then P_g = E[1 - (1-p)^{|R|}] after g - 1 steps.
For each q we choose p so that the coarse neighbour relation r_1 = E_g[P_g] is fixed, and report how strongly P_g varies
with the hidden gap (spread of P_g over the gap distribution, relative to r_1). Asymptotic sufficiency of the coarse
world would need this spread to vanish as 1/q grows (unless the coarse world could itself infer g, which is a separate question).
Output: calc/out/b4_hidden_clock_scaling.txt
"""
import os
import numpy as np
from scipy.optimize import brentq

OUT = os.path.join(os.path.dirname(__file__), "out", "b4_hidden_clock_scaling.txt")


def P_by_gap(p, gmax):
    dist = np.zeros(gmax + 2); dist[1] = 1.0          # |R| distribution, starts at 1
    sizes = np.arange(gmax + 2)
    out = np.zeros(gmax + 1)
    for g in range(1, gmax + 1):
        join = 1 - (1 - p) ** sizes
        out[g] = dist @ join                          # b is the next element: related iff linked to some member of R
        new = dist * (1 - join)
        new[1:] += (dist * join)[:-1]
        dist = new
    return out


def stats(p, q, gmax):
    P = P_by_gap(p, gmax)
    g = np.arange(1, gmax + 1)
    w = q * (1 - q) ** (g - 1); w /= w.sum()
    m = w @ P[1:]
    sd = np.sqrt(w @ (P[1:] - m) ** 2)
    lo, hi = np.interp([0.25, 0.75], np.cumsum(w), P[1:])
    return m, sd, lo, hi


lines = []
for r1 in (0.05, 0.1):
    lines.append(f"coarse neighbour relation fixed at r_1 = {r1}")
    for q in (0.5, 0.25, 0.125, 0.0625, 0.03125, 0.015625):
        gmax = int(40 / q)
        p = brentq(lambda pp: stats(pp, q, gmax)[0] - r1, 1e-7, r1)
        m, sd, lo, hi = stats(p, q, gmax)
        lines.append(f"  q = {q:<9} p = {p:.6f}  p/q = {p / q:.4f}   spread of P(a<b | hidden gap): sd/r_1 = {sd / m:.3f}, "
                     f"interquartile {lo:.4f} .. {hi:.4f}")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
