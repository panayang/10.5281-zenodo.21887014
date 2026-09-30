"""B1: the rate ratio of a bound pair can be read locally from mutual windows.

For a_i on A, W_B(i) = number of B ticks incomparable to a_i (B's count of a_i's span);
for b_j on B, W_A(j) likewise. For a strip-shaped admissible region (bounded windows) of slope s,
vertical width / horizontal width = s, so W_B(a)/W_A(b) -> rate ratio e^{sigma_B - sigma_A}.
For a receding pair the ratio depends on which a_i and b_j are compared (the slicing), as in F2.
Output: calc/out/b1_mutual_windows.txt
"""
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from twochain import TwoChain, unit_ticks, static_pair, receding, frw_comoving, Worldline, minkowski_pair

OUT = os.path.join(os.path.dirname(__file__), "out", "b1_mutual_windows.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def windows(F, G, N, M):
    tc = TwoChain(F, G, unit_ticks(N), unit_ticks(M))
    WB = tc.hi - tc.lo                       # B ticks incomparable to A's i-th tick (region's vertical width)
    tcr = TwoChain(G, F, unit_ticks(M), unit_ticks(N))
    WA = tcr.hi - tcr.lo                     # A ticks incomparable to B's j-th tick
    return WB, WA


if __name__ == "__main__":
    N = 3000
    cases = [("static pair, lapse ratio 0.8", static_pair(1.0, 0.8, 20.0), 0.8),
             ("static pair, lapse ratio 1.3", static_pair(1.0, 1.3, 20.0), 1.3)]
    for name, (F, G), s in cases:
        WB, WA = windows(F, G, N, int(3 * N))
        i = np.arange(1000, 2000, 100)
        j = np.round(s * i).astype(int)
        r = WB[i] / WA[j]
        say(f"{name}: W_B(a_i)/W_A(b_j) at matched ticks: mean {r.mean():.4f} (min {r.min():.4f}, max {r.max():.4f}); rate ratio {s}")
    # bound but moving: B oscillates; compare period-averaged windows
    R, w = 3.0, 0.2
    A = Worldline(lambda t: 0 * t, tmax=20000)
    B = Worldline(lambda t: 10 + R * np.sin(w * t), tmax=20000)
    F, G = minkowski_pair(A, B)
    WB, WA = windows(F, G, 2000, 2400)
    th = np.linspace(0, 2 * math.pi, 200001)
    rate = float(np.mean(np.sqrt(1 - (R * w * np.cos(th)) ** 2)))
    say(f"oscillating pair: mean W_B / mean W_A over many periods = {WB[200:1800].mean() / WA[200:1600].mean():.4f}; long-run rate {rate:.4f}")
    # receding: the ratio depends on the slicing
    eta = 0.5
    F, G = receding(eta)
    WB, WA = windows(F, G, N, int(2 * N))
    for s in (math.exp(-eta / 2), 1.0, math.exp(eta / 2)):
        i = np.arange(1000, 1500, 50)
        j = np.round(s * i).astype(int)
        say(f"receding eta={eta}, comparing a_i with b_j at j = {s:.3f} i: W_B/W_A = {np.mean(WB[i] / WA[j]):.4f}"
            f"   (strip formula e^eta e^-eta / s = {1 / s:.4f})")
    # decelerating FRW: sublinear windows, rigid rate 1
    F, G = frw_comoving(0.5, 2.0, 10.0)
    WB, WA = windows(F, G, N, int(1.5 * N))
    i = np.arange(1000, 3000, 200)
    say(f"FRW a=t^0.5: W_B/W_A at equal ticks: mean {np.mean(WB[i] / WA[i]):.4f}; rigid rate 1")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
