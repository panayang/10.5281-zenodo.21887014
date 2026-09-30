"""C9: the pair-rigidity criterion C1' in a concrete inhomogeneous law (Schwarzschild exterior, comparison family).

Tidal components along the separation of two nearby free processes momentarily at rest at radius r (geodesic deviation
xi'' = -K xi, units G = c = 1): radial K = -2M/r^3 (defocusing), tangential K = +M/r^3 (focusing).
Criterion: the pair's rate is an order fact iff the tidal focusing cancels the relative velocity (xi'(inf) = 0) or the pair is bound.
We integrate the Newtonian-limit deviation of two particles released from rest at r0 = 20M falling radially, for radial and
tangential separations, and report xi(t)/xi(0) until r = 4M.
Output: calc/out/c9_schwarzschild_pairs.txt
"""
import os
import numpy as np
from scipy.integrate import solve_ivp

OUT = os.path.join(os.path.dirname(__file__), "out", "c9_schwarzschild_pairs.txt")
M, r0 = 1.0, 20.0


def rhs(t, y):
    r, v, xr, vr, xt, vt = y
    return [v, -M / r ** 2, vr, 2 * M / r ** 3 * xr, vt, -M / r ** 3 * xt]


def hit(t, y):
    return y[0] - 4 * M
hit.terminal = True
sol = solve_ivp(rhs, (0, 1e4), [r0, 0, 1, 0, 1, 0], events=hit, rtol=1e-10, atol=1e-12, dense_output=True)
lines = ["radial infall from rest at r0 = 20M (Newtonian deviation equations, units G = c = M = 1)",
         f"{'r':>8} {'radial xi/xi0':>14} {'tangential xi/xi0':>18}"]
for r in (20, 15, 10, 7, 5, 4):
    ts = sol.t[np.argmin(np.abs(sol.y[0] - r))]
    y = sol.sol(ts)
    lines.append(f"{y[0]:8.2f} {y[2]:14.4f} {y[4]:18.4f}")
lines.append("radial pairs separate (defocusing tides: rates hidden, like F2); tangential pairs converge (focusing: toward rigidity)")
lines.append("a circular-orbit pair at fixed separation is bound (F1). One and the same content gives all three regimes, by direction:")
lines.append("the pair criterion depends on the tidal (Weyl) direction, while the family average (sum of K = R_uu = 0 here) is set by content")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
