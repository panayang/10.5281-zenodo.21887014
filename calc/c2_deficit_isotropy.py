"""C2: does the count deficit of small intervals depend on the direction of the interval's axis, outside a static source?

Deficit of a small interval with axis u (C1): V/V0 - 1 = -tau^2 (R/180 - R_uu/30).
Comparison metrics (weak field, first order in M, point at r = (x, y, z) = (3, 0, 0)):
  (i)  mu-only (conformally flat, the order of flat space kept):   g = (1 - 2M/r) eta              ("Nordstrom-type")
  (ii) order deformed (linearized Schwarzschild, isotropic form):  g = diag(-(1 - 2M/r), (1 + 2M/r) I)
  (iii) order deformed with a general gamma:                        g = diag(-(1 - 2M/r), (1 + 2 gamma M/r) I)
For each, the tau^2 coefficient of the deficit for a static axis and for boosted axes (v = 0.5 radial / tangential).
Output: calc/out/c2_deficit_isotropy.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c2_deficit_isotropy.txt")
t, x, y, z, M, gam = sp.symbols("t x y z M gamma", real=True)
X = [t, x, y, z]
r = sp.sqrt(x ** 2 + y ** 2 + z ** 2)
lines = []


def ricci(g):
    ginv = g.inv()
    n = 4
    Gam = [[[sum(ginv[a, d] * (sp.diff(g[d, b], X[c]) + sp.diff(g[d, c], X[b]) - sp.diff(g[b, c], X[d])) for d in range(n)) / 2
             for c in range(n)] for b in range(n)] for a in range(n)]
    Ric = sp.zeros(n)
    for b in range(n):
        for c in range(n):
            Ric[b, c] = sum(sp.diff(Gam[a][b][c], X[a]) - sp.diff(Gam[a][b][a], X[c])
                            + sum(Gam[a][a][d] * Gam[d][b][c] - Gam[a][c][d] * Gam[d][b][a] for d in range(n)) for a in range(n))
    return Ric, ginv


def first_order(e):
    return sp.series(e, M, 0, 2).removeO()


pt = {x: 3, y: 0, z: 0}
eta = sp.diag(-1, 1, 1, 1)
metrics = {"(i) mu only (conformally flat)": (1 - 2 * M / r) * eta,
           "(ii) linearized Schwarzschild": sp.diag(-(1 - 2 * M / r), 1 + 2 * M / r, 1 + 2 * M / r, 1 + 2 * M / r),
           "(iii) general gamma": sp.diag(-(1 - 2 * M / r), 1 + 2 * gam * M / r, 1 + 2 * gam * M / r, 1 + 2 * gam * M / r)}
v = sp.Rational(1, 2)
g_ = 1 / sp.sqrt(1 - v ** 2)
axes = {"static": [1, 0, 0, 0], "radial v=1/2": [g_, g_ * v, 0, 0], "tangential v=1/2": [g_, 0, g_ * v, 0]}
for name, g in metrics.items():
    Ric, ginv = ricci(g)
    Ric0 = Ric.subs(pt)
    R = first_order(sp.simplify(sum(ginv[a, b] * Ric[a, b] for a in range(4) for b in range(4)).subs(pt)))
    lines.append(f"{name}:  R = {sp.simplify(R)}")
    for an, u in axes.items():
        # to first order in M the flat-normalised u is enough (normalisation corrections are second order in M times Ric)
        Ruu = first_order(sp.simplify(sum(Ric0[a, b] * u[a] * u[b] for a in range(4) for b in range(4))))
        coeff = sp.simplify(-(R / 180 - Ruu / 30))
        lines.append(f"    axis {an:18s}: R_uu = {sp.simplify(Ruu)},  deficit coefficient of tau^2 = {coeff}")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
