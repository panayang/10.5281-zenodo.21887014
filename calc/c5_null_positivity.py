"""C5: within the one-parameter comparison family g = diag(-(1 - 2M/r), (1 + 2 gamma M/r) I) (first order in M),
outside the source: the gamma_rel^2 coefficient of R_uu as the axis becomes nearly null (R_kk for null k), for radial and
tangential null directions. 'Counted content never defocuses nearly null free processes' requires R_kk >= 0 for all k.
Output: calc/out/c5_null_positivity.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c5_null_positivity.txt")
t, x, y, z, M, gp = sp.symbols("t x y z M gamma_ppn", real=True)
X = [t, x, y, z]
r = sp.sqrt(x ** 2 + y ** 2 + z ** 2)
g = sp.diag(-(1 - 2 * M / r), 1 + 2 * gp * M / r, 1 + 2 * gp * M / r, 1 + 2 * gp * M / r)
ginv = g.inv()
Gam = [[[sum(ginv[a, d] * (sp.diff(g[d, b], X[c]) + sp.diff(g[d, c], X[b]) - sp.diff(g[b, c], X[d])) for d in range(4)) / 2
         for c in range(4)] for b in range(4)] for a in range(4)]
Ric = sp.zeros(4)
for b in range(4):
    for c in range(4):
        Ric[b, c] = sum(sp.diff(Gam[a][b][c], X[a]) - sp.diff(Gam[a][b][a], X[c])
                        + sum(Gam[a][a][d] * Gam[d][b][c] - Gam[a][c][d] * Gam[d][b][a] for d in range(4)) for a in range(4))
pt = {x: 3, y: 0, z: 0}
R0 = Ric.subs(pt)
lines = ["outside the source, point r = 3, first order in M:"]
for name, k in [("radial null k = (1, 1, 0, 0)", [1, 1, 0, 0]), ("tangential null k = (1, 0, 1, 0)", [1, 0, 1, 0])]:
    Rkk = sp.series(sp.simplify(sum(R0[a, b] * k[a] * k[b] for a in range(4) for b in range(4))), M, 0, 2).removeO()
    lines.append(f"  {name}: R_kk = {sp.factor(sp.simplify(Rkk))}")
lines.append("R_kk >= 0 in both directions (M > 0) only for gamma_ppn = 1, where both vanish; any gamma != 1 defocuses one direction")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
