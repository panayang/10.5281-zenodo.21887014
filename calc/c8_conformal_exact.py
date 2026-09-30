"""C8: exact (nonlinear) null focusing for any static, spherically symmetric, measure-only law g = e^{2 phi(r)} eta.
Tangential null direction k = (1, 0, 1, 0) at the point (x, y, z) = (r0, 0, 0): R_kk should equal -2 phi'(r0)/r0 exactly.
Output: calc/out/c8_conformal_exact.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c8_conformal_exact.txt")
t, x, y, z = sp.symbols("t x y z", real=True)
X = [t, x, y, z]
phi = sp.Function("phi")
r = sp.sqrt(x ** 2 + y ** 2 + z ** 2)
g = sp.exp(2 * phi(r)) * sp.diag(-1, 1, 1, 1)
ginv = g.inv()
Gam = [[[sum(ginv[a, d] * (sp.diff(g[d, b], X[c]) + sp.diff(g[d, c], X[b]) - sp.diff(g[b, c], X[d])) for d in range(4)) / 2
         for c in range(4)] for b in range(4)] for a in range(4)]
k = [1, 0, 1, 0]
Rkk = 0
for b in range(4):
    for c in range(4):
        if k[b] * k[c] == 0:
            continue
        Rbc = sum(sp.diff(Gam[a][b][c], X[a]) - sp.diff(Gam[a][b][a], X[c])
                  + sum(Gam[a][a][d] * Gam[d][b][c] - Gam[a][c][d] * Gam[d][b][a] for d in range(4)) for a in range(4))
        Rkk += k[b] * k[c] * Rbc
r0 = sp.symbols("r0", positive=True)
val = sp.simplify(Rkk.subs({x: r0, y: 0, z: 0}).doit())
lines = [f"R_kk (tangential null, exact) = {val}",
         "i.e. -2 phi'(r0)/r0: negative wherever phi' > 0, which is exactly where free processes fall inward (clocks slower inside)"]
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
