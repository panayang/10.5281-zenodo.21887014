"""C4: the rigidity threshold (F3: cosmic time is a fact of the order iff decelerating) versus the axis-dependent part
of the count deficit along the comoving axis, in flat FRW a = t^p (comparison family).

Deficit coefficient of tau^2 for an axis u: c(u) = -R/180 + R_uu/30 (C1). Its axis-dependent part is R_uu/30.
Output: calc/out/c4_focusing_rigidity.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c4_focusing_rigidity.txt")
t, x, y, z, p = sp.symbols("t x y z p", positive=True)
X = [t, x, y, z]
a = t ** p
g = sp.diag(-1, a ** 2, a ** 2, a ** 2)
ginv = g.inv()
Gam = [[[sum(ginv[i, d] * (sp.diff(g[d, j], X[k]) + sp.diff(g[d, k], X[j]) - sp.diff(g[j, k], X[d])) for d in range(4)) / 2
         for k in range(4)] for j in range(4)] for i in range(4)]
Ric = sp.zeros(4)
for j in range(4):
    for k in range(4):
        Ric[j, k] = sp.simplify(sum(sp.diff(Gam[i][j][k], X[i]) - sp.diff(Gam[i][j][i], X[k])
                                    + sum(Gam[i][i][d] * Gam[d][j][k] - Gam[i][k][d] * Gam[d][j][i] for d in range(4)) for i in range(4)))
R = sp.simplify(sum(ginv[i, j] * Ric[i, j] for i in range(4) for j in range(4)))
Rtt = sp.simplify(Ric[0, 0])
q = sp.simplify(-sp.diff(a, t, 2) * a / sp.diff(a, t) ** 2)   # deceleration parameter
lines = [f"flat FRW a = t^p:  R_tt (comoving axis) = {sp.factor(Rtt)},  R = {sp.factor(R)},  deceleration q = {sp.factor(q)}",
         f"axis-dependent deficit part along the comoving axis R_tt/30 = {sp.factor(Rtt / 30)}",
         "sign: R_tt > 0  <=>  p < 1  <=>  q > 0 (decelerating)  <=>  rigid (F3);  R_tt = 0 at p = 1 (critical, Milne-like);  R_tt < 0 for p > 1",
         "de Sitter (a = e^{Ht}): R_tt = -3 H^2 < 0 (accelerating, rates hidden)"]
for pv in (sp.Rational(1, 2), sp.Rational(2, 3), 1, 2):
    lines.append(f"  p = {pv}: R_tt = {sp.simplify(Rtt.subs(p, pv))}")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
