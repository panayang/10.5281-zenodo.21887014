"""C1: small causal diamond volumes in 3+1 (comparison geometry, not a premise).

Fix the coefficients in V(tau) = (pi tau^4 / 24) [1 + tau^2 (a R + b R_ab u^a u^b) + O(tau^4)] (signature -+++),
using two metrics with known curvature along a comoving/static worldline:
  de Sitter (flat slicing, a = e^{Ht}):  R = 12 H^2,  R_uu = -3 H^2
  Einstein static universe (radius A):   R = 6 / A^2, R_uu = 0
Then ask: for which Ricci tensors does the correction vanish for every timelike u?
Output: calc/out/c1_diamond_volume.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c1_diamond_volume.txt")
t, T, H, A, x = sp.symbols("t tau H A x", positive=True)
lines = []
V0 = sp.pi * T ** 4 / 24

# de Sitter: future cone of p = (-T/2, 0) and past cone of q = (T/2, 0) in comoving radius
rp = (sp.exp(H * T / 2) - sp.exp(-H * t)) / H
rq = (sp.exp(-H * t) - sp.exp(-H * T / 2)) / H
ts = -sp.log(sp.cosh(H * T / 2)) / H            # equal radii here, not at t = 0
w = lambda r: sp.exp(3 * H * t) * sp.Rational(4, 3) * sp.pi * r ** 3
ser = lambda f: sp.series(f, H, 0, 3).removeO()
V_ds = sp.integrate(ser(w(rp)), (t, -T / 2, ts)) + sp.integrate(ser(w(rq)), (t, ts, T / 2))
V_ds = sp.series(sp.simplify(V_ds), H, 0, 3).removeO()
c_ds = sp.simplify(sp.expand(V_ds / V0 - 1))
lines.append(f"de Sitter: V/V0 - 1 = {c_ds}  (to order H^2)")

# Einstein static universe: chi_max = (T/2 - |t|)/A ; geodesic ball volume 4 pi A^3 (chi/2 - sin(2 chi)/4)
chi = (T / 2 - t) / A
ball = 4 * sp.pi * A ** 3 * (chi / 2 - sp.sin(2 * chi) / 4)
V_esu = 2 * sp.integrate(sp.series(ball, A, sp.oo, 8).removeO(), (t, 0, T / 2))
c_esu = sp.expand(V_esu / V0 - 1)
c_esu = sp.simplify(c_esu.coeff(T, 2) * T ** 2)
lines.append(f"Einstein static: V/V0 - 1 = {c_esu}  (leading order)")

a, b = sp.symbols("a b")
sol = sp.solve([sp.Eq(T ** 2 * (a * 12 * H ** 2 + b * (-3 * H ** 2)), c_ds), sp.Eq(T ** 2 * (a * 6 / A ** 2), c_esu)], [a, b])
lines.append(f"coefficients: V = V0 [1 + tau^2 ({sol[a]} R + {sol[b]} R_uu)]")
ratio = sp.simplify(sol[a] / sol[b])
lines.append(f"a/b = {ratio}; an Einstein space R_ab = L g_ab passes 'no correction for every u' only if a/b = 1/4")
lines.append("so: correction = 0 for every timelike u  <=>  R_ab u^a u^b = -(a/b) R for all unit u  <=>  R_ab = 0")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
