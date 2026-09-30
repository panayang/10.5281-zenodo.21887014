"""C6: causal diamond volume in a vacuum plane gravitational wave (comparison family), exact in closed form.

Brinkmann form ds^2 = 2 du dv - a^2 (x^2 - y^2) du^2 + dx^2 + dy^2 (Ricci-flat, Weyl != 0).
World function between (u1, v1, x1, y1) and (u2, v2, x2, y2), du = u2 - u1:
  2 sigma = du [2 dv + S_x + S_y],  S_x = a/sin(a du) [(x1^2 + x2^2) cos(a du) - 2 x1 x2],  S_y = same with sinh, cosh.
Observer x = y = 0 (a geodesic); tips p = 0, q = (U, V, 0, 0) with 2 U V = -tau^2, U = tau e^eta / sqrt 2 (eta = rapidity
of the observer relative to the wave). Diamond: for each u the allowed (x, y, v) region is an ellipse times an interval, giving
  Vol = int_0^U pi V^2 / (2 sqrt(alpha beta)) du,  alpha = a/2 [cot(a u) + cot(a (U - u))],  beta = a/2 [coth(a u) + coth(a (U - u))].
Output: calc/out/c6_planewave_diamond.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c6_planewave_diamond.txt")
a, u, U, V, tau, eta, e = sp.symbols("a u U V tau eta epsilon", positive=True)
w = U - u
z = sp.symbols("z")
cot_s = sp.series(sp.cot(z), z, 0, 8).removeO()        # 1/z - z/3 - z^3/45 - 2 z^5/945
coth_s = sp.series(sp.coth(z), z, 0, 8).removeO()
s0 = U / (2 * u * w)                                    # flat value of alpha and beta (from the 1/z poles)
Pc, Ph = sp.expand(cot_s - 1 / z), sp.expand(coth_s - 1 / z)   # regular parts: polynomials in z
alpha = s0 + sp.expand(a / 2 * (Pc.subs(z, a * u) + Pc.subs(z, a * w)))
beta = s0 + sp.expand(a / 2 * (Ph.subs(z, a * u) + Ph.subs(z, a * w)))
delta = sp.expand(alpha * beta - s0 ** 2)
delta = sum(delta.coeff(a, k) * a ** k for k in range(0, 7))   # keep through a^6
# 1/sqrt(s0^2 + delta) = (1/s0) (1 - delta/(2 s0^2) + 3 delta^2/(8 s0^4) ...)
inv = (1 / s0) * (1 - delta / (2 * s0 ** 2) + 3 * delta ** 2 / (8 * s0 ** 4))
inv = sp.expand(inv)
inv = sum(sp.simplify(inv.coeff(a, k)) * a ** k for k in range(0, 5))
ser = sp.pi * V ** 2 / 2 * inv
vol = sp.simplify(sp.integrate(ser, (u, 0, U)))
V0 = sp.pi * V ** 2 * U ** 2 / 6
rel = sp.simplify(sp.expand(vol / V0 - 1))
lines = [f"Vol / Vol_flat - 1 = {sp.factor(rel)}   (in terms of U, the u-extent of the diamond)"]
rel_tau = sp.simplify(rel.subs(U, tau * sp.exp(eta) / sp.sqrt(2)))
lines.append(f"with U = tau e^eta / sqrt 2:  Vol / Vol_flat - 1 = {sp.factor(rel_tau)}")
lines.append("order a^2 vanishes (Ricci-flat); the leading term is order a^4 tau^4 e^{4 eta}: positive, and it depends on the axis")
lines.append("(the observer's rapidity relative to the wave) -- read at finite tau it is an apparent, direction-dependent content")
lines.append("growing like tau^2 relative to the tau^2 coefficient: content runs with the interval size")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
