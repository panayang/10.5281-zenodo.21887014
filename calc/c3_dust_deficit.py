"""C3: the count deficit inside content, in the comparison family (linearized Einstein equation with dust).

delta(u) leading coefficient = -(R/180 - R_uu/30) tau^2, with R_ab = 8 pi G (T_ab - T g_ab / 2), T_ab = rho w_a w_b (dust with 4-velocity w).
gamma_rel = -u.w is the relative Lorentz factor between the interval's axis u and the content process w (readable from counts).
Output: calc/out/c3_dust_deficit.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "c3_dust_deficit.txt")
G, rho, g = sp.symbols("G rho gamma", positive=True)
# mostly plus: T = -rho ; R_ab u^a u^b = 8 pi G (rho g^2 - (-rho)(-1)/2) = 8 pi G rho (g^2 - 1/2); R = -8 pi G T = 8 pi G rho
Ruu = 8 * sp.pi * G * rho * (g ** 2 - sp.Rational(1, 2))
R = 8 * sp.pi * G * rho
coef = sp.simplify(-(R / 180 - Ruu / 30))
lines = [f"deficit coefficient of tau^2 for an axis with relative Lorentz factor gamma to the dust: {sp.factor(coef)}",
         f"  static axis (gamma = 1): {sp.simplify(coef.subs(g, 1))}   (> 0: more records than the chain baseline)",
         "  it grows like gamma^2: the content's contribution depends on the axis through (u.w)^2 -- a two-index source, not a count",
         "  a scalar source (the number of content records, Lorentz invariant) would give an axis-independent (isotropic, Lambda-like) deficit",
         "  the ratio of the gamma^2 term to the constant term is fixed by conservation of content plus integrability (contracted Bianchi identity)"]
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
