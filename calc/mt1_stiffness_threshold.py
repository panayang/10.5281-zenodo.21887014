"""MT1: which kinds of content can form stable bound individuals? Virial scaling (comparison family, Newtonian limit).

A self-bound body of fixed content amount and size R in d >= 3 spatial dimensions: internal energy A R^{-m}, m = d(Gamma - 1)
(adiabatic index Gamma); gravitational energy -B R^{-n}, n = d - 2 (potential ~ 1/r^{d-2}).
E'' = R^{-2} [A m(m+1) R^{-m} - B n(n+1) R^{-n}]; at equilibrium A m R^{-m} = B n R^{-n}, so E'' = B n R^{-n-2} (m - n).
Stable iff m > n.
Output: calc/out/mt1_stiffness_threshold.txt
"""
import os
import sympy as sp

OUT = os.path.join(os.path.dirname(__file__), "out", "mt1_stiffness_threshold.txt")
R, A, B, m, n = sp.symbols("R A B m n", positive=True)
E = A * R ** (-m) - B * R ** (-n)
E2 = sp.diff(E, R, 2)
Aeq = sp.solve(sp.Eq(sp.diff(E, R), 0), A)[0]
check = sp.simplify(E2.subs(A, Aeq) - B * n * R ** (-n - 2) * (m - n))
lines = [f"check of E'' = B n R^(-n-2) (m - n) at equilibrium: residual {check}",
         "stable iff d (Gamma - 1) > d - 2, i.e. Gamma > 2 - 2/d"]
for dd in (3, 4, 5):
    lines.append(f"  d = {dd}: Gamma > {sp.Rational(2) - sp.Rational(2, dd)}")
lines.append("d = 3: radiation-like content (Gamma = 4/3) is exactly marginal; relativistic corrections raise the threshold")
lines.append("(Chandrasekhar: Gamma > 4/3 + O(GM/Rc^2)), so no stable individual is arbitrarily compact")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
