"""C7: diamond volume in a vacuum plane wave with an oscillating profile h(u) = eps cos(omega u) (comparison family).

ds^2 = 2 du dv - h(u)(x^2 - y^2) du^2 + dx^2 + dy^2. For an observer at x = y = 0 with tips at u = 0 and u = U:
  alpha(u) = (1/2) [J1'(u)/J1(u) + J2'(U-u)... ]  where J solves the Jacobi equation J'' = -h J (x) or J'' = +h J (y),
  J1 from the lower tip forward (J1(0) = 0, J1'(0) = 1), J2 from the upper tip backward; S_x(u) = x^2 (J1'/J1 + K1) etc.
  Vol = int_0^U pi V^2 / (2 sqrt(alpha beta)) du,  flat Vol0 = pi V^2 U^2 / 6.
Constant h = a^2 reproduces C6 (a^4 U^4 / 252). Question: for omega U >> 1 does Vol/Vol0 - 1 grow like U^2 (a tau^2 coefficient that
no longer runs, i.e. an effective content quadratic in the axis) instead of U^4?
Output: calc/out/c7_planewave_average.txt
"""
import os
import numpy as np
from scipy.integrate import solve_ivp, quad

OUT = os.path.join(os.path.dirname(__file__), "out", "c7_planewave_average.txt")


def jacobi_ratio(hfun, sign, U, forward, n=4001):
    """returns a function u -> J'(s)/J(s) along the direction away from the starting tip, s = distance from the tip."""
    def rhs(s, y):
        uu = s if forward else U - s
        return [y[1], -sign * hfun(uu) * y[0]]
    ss = np.linspace(0, U, n)
    sol = solve_ivp(rhs, (0, U), [0.0, 1.0], t_eval=ss, rtol=1e-12, atol=1e-14, dense_output=True)
    return sol.sol


def volume_ratio(hfun, U):
    fx_f, fx_b = jacobi_ratio(hfun, +1, U, True), jacobi_ratio(hfun, +1, U, False)
    fy_f, fy_b = jacobi_ratio(hfun, -1, U, True), jacobi_ratio(hfun, -1, U, False)
    def integrand(u):
        s1, s2 = u, U - u
        a1, b1 = fx_f(s1), fx_b(s2)
        c1, d1 = fy_f(s1), fy_b(s2)
        alpha = 0.5 * (a1[1] / a1[0] + b1[1] / b1[0])
        beta = 0.5 * (c1[1] / c1[0] + d1[1] / d1[0])
        return 1.0 / np.sqrt(alpha * beta)
    eps = 1e-9 * U
    val = quad(integrand, eps, U - eps, limit=400, epsabs=0, epsrel=1e-11)[0]
    flat = U ** 2 / 3.0
    return val / flat - 1.0


lines = []
a2 = 0.01
r = volume_ratio(lambda u: a2, 2.0)
lines.append(f"check, constant h = a^2 = {a2}, U = 2: numerical {r:.6e}   closed form a^4 U^4 / 252 = {a2 ** 2 * 16 / 252:.6e}")
eps, om = 0.02, 1.0
lines.append(f"oscillating h = {eps} cos(u):  U,  Vol/Vol0 - 1,  divided by eps^2 U^2,  divided by eps^2 U^4")
for U in (0.25, 0.5, 1.0, 2.0, 5.0, 10.0, 20.0, 40.0, 80.0):
    r = volume_ratio(lambda u: eps * np.cos(om * u), U)
    lines.append(f"  U = {U:6.2f}   {r: .4e}   {r / (eps ** 2 * U ** 2): .4e}   {r / (eps ** 2 * U ** 4): .4e}")
lines.append("for omega U << 1 the ratio / U^4 is constant (local tidal, quartic in the axis); for omega U >> 1 the ratio / U^2 tends to a constant:")
lines.append("an averaged, non-running tau^2 coefficient scaling like U^2 ~ e^{2 eta} -- quadratic in the axis, like content (Isaacson-type effective content)")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
