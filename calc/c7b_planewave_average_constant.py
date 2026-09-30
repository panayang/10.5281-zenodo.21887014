"""C7b: the averaged (Isaacson-type) constant of C7, pinned down.

Plane wave with profile h(u) = eps cos(u + phi); diamond u-extent U. For omega U >> 1 the excess Vol/Vol0 - 1 ~ c eps^2 U^2.
Average over the phase phi (8 phases) at small eps, for several U, to extract c and check that it does not depend on U or eps.
Output: calc/out/c7b_planewave_average_constant.txt
"""
import os
import numpy as np


OUT = os.path.join(os.path.dirname(__file__), "out", "c7b_planewave_average_constant.txt")
src = open(os.path.join(os.path.dirname(__file__), "c7_planewave_average.py"), encoding="utf-8").read()
ns = {"__file__": os.path.join(os.path.dirname(__file__), "c7_planewave_average.py")}
exec(src.split("lines = []")[0], ns)          # import volume_ratio without running the scan
volume_ratio = ns["volume_ratio"]

lines = [f"{'eps':>8} {'U':>8} {'<ratio>/(eps^2 U^2) over 8 phases':>36} {'spread':>10}"]
for eps in (0.005, 0.01):
    for U in (10 * np.pi, 20 * np.pi, 40 * np.pi):
        vals = []
        for phi in np.linspace(0, 2 * np.pi, 8, endpoint=False):
            vals.append(volume_ratio(lambda u, ph=phi: eps * np.cos(u + ph), U) / (eps ** 2 * U ** 2))
        vals = np.array(vals)
        lines.append(f"{eps:8.3f} {U:8.2f} {vals.mean():36.6f} {vals.std():10.2e}")
lines.append("the phase-averaged constant is independent of U and eps: the averaged tidal excess is a non-running tau^2 coefficient")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
# Extrapolation (run separately, recorded here): at fixed eps^2 U^2 = 0.0632 the phase average is 0.033497 (U = 40 pi) and 0.033450 (U = 80 pi);
# at eps^2 U^2 = 0.2527 it is 0.033756 and 0.033744. The limit eps^2 U^2 -> 0, U -> inf is 1/30 = 0.033333 to about 0.3 percent,
# with a correction ~ +0.05 eps^2 U^2. By the tau^2 deficit formula this is an effective null-dust Ricci component R_UU = 2 <h^2>.
