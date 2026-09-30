"""T2: for receding inertial observers the undetermined rate is a frame rapidity.

(a) Exact: the simultaneity slices of the inertial frame with rapidity phi (relative to A) advance
    B's proper time against A's at the rate s(phi) = cosh(phi) / cosh(eta - phi). This is a strictly
    increasing bijection R -> (e^-eta, e^eta), since ds/dphi = sinh(eta) / cosh^2(eta - phi).
(b) Numerical: the extreme rates of the uniform order-invariant measure approach e^-eta and e^eta,
    with an N^(-1/2) boundary layer; extrapolated here.
(c) Numerical: conditioning on the slice of frame phi reproduces s(phi) in the middle.
Output: calc/out/t2_rapidity.txt
"""
import math
import os
import sys
import numpy as np
import sympy as sp

sys.path.insert(0, os.path.dirname(__file__))
from twochain import TwoChain, unit_ticks, receding

OUT = os.path.join(os.path.dirname(__file__), "out", "t2_rapidity.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def frame_rate(phi, eta):
    return math.cosh(phi) / math.cosh(eta - phi)


if __name__ == "__main__":
    # (a) symbolic check of the frame map
    ph, et = sp.symbols("phi eta", real=True)
    s = sp.cosh(ph) / sp.cosh(et - ph)
    ds = sp.simplify(sp.diff(s, ph) - sp.sinh(et) / sp.cosh(et - ph) ** 2)
    lim_lo = sp.limit(s, ph, -sp.oo)
    lim_hi = sp.limit(s, ph, sp.oo)
    say("(a) frame map s(phi) = cosh(phi)/cosh(eta-phi)")
    say(f"    ds/dphi - sinh(eta)/cosh^2(eta-phi) simplifies to: {ds}")
    say(f"    limits: phi -> -oo: {sp.simplify(lim_lo)},  phi -> +oo: {sp.simplify(lim_hi)}")
    # Also: each frame's slicing is itself a linear extension; check it respects the order.
    # A frame slice t' = const is spacelike, so it never separates a cause from its effect: automatic.

    # (b) extremes and their extrapolation
    say("\n(b) extreme middle rates of the uniform order-invariant measure, fit a + b N^-1/2")
    Ns = [500, 1000, 2000, 4000, 8000]
    for eta in (0.25, 0.5, 1.0):
        lo_r, hi_r = [], []
        for N in Ns:
            tc = TwoChain(*receding(eta), unit_ticks(N), unit_ticks(int(math.exp(eta) * N * 1.2) + 50))
            a, b = tc.extremes()
            lo_r.append(a)
            hi_r.append(b)
        X = np.column_stack([np.ones(len(Ns)), np.array(Ns, float) ** -0.5])
        clo = np.linalg.lstsq(X[1:], np.array(lo_r[1:]), rcond=None)[0]
        chi = np.linalg.lstsq(X[1:], np.array(hi_r[1:]), rcond=None)[0]
        say(f"eta={eta}: lower {['%.4f' % v for v in lo_r]} -> {clo[0]:.4f}  (e^-eta = {math.exp(-eta):.4f})")
        say(f"         upper {['%.4f' % v for v in hi_r]} -> {chi[0]:.4f}  (e^eta  = {math.exp(eta):.4f})")

    # (c) conditioning on a frame's slice gives that frame's rate in the middle
    say("\n(c) end on the slice of frame phi; middle rate vs s(phi)   [eta = 0.5, N = 4000]")
    eta, N = 0.5, 4000
    tc = TwoChain(*receding(eta), unit_ticks(N), unit_ticks(int(math.exp(eta) * N * 1.2) + 50))
    f = tc.forward(N // 2)
    for phi in (-1.5, -0.5, 0.0, 0.25, 0.5, 1.0, 2.0):
        r = frame_rate(phi, eta)
        say(f"phi={phi:+.2f}: s(phi)={r:.4f}  middle={tc.middle_rate(tc.endpoint_for_rate(r), N // 2, f):.4f}")

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
