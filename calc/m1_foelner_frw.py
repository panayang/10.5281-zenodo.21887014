"""M1: two individuation-free exhaustion conditions for frequency questions (anchor 1, docs/anchor-measure.md).

An observer's worlds are its causal pasts P(t) (no slicing is chosen). Weight = spacetime 4-volume (the test-family stand-in
for "number of records"). Two conditions, computed in the FRW test family (3+1, a comparison arena, not a premise):
  (A) between observers: S_AB = vol(P1 symmetric-difference P2) / vol(P1) for two comoving observers at comoving distance d,
      compared at the same proper time. S_AB -> 0 means both observers' exhaustions give the same frequencies for any
      bounded inhomogeneity (a Folner-type condition between observers).
  (B) along one observer: S_t = [vol P(t) - vol P(t - dt)] / vol P(t) for a fixed proper-time step dt (youngness).
Cases: flat a = t^p for p = 0.5, 0.8, 1, 1.5; de Sitter a = e^t (flat slicing); Milne (open, hyperbolic slices, a = t).
Output: calc/out/m1_foelner_frw.txt
"""
import os
import numpy as np
from scipy.integrate import quad, dblquad

OUT = os.path.join(os.path.dirname(__file__), "out", "m1_foelner_frw.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def ball_flat(R):
    return 4 * np.pi / 3 * R ** 3


def inter_flat(R, d):
    return 0.0 if d >= 2 * R else np.pi * (4 * R + d) * (2 * R - d) ** 2 / 12


def ball_hyp(R):
    return np.pi * (np.sinh(2 * R) - 2 * R)


def inter_hyp(R, d):
    if d >= 2 * R:
        return 0.0
    # points within R of centre 1 and within R of centre 2 (distance d apart), H^3 with curvature -1
    def inner(r):
        # cos(theta) threshold: cosh r2 <= cosh R  <=>  cos(theta) >= (cosh r cosh d - cosh R) / (sinh r sinh d)
        if r == 0:
            return 0.0
        c = (np.cosh(r) * np.cosh(d) - np.cosh(R)) / (np.sinh(r) * np.sinh(d))
        c = min(max(c, -1.0), 1.0)
        return 2 * np.pi * np.sinh(r) ** 2 * (1 - c)
    return quad(inner, 0, R, limit=200)[0]


class FRW:
    """a(eta) in conformal time; observers at the same conformal time eta_obs (same proper time by symmetry)."""
    def __init__(self, name, a_of_eta, eta_min, eta_of_t, hyper=False, t_of_eta=None, eta_max=np.inf):
        self.name, self.a, self.eta_min, self.eta_of_t, self.hyper = name, a_of_eta, eta_min, eta_of_t, hyper
        self.t_of_eta, self.eta_max = t_of_eta, eta_max

    def rho(self, t, d):
        """window / elapsed: round trip to a comoving partner at distance d, W = t(eta + 2d) - t, divided by t"""
        e2 = self.eta_of_t(t) + 2 * d
        return np.inf if e2 >= self.eta_max else (self.t_of_eta(e2) - t) / t

    def _integral(self, eo, f):
        """integrate (a(e)/a(eo))^4 f(eo - e) over e in (eta_min, eo), in the lookback R = eo - e on a log scale."""
        a0 = self.a(eo)
        Rmax = eo - self.eta_min
        g = lambda s: (self.a(eo - np.exp(s)) / a0) ** 4 * f(np.exp(s)) * np.exp(s)
        lo, hi = np.log(Rmax) - 60, np.log(Rmax)
        pts = np.linspace(lo, hi, 61)
        return sum(quad(g, x0, x1, limit=200)[0] for x0, x1 in zip(pts[:-1], pts[1:]))

    def vols(self, t, d):
        eo = self.eta_of_t(t)
        ball = ball_hyp if self.hyper else ball_flat
        inter = inter_hyp if self.hyper else inter_flat
        V = self._integral(eo, ball)
        I = self._integral(eo, lambda R: inter(R, d))
        return V, 2 * (V - I)

    def vol_ratio(self, t, dt):
        """vol P(t - dt) / vol P(t), both normalised by a(eta(t))^4"""
        eo, em = self.eta_of_t(t), self.eta_of_t(t - dt)
        ball = ball_hyp if self.hyper else ball_flat
        V = self._integral(eo, ball)
        Vm = self._integral(em, ball) * (self.a(em) / self.a(eo)) ** 4
        return Vm / V


def power(p):
    # a = t^p; eta = t^(1-p)/(1-p) for p != 1 (p > 1: eta in (-inf, 0)); p = 1 flat coasting: eta = log t
    if p == 1:
        return FRW("flat a=t (coasting)", lambda e: np.exp(e), -40.0, np.log, t_of_eta=np.exp)
    if p < 1:
        return FRW(f"flat a=t^{p}", lambda e: ((1 - p) * e) ** (p / (1 - p)), 0.0, lambda t: t ** (1 - p) / (1 - p),
                   t_of_eta=lambda e: ((1 - p) * e) ** (1 / (1 - p)))
    return FRW(f"flat a=t^{p}", lambda e: ((1 - p) * e) ** (p / (1 - p)), -1e6, lambda t: t ** (1 - p) / (1 - p),
               t_of_eta=lambda e: ((1 - p) * e) ** (1 / (1 - p)), eta_max=0.0)


cases = [power(0.5), power(0.8), power(1), power(1.5),
         FRW("de Sitter a=e^t (flat)", lambda e: -1.0 / e, -1e6, lambda t: -np.exp(-t), t_of_eta=lambda e: -np.log(-e), eta_max=0.0),
         FRW("Milne (open, a=t)", lambda e: np.exp(e), -40.0, np.log, hyper=True, t_of_eta=np.exp)]
d, dt = 1.0, 1.0
say(f"comoving separation d = {d}; proper-time step dt = {dt}; weights = 4-volume")
say(f"{'case':26s} {'t':>8s} {'S_AB (between observers)':>26s} {'rho = W/P':>10s} {'S_t (youngness)':>18s}")
for c in cases:
    for t in ((10.0, 100.0, 1000.0, 10000.0) if 'Sitter' not in c.name else (5.0, 10.0, 20.0, 40.0)):
        try:
            V, D = c.vols(t, d)
            say(f"{c.name:26s} {t:8.0f} {D / V:26.4f} {c.rho(t, d):10.4f} {1 - c.vol_ratio(t, dt):18.4f}")
        except Exception as ex:
            say(f"{c.name:26s} {t:8.0f} failed: {ex}")
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
