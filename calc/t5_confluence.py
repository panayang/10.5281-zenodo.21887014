"""T5: the two ways gluing fails, in flat FRW.

(1) Rigidity (F3): W(t)/t -> 0, with W the synchronisation window of a comoving pair.
    Claim: W(t) = 2 chi a(t) (1 + o(1)) for small chi, so rigidity <=> a(t)/t -> 0.
(2) Confluence (.2 of S4.2): any two events have a common causal future.
    In conformal coordinates the causal order is Minkowski's on {eta < eta_max}; the earliest common
    future of u, v is at eta = (eta_u + eta_v + |x_u - x_v|)/2, so .2 <=> eta_max = +inf
    <=> no event horizon <=> integral^inf dt/a diverges.
(3) Nesting: a = o(t) => 1/a >= c/t eventually => the integral diverges: rigid => confluent.
Numerical checks of (1) and explicit .2 counterexamples when eta_max < inf.
Output: calc/out/t5_confluence.txt
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from twochain import frw_comoving

OUT = os.path.join(os.path.dirname(__file__), "out", "t5_confluence.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def window(F, t):
    lo, hi = 0.0, t
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        lo, hi = (mid, hi) if F(mid) < t else (lo, mid)
    return F(t) - lo


def eta_max(p):
    return math.inf if p <= 1 else 0.0  # a = t^p: eta = t^(1-p)/(1-p), log t, or -t^(1-p)/(p-1)


def conf(p, t):
    if p == 1:
        return math.log(t)
    return t ** (1 - p) / (1 - p) if p < 1 else -t ** (1 - p) / (p - 1)


if __name__ == "__main__":
    say("(1) window of a comoving pair vs 2 chi a(t), chi = 0.05, T0 = 10 (tau = t - T0)")
    for p in (0.5, 2 / 3, 1.0, 1.2):
        F, _ = frw_comoving(p, 0.05, 10.0)
        row = []
        for t in (100.0, 1000.0, 10000.0):
            try:
                w = window(F, t - 10.0)
            except OverflowError:
                w = math.inf
            row.append(f"t={t:.0f}: W={w:.3f} vs {2 * 0.05 * t ** p:.3f}, W/t={w / t:.4f}")
        say(f"p={p:.3f}  " + " | ".join(row))

    say("\n(2) confluence: an explicit pair with no common future exists iff eta_max < inf")
    for p in (0.5, 1.0, 1.5, 2.0):
        em = eta_max(p)
        if em == math.inf:
            say(f"p={p}: eta_max = inf -> every pair has a common future (.2 holds)")
            continue
        w_eta = conf(p, 1.0)            # w at t = 1, x = 0
        eps = 1e-3 * (em - w_eta)
        eu = ev = em - eps
        xu, xv = -(eu - w_eta) * 0.999, (ev - w_eta) * 0.999   # both in the future of w
        need = 0.5 * (eu + ev + abs(xu - xv))
        say(f"p={p}: eta_max = {em}, w at eta={w_eta:.3f}; u, v at eta={eu:.4f}, x={xu:.3f},{xv:.3f}; "
            f"earliest common future at eta={need:.4f} {'>= eta_max: no common future (.2 fails)' if need >= em else '(exists)'}")

    say("\n(3) nesting on power laws: rigid (p<1) => confluent (p<=1); Milne p=1 confluent, not rigid;"
        " p>1 neither")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
