"""L2b: the rigidity map from order data alone.

Sprinkle a Poisson sample (unit density in proper volume) into the causal diamond of each of two
geodesic observers; take the longest chain in each diamond as that observer's worldline (longest
chains approximate geodesics, and their length is proportional to proper time); read every
relation between the two chains off the sprinkled order; use the position along each chain as its
clock. No metric information enters after the sprinkling.

In 1+1 the causal order is the dominance order in light-cone coordinates (u, v) = (eta - x, eta + x)
with eta the conformal time, so a longest chain is a longest increasing subsequence.
Output: calc/out/l2b_intrinsic.txt
"""
import bisect
import math
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
from twochain import TwoChain

OUT = os.path.join(os.path.dirname(__file__), "out", "l2b_intrinsic.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def longest_chain(u, v):
    """Indices of a longest chain in the dominance order (u, v both non-decreasing)."""
    order = np.lexsort((v, u))
    vs = v[order]
    tails, tails_idx, prev = [], [], np.full(len(vs), -1)
    for k, val in enumerate(vs):
        pos = bisect.bisect_right(tails, val)
        if pos == len(tails):
            tails.append(val)
            tails_idx.append(k)
        else:
            tails[pos] = val
            tails_idx[pos] = k
        prev[k] = tails_idx[pos - 1] if pos > 0 else -1
    k = tails_idx[-1]
    chain = []
    while k != -1:
        chain.append(order[k])
        k = prev[k]
    return np.array(chain[::-1])


def sprinkle_diamond(conf, inv_conf, a, t0, t1, xc, rng, rate_scale):
    """Poisson points (proper-volume density rate_scale) in the diamond between (t0, xc) and (t1, xc),
    for ds^2 = -dt^2 + a(t)^2 dx^2 with comoving x and conformal time conf(t)."""
    e0, e1 = conf(t0), conf(t1)
    tg = np.linspace(t0, t1, 200001)
    eg = conf(tg)
    half = np.minimum(eg - e0, e1 - eg)          # half-width of the diamond in comoving x
    dens = a(tg) * 2 * half * rate_scale          # proper volume per unit t: a(t) dt dx
    cdf = np.concatenate([[0.0], np.cumsum(0.5 * (dens[1:] + dens[:-1]) * np.diff(tg))])
    n = rng.poisson(cdf[-1])
    t = np.interp(rng.random(n) * cdf[-1], cdf, tg)
    e = conf(t)
    h = np.minimum(e - e0, e1 - e)
    x = xc + (2 * rng.random(n) - 1) * h
    print(f"    sprinkled {n} points", flush=True)
    e = np.concatenate([[e0], e, [e1]])
    x = np.concatenate([[xc], x, [xc]])
    return e, x


def chain_of(conf, inv_conf, a, t0, t1, xc, rng, rate_scale):
    e, x = sprinkle_diamond(conf, inv_conf, a, t0, t1, xc, rng, rate_scale)
    u, v = e - x, e + x
    idx = longest_chain(u, v)
    return u[idx], v[idx]


def relations(uA, vA, uB, vB):
    """F[i] = 1-based index of the first B element in A_i's future (inf if none), and G likewise."""
    def first_after(uX, vX, uY, vY):
        ju = np.searchsorted(uY, uX, side="left")
        jv = np.searchsorted(vY, vX, side="left")
        j = np.maximum(ju, jv).astype(float) + 1.0
        j[j > len(uY)] = np.inf
        return j
    return first_after(uA, vA, uB, vB), first_after(uB, vB, uA, vA)


def run(name, uA, vA, uB, vB, expect):
    if uA[0] == uB[0] and vA[0] == vB[0]:   # both chains start at the same event: keep it in A only
        uB, vB = uB[1:], vB[1:]
    FA, GB = relations(uA, vA, uB, vB)
    N, M = len(uA), len(uB)
    Nuse = int(0.5 * N)   # stay clear of the top of the diamonds, where the chains end
    F = lambda t: FA[int(round(t)) - 1]
    G = lambda s: GB[int(round(s)) - 1]
    tc = TwoChain(F, G, np.arange(1, Nuse + 1, dtype=float), np.arange(1, M + 1, dtype=float))
    lo, hi = tc.extremes()
    # rescale counts to proper time: chain length per unit proper time is the same for both (same density)
    say(f"{name}: chain lengths A={N}, B={M}; middle rate (B elements per A element) extremes "
        f"{lo:.4f} .. {hi:.4f}  spread {hi - lo:.4f}   [expected: {expect}]")


if __name__ == "__main__":
    rng = np.random.default_rng(7)
    # Minkowski: a = 1, conformal time = t
    ident = lambda t: t
    one = lambda t: np.ones_like(t) if isinstance(t, np.ndarray) else 1.0
    scale = 2.0
    for T in (400.0, 1000.0):
        # at rest, separation d
        uA, vA = chain_of(ident, ident, one, 0.0, T, 0.0, rng, scale)
        uB, vB = chain_of(ident, ident, one, 0.0, T, 20.0, rng, scale)
        run(f"Minkowski at rest, T={T:.0f}", uA, vA, uB, vB, "rigid, rate 1")
        # receding at rapidity eta from a common event: B's diamond in boosted coordinates
        eta = 0.5
        uA, vA = chain_of(ident, ident, one, 0.0, T, 0.0, rng, scale)
        uB0, vB0 = chain_of(ident, ident, one, 0.0, T, 0.0, rng, scale)
        uB, vB = uB0 * math.exp(-eta), vB0 * math.exp(eta)   # boost: u -> e^-eta u, v -> e^eta v
        run(f"Minkowski receding eta={eta}, T={T:.0f}", uA, vA, uB, vB,
            f"not rigid, extremes toward {math.exp(-eta):.3f} .. {math.exp(eta):.3f}")
    # FRW a = t^p, comoving observers at conformal separation chi, from T0 to T1
    for p, chi, T1 in [(0.5, 2.0, 1500.0), (1.0, 0.5, 1500.0)]:
        if p == 1.0:
            conf, inv = np.log, np.exp
        else:
            conf = lambda t, p=p: t ** (1 - p) / (1 - p)
            inv = lambda e, p=p: (e * (1 - p)) ** (1 / (1 - p))
        a = lambda t, p=p: t ** p
        uA, vA = chain_of(conf, inv, a, 10.0, T1, 0.0, rng, scale)
        uB, vB = chain_of(conf, inv, a, 10.0, T1, chi, rng, scale)
        run(f"FRW a=t^{p}, chi={chi}", uA, vA, uB, vB,
            "rigid, rate 1" if p < 1 else f"not rigid, extremes toward {math.exp(-chi):.3f} .. {math.exp(chi):.3f}")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
