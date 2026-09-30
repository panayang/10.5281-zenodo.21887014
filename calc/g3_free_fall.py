"""G3: free fall from counting. A process that is a longest chain (most ticks between two events) in a region with a
sigma gradient bulges toward faster clocks -- the shape of a projectile thrown up and falling back (acceleration
toward lower sigma, i.e. toward content).

Test order (a test, not a premise): 1+1 sprinkling with density proportional to e^{2 sigma(x)} in the causal diamond
between (0, 0) and (T, 0), sigma = g x. In 1+1 every metric is conformally flat, so this is the whole geometry.
Continuum prediction (maximise the proper time integral of e^sigma sqrt(1 - v^2)): x(t) = (g/2) t (T - t),
midpoint displacement g T^2 / 8 toward larger sigma. Control: g = 0.
Output: calc/out/g3_free_fall.txt
"""
import bisect
import math
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "out", "g3_free_fall.txt")


def sprinkle(T, rho0, g, rng):
    # rejection sampling in the diamond |x| <= min(t, T - t) with density rho0 * exp(2 g x)
    wmax = math.exp(2 * abs(g) * T / 2)
    n_prop = rng.poisson(rho0 * wmax * T * T)   # bounding box [0,T] x [-T/2, T/2]
    t = rng.uniform(0, T, n_prop)
    x = rng.uniform(-T / 2, T / 2, n_prop)
    keep = (np.abs(x) <= np.minimum(t, T - t)) & (rng.uniform(0, 1, n_prop) < np.exp(2 * g * x) / wmax)
    t, x = t[keep], x[keep]
    t = np.concatenate([[0.0], t, [T]])
    x = np.concatenate([[0.0], x, [0.0]])
    return t, x


def longest_chain(t, x):
    u, v = t - x, t + x
    order = np.lexsort((v, u))
    vs = v[order]
    tails, tails_i, prev = [], [], np.full(len(vs), -1)
    for k, val in enumerate(vs):
        pos = bisect.bisect_right(tails, val)
        if pos == len(tails):
            tails.append(val); tails_i.append(k)
        else:
            tails[pos] = val; tails_i[pos] = k
        prev[k] = tails_i[pos - 1] if pos > 0 else -1
    k = tails_i[-1]
    chain = []
    while k != -1:
        chain.append(order[k]); k = prev[k]
    return np.array(chain[::-1])


def midpoint_x(t, x, idx, T):
    tc, xc = t[idx], x[idx]
    j = np.searchsorted(tc, T / 2)
    j = min(max(j, 1), len(tc) - 1)
    f = (T / 2 - tc[j - 1]) / (tc[j] - tc[j - 1])
    return xc[j - 1] + f * (xc[j] - xc[j - 1])


if __name__ == "__main__":
    rng = np.random.default_rng(11)
    T, rho0, seeds = 200.0, 4.0, 48
    lines = [f"1+1, T = {T}, density rho0 e^(2 g x) with rho0 = {rho0}; {seeds} seeds each"]
    for g in (0.0, 0.004, 0.008):
        mids = []
        for _ in range(seeds):
            t, x = sprinkle(T, rho0, g, rng)
            idx = longest_chain(t, x)
            mids.append(midpoint_x(t, x, idx, T))
        mids = np.array(mids)
        pred = g * T * T / 8
        lines.append(f"g = {g:.3f}: mean midpoint displacement {mids.mean():+7.2f} +- {mids.std(ddof=1) / math.sqrt(seeds):5.2f}"
                     f"   continuum geodesic {pred:+7.2f}   (spread of single chains {mids.std(ddof=1):.1f})")
    print("\n".join(lines))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
