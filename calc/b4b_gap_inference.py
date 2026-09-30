"""B4b: can the coarse world absorb the hidden gap? (caveat of B4)

Thinned TP(p) with keep-probability q. For adjacent kept pairs (a, b) record the hidden gap g, whether a < b, and a coarse
context: how many of the K kept elements before a lie below b (c_b), and how many lie below a (c_a).
If the coarse world were (asymptotically) sufficient, P(a < b | context, g) would not depend on g once the context is fixed.
Output: calc/out/b4b_gap_inference.txt
"""
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "out", "b4b_gap_inference.txt")
K = 8


def tp_past(n, p, rng):
    past = np.zeros((n, n), dtype=bool)
    for j in range(1, n):
        e = rng.random(j) < p
        if e.any():
            past[j, :j] = e | past[:j][e].any(axis=0)[:j]
    return past


def run(p, q, n, samples, rng):
    rows = []
    for _ in range(samples):
        P = tp_past(n, p, rng)
        kept = np.flatnonzero(rng.random(n) < q)
        for t in range(K + n // 4 * 0, len(kept)):
            if t < K + 1:
                continue
            a, b = kept[t - 1], kept[t]
            prev = kept[t - 1 - K:t - 1]
            rows.append((b - a, P[b, a], P[b, prev].sum(), P[a, prev].sum()))
    return np.array(rows)


lines = []
rng = np.random.default_rng(5)
lines.append("unconditional vs stratified effect of the hidden gap (gap above vs at-or-below its median) on P(a < b);")
lines.append("stratified = pair-weighted mean of within-context differences over all contexts (c_b, c_a)")
for p, q, samples in [(0.0918, 0.5, 60), (0.079, 0.25, 90), (0.063, 0.125, 180), (0.046, 0.0625, 150)]:
    n = int(120 / q)
    R = run(p, q, n, samples, rng)
    g, rel, cb, ca = R.T
    gm = np.median(g)
    hi = g > gm
    d0 = rel[hi].mean() - rel[~hi].mean()
    se0 = np.sqrt(rel[hi].var() / hi.sum() + rel[~hi].var() / (~hi).sum())
    num, den, var = 0.0, 0, 0.0
    for key in set(zip(cb.astype(int), ca.astype(int))):
        m = (cb == key[0]) & (ca == key[1])
        a_, b_ = m & hi, m & ~hi
        if a_.sum() >= 5 and b_.sum() >= 5:
            w = m.sum()
            d = rel[a_].mean() - rel[b_].mean()
            v = rel[a_].var() / a_.sum() + rel[b_].var() / b_.sum()
            num += w * d; den += w; var += w * w * v
    ds, ses = num / den, np.sqrt(var) / den
    lines.append(f"  q = {q:<7} p = {p:<7} pairs {len(R):6d}  P(a<b) = {rel.mean():.4f}  unconditional diff {d0:+.4f} +- {se0:.4f}   "
                 f"stratified diff {ds:+.4f} +- {ses:.4f}   (relative to P(a<b): {d0 / rel.mean():+.2f} -> {ds / rel.mean():+.2f})")
    print(lines[-1], flush=True)
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write(chr(10).join(lines) + chr(10))
