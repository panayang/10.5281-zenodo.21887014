"""L2b follow-up: for intrinsic worldlines (longest chains) of two observers at rest, how does the
synchronisation window grow? Straight worldlines give a bounded window; maximal chains wander
transversally (Ulam/KPZ: ~ tau^(2/3)), so W should grow sublinearly and W/P -> 0 (still rigid).
Statistic: window width at A-index m divided by m, averaged over seeds and several m.
Output: calc/out/l2b_window_scaling.txt
"""
import os
import sys
import numpy as np

sys.path.insert(0, os.path.dirname(__file__))
import l2b_intrinsic as L
from twochain import TwoChain

OUT = os.path.join(os.path.dirname(__file__), "out", "l2b_window_scaling.txt")
ident = lambda t: t
one = lambda t: np.ones_like(t) if isinstance(t, np.ndarray) else 1.0

rows = []
for T in (250.0, 500.0, 1000.0, 2000.0):
    ratios = {0.2: [], 0.3: [], 0.4: []}
    for seed in range(20, 26):
        rng = np.random.default_rng(seed)
        uA, vA = L.chain_of(ident, ident, one, 0.0, T, 0.0, rng, 2.0)
        uB, vB = L.chain_of(ident, ident, one, 0.0, T, 20.0, rng, 2.0)
        FA, GB = L.relations(uA, vA, uB, vB)
        N, M = len(uA), len(uB)
        tc = TwoChain(lambda t: FA[int(round(t)) - 1], lambda s: GB[int(round(s)) - 1],
                      np.arange(1, N + 1, dtype=float), np.arange(1, M + 1, dtype=float))
        for f in ratios:
            m = int(f * N)
            ratios[f].append((tc.hi[m] - tc.lo[m]) / m)
    line = f"T={T:6.0f}  chain ~{N}  mean W/m at m = 0.2N, 0.3N, 0.4N: " + ", ".join(
        f"{np.mean(v):.4f}" for v in ratios.values())
    print(line, flush=True)
    rows.append(line)
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(rows) + "\n")
