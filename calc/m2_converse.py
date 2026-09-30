"""M2: the converse of M1. The description "this record belongs to process j" witnesses disagreement.

Along i's pasts the share of j-records relative to i-records is n_j(t)/t = 1/r2, along j's pasts it is s/m_i(s) = r1,
where s = tau_j(t) ~ r1 t (j first sees i's t-th record) and tau_i(s) ~ r2 s. The round trip gives 1 + rho = r1 r2.
So the two exhaustions agree on this description iff r1 r2 -> 1 iff rho -> 0.
Checked here on comoving pairs in the FRW test family (proper time = ticks); symmetric pairs have r1 = r2 = 1 + z.
Output: calc/out/m2_converse.txt
"""
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "out", "m2_converse.txt")
lines = []


def fam(p):
    if p == 1:
        return np.log, np.exp, np.inf
    eta = lambda t: t ** (1 - p) / (1 - p)
    tof = lambda e: ((1 - p) * e) ** (1 / (1 - p))
    return eta, tof, (0.0 if p > 1 else np.inf)


d = 1.0
lines.append(f"comoving pair at comoving distance d = {d}; share of j-records per i-record")
lines.append(f"{'a ~ t^p':>9} {'t':>8} {'along i: 1/r2':>14} {'along j: r1':>12} {'rho = r1 r2 - 1':>16}")
for p in (0.5, 0.8, 1.0, 1.5):
    eta, tof, emax = fam(p)
    for t in (1e2, 1e4, 1e6):
        e1 = eta(t) + d
        if e1 >= emax:
            lines.append(f"{p:9.1f} {t:8.0e} {'j never sees':>14} {'-':>12} {'inf':>16}")
            continue
        s = tof(e1)                     # j's proper time when it first sees i's record at t
        r1 = s / t
        r2 = tof(eta(s) + d) / s        # i sees j's record at s
        lines.append(f"{p:9.1f} {t:8.0e} {1 / r2:14.5f} {r1:12.5f} {r1 * r2 - 1:16.5f}")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
