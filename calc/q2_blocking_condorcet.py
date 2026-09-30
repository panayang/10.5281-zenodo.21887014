"""Q2: blocking weights of any partial order obey the Condorcet bound w(A,B) + w(B,C) + w(C,A) <= 2.

Pointwise: for a in A, b in B, c in C the three relations a<b, b<c, c<a cannot all hold (that would be a cycle), so the
sum of indicators is <= 2; averaging over independent draws gives the bound for the weights. Numerical sanity check:
random 1+1 sprinklings (and random partial orders from random DAGs), random disjoint clusters, maximise the cyclic sum.
Output: calc/out/q2_blocking_condorcet.txt
"""
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "out", "q2_blocking_condorcet.txt")
rng = np.random.default_rng(7)


def sprinkle_order(n):
    u, v = rng.random(n), rng.random(n)
    return (u[:, None] < u[None, :]) & (v[:, None] < v[None, :])      # i < j iff u_i < u_j and v_i < v_j


def dag_order(n, p):
    A = np.triu(rng.random((n, n)) < p, 1)
    R = A.copy()
    for k in range(n):                                                    # transitive closure
        R |= R[:, [k]] & R[[k], :]
    perm = rng.permutation(n)
    return R[np.ix_(perm, perm)]


def w(R, X, Y):
    return R[np.ix_(X, Y)].mean()


best = 0.0
for trial in range(4000):
    n = 60
    R = sprinkle_order(n) if trial % 2 == 0 else dag_order(n, rng.uniform(0.02, 0.3))
    idx = rng.permutation(n)
    k1, k2 = sorted(rng.choice(np.arange(1, n - 1), 2, replace=False))
    A, B, C = idx[:k1], idx[k1:k2], idx[k2:]
    for X, Y, Z in ((A, B, C), (A, C, B)):
        s = w(R, X, Y) + w(R, Y, Z) + w(R, Z, X)
        best = max(best, s)
lines = [f"largest cyclic sum w(A,B) + w(B,C) + w(C,A) over 8000 random cluster triples in random posets: {best:.4f} (bound 2)",
         "so a cyclic weight pattern above 2 cannot come from blocking any sharp order: it needs refinements with no common refinement"]
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
