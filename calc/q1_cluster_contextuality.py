"""Q1: a cluster (preorder class) whose internal order is resolved pairwise, in incompatible refinements.

Three records a, b, c in one cluster. Context {x, y} = a refinement that resolves the order of x and y (and only those).
Empirical law in context {x, y}: P(x before y) as given. A global (noncontextual) law is a distribution over the
13 weak orders ... we use strict partial orders on {a, b, c} (19 of them) with 'resolved pair' meaning comparable;
to keep each context's answer binary we use linear orders (6) as the global candidates, which is the case where
every refinement resolves the pair. Noncontextual fraction NCF = max lambda such that lambda * (marginals of some global
law) <= empirical probabilities on every outcome of every context (Abramsky-Brandenburger); eta = 1 - NCF.
Scan the cyclic assignment P(a<b) = P(b<c) = P(c<a) = q.
Output: calc/out/q1_cluster_contextuality.txt
"""
import itertools
import os
import numpy as np
from scipy.optimize import linprog

OUT = os.path.join(os.path.dirname(__file__), "out", "q1_cluster_contextuality.txt")
recs = "abc"
orders = list(itertools.permutations(recs))          # linear orders as global assignments
contexts = [("a", "b"), ("b", "c"), ("c", "a")]


def ncf(q):
    # variables: weights w_o >= 0 on linear orders (sub-normalised); maximise sum w
    # constraints: for each context (x, y) and outcome (x<y or y<x): sum_{o with outcome} w_o <= empirical prob
    A, b = [], []
    for x, y in contexts:
        for outcome in (True, False):
            A.append([1.0 if ((o.index(x) < o.index(y)) == outcome) else 0.0 for o in orders])
            b.append(q if outcome else 1 - q)
    res = linprog(-np.ones(len(orders)), A_ub=A, b_ub=b, bounds=[(0, None)] * len(orders), method="highs")
    return -res.fun


lines = ["cyclic pairwise resolution of a 3-record cluster: P(a<b) = P(b<c) = P(c<a) = q",
         f"{'q':>6} {'sum of cyclic probs':>20} {'NCF':>8} {'eta = 1 - NCF':>14}"]
for q in (0.5, 0.6, 2 / 3, 0.75, 0.9, 1.0):
    f = ncf(q)
    lines.append(f"{q:6.3f} {3 * q:20.3f} {f:8.4f} {1 - f:14.4f}")
lines.append("NCF = min(1, 3(1 - q)), eta = max(0, 3q - 2): eta > 0 exactly when 3q > 2 (the Condorcet bound of law.md section 6); strongly contextual at q = 1")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
