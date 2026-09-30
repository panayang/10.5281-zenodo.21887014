"""Q3: classical / quantum / exclusivity-only bounds from exclusivity graphs (Cabello-Severini-Winter graph approach).

Vertices = events; edges = pairs of events that cannot both occur (in the framework: possible records that never coexist).
  alpha(G)       : max over deterministic assignments (a global world assigning every question)      -> noncontextual bound
  theta(G)       : Lovasz number, max over orthonormal representations                               -> quantum bound (CSW)
  alpha*(G)      : fractional packing, sum p <= 1 on every clique (exclusivity applied to cliques)     -> exclusivity, single copy
Graphs: KCBS pentagon C5, and the CHSH graph (8 winning events, exclusive when they share a party's setting with different outcomes).
Output: calc/out/q3_exclusivity_bounds.txt
"""
import itertools
import os
import numpy as np
import cvxpy as cp
import networkx as nx

OUT = os.path.join(os.path.dirname(__file__), "out", "q3_exclusivity_bounds.txt")


def theta(G):
    n = G.number_of_nodes()
    idx = {v: i for i, v in enumerate(G.nodes())}
    X = cp.Variable((n, n), symmetric=True)
    cons = [X >> 0, cp.trace(X) == 1] + [X[idx[u], idx[v]] == 0 for u, v in G.edges()]
    return cp.Problem(cp.Maximize(cp.sum(X)), cons).solve(solver=cp.SCS, eps=1e-9)


def alpha(G):
    return max(len(c) for c in nx.find_cliques(nx.complement(G)))


def alpha_star(G):
    nodes = list(G.nodes())
    p = cp.Variable(len(nodes), nonneg=True)
    idx = {v: i for i, v in enumerate(nodes)}
    cons = [cp.sum(p[[idx[v] for v in c]]) <= 1 for c in nx.find_cliques(G)]
    return cp.Problem(cp.Maximize(cp.sum(p)), cons).solve()


C5 = nx.cycle_graph(5)
ev = [(a, b, x, y) for a, b, x, y in itertools.product((0, 1), repeat=4) if (a ^ b) == (x & y)]
CH = nx.Graph()
CH.add_nodes_from(ev)
for e1, e2 in itertools.combinations(ev, 2):
    (a1, b1, x1, y1), (a2, b2, x2, y2) = e1, e2
    if (x1 == x2 and a1 != a2) or (y1 == y2 and b1 != b2):
        CH.add_edge(e1, e2)
lines = []
for name, G, conv in [("KCBS pentagon", C5, None), ("CHSH (sum of 4 winning probabilities per setting pair, total over 8 events)", CH, "chsh")]:
    a, t, s = alpha(G), theta(G), alpha_star(G)
    lines.append(f"{name}: alpha = {a}, theta = {t:.5f}, alpha* = {s:.5f}")
    if conv:
        # sum over the 8 events of P = 4 * P(win) ; CHSH correlator value = 8 P(win) - 4
        for lab, v in (("noncontextual", a), ("quantum (theta)", t), ("exclusivity single copy", s)):
            lines.append(f"    {lab:26s}: P(win) = {v / 4:.5f},  CHSH = {2 * v - 4:.5f}")
tc = theta(nx.complement(CH))
lines.append(f"CHSH graph is vertex-transitive: theta(G) * theta(complement) = {theta(CH) * tc:.5f} (n = 8).")
lines.append("  Two-copy exclusivity (Cabello's argument): the diagonal events (i, i) of G and its complement are pairwise exclusive, so sum_i p_i q_i <= 1;")
lines.append(f"  with uniform p0 on G and a complement experiment reaching q0 = theta(complement)/8 = {tc / 8:.5f}, p0 <= 1/theta(complement) and the total <= theta(G) = Tsirelson.")
lines.append("CHSH: classical 2, quantum 2 sqrt 2 = 2.82843 from theta, single-copy exclusivity reaches the no-signalling value 4 here;")
lines.append("the Tsirelson bound needs exclusivity applied also to independent copies (literature), i.e. the flag/pairwise principle used jointly with products")
print("\n".join(lines))
os.makedirs(os.path.dirname(OUT), exist_ok=True)
open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
