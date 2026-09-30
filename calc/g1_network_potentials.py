"""G1: which exchange laws give a Newtonian 1/r potential around content? (gravity directions, night of 2026-09-29)

Arena (a test, not a premise): N static processes placed uniformly in a d-dimensional ball; their mutual windows
are proportional to their separations, so "window" and "distance" are used interchangeably below.
A content region (radius a at the centre) holds sigma = -1; processes near the outer boundary hold sigma = 0.
Each mechanism fixes sigma elsewhere by a different rule; we fit sigma(r) against r.

  local consensus : sigma_i = weighted mean of sigma over processes within window r0 (a local averaging law)
  link exchange   : weights ~ 1/window for all pairs (causal links between static worldlines scale like 1/r,
                    see the note in docs/gravity-directions.md) -- a nonlocal averaging law
Harmonic reference: 1/r in 3D, log r in 2D, linear in 1D.
Output: calc/out/g1_network_potentials.txt
"""
import os
import numpy as np
from scipy.spatial import cKDTree
from scipy.sparse import coo_matrix, csr_matrix
from scipy.sparse.linalg import cg, spsolve

OUT = os.path.join(os.path.dirname(__file__), "out", "g1_network_potentials.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def points(d, N, R, rng):
    X = []
    while len(X) < N:
        P = rng.uniform(-R, R, size=(N, d))
        P = P[np.linalg.norm(P, axis=1) <= R]
        X.extend(P.tolist())
    return np.array(X[:N])


def solve(W, fixed_mask, fixed_val):
    """Solve sum_j W_ij (s_i - s_j) = 0 for free i, s fixed on fixed_mask."""
    N = W.shape[0]
    deg = np.asarray(W.sum(axis=1)).ravel()
    free = ~fixed_mask
    L = (csr_matrix((deg, (np.arange(N), np.arange(N))), shape=(N, N)) - W).tocsr()
    Lff = L[free][:, free]
    rhs = -L[free][:, fixed_mask] @ fixed_val[fixed_mask]
    s = fixed_val.copy()
    s[free] = spsolve(Lff.tocsc(), rhs)
    return s


def profile(X, s, a, R, nb=10):
    r = np.linalg.norm(X, axis=1)
    edges = np.linspace(1.5 * a, 0.7 * R, nb + 1)
    out = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        m = (r >= lo) & (r < hi)
        if m.sum() > 5:
            out.append((0.5 * (lo + hi), s[m].mean()))
    return np.array(out)


def fit_forms(prof, R):
    """Compare sigma(r) with the three harmonic forms (Dirichlet at r = a and r = R)."""
    r, s = prof[:, 0], prof[:, 1]
    res = {}
    for name, f in [("1/r - 1/R", lambda r: 1 / r - 1 / R), ("log(R/r)", lambda r: np.log(R / r)), ("R - r", lambda r: R - r)]:
        g = f(r)
        c = (g @ s) / (g @ g)
        res[name] = np.sqrt(np.mean((s - c * g) ** 2)) / np.std(s)
    # local power-law slope of |sigma|
    k = np.polyfit(np.log(r), np.log(np.abs(s) + 1e-12), 1)[0]
    return res, k


if __name__ == "__main__":
    rng = np.random.default_rng(3)
    for d, N, r0 in [(1, 3000, 0.02), (2, 12000, 0.05), (3, 20000, 0.12)]:
        R, a = 1.0, 0.1
        X = points(d, N, R, rng)
        r = np.linalg.norm(X, axis=1)
        fixed = (r <= a) | (r >= 0.95 * R)
        val = np.where(r <= a, -1.0, 0.0)
        # local consensus
        tree = cKDTree(X)
        pairs = tree.query_pairs(r0, output_type="ndarray")
        W = coo_matrix((np.ones(len(pairs)), (pairs[:, 0], pairs[:, 1])), shape=(N, N))
        W = (W + W.T).tocsr()
        s_loc = solve(W, fixed, val)
        pl = profile(X, s_loc, a, R)
        res, k = fit_forms(pl, 0.95 * R)
        say(f"d={d} local consensus (window < {r0}): relative rms misfit  " +
            "  ".join(f"{n}: {v:.3f}" for n, v in res.items()) + f"   local slope of |sigma| vs r: {k:+.2f}")
        # nonlocal link exchange: weights 1/window for all pairs (subsample for size)
        M = min(N, 2500)
        idx = rng.choice(N, M, replace=False)
        Y = X[idx]
        ry = np.linalg.norm(Y, axis=1)
        D = np.linalg.norm(Y[:, None, :] - Y[None, :, :], axis=2)
        np.fill_diagonal(D, np.inf)
        Wn = csr_matrix(1.0 / D)
        fy = (ry <= a) | (ry >= 0.95 * R)
        vy = np.where(ry <= a, -1.0, 0.0)
        s_nl = solve(Wn, fy, vy)
        pn = profile(Y, s_nl, a, R)
        res2, k2 = fit_forms(pn, 0.95 * R)
        spread = pn[:, 1].max() - pn[:, 1].min()
        say(f"d={d} link exchange (weights 1/window, all pairs): relative rms misfit  " +
            "  ".join(f"{n}: {v:.3f}" for n, v in res2.items()) + f"   local slope: {k2:+.2f}; sigma range over shells {spread:.3f}")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
