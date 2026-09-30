"""T6: which families of events can one observer eventually record together? (p-ZFC coexistence)

Worlds are causal pasts; a family of events coexists in some world iff it has a common future.
In flat FRW with bounded conformal time (de Sitter, p > 1), shifted so eta_max = 0, the future of
an event (eta_e, x_e) meets future conformal infinity in the open ball B(x_e, |eta_e|) - its horizon
footprint - and a family coexists iff its footprints have a common point (F8). So the coexistence
complex is the nerve of the footprints: Helly => decided by (d+1)-subsets; Wegner => d-Leray.

Exact test (no optimiser): if a family of closed balls in R^d has nonempty intersection, the
intersection's leftmost point (min first coordinate) is the leftmost point of a single ball, of the
circle where two spheres meet (d >= 2), or a point where three spheres meet (d = 3). Checking these
candidates is exact for closed balls; families within 1e-7 of the boundary are discarded as undecided.
Output: calc/out/t6_coexistence.txt
"""
import itertools
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "out", "t6_coexistence.txt")
lines = []
EPS = 1e-7


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def _in_all(p, C, R, slack):
    return np.all(np.linalg.norm(C - p, axis=1) <= R + slack)


def _candidates(C, R):
    n, d = C.shape
    e1 = np.zeros(d); e1[0] = 1.0
    for i in range(n):
        yield C[i] - R[i] * e1
    if d >= 2:
        for i, j in itertools.combinations(range(n), 2):
            v = C[j] - C[i]
            L = np.linalg.norm(v)
            if L == 0 or L > R[i] + R[j] or L < abs(R[i] - R[j]):
                continue
            a = (R[i] ** 2 - R[j] ** 2 + L ** 2) / (2 * L)
            rho = np.sqrt(max(R[i] ** 2 - a ** 2, 0.0))
            nrm = v / L
            c = C[i] + a * nrm
            w = e1 - np.dot(e1, nrm) * nrm          # direction of e1 within the circle's plane
            wl = np.linalg.norm(w)
            if wl < 1e-15:
                yield c
                continue
            if d == 2:
                t = np.array([-nrm[1], nrm[0]])
                yield c + rho * t
                yield c - rho * t
            else:
                yield c - rho * w / wl
    if d == 3:
        for i, j, k in itertools.combinations(range(n), 3):
            for p in _three_spheres(C[i], R[i], C[j], R[j], C[k], R[k]):
                yield p


def _three_spheres(c1, r1, c2, r2, c3, r3):
    ex = c2 - c1
    D = np.linalg.norm(ex)
    if D == 0:
        return []
    ex = ex / D
    i_ = np.dot(ex, c3 - c1)
    ey = c3 - c1 - i_ * ex
    ey_n = np.linalg.norm(ey)
    if ey_n == 0:
        return []
    ey = ey / ey_n
    ez = np.cross(ex, ey)
    j_ = np.dot(ey, c3 - c1)
    x = (r1 ** 2 - r2 ** 2 + D ** 2) / (2 * D)
    y = (r1 ** 2 - r3 ** 2 + i_ ** 2 + j_ ** 2) / (2 * j_) - i_ * x / j_
    z2 = r1 ** 2 - x ** 2 - y ** 2
    if z2 < 0:
        return []
    z = np.sqrt(z2)
    base = c1 + x * ex + y * ey
    return [base + z * ez, base - z * ez]


def balls_meet(C, R, slack):
    return any(_in_all(p, C, R, slack) for p in _candidates(C, R))


def coexist(eta, X):
    """True/False, or None if too close to call. Footprints: centres X, radii -eta (eta < 0)."""
    R = -eta
    loose, tight = balls_meet(X, R + EPS, 1e-12), balls_meet(X, R - EPS, 1e-12)
    if loose != tight:
        return None
    return tight


def random_events(rng, k, d):
    return rng.uniform(-1.0, -0.3, size=k), rng.uniform(-0.6, 0.6, size=(k, d))


if __name__ == "__main__":
    rng = np.random.default_rng(5)
    # sanity: 1+1 exact formula (common future iff (max u + max v)/2 < 0)
    bad = 0
    for _ in range(5000):
        eta, X = random_events(rng, 3, 1)
        u, v = eta - X[:, 0], eta + X[:, 0]
        ex = 0.5 * (u.max() + v.max())
        c = coexist(eta, X)
        if c is not None and abs(ex) > 1e-6 and c != (ex < 0):
            bad += 1
    say(f"sanity (d=1): candidate test vs exact light-cone formula, 5000 triples: {bad} disagreements")
    for d in (1, 2, 3):
        viol = checked = 0
        for _ in range(20000):
            eta, X = random_events(rng, d + 2, d)
            subs = [coexist(eta[list(s)], X[list(s)]) for s in itertools.combinations(range(d + 2), d + 1)]
            whole = coexist(eta, X)
            if None in subs or whole is None:
                continue
            if all(subs):
                checked += 1
                viol += (not whole)
        hollow = found = 0
        for _ in range(20000):
            eta, X = random_events(rng, d + 1, d)
            faces = [coexist(eta[list(s)], X[list(s)]) for s in itertools.combinations(range(d + 1), d)]
            whole = coexist(eta, X)
            if None in faces or whole is None:
                continue
            if all(faces):
                found += 1
                hollow += (not whole)
        say(f"d={d}: Helly (every {d + 1} coexist => all {d + 2} coexist): {checked} families, {viol} violations;"
            f"  hollow {d + 1}-families (every {d} coexist, all not): {hollow} of {found}")
    say("")
    for d in (2, 3):
        V = np.eye(d + 1); V -= V.mean(axis=0)
        B = np.linalg.svd(V)[2][:d]; P = V @ B.T; P /= np.linalg.norm(P[0])
        facet = max(np.linalg.norm(P[list(s)] - P[list(s)].mean(axis=0), axis=1).max()
                    for s in itertools.combinations(range(d + 1), d))
        h = 0.5 * (1.0 + facet)
        eta = np.full(d + 1, -h)
        faces = [coexist(eta[list(s)], P[list(s)]) for s in itertools.combinations(range(d + 1), d)]
        say(f"regular {d}-simplex (circumradius 1, facet circumradius {facet:.4f}) at eta = -{h:.4f}: "
            f"every {d} coexist: {all(faces)}; all {d + 1} coexist: {coexist(eta, P)}")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
