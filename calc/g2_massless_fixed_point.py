"""G2: A5 (shift invariance of sigma) forbids a mass term; the massless field is the one that survives coarse-graining.

sigma as a Gaussian field on a 3D lattice (test arena) with precision  K = kappa * (graph Laplacian) + m^2.
(1) Conditional mean given content (sigma = -1 on a central ball, 0 far away): m = 0 gives the harmonic 1/r profile,
    m > 0 a screened (Yukawa) profile. Shift invariance sigma -> sigma + c holds only for m = 0.
(2) Coarse-graining: block 2x2x2 cells and measure the effective screening length of the conditional mean in
    lattice units of the coarse level. For m = 0 there is no length (stays infinite); for m > 0 the screening length in
    coarse units halves at each blocking -- the mass is relevant and flows away, so only m = 0 can be consistent at
    every level (P4).
Output: calc/out/g2_massless_fixed_point.txt
"""
import os
import numpy as np
from scipy.sparse import diags, kron, identity
from scipy.sparse.linalg import spsolve

OUT = os.path.join(os.path.dirname(__file__), "out", "g2_massless_fixed_point.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


def lap1(n):
    return diags([-np.ones(n - 1), 2 * np.ones(n), -np.ones(n - 1)], [-1, 0, 1])


def lap3(n):
    I = identity(n)
    L = lap1(n)
    return (kron(kron(L, I), I) + kron(kron(I, L), I) + kron(kron(I, I), L)).tocsr()


def conditional_mean(n, m2, a):
    """sigma = -1 inside radius a (content), 0 on the outer faces; mean of the Gaussian field elsewhere."""
    K = (lap3(n) + m2 * identity(n ** 3)).tocsr()
    c = (n - 1) / 2
    g = np.indices((n, n, n)).reshape(3, -1).T - c
    r = np.linalg.norm(g, axis=1)
    boundary = (np.abs(g) >= c - 0.5).any(axis=1)
    fixed = (r <= a) | boundary
    val = np.where(r <= a, -1.0, 0.0)
    free = ~fixed
    s = val.copy()
    s[free] = spsolve(K[free][:, free].tocsc(), -K[free][:, fixed] @ val[fixed])
    return r, s


def screening_length(r, s, a, rmax):
    """Fit log(r |sigma|) = const - r / lambda on a < r < rmax; lambda = inf means pure 1/r."""
    m = (r > a + 1.5) & (r < rmax) & (np.abs(s) > 1e-12)
    x, y = r[m], np.log(r[m] * np.abs(s[m]))
    slope = np.polyfit(x, y, 1)[0]
    return np.inf if slope >= 0 else -1.0 / slope, slope


if __name__ == "__main__":
    n, a = 41, 3.0
    say("conditional mean of sigma around content on a 41^3 lattice; fit log(r|sigma|) = c - r/lambda")
    for m2 in (0.0, 0.01, 0.04):
        r, s = conditional_mean(n, m2, a)
        lam, slope = screening_length(r, s, a, 12.0)
        exact = np.inf if m2 == 0 else 1 / np.sqrt(m2)
        say(f"  m^2 = {m2:5.3f}: fitted screening length {lam:8.2f}  (slope {slope:+.4f}; Yukawa length 1/m = {exact:.2f})")
    say("\ncoarse-graining by 2x2x2 blocks: the same continuum field on a lattice with spacing doubled")
    say("(a mass m in fine units is m * 2 in coarse units; the screening length in lattice units halves)")
    for m2_fine in (0.0, 0.01):
        for level in range(3):
            m2 = m2_fine * (4 ** level)          # m -> 2m per blocking, m^2 -> 4 m^2
            a_l = a / (2 ** level) if level else a
            nn = n
            r, s = conditional_mean(nn, m2, max(a_l, 1.0))
            lam, _ = screening_length(r, s, max(a_l, 1.0), 12.0)
            say(f"  fine m^2 = {m2_fine:4.2f}, level {level}: m^2 in lattice units {m2:6.3f}, screening length {lam:8.2f} lattice units")
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
