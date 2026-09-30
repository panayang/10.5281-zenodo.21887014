"""Two worldlines, their causal order, and the uniform order-invariant measure on its linear extensions.

A worldline ticks at proper times tA[0..N-1] (A) and sB[0..M-1] (B). The geometry enters only
through F and G: F(t) is the B proper time at which A's future light ray from A-time t arrives,
G(s) the same from B to A (INF if it never arrives). Both must be non-decreasing.

A linear extension is a lattice path through states (i, j) = (#A ticks done, #B ticks done).
State (i, j) is admissible iff it is a down-set:
    i >= cntA(j) = #{a : F(tA_a) <= sB_j}   and   j >= cntB(i) = #{b : G(sB_b) <= tA_i}.
Uniform linear extensions of the finite truncation are counted exactly in log scale. Conditioning
on the endpoint (N, jE) is conditioning on the last simultaneity slice; the measure is rigid when
the law in the middle forgets jE as N grows (p-ZFC's rigidity = uniqueness of the order-invariant
measure in Brightwell-Luczak's sense).
"""
import math
import numpy as np

INF = float("inf")
NEG = -np.inf


def unit_ticks(n, start=1.0):
    return start + np.arange(n, dtype=float)


def poisson_ticks(n, rng, start=0.0):
    return start + np.cumsum(rng.exponential(1.0, size=n))


class TwoChain:
    def __init__(self, F, G, tA, sB):
        self.tA, self.sB = np.asarray(tA, float), np.asarray(sB, float)
        self.N, self.M = len(self.tA), len(self.sB)
        FA = np.array([F(t) for t in self.tA])
        GB = np.array([G(s) for s in self.sB])
        if np.any(np.diff(FA[np.isfinite(FA)]) < 0) or np.any(np.diff(GB[np.isfinite(GB)]) < 0):
            raise ValueError("F and G must be non-decreasing")
        cntA = np.searchsorted(FA, np.concatenate([[-INF], self.sB]), side="right")  # j = 0..M
        cntB = np.searchsorted(GB, np.concatenate([[-INF], self.tA]), side="right")  # i = 0..N
        self.lo = np.minimum(cntB, self.M)
        self.hi = np.searchsorted(cntA, np.arange(self.N + 1), side="right") - 1      # max j, cntA(j) <= i
        if np.any(self.lo > self.hi):
            raise ValueError("empty row: truncation too short on the B side")

    # --- exact log counts -------------------------------------------------------------
    def forward(self, m):
        lo, hi = self.lo, self.hi
        row = np.full(hi[0] + 1, NEG)
        row[lo[0]:hi[0] + 1] = 0.0
        for i in range(1, m + 1):
            prev = np.full(hi[i] + 1, NEG)
            k = min(len(row), hi[i] + 1)
            prev[:k] = row[:k]
            new = np.full(hi[i] + 1, NEG)
            new[lo[i]:hi[i] + 1] = np.logaddexp.accumulate(prev[lo[i]:hi[i] + 1])
            row = new - new.max()
        return row

    def backward(self, m, jE):
        lo, hi, N = self.lo, self.hi, self.N
        b = np.full(hi[N] + 1, NEG)
        b[lo[N]:jE + 1] = 0.0
        for i in range(N - 1, m, -1):
            nxt = np.full(hi[i] + 1, NEG)
            k = min(len(b), hi[i] + 1)
            nxt[:k] = b[:k]
            new = np.full(hi[i] + 1, NEG)
            seg = nxt[lo[i]:hi[i] + 1]
            new[lo[i]:hi[i] + 1] = np.logaddexp.accumulate(seg[::-1])[::-1]
            b = new - new.max()
        return b

    def exit_law(self, m, jE, fwd=None):
        """Law of the column j at which the path leaves row m (A has done m ticks, B has done j)."""
        f = self.forward(m) if fwd is None else fwd
        b = self.backward(m, jE)
        k = min(len(f), len(b))
        lw = f[:k] + b[:k]
        w = np.exp(lw - lw.max())
        return w / w.sum()

    def middle_rate(self, jE, m=None, fwd=None):
        """Mean B-proper-time elapsed per A-proper-time at A's m-th tick, given endpoint jE."""
        m = self.N // 2 if m is None else m
        w = self.exit_law(m, jE, fwd)
        sB0 = np.concatenate([[0.0], self.sB])
        return float((w * sB0[:len(w)]).sum() / self.tA[m - 1])

    def endpoint_for_rate(self, rate):
        jE = int(np.searchsorted(self.sB, rate * self.tA[-1]))
        return max(self.lo[self.N], min(self.hi[self.N], jE))

    def extremes(self, m=None):
        m = self.N // 2 if m is None else m
        f = self.forward(m)
        return self.middle_rate(self.lo[self.N], m, f), self.middle_rate(self.hi[self.N], m, f)


# --- geometries ----------------------------------------------------------------------

def static_pair(a1, a2, delay):
    """Static observers with proper rates a1, a2 per coordinate time, constant coordinate light delay.
    Exact for static observers in any static spacetime (e.g. Schwarzschild, delay from r*)."""
    return (lambda t: a2 * (t / a1 + delay)), (lambda s: a1 * (s / a2 + delay))


def receding(eta):
    """Inertial observers leaving a common event with relative rapidity eta (Doppler factor e^eta)."""
    D = math.exp(eta)
    return (lambda t: D * t), (lambda s: D * s)


def frw_comoving(p, chi, T0):
    """Comoving observers in 1+1 FRW, a = t^p, conformal separation chi; proper time = cosmic time - T0."""
    if abs(p - 1) < 1e-12:
        conf, inv = math.log, math.exp
    elif p < 1:
        conf = lambda t: t ** (1 - p) / (1 - p)
        inv = lambda e: (e * (1 - p)) ** (1 / (1 - p))
    else:
        conf = lambda t: -t ** (1 - p) / (p - 1)
        inv = lambda e: (-e * (p - 1)) ** (-1 / (p - 1))

    def F(tau):
        e = conf(T0 + tau) + chi
        if p > 1 and e >= 0:
            return INF
        return inv(e) - T0

    return F, F


def de_sitter_comoving(H, chi, T0=0.0):
    """Comoving observers in 1+1 de Sitter, a = e^{Ht}, conformal separation chi (conformal time -e^{-Ht}/H).
    A's ray from proper time tau reaches B iff e^{-H(T0+tau)} > H chi: the event horizon."""
    def F(tau):
        x = math.exp(-H * (T0 + tau)) - H * chi
        return INF if x <= 0 else -math.log(x) / H - T0
    return F, F


class Worldline:
    """Timelike worldline in 1+1 Minkowski, x(t) given as a vectorised function of coordinate time."""

    def __init__(self, x, tmax, n=200001):
        self.t = np.linspace(0.0, tmax, n)
        self.xs = x(self.t)
        v = np.gradient(self.xs, self.t)
        if np.any(np.abs(v) >= 1):
            raise ValueError("not timelike")
        dtau = np.sqrt(1 - v ** 2)
        self.tau = np.concatenate([[0.0], np.cumsum(0.5 * (dtau[1:] + dtau[:-1]) * np.diff(self.t))])

    def at_tau(self, tau):
        t = np.interp(tau, self.tau, self.t)
        return t, np.interp(t, self.t, self.xs)

    def arrival_tau(self, t0, x0):
        """Proper time at which the future light cone of (t0, x0) first meets this worldline."""
        g = self.t - t0 - np.abs(self.xs - x0)  # increasing along a timelike worldline
        k = np.searchsorted(g, 0.0)
        if k >= len(g):
            return INF
        if k == 0:
            return float(self.tau[0])
        f = -g[k - 1] / (g[k] - g[k - 1])
        return float(self.tau[k - 1] + f * (self.tau[k] - self.tau[k - 1]))


def minkowski_pair(A, B):
    def F(tau):
        return B.arrival_tau(*A.at_tau(tau))

    def G(tau):
        return A.arrival_tau(*B.at_tau(tau))

    return F, G
