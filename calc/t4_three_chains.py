"""T4: three worldlines. Is the hidden parameter a Lorentz frame, or a general slicing?

Three inertial observers leaving a common event in 1+1 with rapidities 0, e1, e2. Inertial frames
give a ONE-parameter family of asymptotic rates (s_B, s_C)(phi). p-ZFC's multi-chain theorem
predicts a rate polytope of dimension = number of scale-free edges, i.e. TWO. If an endpoint
off the frame curve is reproduced in the middle, the hidden parameters are general (asymptotic)
slicings - many-fingered time - and inertial frames are a curve inside them.
Control: A, B mutually at rest (bounded edge) and C receding: one hidden parameter only.
Output: calc/out/t4_three_chains.txt
"""
import math
import os
import numpy as np
import sys
sys.path.insert(0, os.path.dirname(__file__))
from twochain import Worldline

NEG = -np.inf
OUT = os.path.join(os.path.dirname(__file__), "out", "t4_three_chains.txt")
lines = []


def say(s=""):
    print(s, flush=True)
    lines.append(s)


class ThreeChain:
    """Chains X = 0, 1, 2 with n[X] unit ticks; arr[X][Y](t) = Y-time at which X's ray from X-time t arrives."""

    def __init__(self, arr, n):
        self.n = n
        # cnt[Y][X][k] = #{ticks a of X : arr[X][Y](a) <= k}, k = 0..n[Y]  (X-ticks that must precede Y's k-th)
        self.cnt = {}
        for X in range(3):
            for Y in range(3):
                if X == Y:
                    continue
                FA = np.array([arr[X][Y](a) for a in range(1, n[X] + 1)])
                self.cnt[(Y, X)] = np.searchsorted(FA, np.arange(n[Y] + 1), side="right")

    def need(self, Y, X, k):
        return self.cnt[(Y, X)][k]

    def admissible_k(self, i, j):
        """Interval of k with (i, j, k) a down-set, or None."""
        c = self.cnt
        if c[(0, 1)][i] > j or c[(1, 0)][j] > i:   # A-tick i needs B ticks, B-tick j needs A ticks
            return None
        # k must satisfy: C ticks needed by A_i and B_j are done; A_i/B_j done covers C_k's needs.
        lo = max(self._need_C_by(0, i), self._need_C_by(1, j))
        hi = min(self._max_k_given(0, i), self._max_k_given(1, j), self.n[2])
        return (lo, hi) if lo <= hi else None

    def _need_C_by(self, X, idx):
        # number of C ticks that must precede X's idx-th tick = cnt[(X, 2)][idx]
        return self.cnt[(X, 2)][idx]

    def _max_k_given(self, X, idx):
        # largest k such that C's k-th tick needs at most idx ticks of X: cnt[(2, X)][k] <= idx
        return int(np.searchsorted(self.cnt[(2, X)], idx, side="right") - 1)

    def slices(self, i_from, i_to, step, init, jE=None, kE=None):
        """Log path counts on slices i (forward if step = +1 from (0,0,0), backward if -1 to the endpoint)."""
        nB, nC = self.n[1], self.n[2]
        cur = init
        out = {}
        rng_i = range(i_from, i_to + step, step)
        for idx, i in enumerate(rng_i):
            new = np.full((nB + 1, nC + 1), NEG)
            j_iter = range(0, nB + 1) if step > 0 else range(nB, -1, -1)
            for j in j_iter:
                kk = self.admissible_k(i, j)
                if kk is None:
                    continue
                lo, hi = kk
                if step > 0:
                    src = cur[j, lo:hi + 1].copy() if cur is not None else np.full(hi - lo + 1, NEG)
                    if idx == 0 and cur is None and j == 0:
                        src[0] = 0.0 if lo == 0 else NEG
                    if j > 0:
                        src = np.logaddexp(src, new[j - 1, lo:hi + 1])
                    new[j, lo:hi + 1] = np.logaddexp.accumulate(src)
                else:
                    src = cur[j, lo:hi + 1].copy() if cur is not None else np.full(hi - lo + 1, NEG)
                    if idx == 0 and cur is None:
                        # endpoint slice: paths from (i, j, k) to (N, jE, kE) inside the last slice
                        pass
                    if j < nB:
                        src = np.logaddexp(src, new[j + 1, lo:hi + 1])
                    new[j, lo:hi + 1] = np.logaddexp.accumulate(src[::-1])[::-1]
            if step < 0 and idx == 0 and cur is None:
                new = self._last_slice(i, jE, kE)
            mx = new[np.isfinite(new)].max()
            cur = new - mx
            out[i] = cur
        return out

    def _last_slice(self, i, jE, kE):
        nB, nC = self.n[1], self.n[2]
        new = np.full((nB + 1, nC + 1), NEG)
        for j in range(jE, -1, -1):
            kk = self.admissible_k(i, j)
            if kk is None:
                continue
            lo, hi = kk
            hi = min(hi, kE) if j == jE else hi
            if lo > hi:
                continue
            src = np.full(hi - lo + 1, NEG)
            if j == jE:
                if lo <= kE <= hi:
                    src[kE - lo] = 0.0
            else:
                src = new[j + 1, lo:hi + 1].copy()
            new[j, lo:hi + 1] = np.logaddexp.accumulate(src[::-1])[::-1]
        return new

    def middle_rates(self, jE, kE, m):
        f = self.slices(0, m, +1, None)[m]
        N = self.n[0]
        b = self.slices(N, m + 1, -1, None, jE, kE)[m + 1]
        lw = f + b  # leave slice m at (m, j, k), then step to (m+1, j, k)
        w = np.exp(lw - lw[np.isfinite(lw)].max())
        w[~np.isfinite(lw)] = 0
        w /= w.sum()
        J, K = np.meshgrid(np.arange(w.shape[0]), np.arange(w.shape[1]), indexing="ij")
        return float((w * J).sum() / m), float((w * K).sum() / m)


def receding3(etas):
    arr = [[None] * 3 for _ in range(3)]
    for X in range(3):
        for Y in range(3):
            if X != Y:
                D = math.exp(abs(etas[X] - etas[Y]))
                arr[X][Y] = (lambda D: (lambda t: D * t))(D)
    return arr


if __name__ == "__main__":
    N = 120
    e1, e2 = 0.5, 1.0
    arr = receding3([0.0, e1, e2])
    n = [N, int(math.exp(e1) * N * 1.3) + 5, int(math.exp(e2) * N * 1.3) + 5]
    tc = ThreeChain(arr, n)
    fr = lambda phi, e: math.cosh(phi) / math.cosh(e - phi)
    say(f"three receding observers, rapidities 0, {e1}, {e2}; N = {N}; middle at A-tick {N // 2}")
    targets = [("frame phi=0.5", fr(0.5, e1), fr(0.5, e2)),
               ("frame phi=0.0", fr(0.0, e1), fr(0.0, e2)),
               ("off-curve", fr(0.5, e1), 1.30),
               ("off-curve", fr(0.0, e1), 1.30)]
    for label, sB, sC in targets:
        jE, kE = int(round(sB * N)), int(round(sC * N))
        mB, mC = tc.middle_rates(jE, kE, N // 2)
        say(f"{label:14s} end (sB, sC) = ({sB:.4f}, {sC:.4f}) -> middle ({mB:.4f}, {mC:.4f})")

    say("\ncontrol: A at x=0 and B at x=-10 at rest (bounded edge), C leaves A's origin at rapidity 0.5")
    v = math.tanh(0.5)
    wl = [Worldline(lambda t: 0 * t, 3000), Worldline(lambda t: -10 + 0 * t, 3000),
          Worldline(lambda t: v * t, 3000)]
    arr = [[None] * 3 for _ in range(3)]
    for X in range(3):
        for Y in range(3):
            if X != Y:
                arr[X][Y] = (lambda X, Y: (lambda t: wl[Y].arrival_tau(*wl[X].at_tau(t))))(X, Y)
    n = [N, N + 40, int(math.exp(0.5) * N * 1.3) + 5]
    tc = ThreeChain(arr, n)
    for sB, sC in [(1.0, 1.0), (0.93, 1.0), (1.07, 1.0), (1.0, 1.3), (1.0, 0.8), (0.93, 1.3)]:
        mB, mC = tc.middle_rates(int(round(sB * N)), int(round(sC * N)), N // 2)
        say(f"end (sB, sC) = ({sB:.2f}, {sC:.2f}) -> middle ({mB:.4f}, {mC:.4f})")

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
