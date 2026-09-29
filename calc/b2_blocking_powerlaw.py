"""B2: check proposition B7 (pure geometry gives a power law in cluster size / window).

Two static processes in 1+1, A at x = 0 and B at x = d (window 2d in proper time). Blocking: squares of side
delta in light-cone coordinates (u, v) = (t - x, t + x); in 1+1 these squares are causal diamonds. Shares are
proper-time lengths of each process inside a square. For an A-cluster X and a B-cluster Y the forward weight
is the fraction of (a, b) pairs with a < b, computed exactly from the 1D intervals involved.
Measured: (1) fuzzy share = B-share in clusters with 0 < w < 1 in either direction, per unit of true window;
(2) merged share = fraction of A's share lying in a cluster that also contains B.
Expectation (B7): both ~ (delta / window)^1 for delta << window. Output: calc/out/b2_blocking_powerlaw.txt
"""
import math
import os
import numpy as np

OUT = os.path.join(os.path.dirname(__file__), "out", "b2_blocking_powerlaw.txt")


def pieces(u0, T, du_dt, dv_dt, delta):
    """Cut the worldline u = u0 + du_dt t, v = v0... into (cell index, t-interval) pieces for t in [0, T]."""
    raise NotImplementedError


def cells_of_line(offset, T, delta, n=400000):
    # worldline at fixed x: u = t - x, v = t + x ; sample densely, group consecutive samples by cell
    t = np.linspace(0.0, T, n)
    x = offset
    iu = np.floor((t - x) / delta).astype(np.int64)
    iv = np.floor((t + x) / delta).astype(np.int64)
    key = iu * 10_000_000 + iv
    cells = {}
    dt = t[1] - t[0]
    for k, tt, a, b in zip(key, t, iu, iv):
        c = cells.get(k)
        if c is None:
            cells[k] = [a, b, tt, tt]
        else:
            c[3] = tt
    return [(v[0], v[1], v[2], v[3] + dt) for v in cells.values()]   # (iu, iv, t_start, t_end)


def frac_less(lo1, hi1, lo2, hi2):
    """P(X < Y) for X ~ U[lo1, hi1], Y ~ U[lo2, hi2]."""
    if hi1 <= lo2:
        return 1.0
    if hi2 <= lo1:
        return 0.0
    xs = np.linspace(lo1, hi1, 201)
    p = np.clip((hi2 - np.maximum(xs, lo2)) / (hi2 - lo2), 0, 1)
    return float(np.trapezoid(p, xs) / (hi1 - lo1))


def run(d, delta, T):
    A = cells_of_line(0.0, T, delta)
    B = cells_of_line(d, T, delta)
    # a = (t_a, 0): u_a = v_a = t_a ; b = (t_b, d): u_b = t_b - d, v_b = t_b + d
    # a < b  iff  u_a <= u_b and v_a <= v_b  iff  t_a <= t_b - d
    # b < a  iff  t_b + d <= t_a
    fuzzy, window, merged, amass = 0.0, 0.0, 0.0, 0.0
    Bset = {(c[0], c[1]) for c in B}
    for (iu, iv, a0, a1) in A:
        if a0 < 0.25 * T or a1 > 0.75 * T:
            continue
        ma = a1 - a0
        amass += ma
        if (iu, iv) in Bset:
            merged += ma
        for (ju, jv, b0, b1) in B:
            if b1 < a0 - 3 * d - 3 * delta or b0 > a1 + 3 * d + 3 * delta:
                continue
            mb = b1 - b0
            wf = frac_less(a0, a1, b0 - d, b1 - d)      # P(t_a < t_b - d)
            wb = frac_less(b0 + d, b1 + d, a0, a1)      # P(t_b + d < t_a)
            if (0 < wf < 1) or (0 < wb < 1):
                fuzzy += ma * mb
        window += ma * 2 * d
    return fuzzy / window, merged / amass


if __name__ == "__main__":
    d, T = 50.0, 2000.0
    lines = ["d = 50 (window 2d = 100); columns: delta/window, fuzzy share per window, merged share"]
    rows = []
    for delta in (1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0, 200.0, 400.0):
        f, m = run(d, delta, T)
        rows.append((delta / (2 * d), f, m))
        lines.append(f"{delta / (2 * d):8.3f} {f:10.4f} {m:10.4f}")
    small = [(r, f) for r, f, _ in rows if r <= 0.2 and f > 0]
    k = np.polyfit(np.log([r for r, _ in small]), np.log([f for _, f in small]), 1)[0]
    lines.append(f"fitted exponent of fuzzy share for delta/window <= 0.2: {k:.3f}   (B7 predicts 1)")
    print("\n".join(lines))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w", encoding="utf-8").write("\n".join(lines) + "\n")
