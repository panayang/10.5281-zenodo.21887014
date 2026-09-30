//! B-phys: how far does a longest chain wander from the straight worldline?
//!
//! Sprinkle a Poisson sample (unit density) in the causal interval between (0, 0) and (T, 0) of
//! D-dimensional Minkowski space; take a longest chain (dynamic programming over time-sorted points,
//! O(n^2)); record the spatial distance of the chain from the axis at t = T/2. If the RMS transverse
//! deviation grows like T^xi, then (F11) two longest-chain processes at distance d stay distinct over
//! a duration T only if d >~ rho^(-(1-xi)/D ...) T^xi; with the discreteness at the Planck scale this
//! turns into a physical length. D = 2 validates the code against the known xi = 2/3.

use crate::SplitMix;

fn gauss(rng: &mut SplitMix) -> f64 {
    let u1 = rng.unif(1e-300, 1.0);
    let u2 = rng.unif(0.0, 1.0);
    (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
}

fn poisson(rng: &mut SplitMix, mean: f64) -> usize {
    (mean + gauss(rng) * mean.sqrt()).round().max(0.0) as usize
}

fn unit_ball_volume(k: usize) -> f64 {
    match k {
        1 => 2.0,
        2 => std::f64::consts::PI,
        3 => 4.0 / 3.0 * std::f64::consts::PI,
        _ => unreachable!(),
    }
}

/// Points of a unit-density sprinkling of the interval between (0,0) and (T,0) in D = 1 + k dims.
fn sprinkle(rng: &mut SplitMix, t: f64, k: usize) -> Vec<(f64, [f64; 3])> {
    // volume = 2 * integral_0^{T/2} V_k s^k ds = 2 V_k (T/2)^{k+1} / (k+1)
    let vol = 2.0 * unit_ball_volume(k) * (t / 2.0).powi(k as i32 + 1) / (k as f64 + 1.0);
    let n = poisson(rng, vol);
    let mut pts = Vec::with_capacity(n + 2);
    pts.push((0.0, [0.0; 3]));
    pts.push((t, [0.0; 3]));
    while pts.len() < n + 2 {
        // uniform in the bounding box, rejected outside the interval: uniform in proper volume
        let tt = rng.unif(0.0, t);
        let r = tt.min(t - tt);
        let mut x = [0.0; 3];
        for a in 0..k {
            x[a] = rng.unif(-t / 2.0, t / 2.0);
        }
        if (x[0] * x[0] + x[1] * x[1] + x[2] * x[2]).sqrt() <= r {
            pts.push((tt, x));
        }
    }
    pts.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
    pts
}

fn precedes(a: &(f64, [f64; 3]), b: &(f64, [f64; 3])) -> bool {
    let dt = b.0 - a.0;
    if dt <= 0.0 {
        return false;
    }
    let dx = [b.1[0] - a.1[0], b.1[1] - a.1[1], b.1[2] - a.1[2]];
    dx[0] * dx[0] + dx[1] * dx[1] + dx[2] * dx[2] <= dt * dt
}

/// Longest chain from the bottom tip to the top tip; returns (length, transverse distance at T/2).
fn longest_chain(pts: &[(f64, [f64; 3])], t: f64) -> (usize, f64) {
    let n = pts.len();
    let mut len = vec![0usize; n];
    let mut prev = vec![usize::MAX; n];
    len[0] = 1;
    for j in 1..n {
        let mut best = 0usize;
        let mut arg = usize::MAX;
        for i in 0..j {
            if len[i] + 1 > best + 1 && len[i] > 0 && precedes(&pts[i], &pts[j]) {
                best = len[i];
                arg = i;
            }
        }
        if arg != usize::MAX {
            len[j] = best + 1;
            prev[j] = arg;
        }
    }
    // the top tip is the last point with t = T
    let top = (0..n).find(|&i| pts[i].0 == t).unwrap();
    let mut chain = Vec::new();
    let mut k = top;
    while k != usize::MAX {
        chain.push(k);
        k = prev[k];
    }
    chain.reverse();
    // transverse distance at t = T/2, linear interpolation between neighbouring chain elements
    let mut dev = 0.0;
    for w in chain.windows(2) {
        let (p, q) = (&pts[w[0]], &pts[w[1]]);
        if p.0 <= t / 2.0 && q.0 >= t / 2.0 {
            let f = if q.0 > p.0 { (t / 2.0 - p.0) / (q.0 - p.0) } else { 0.0 };
            let x = [p.1[0] + f * (q.1[0] - p.1[0]), p.1[1] + f * (q.1[1] - p.1[1]), p.1[2] + f * (q.1[2] - p.1[2])];
            dev = (x[0] * x[0] + x[1] * x[1] + x[2] * x[2]).sqrt();
            break;
        }
    }
    (chain.len(), dev)
}

pub fn run(dim: usize, ts: &[f64], seeds: u64) {
    let k = dim - 1;
    println!("D = {dim}: longest chain in a unit-density causal interval of height T; RMS transverse distance at T/2");
    println!("{:>8} {:>10} {:>10} {:>12}", "T", "points", "chain", "rms dev");
    let mut logs = Vec::new();
    for &t in ts {
        let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4) as u64;
        let results: Vec<(f64, f64, f64)> = std::thread::scope(|sc| {
            let handles: Vec<_> = (0..threads)
                .map(|w| {
                    sc.spawn(move || {
                        let mut acc = (0.0, 0.0, 0.0);
                        let mut s = w;
                        while s < seeds {
                            let mut rng = SplitMix(0xD1CE ^ (s * 7919) ^ ((t * 1000.0) as u64) ^ ((dim as u64) << 50));
                            let pts = sprinkle(&mut rng, t, k);
                            let (l, dev) = longest_chain(&pts, t);
                            acc.0 += pts.len() as f64;
                            acc.1 += l as f64;
                            acc.2 += dev * dev;
                            s += threads;
                        }
                        acc
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let (np, cl, d2) = results.iter().fold((0.0, 0.0, 0.0), |a, r| (a.0 + r.0, a.1 + r.1, a.2 + r.2));
        let kk = seeds as f64;
        let rms = (d2 / kk).sqrt();
        println!("{:>8.1} {:>10.0} {:>10.1} {:>12.4}", t, np / kk, cl / kk, rms);
        logs.push((t.ln(), rms.ln()));
    }
    let n = logs.len() as f64;
    let (sx, sy) = logs.iter().fold((0.0, 0.0), |a, p| (a.0 + p.0, a.1 + p.1));
    let (mx, my) = (sx / n, sy / n);
    let (num, den) = logs.iter().fold((0.0, 0.0), |a, p| (a.0 + (p.0 - mx) * (p.1 - my), a.1 + (p.0 - mx).powi(2)));
    println!("fitted transverse exponent xi (rms dev ~ T^xi): {:.3}", num / den);
}
