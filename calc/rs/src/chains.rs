//! L2b redone on a single sprinkling (F6 follow-up).
//!
//! Two observers at rest in 1+1 Minkowski, separation d, from t = 0 to t = T. In light-cone
//! coordinates u = t - x, v = t + x their causal diamonds are the squares [0,T]^2 and
//! [-d, T-d] x [d, T+d]. One Poisson sample (density rho in proper volume, i.e. rho/2 per du dv)
//! is drawn on the union; each observer's worldline is the longest chain in its own diamond
//! (a longest increasing subsequence). Every relation between the two chains is read off the
//! sample's order (dominance in (u, v)). The window W(m) is the number of B elements incomparable
//! to A's m-th element; rigidity of the rate needs W(m)/m -> 0 (F5).
//! Straight worldlines would give a bounded window (about 2 d sqrt(2 rho)); maximal chains wander
//! transversally (Ulam/KPZ, ~ L^(2/3)), so W should grow like N^(2/3).

use crate::SplitMix;

fn poisson(rng: &mut SplitMix, mean: f64) -> usize {
    // normal approximation is fine for the means used here (>= 1e4)
    let u1 = rng.unif(1e-300, 1.0);
    let u2 = rng.unif(0.0, 1.0);
    let z = (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos();
    (mean + z * mean.sqrt()).round().max(0.0) as usize
}

/// Longest chain (u and v both increasing) among the points; returns them in order.
fn longest_chain(mut pts: Vec<(f64, f64)>) -> Vec<(f64, f64)> {
    pts.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().then(a.1.partial_cmp(&b.1).unwrap()));
    let n = pts.len();
    let mut tails_v: Vec<f64> = Vec::new();
    let mut tails_i: Vec<usize> = Vec::new();
    let mut prev = vec![usize::MAX; n];
    for (k, p) in pts.iter().enumerate() {
        let pos = tails_v.partition_point(|&x| x <= p.1);
        if pos == tails_v.len() {
            tails_v.push(p.1);
            tails_i.push(k);
        } else {
            tails_v[pos] = p.1;
            tails_i[pos] = k;
        }
        prev[k] = if pos > 0 { tails_i[pos - 1] } else { usize::MAX };
    }
    let mut out = Vec::new();
    let mut k = *tails_i.last().unwrap();
    loop {
        out.push(pts[k]);
        if prev[k] == usize::MAX {
            break;
        }
        k = prev[k];
    }
    out.reverse();
    out
}

/// B elements incomparable to a = (u, v): B is a chain increasing in u and v. With a single
/// sprinkling the two chains may share an event; a shared event is comparable (equal), counted once.
fn window(b: &[(f64, f64)], a: (f64, f64)) -> usize {
    let m = b.len();
    // at or below a: u <= a.u and v <= a.v (a prefix, since B increases in both)
    let below = b.partition_point(|p| p.0 <= a.0).min(b.partition_point(|p| p.1 <= a.1));
    // strictly above a: u >= a.u and v >= a.v, excluding a itself
    let start = b.partition_point(|p| p.0 < a.0).max(b.partition_point(|p| p.1 < a.1));
    let mut above = m - start;
    if start < below {
        above -= below - start; // the shared event(s) already counted as below
    }
    m - below - above
}

pub fn run(rho: f64, d: f64, ts: &[f64], seeds: u64) {
    println!("two observers at rest, separation d = {d}, density rho = {rho}; one sprinkling, longest chains");
    println!("{:>8} {:>8} {:>10} {:>10} {:>12} {:>14}", "T", "N", "W(N/4)", "W(N/2)", "W(N/2)/(N/2)", "shared frac");
    let mut logs: Vec<(f64, f64)> = Vec::new();
    for &t in ts {
        let (mut nsum, mut w4, mut w2, mut shared) = (0.0, 0.0, 0.0, 0.0);
        for s in 0..seeds {
            let mut rng = SplitMix(0xC0FFEE ^ (s * 7919) ^ (t as u64));
            // bounding box of the two squares in (u, v)
            let (u0, u1, v0, v1) = (-d, t, 0.0, t + d);
            let mean = rho / 2.0 * (u1 - u0) * (v1 - v0);
            let n = poisson(&mut rng, mean);
            let mut a_pts = vec![(0.0, 0.0), (t, t)];
            let mut b_pts = vec![(-d, d), (t - d, t + d)];
            for _ in 0..n {
                let u = rng.unif(u0, u1);
                let v = rng.unif(v0, v1);
                if (0.0..=t).contains(&u) && (0.0..=t).contains(&v) {
                    a_pts.push((u, v));
                }
                if (-d..=t - d).contains(&u) && (d..=t + d).contains(&v) {
                    b_pts.push((u, v));
                }
            }
            let a = longest_chain(a_pts);
            let b = longest_chain(b_pts);
            let na = a.len();
            nsum += na as f64;
            w4 += window(&b, a[na / 4]) as f64;
            w2 += window(&b, a[na / 2]) as f64;
            let bs: std::collections::HashSet<(u64, u64)> = b.iter().map(|p| (p.0.to_bits(), p.1.to_bits())).collect();
            shared += a.iter().filter(|p| bs.contains(&(p.0.to_bits(), p.1.to_bits()))).count() as f64 / na as f64;
        }
        let k = seeds as f64;
        let (nn, ww4, ww2) = (nsum / k, w4 / k, w2 / k);
        println!("{:>8.0} {:>8.0} {:>10.1} {:>10.1} {:>12.4} {:>14.3}", t, nn, ww4, ww2, ww2 / (nn / 2.0), shared / k);
        if ww2 > 0.0 {
            logs.push((nn.ln(), ww2.ln()));
        }
    }
    // least-squares slope of log W(N/2) against log N
    let n = logs.len() as f64;
    let (sx, sy) = logs.iter().fold((0.0, 0.0), |a, p| (a.0 + p.0, a.1 + p.1));
    let (mx, my) = (sx / n, sy / n);
    let (num, den) = logs.iter().fold((0.0, 0.0), |a, p| (a.0 + (p.0 - mx) * (p.1 - my), a.1 + (p.0 - mx).powi(2)));
    println!("wandering scale rho^(-1/6) T^(2/3) at the largest T: {:.0} (vs d = {d})", rho.powf(-1.0 / 6.0) * ts.last().unwrap().powf(2.0 / 3.0));
    println!("fitted exponent of W(N/2) in N (nonzero samples): {:.3}", num / den);
}

/// One sprinkling, two observers at rest: (chain length of A, fraction of A's elements shared with B,
/// window at A's middle element).
fn one_pair(rho: f64, d: f64, t: f64, seed: u64) -> (usize, f64, usize) {
    let mut rng = SplitMix(seed);
    let (u0, u1, v0, v1) = (-d, t, 0.0, t + d);
    let n = poisson(&mut rng, rho / 2.0 * (u1 - u0) * (v1 - v0));
    let mut a_pts = vec![(0.0, 0.0), (t, t)];
    let mut b_pts = vec![(-d, d), (t - d, t + d)];
    for _ in 0..n {
        let u = rng.unif(u0, u1);
        let v = rng.unif(v0, v1);
        if (0.0..=t).contains(&u) && (0.0..=t).contains(&v) {
            a_pts.push((u, v));
        }
        if (-d..=t - d).contains(&u) && (d..=t + d).contains(&v) {
            b_pts.push((u, v));
        }
    }
    let a = longest_chain(a_pts);
    let b = longest_chain(b_pts);
    let bs: std::collections::HashSet<(u64, u64)> = b.iter().map(|p| (p.0.to_bits(), p.1.to_bits())).collect();
    let shared = a.iter().filter(|p| bs.contains(&(p.0.to_bits(), p.1.to_bits()))).count();
    (a.len(), shared as f64 / a.len() as f64, window(&b, a[a.len() / 2]))
}

/// B5: distinguishability of two processes vs resolution. If maximal chains wander like
/// rho^(-1/6) T^(2/3), the shared fraction should depend on (rho, T, d) only through
/// x = d rho^(1/6) / T^(2/3): coalescence below x ~ 1, i.e. distinct only if rho >~ T^4 / d^6.
pub fn collapse(seeds: u64) {
    println!("B5: shared fraction of two maximal-chain worldlines vs x = d rho^(1/6) / T^(2/3)");
    println!("{:>6} {:>6} {:>8} {:>8} {:>8} {:>10} {:>14}", "rho", "T", "d", "x", "N", "shared", "W_mid/(N/2)");
    let combos: [(f64, f64); 6] = [(0.5, 1000.0), (0.5, 4000.0), (2.0, 500.0), (2.0, 2000.0), (8.0, 250.0), (8.0, 1000.0)];
    let xs = [0.1, 0.25, 0.5, 1.0, 2.0, 4.0];
    for &(rho, t) in &combos {
        for &x in &xs {
            let d = x * t.powf(2.0 / 3.0) * rho.powf(-1.0 / 6.0);
            let (mut nn, mut sh, mut ww) = (0.0, 0.0, 0.0);
            for s in 0..seeds {
                let (na, f, w) = one_pair(rho, d, t, 0xB5 ^ (s * 104729) ^ ((rho * 1000.0) as u64) ^ ((t as u64) << 20) ^ ((x * 100.0) as u64) << 40);
                nn += na as f64;
                sh += f;
                ww += w as f64 / (na as f64 / 2.0);
            }
            let k = seeds as f64;
            println!("{:>6.1} {:>6.0} {:>8.1} {:>8.2} {:>8.0} {:>10.3} {:>14.4}", rho, t, d, x, nn / k, sh / k, ww / k);
        }
    }
}
