//! B/D15: a process determined by its past, not by a future endpoint.
//!
//! 1+1 sprinkling of the future of an origin event, light-cone coordinates (u, v), unit density
//! (density 1/2 per du dv). The height H(y) = length of the longest chain from the origin to y is
//! computed for every point (Fenwick tree over v-ranks, O(n log n)). The process starts at the
//! origin and at each step moves to the element y > p in its near future (the interval between p and y
//! contains at most K points, counted, and y lies within a local box) that maximises H(y): it keeps
//! the largest proper time from where it began, using only the past. We measure how far its path
//! strays from the chord joining its start and its position at time T (the same statistic as F12
//! for longest chains between endpoints), for T spanning a decade.

use crate::SplitMix;

fn gauss(rng: &mut SplitMix) -> f64 {
    let u1 = rng.unif(1e-300, 1.0);
    let u2 = rng.unif(0.0, 1.0);
    (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos()
}

struct Fenwick(Vec<u32>);
impl Fenwick {
    fn update(&mut self, mut i: usize, v: u32) {
        i += 1;
        while i < self.0.len() {
            if self.0[i] < v {
                self.0[i] = v;
            }
            i += i & i.wrapping_neg();
        }
    }
    fn query(&self, mut i: usize) -> u32 {
        // max over positions [0, i)
        let mut r = 0;
        while i > 0 {
            r = r.max(self.0[i]);
            i -= i & i.wrapping_neg();
        }
        r
    }
}

/// One run: returns (steps, time reached, transverse deviation at half time) for each checkpoint time.
fn one_run(seed: u64, s: f64, k_max: usize, h: f64, checkpoints: &[f64]) -> Vec<Option<f64>> {
    let mut rng = SplitMix(seed);
    let mean = 0.5 * s * s;
    let n = (mean + gauss(&mut rng) * mean.sqrt()).round() as usize;
    let mut pts: Vec<(f64, f64)> = (0..n).map(|_| (rng.unif(0.0, s), rng.unif(0.0, s))).collect();
    pts.push((0.0, 0.0));
    pts.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().then(a.1.partial_cmp(&b.1).unwrap()));
    let n = pts.len();
    // heights from the origin (index of origin = 0 after sorting, u = v = 0)
    let mut vs: Vec<f64> = pts.iter().map(|p| p.1).collect();
    vs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let rank = |v: f64| vs.partition_point(|&x| x < v);
    let mut fw = Fenwick(vec![0; n + 1]);
    let mut height = vec![0u32; n];
    // process in u order; points with equal u are not comparable (measure zero)
    for i in 0..n {
        let r = rank(pts[i].1);
        let hgt = if i == 0 { 1 } else { fw.query(r) + 1 };
        height[i] = hgt;
        fw.update(r, hgt);
    }
    // spatial index: points sorted by u already; for the local search scan u in (u_p, u_p + h]
    let mut path: Vec<(f64, f64)> = vec![(0.0, 0.0)];
    let mut cur = 0usize;
    loop {
        let (up, vp) = pts[cur];
        let start = pts.partition_point(|q| q.0 <= up);
        let end = pts.partition_point(|q| q.0 <= up + h);
        let cands: Vec<usize> = (start..end).filter(|&j| pts[j].1 > vp && pts[j].1 <= vp + h).collect();
        let mut best: Option<(u32, usize, usize)> = None; // (height, -interval count, index)
        for &j in &cands {
            let (uj, vj) = pts[j];
            let inside = cands.iter().filter(|&&m| m != j && pts[m].0 < uj && pts[m].1 < vj).count();
            if inside > k_max {
                continue;
            }
            let key = (height[j], usize::MAX - inside, j);
            if best.map_or(true, |b| (key.0, key.1) > (b.0, b.1)) {
                best = Some(key);
            }
        }
        match best {
            None => break,
            Some((_, _, j)) => {
                cur = j;
                path.push(pts[j]);
            }
        }
        let t = 0.5 * (pts[cur].0 + pts[cur].1);
        if t > *checkpoints.last().unwrap() || pts[cur].0 > s - h || pts[cur].1 > s - h {
            break;
        }
    }
    // deviation from the chord between the origin and the point reached at each checkpoint time
    checkpoints
        .iter()
        .map(|&tc| {
            let idx = path.iter().position(|p| 0.5 * (p.0 + p.1) >= tc)?;
            let (ue, ve) = path[idx];
            let (te, xe) = (0.5 * (ue + ve), 0.5 * (ve - ue));
            // point of the path at half the time
            let mid = path.iter().position(|p| 0.5 * (p.0 + p.1) >= te / 2.0)?;
            let (um, vm) = path[mid];
            let (tm, xm) = (0.5 * (um + vm), 0.5 * (vm - um));
            let x_chord = xe * tm / te;
            // distance measured in the rest frame of the chord (boost by its rapidity)
            let beta = xe / te;
            let gamma = 1.0 / (1.0 - beta * beta).sqrt();
            Some(gamma * ((xm - x_chord) - beta * 0.0))
        })
        .collect()
}

pub fn run(seeds: u64) {
    let checkpoints = [50.0, 100.0, 200.0, 400.0, 800.0];
    let s = 1.25 * 2.0 * checkpoints.last().unwrap() + 20.0;
    println!("past-determined process in 1+1 (maximise the height from the origin within the near future)");
    for &(k_max, h) in &[(0usize, 6.0), (4, 8.0), (16, 12.0)] {
        let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4) as u64;
        let all: Vec<Vec<Option<f64>>> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..threads)
                .map(|w| {
                    sc.spawn(move || {
                        let mut out = Vec::new();
                        let mut sd = w;
                        while sd < seeds {
                            out.push(one_run(0x6EED ^ (sd * 7919) ^ ((k_max as u64) << 40), s, k_max, h, &checkpoints));
                            sd += threads;
                        }
                        out
                    })
                })
                .collect();
            hs.into_iter().flat_map(|x| x.join().unwrap()).collect()
        });
        println!("K = {k_max} (interval count bound), local box h = {h}");
        println!("{:>8} {:>8} {:>12}", "T", "runs", "rms dev");
        let mut logs = Vec::new();
        for (ci, &tc) in checkpoints.iter().enumerate() {
            let devs: Vec<f64> = all.iter().filter_map(|r| r[ci]).collect();
            if devs.is_empty() {
                continue;
            }
            let rms = (devs.iter().map(|d| d * d).sum::<f64>() / devs.len() as f64).sqrt();
            println!("{:>8.0} {:>8} {:>12.4}", tc, devs.len(), rms);
            logs.push((tc.ln(), rms.ln()));
        }
        let n = logs.len() as f64;
        let (sx, sy) = logs.iter().fold((0.0, 0.0), |a, p| (a.0 + p.0, a.1 + p.1));
        let (mx, my) = (sx / n, sy / n);
        let (num, den) = logs.iter().fold((0.0, 0.0), |a, p| (a.0 + (p.0 - mx) * (p.1 - my), a.1 + (p.0 - mx).powi(2)));
        println!("fitted exponent: {:.3}   (longest chains between endpoints: 2/3)\n", num / den);
    }
}
