//! P4 test (D20): is transitive percolation closed under coarse-graining?
//!
//! TP(p): elements 0..n-1 are born in order; each pair i < j gets an edge with probability p
//! independently; the order is the transitive closure. P(i < j) depends only on the elements
//! between i and j, so statistics taken in the middle of a sample have no boundary effects.
//! Coarse-graining here: keep each element independently with probability q, take the induced order.
//! Fit p' to the thinned sample by the neighbour relation probability r_1, then compare every other
//! statistic with TP(p'): r_k for k = 1..8, and the 7 relation patterns of three consecutive elements
//! (patterns are sensitive to the hidden common causes the removed elements leave behind).
//! Closure under thinning would make all differences vanish within errors.

use crate::SplitMix;

const K: usize = 8;

struct Order {
    words: usize,
    past: Vec<u64>, // row j: bitset of i < j with i < j in the order
}

impl Order {
    fn tp(n: usize, p: f64, rng: &mut SplitMix) -> Order {
        let words = (n + 63) / 64;
        let mut past = vec![0u64; n * words];
        let thr = (p * (u64::MAX as f64)) as u64;
        for j in 0..n {
            for i in 0..j {
                if rng.next() < thr {
                    // past[j] |= past[i] | {i}
                    let (lo, hi) = past.split_at_mut(j * words);
                    let pi = &lo[i * words..(i + 1) * words];
                    let pj = &mut hi[..words];
                    for w in 0..words {
                        pj[w] |= pi[w];
                    }
                    pj[i / 64] |= 1u64 << (i % 64);
                }
            }
        }
        Order { words, past }
    }
    fn less(&self, i: usize, j: usize) -> bool {
        // i < j in labels assumed
        self.past[j * self.words + i / 64] >> (i % 64) & 1 == 1
    }
}

#[derive(Clone, Default)]
struct Stats {
    rk: [u64; K],
    rk_n: [u64; K],
    pat: [u64; 8],
    pat_n: u64,
}

impl Stats {
    fn add(&mut self, o: &Order, idx: &[usize]) {
        let m = idx.len();
        let (a0, a1) = (m / 4, 3 * m / 4);
        for t in a0..a1 {
            for k in 1..=K {
                if t + k < m {
                    self.rk_n[k - 1] += 1;
                    if o.less(idx[t], idx[t + k]) {
                        self.rk[k - 1] += 1;
                    }
                }
            }
            if t + 2 < m {
                let (a, b, c) = (idx[t], idx[t + 1], idx[t + 2]);
                let code = (o.less(a, b) as usize) << 2 | (o.less(b, c) as usize) << 1 | (o.less(a, c) as usize);
                self.pat[code] += 1;
                self.pat_n += 1;
            }
        }
    }
    fn merge(&mut self, o: &Stats) {
        for k in 0..K {
            self.rk[k] += o.rk[k];
            self.rk_n[k] += o.rk_n[k];
        }
        for c in 0..8 {
            self.pat[c] += o.pat[c];
        }
        self.pat_n += o.pat_n;
    }
    /// statistic vector: r_1..r_K then the 7 admissible pattern probabilities
    fn vector(&self) -> Vec<(f64, f64)> {
        let mut v = Vec::new();
        for k in 0..K {
            let n = self.rk_n[k] as f64;
            let p = self.rk[k] as f64 / n;
            v.push((p, (p * (1.0 - p) / n).sqrt()));
        }
        for &c in &[0usize, 4, 2, 1, 5, 3, 7] {
            let n = self.pat_n as f64;
            let p = self.pat[c] as f64 / n;
            v.push((p, (p * (1.0 - p) / n).sqrt()));
        }
        v
    }
}

fn labels() -> Vec<String> {
    let mut l: Vec<String> = (1..=K).map(|k| format!("r_{k}")).collect();
    for s in ["none", "ab", "bc", "ac", "ab+ac", "bc+ac", "chain"] {
        l.push(format!("pat {s}"));
    }
    l
}

fn collect(threads: u64, samples: u64, f: impl Fn(u64) -> Stats + Sync) -> Stats {
    let parts: Vec<Stats> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|w| {
                let f = &f;
                sc.spawn(move || {
                    let mut acc = Stats::default();
                    let mut s = w;
                    while s < samples {
                        acc.merge(&f(s));
                        s += threads;
                    }
                    acc
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut tot = Stats::default();
    for p in &parts {
        tot.merge(p);
    }
    tot
}

pub fn run(p: f64, q: f64, n_kept: usize, samples: u64) {
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4) as u64;
    let n_full = (n_kept as f64 / q).round() as usize;
    // thinned TP(p)
    let thin = collect(threads, samples, |s| {
        let mut rng = SplitMix(0x7EA1 ^ (s * 7919) ^ ((p * 1e6) as u64) << 20 ^ ((q * 1e6) as u64) << 40);
        let o = Order::tp(n_full, p, &mut rng);
        let idx: Vec<usize> = (0..n_full).filter(|_| rng.unif(0.0, 1.0) < q).collect();
        let mut st = Stats::default();
        st.add(&o, &idx);
        st
    });
    let tv = thin.vector();
    // direct TP(p') on a wide grid; choose p' minimising chi^2 over ALL statistics
    let grid: Vec<f64> = (0..31).map(|i| p * (0.4 * (1.08f64).powi(i))).collect();
    let direct: Vec<Vec<(f64, f64)>> = grid
        .iter()
        .map(|&pp| {
            collect(threads, samples, |s| {
                let mut rng = SplitMix(0xD1EC ^ (s * 104729) ^ ((pp * 1e7) as u64) << 20);
                let o = Order::tp(n_kept, pp, &mut rng);
                let idx: Vec<usize> = (0..n_kept).collect();
                let mut st = Stats::default();
                st.add(&o, &idx);
                st
            })
            .vector()
        })
        .collect();
    let chi2 = |d: &Vec<(f64, f64)>| -> f64 {
        tv.iter()
            .zip(d)
            .map(|(a, b)| {
                let se2 = a.1 * a.1 + b.1 * b.1;
                if se2 > 0.0 { (a.0 - b.0).powi(2) / se2 } else { 0.0 }
            })
            .sum()
    };
    let chis: Vec<f64> = direct.iter().map(|d| chi2(d)).collect();
    let bi = (0..grid.len()).min_by(|&i, &j| chis[i].partial_cmp(&chis[j]).unwrap()).unwrap();
    let dof = tv.len() as f64 - 1.0;
    let r1i = (0..grid.len())
        .min_by(|&i, &j| (direct[i][0].0 - tv[0].0).abs().partial_cmp(&(direct[j][0].0 - tv[0].0).abs()).unwrap())
        .unwrap();
    println!("TP(p = {p}) thinned with q = {q} (about {n_kept} kept of {n_full}), {samples} samples");
    println!("best p' over all 15 statistics = {:.5}: chi^2 = {:.1} for {} degrees of freedom", grid[bi], chis[bi], dof);
    println!("p' matching r_1 alone ~ {:.5}: chi^2 = {:.1}", grid[r1i], chis[r1i]);
    println!("{:>10} {:>10} {:>12} {:>8}", "statistic", "thinned", "TP(best p')", "z");
    for (i, name) in labels().iter().enumerate() {
        let se = (tv[i].1.powi(2) + direct[bi][i].1.powi(2)).sqrt();
        println!("{:>10} {:>10.5} {:>12.5} {:>+8.1}", name, tv[i].0, direct[bi][i].0, (tv[i].0 - direct[bi][i].0) / se.max(1e-12));
    }
    println!();
}
