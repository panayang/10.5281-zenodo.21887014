//! D20 step 3: do covariance (P2) and Bell causality (P3) survive coarse-graining?
//!
//! Grow transitive percolation TP(p) from the empty order, keep each element with probability q, and
//! look at the growth process formed by the first retained elements (a labelled sequence, like a
//! CSG process). Tests:
//!  P2 covariance: every natural labelling of the same unlabelled 4-element order is equally likely
//!     (chi^2 of uniformity within each isomorphism class).
//!  P3 Bell causality: the ratio P(new past = {1}) / P(new past = {}) must be the same whether the
//!     existing order is {1}, the antichain {1, 2} or the chain 1 < 2 (the union of the two pasts is {1}).
//!  No signalling: P(new element above 1) must not change when an element unrelated to 1 is present.
//! q = 1 is TP itself (a CSG model) and must pass every test.

use crate::SplitMix;
use std::collections::HashMap;

const NR: usize = 4; // retained elements examined

/// Relations among the first NR retained elements: bit (i, j) for i < j set if i precedes j.
fn one_run(p: f64, q: f64, rng: &mut SplitMix) -> u16 {
    let thr = (p * (u64::MAX as f64)) as u64;
    let qthr = (q * (u64::MAX as f64)) as u64;
    // underlying elements: past bitsets over underlying labels (u128 is enough: we stop early)
    let mut past: Vec<u128> = Vec::new();
    let mut kept: Vec<usize> = Vec::new();
    while kept.len() < NR {
        let j = past.len();
        if j >= 127 {
            break;
        }
        let mut pj: u128 = 0;
        for i in 0..j {
            if rng.next() < thr {
                pj |= past[i] | (1u128 << i);
            }
        }
        past.push(pj);
        if rng.next() < qthr {
            kept.push(j);
        }
    }
    let mut code: u16 = 0;
    let mut bit = 0;
    for a in 0..NR {
        for b in (a + 1)..NR {
            if a < kept.len() && b < kept.len() && past[kept[b]] >> kept[a] & 1 == 1 {
                code |= 1 << bit;
            }
            bit += 1;
        }
    }
    code
}

fn rel(code: u16, a: usize, b: usize) -> bool {
    // a < b
    let mut bit = 0;
    for x in 0..NR {
        for y in (x + 1)..NR {
            if x == a && y == b {
                return code >> bit & 1 == 1;
            }
            bit += 1;
        }
    }
    unreachable!()
}

/// Canonical form of an unlabelled order on 4 elements: minimal relation matrix over all permutations.
fn canon4(code: u16) -> u16 {
    let mut m = [[false; 4]; 4];
    for a in 0..4 {
        for b in (a + 1)..4 {
            m[a][b] = rel(code, a, b);
        }
    }
    let perms: Vec<[usize; 4]> = {
        let mut v = Vec::new();
        for a in 0..4 { for b in 0..4 { for c in 0..4 { for d in 0..4 {
            let p = [a, b, c, d];
            let mut s = [false; 4];
            if p.iter().all(|&x| { let r = !s[x]; s[x] = true; r }) { v.push(p); }
        }}}}
        v
    };
    let mut best = u16::MAX;
    for pm in perms {
        let mut c: u16 = 0;
        let mut bit = 0;
        for x in 0..4 {
            for y in 0..4 {
                if x != y {
                    let (a, b) = (pm[x], pm[y]);
                    let r = if a < b { m[a][b] } else { false };
                    if r { c |= 1 << bit; }
                    bit += 1;
                }
            }
        }
        best = best.min(c);
    }
    best
}

pub fn run(p: f64, q: f64, samples: u64) {
    let threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4) as u64;
    let counts: HashMap<u16, u64> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..threads)
            .map(|w| {
                sc.spawn(move || {
                    let mut rng = SplitMix(0xC0B ^ (w * 7919) ^ ((p * 1e6) as u64) << 24 ^ ((q * 1e6) as u64) << 44);
                    let mut h: HashMap<u16, u64> = HashMap::new();
                    let per = samples / threads;
                    for _ in 0..per {
                        *h.entry(one_run(p, q, &mut rng)).or_insert(0) += 1;
                    }
                    h
                })
            })
            .collect();
        let mut tot: HashMap<u16, u64> = HashMap::new();
        for hh in hs {
            for (k, v) in hh.join().unwrap() {
                *tot.entry(k).or_insert(0) += v;
            }
        }
        tot
    });
    let total: u64 = counts.values().sum();
    // marginal counts over the first 2 and first 3 elements
    let c2 = |r12: bool| counts.iter().filter(|(k, _)| rel(**k, 0, 1) == r12).map(|(_, v)| *v).sum::<u64>();
    let c3 = |r12: bool, r13: bool, r23: bool| {
        counts
            .iter()
            .filter(|(k, _)| rel(**k, 0, 1) == r12 && rel(**k, 0, 2) == r13 && rel(**k, 1, 2) == r23)
            .map(|(_, v)| *v)
            .sum::<u64>()
    };
    println!("TP(p = {p}) thinned with q = {q}: {total} runs");
    // P2: one 2-chain plus one isolated element, three natural labellings
    let (l12, l13, l23) = (c3(true, false, false), c3(false, true, false), c3(false, false, true));
    let mean = (l12 + l13 + l23) as f64 / 3.0;
    let chi = [l12, l13, l23].iter().map(|&x| (x as f64 - mean).powi(2) / mean).sum::<f64>();
    println!("  P2 (3 elements, chain + isolated): {{1<2}} {:.5}  {{1<3}} {:.5}  {{2<3}} {:.5}   chi^2 = {:.1} (2 dof)",
        l12 as f64 / total as f64, l13 as f64 / total as f64, l23 as f64 / total as f64, chi);
    // P2: 4-element classes
    let mut classes: HashMap<u16, Vec<u64>> = HashMap::new();
    for (k, v) in &counts {
        classes.entry(canon4(*k)).or_default().push(*v);
    }
    let (mut chi4, mut dof4) = (0.0, 0usize);
    for v in classes.values() {
        if v.len() < 2 {
            continue;
        }
        let m = v.iter().sum::<u64>() as f64 / v.len() as f64;
        if m < 50.0 {
            continue;
        }
        chi4 += v.iter().map(|&x| (x as f64 - m).powi(2) / m).sum::<f64>();
        dof4 += v.len() - 1;
    }
    println!("  P2 (4 elements, all classes with several natural labellings): chi^2 = {:.1} for {} dof", chi4, dof4);
    // P3: Bell ratio past {1} vs past {} with existing order {1}, antichain {1,2}, chain 1<2
    let r_single = c2(true) as f64 / c2(false) as f64;
    let r_anti = c3(false, true, false) as f64 / c3(false, false, false) as f64;
    let r_chain = c3(true, true, false) as f64 / c3(true, false, false) as f64; // past {1} in chain means 3>1, not 3>2
    let se = |a: u64, b: u64| ((1.0 / a as f64) + (1.0 / b as f64)).sqrt(); // relative s.e. of a ratio
    println!("  P3 Bell ratio P(past={{1}})/P(past={{}}): given {{1}}: {:.5}   given antichain {{1,2}}: {:.5}   given chain 1<2: {:.5}",
        r_single, r_anti, r_chain);
    println!("      relative differences from the {{1}} case: antichain {:+.4} (+- {:.4}), chain {:+.4} (+- {:.4})",
        r_anti / r_single - 1.0, se(c3(false, true, false), c3(false, false, false)),
        r_chain / r_single - 1.0, se(c3(true, true, false), c3(true, false, false)));
    // no signalling: P(new above 1) after {1} vs after antichain {1,2}
    let p_after1 = c2(true) as f64 / total as f64;
    let n_anti = c3(false, true, false) + c3(false, false, false) + c3(false, true, true) + c3(false, false, true);
    let p_after_anti = (c3(false, true, false) + c3(false, true, true)) as f64 / n_anti as f64;
    println!("  no signalling: P(new above 1 | {{1}}) = {:.5}   P(new above 1 | antichain {{1,2}}) = {:.5}", p_after1, p_after_anti);
    println!();
}
