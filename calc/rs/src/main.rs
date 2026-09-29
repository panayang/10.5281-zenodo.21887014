//! scd-calc: compute-heavy checks for SCD v2.
//!
//! `nerve`: horizon covers and contextuality (F9). For random families of events in a flat FRW
//! universe with an event horizon (d space dimensions), build the coexistence complex (the nerve
//! of the horizon footprints, F8), take its maximal simplices as the measurement contexts, and test
//! alpha-acyclicity by GYO reduction. By Vorob'ev (1962) / Beeri-Fagin-Maier-Yannakakis (1983),
//! locally consistent marginals always glue into a global law iff the context hypergraph is
//! alpha-acyclic. Prediction: d = 1 always acyclic (interval nerves are chordal); d >= 2 not.

mod chains;
mod geom;

use geom::{coexist, V};
use std::env;

pub struct SplitMix(pub u64);
impl SplitMix {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    pub fn unif(&mut self, a: f64, b: f64) -> f64 {
        a + (b - a) * ((self.next() >> 11) as f64 / (1u64 << 53) as f64)
    }
}

/// Coexistence complex on k <= 16 events as a table over bitmasks; None if any test was undecided.
fn nerve(c: &[V], r: &[f64], d: usize, eps: f64) -> Option<Vec<bool>> {
    let k = c.len();
    let n = 1usize << k;
    let mut simplex = vec![false; n];
    let mut buf = Vec::new();
    simplex[0] = true;
    let mut masks: Vec<usize> = (1..n).collect();
    masks.sort_by_key(|m| m.count_ones());
    for m in masks {
        let size = m.count_ones() as usize;
        // downward closure first: every facet must be a simplex
        let mut facets_ok = true;
        for i in 0..k {
            if m & (1 << i) != 0 && !simplex[m & !(1 << i)] {
                facets_ok = false;
                break;
            }
        }
        if !facets_ok {
            continue;
        }
        if size <= d + 1 {
            let idx: Vec<usize> = (0..k).filter(|i| m & (1 << i) != 0).collect();
            let cc: Vec<V> = idx.iter().map(|&i| c[i]).collect();
            let rr: Vec<f64> = idx.iter().map(|&i| r[i]).collect();
            match coexist(&cc, &rr, d, eps, &mut buf) {
                None => return None,
                Some(b) => simplex[m] = b,
            }
        } else {
            simplex[m] = true; // Helly: all (d+1)-subsets coexist (checked through the facets)
        }
    }
    Some(simplex)
}

fn maximal_simplices(simplex: &[bool], k: usize) -> Vec<usize> {
    (1..simplex.len())
        .filter(|&m| simplex[m] && (0..k).all(|i| m & (1 << i) != 0 || !simplex[m | (1 << i)]))
        .collect()
}

/// GYO reduction: alpha-acyclic iff the hypergraph reduces to at most one edge.
fn alpha_acyclic(edges: &[usize]) -> bool {
    let mut e: Vec<usize> = edges.to_vec();
    loop {
        let mut changed = false;
        // remove vertices that occur in exactly one edge
        let all: usize = e.iter().fold(0, |a, x| a | x);
        for v in 0..64 {
            let bit = 1usize << v;
            if all & bit == 0 {
                continue;
            }
            let cnt = e.iter().filter(|x| *x & bit != 0).count();
            if cnt == 1 {
                for x in e.iter_mut() {
                    *x &= !bit;
                }
                changed = true;
            }
        }
        // remove empty edges and edges contained in another edge
        let before = e.len();
        let mut keep = Vec::new();
        for (i, &x) in e.iter().enumerate() {
            let contained = x == 0
                || e.iter().enumerate().any(|(j, &y)| j != i && (x & y) == x && (x != y || j < i));
            if !contained {
                keep.push(x);
            }
        }
        if keep.len() != before {
            changed = true;
        }
        e = keep;
        if e.len() <= 1 {
            return true;
        }
        if !changed {
            return false;
        }
    }
}

fn run_nerve(d: usize, k: usize, spread: f64, trials: usize, seed: u64) {
    let mut rng = SplitMix(seed);
    let (mut ok, mut acyc, mut skipped, mut hollow_tri) = (0usize, 0usize, 0usize, 0usize);
    for _ in 0..trials {
        let mut c = vec![[0.0; 3]; k];
        let mut r = vec![0.0; k];
        for i in 0..k {
            for a in 0..d {
                c[i][a] = rng.unif(-spread, spread);
            }
            r[i] = rng.unif(0.3, 1.0); // footprint radius = |eta|
        }
        let Some(s) = nerve(&c, &r, d, 1e-9) else {
            skipped += 1;
            continue;
        };
        ok += 1;
        let edges = maximal_simplices(&s, k);
        if alpha_acyclic(&edges) {
            acyc += 1;
        }
        // any hollow triangle: all three pairs coexist, the triple does not
        let mut found = false;
        'outer: for a in 0..k {
            for b in (a + 1)..k {
                for cc in (b + 1)..k {
                    let (ab, bc, ac) = ((1 << a) | (1 << b), (1 << b) | (1 << cc), (1 << a) | (1 << cc));
                    if s[ab] && s[bc] && s[ac] && !s[ab | (1 << cc)] {
                        found = true;
                        break 'outer;
                    }
                }
            }
        }
        if found {
            hollow_tri += 1;
        }
    }
    println!(
        "d={d} k={k} spread={spread}: {ok} covers ({skipped} undecided); alpha-acyclic {acyc} ({:.2}%); with a hollow triangle {hollow_tri}",
        100.0 * acyc as f64 / ok.max(1) as f64
    );
}

fn self_test() {
    // GYO sanity: triangle {ab, bc, ca} is cyclic; path {ab, bc} and a filled triangle {abc} are acyclic.
    assert!(!alpha_acyclic(&[0b011, 0b110, 0b101]));
    assert!(alpha_acyclic(&[0b011, 0b110]));
    assert!(alpha_acyclic(&[0b111]));
    // 4-cycle {ab, bc, cd, da} is cyclic; with a chord's triangles {abc, acd} acyclic
    assert!(!alpha_acyclic(&[0b0011, 0b0110, 0b1100, 0b1001]));
    assert!(alpha_acyclic(&[0b0111, 0b1101]));
    println!("self-test: GYO reduction ok");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("nerve") => {
            self_test();
            let trials: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(20000);
            for &(d, k, spread) in &[(1, 8, 1.5), (1, 12, 2.5), (2, 8, 1.2), (2, 12, 1.8), (3, 8, 1.0), (3, 12, 1.4)] {
                run_nerve(d, k, spread, trials, 12345 + d as u64 * 100 + k as u64);
            }
        }
        Some("chains") => {
            let seeds: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(8);
            for &d in &[20.0, 100.0, 400.0] {
                chains::run(2.0, d, &[250.0, 500.0, 1000.0, 2000.0, 4000.0], seeds);
                println!();
            }
        }
        Some("collapse") => {
            let seeds: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(6);
            chains::collapse(seeds);
        }
        _ => eprintln!("usage: scd-calc nerve [trials] | chains [seeds] | collapse [seeds]"),
    }
}
