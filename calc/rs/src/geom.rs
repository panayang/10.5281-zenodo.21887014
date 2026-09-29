//! Horizon footprints and the exact coexistence test (F8).
//!
//! In flat FRW with bounded conformal time, shifted so eta_max = 0, the future of an event
//! (eta, x) meets future conformal infinity in the open ball B(x, -eta). A family of events has a
//! common future iff its footprints meet. For closed balls, a nonempty intersection has a leftmost
//! point (minimal first coordinate) which is the leftmost point of one ball, the leftmost point of
//! the circle where two spheres meet, or a point where three spheres meet (d = 3); in d = 2 the
//! two-sphere case is the pair of circle intersection points. Checking those candidates is exact.

pub type V = [f64; 3];

fn sub(a: &V, b: &V) -> V {
    [a[0] - b[0], a[1] - b[1], a[2] - b[2]]
}
fn add(a: &V, b: &V) -> V {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2]]
}
fn scale(a: &V, s: f64) -> V {
    [a[0] * s, a[1] * s, a[2] * s]
}
fn dot(a: &V, b: &V) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
}
fn norm(a: &V) -> f64 {
    dot(a, a).sqrt()
}
fn cross(a: &V, b: &V) -> V {
    [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
}

/// Candidate leftmost points of the intersection of the balls (c[i], r[i]) in dimension d (1..=3).
fn candidates(c: &[V], r: &[f64], d: usize, out: &mut Vec<V>) {
    out.clear();
    let n = c.len();
    let e1: V = [1.0, 0.0, 0.0];
    for i in 0..n {
        out.push(sub(&c[i], &scale(&e1, r[i])));
    }
    if d >= 2 {
        for i in 0..n {
            for j in (i + 1)..n {
                let v = sub(&c[j], &c[i]);
                let l = norm(&v);
                if l == 0.0 || l > r[i] + r[j] || l < (r[i] - r[j]).abs() {
                    continue;
                }
                let a = (r[i] * r[i] - r[j] * r[j] + l * l) / (2.0 * l);
                let rho = (r[i] * r[i] - a * a).max(0.0).sqrt();
                let nrm = scale(&v, 1.0 / l);
                let cc = add(&c[i], &scale(&nrm, a));
                if d == 2 {
                    let t: V = [-nrm[1], nrm[0], 0.0];
                    out.push(add(&cc, &scale(&t, rho)));
                    out.push(sub(&cc, &scale(&t, rho)));
                } else {
                    let w = sub(&e1, &scale(&nrm, dot(&e1, &nrm)));
                    let wl = norm(&w);
                    if wl < 1e-15 {
                        out.push(cc);
                    } else {
                        out.push(sub(&cc, &scale(&w, rho / wl)));
                    }
                }
            }
        }
    }
    if d == 3 {
        for i in 0..n {
            for j in (i + 1)..n {
                for k in (j + 1)..n {
                    three_spheres(&c[i], r[i], &c[j], r[j], &c[k], r[k], out);
                }
            }
        }
    }
}

fn three_spheres(c1: &V, r1: f64, c2: &V, r2: f64, c3: &V, r3: f64, out: &mut Vec<V>) {
    let ex0 = sub(c2, c1);
    let dd = norm(&ex0);
    if dd == 0.0 {
        return;
    }
    let ex = scale(&ex0, 1.0 / dd);
    let i_ = dot(&ex, &sub(c3, c1));
    let ey0 = sub(&sub(c3, c1), &scale(&ex, i_));
    let eyn = norm(&ey0);
    if eyn == 0.0 {
        return;
    }
    let ey = scale(&ey0, 1.0 / eyn);
    let ez = cross(&ex, &ey);
    let j_ = dot(&ey, &sub(c3, c1));
    let x = (r1 * r1 - r2 * r2 + dd * dd) / (2.0 * dd);
    let y = (r1 * r1 - r3 * r3 + i_ * i_ + j_ * j_) / (2.0 * j_) - i_ * x / j_;
    let z2 = r1 * r1 - x * x - y * y;
    if z2 < 0.0 {
        return;
    }
    let z = z2.sqrt();
    let base = add(&add(c1, &scale(&ex, x)), &scale(&ey, y));
    out.push(add(&base, &scale(&ez, z)));
    out.push(sub(&base, &scale(&ez, z)));
}

fn balls_meet(c: &[V], r: &[f64], d: usize, buf: &mut Vec<V>) -> bool {
    candidates(c, r, d, buf);
    buf.iter().any(|p| c.iter().zip(r).all(|(ci, ri)| norm(&sub(ci, p)) <= ri + 1e-12))
}

/// Some(true/false), or None if the answer changes within +-eps of the radii.
pub fn coexist(c: &[V], r: &[f64], d: usize, eps: f64, buf: &mut Vec<V>) -> Option<bool> {
    let rl: Vec<f64> = r.iter().map(|x| x + eps).collect();
    let rt: Vec<f64> = r.iter().map(|x| x - eps).collect();
    let loose = balls_meet(c, &rl, d, buf);
    let tight = balls_meet(c, &rt, d, buf);
    if loose == tight {
        Some(tight)
    } else {
        None
    }
}
