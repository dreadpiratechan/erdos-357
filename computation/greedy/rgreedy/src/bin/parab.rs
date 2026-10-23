//! parab: "parabola + bounded noise" search.
//! P_i = alpha*i^2 + e_i  (i = 0..k), alpha = 2E-1, e_i in [0,E).
//! Because alpha > 2(E-1), P is a Sidon set iff the planar set {(x^2, e_x)} is Sidon in Z^2, i.e. iff all
//! sums (x^2+y^2, e_x+e_y), 0<=x<=y<=k, are distinct.  Simulated annealing on the number of repeated keys.
//! Usage: parab k E iters seed [T0] [outfile]
use std::env;
use std::fs;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let k: usize = a[1].parse().unwrap(); // indices 0..=k  (k+1 points, k terms a_i)
    let e_max: usize = a[2].parse().unwrap();
    let iters: u64 = a[3].parse().unwrap();
    let seed: u64 = a[4].parse().unwrap();
    let t0: f64 = a.get(5).map(|s| s.parse().unwrap()).unwrap_or(0.35);
    let out = a.get(6).cloned();
    let npts = k + 1;
    let tw = 2 * e_max - 1; // possible values of e_x+e_y
    let smax = 2 * k * k + 1;
    let mut cnt = vec![0u8; smax * tw];
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut e: Vec<usize> = (0..npts).map(|_| rng.below(e_max as u64) as usize).collect();
    let sq: Vec<usize> = (0..npts).map(|x| x * x).collect();
    let key = |x: usize, y: usize, ex: usize, ey: usize| -> usize { (sq[x] + sq[y]) * tw + ex + ey };
    // initial violations
    let mut v: i64 = 0;
    for x in 0..npts {
        for y in x..npts {
            let kk = key(x, y, e[x], e[y]);
            v += cnt[kk] as i64;
            cnt[kk] += 1;
        }
    }
    let mut best = v;
    let mut temp = t0;
    let cool = (0.02f64 / t0).powf(1.0 / iters as f64);
    let mut it = 0u64;
    while it < iters && v > 0 {
        it += 1;
        temp *= cool;
        let x = rng.below(npts as u64) as usize;
        let old = e[x];
        let mut nw = rng.below(e_max as u64) as usize;
        if nw == old {
            nw = (nw + 1) % e_max;
            if e_max == 1 {
                continue;
            }
        }
        // remove old keys
        let mut dv: i64 = 0;
        for y in 0..npts {
            let (lo, hi) = if y < x { (y, x) } else { (x, y) };
            let ey = if y == x { old } else { e[y] };
            let kk = key(lo, hi, if lo == x { old } else { e[lo] }, if hi == x { old } else { e[hi] });
            let _ = ey;
            cnt[kk] -= 1;
            dv -= cnt[kk] as i64;
        }
        e[x] = nw;
        for y in 0..npts {
            let (lo, hi) = if y < x { (y, x) } else { (x, y) };
            let kk = key(lo, hi, e[lo], e[hi]);
            dv += cnt[kk] as i64;
            cnt[kk] += 1;
        }
        if dv <= 0 || rng.unit() < (-(dv as f64) / temp).exp() {
            v += dv;
            if v < best {
                best = v;
            }
        } else {
            // revert
            for y in 0..npts {
                let (lo, hi) = if y < x { (y, x) } else { (x, y) };
                let kk = key(lo, hi, e[lo], e[hi]);
                cnt[kk] -= 1;
            }
            e[x] = old;
            for y in 0..npts {
                let (lo, hi) = if y < x { (y, x) } else { (x, y) };
                let kk = key(lo, hi, e[lo], e[hi]);
                cnt[kk] += 1;
            }
        }
        if it % 2_000_000 == 0 {
            eprintln!("  it={} V={} best={} T={:.3}", it, v, best, temp);
        }
    }
    println!("parab k={} E={} seed={} iters={} V={} best={}", k, e_max, seed, it, v, best);
    if v == 0 {
        // independent verification: build the actual sequence a_i and sort all block sums
        let alpha = (2 * e_max - 1) as i64;
        let p: Vec<i64> = (0..npts).map(|i| alpha * (i as i64) * (i as i64) + e[i] as i64 - e[0] as i64).collect();
        let seq: Vec<i64> = (1..npts).map(|i| p[i] - p[i - 1]).collect();
        let inc = seq.windows(2).all(|w| w[0] < w[1]) && seq[0] >= 1;
        let mut sums: Vec<i64> = Vec::with_capacity(npts * (npts - 1) / 2);
        for i in 0..npts {
            for j in (i + 1)..npts {
                sums.push(p[j] - p[i]);
            }
        }
        sums.sort_unstable();
        let distinct = sums.windows(2).all(|w| w[0] != w[1]);
        let n = *seq.last().unwrap();
        println!("VERIFIED increasing={} distinct_block_sums={} k_terms={} max_term={} k/sqrt(max)={:.4}", inc, distinct, seq.len(), n, seq.len() as f64 / (n as f64).sqrt());
        if let Some(f) = out {
            let s: Vec<String> = seq.iter().map(|x| x.to_string()).collect();
            fs::write(f, s.join(",") + "\n").unwrap();
        }
    }
}
