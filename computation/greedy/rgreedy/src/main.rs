//! rgreedy: greedy constructions for Erdos problem 357 (distinct consecutive-block sums).
//!
//! A strictly increasing set a_1 < ... < a_k is valid when all block sums a_u + .. + a_v
//! are pairwise distinct.  Equivalently the prefix sums {P_0..P_k} form a Sidon set.
//!
//! Modes
//!   rev n [--mod q --res r1,r2,..] [--dump file]   reverse greedy: scan x = n..1, keep x iff valid
//!   fwd n [--dump file]                            forward greedy: scan x = 1..n, keep x as new max
//!   verify file                                    independent check (sort all block sums)
//!   brute n                                        exhaustive f(n) for tiny n (oracle)
//!
//! Memory: sums are stored in an open-addressing table with 5-byte slots (values < 2^40).

use std::env;
use std::fs::File;
use std::io::{BufWriter, Read, Write};
use std::time::Instant;

#[derive(Clone)]
struct Table {
    bits: u32,
    mask: u64,
    data: Vec<u8>,
    count: u64,
}

impl Table {
    fn new(bits: u32) -> Table {
        let cap = 1u64 << bits;
        Table { bits, mask: cap - 1, data: vec![0u8; (cap as usize) * 5 + 16], count: 0 }
    }
    #[inline(always)]
    fn h(&self, v: u64) -> u64 {
        (v.wrapping_mul(0x9E37_79B9_7F4A_7C15)) >> (64 - self.bits)
    }
    #[inline(always)]
    fn slot(&self, i: u64) -> u64 {
        unsafe {
            let p = self.data.as_ptr().add((i as usize) * 5) as *const u64;
            p.read_unaligned() & 0xFF_FFFF_FFFF
        }
    }
    #[inline(always)]
    fn set_slot(&mut self, i: u64, key: u64) {
        unsafe {
            let p = self.data.as_mut_ptr().add((i as usize) * 5);
            let b = key.to_le_bytes();
            std::ptr::copy_nonoverlapping(b.as_ptr(), p, 5);
        }
    }
    #[inline(always)]
    fn prefetch(&self, v: u64) {
        #[cfg(target_arch = "x86_64")]
        unsafe {
            let i = self.h(v);
            let p = self.data.as_ptr().add((i as usize) * 5);
            core::arch::x86_64::_mm_prefetch(p as *const i8, core::arch::x86_64::_MM_HINT_T0);
        }
    }
    #[inline(always)]
    fn contains(&self, v: u64) -> bool {
        let key = v + 1;
        let mut i = self.h(v);
        loop {
            let s = self.slot(i);
            if s == 0 {
                return false;
            }
            if s == key {
                return true;
            }
            i = (i + 1) & self.mask;
        }
    }
    #[inline(always)]
    fn insert(&mut self, v: u64) -> bool {
        // returns true if newly inserted, false if already present
        let key = v + 1;
        assert!(key < (1u64 << 40), "value exceeds 40 bits");
        let mut i = self.h(v);
        loop {
            let s = self.slot(i);
            if s == 0 {
                self.set_slot(i, key);
                self.count += 1;
                return true;
            }
            if s == key {
                return false;
            }
            i = (i + 1) & self.mask;
        }
    }
}

fn arg_val(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn auto_bits(n: u64, cmax: f64) -> u32 {
    let k = cmax * (n as f64).sqrt();
    let e = k * k / 2.0 + 1000.0;
    let want = e / 0.55;
    let mut b = 12;
    while ((1u64 << b) as f64) < want {
        b += 1;
    }
    b
}

fn fnv(seq: &[u64]) -> u64 {
    // FNV-1a 64 over decimal text "a,b,c" - a quick fingerprint; the python side computes sha256.
    let mut h: u64 = 0xcbf29ce484222325;
    for (i, &x) in seq.iter().enumerate() {
        if i > 0 {
            h ^= b',' as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        for ch in x.to_string().bytes() {
            h ^= ch as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
    }
    h
}

fn dump(path: &str, seq: &[u64]) {
    let f = File::create(path).expect("create dump");
    let mut w = BufWriter::new(f);
    let strs: Vec<String> = seq.iter().map(|x| x.to_string()).collect();
    writeln!(w, "{}", strs.join(",")).unwrap();
}

fn read_set(path: &str) -> Vec<u64> {
    let mut s = String::new();
    File::open(path).expect("open").read_to_string(&mut s).unwrap();
    s.trim().split(',').filter(|t| !t.is_empty()).map(|t| t.trim().parse::<u64>().unwrap()).collect()
}

/// Independent verification: sort every block sum, require strict increase.
fn verify(seq: &[u64]) -> bool {
    let k = seq.len();
    if k == 0 {
        return true;
    }
    if seq[0] < 1 {
        return false;
    }
    for i in 1..k {
        if seq[i] <= seq[i - 1] {
            return false;
        }
    }
    let mut pre = vec![0u64; k + 1];
    for i in 0..k {
        pre[i + 1] = pre[i] + seq[i];
    }
    let mut sums: Vec<u64> = Vec::with_capacity(k * (k + 1) / 2);
    for i in 0..k {
        for j in (i + 1)..=k {
            sums.push(pre[j] - pre[i]);
        }
    }
    sums.sort_unstable();
    for i in 1..sums.len() {
        if sums[i] == sums[i - 1] {
            return false;
        }
    }
    true
}

struct Stats {
    probes: u64,
    accepts: u64,
    rejects: u64,
}

fn run_rev(n: u64, filt: Option<(u64, Vec<bool>)>, forbid: &[(u64, u64)], skip: f64, seed: u64, bits: u32) -> (Vec<u64>, Stats, Table) {
    let mut rng: u64 = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut t = Table::new(bits);
    let mut c: Vec<u64> = vec![0];
    let mut acc: Vec<u64> = Vec::new();
    let mut st = Stats { probes: 0, accepts: 0, rejects: 0 };
    let mut x = n;
    while x >= 1 {
        if forbid.iter().any(|&(lo, hi)| x >= lo && x <= hi) {
            x -= 1;
            continue;
        }
        if let Some((q, ref ok)) = filt {
            if !ok[(x % q) as usize] {
                x -= 1;
                continue;
            }
        }
        let k = c.len() - 1;
        let base = x + c[k];
        // probe v_m = base - c[m], m = k down to 0, in batches of 8 with prefetch
        let mut hit = false;
        let mut m = k as i64;
        while m >= 0 {
            let lo = (m - 7).max(0);
            for mm in lo..=m {
                t.prefetch(base - c[mm as usize]);
            }
            for mm in (lo..=m).rev() {
                st.probes += 1;
                if t.contains(base - c[mm as usize]) {
                    hit = true;
                    break;
                }
            }
            if hit {
                break;
            }
            m = lo - 1;
        }
        if !hit && skip > 0.0 {
            // randomized variant: decline a valid candidate with probability `skip` (xorshift64*)
            rng ^= rng >> 12;
            rng ^= rng << 25;
            rng ^= rng >> 27;
            let r = (rng.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 11) as f64 / (1u64 << 53) as f64;
            if r < skip {
                st.rejects += 1;
                x -= 1;
                continue;
            }
        }
        if !hit {
            for mm in 0..=k {
                t.insert(base - c[mm]);
            }
            c.push(base);
            acc.push(x);
            st.accepts += 1;
            if t.count * 10 > (1u64 << t.bits) * 9 {
                eprintln!("table nearly full ({} of {}); rerun with larger --bits", t.count, 1u64 << t.bits);
                std::process::exit(3);
            }
        } else {
            st.rejects += 1;
        }
        x -= 1;
    }
    acc.reverse();
    (acc, st, t)
}

fn run_fwd(n: u64, bits: u32) -> (Vec<u64>, Stats, Table) {
    // forward greedy: add x as new maximum.  New sums: x + Q_j, Q_j = sum of the j largest current terms.
    let mut t = Table::new(bits);
    let mut a: Vec<u64> = Vec::new();
    let mut q: Vec<u64> = vec![0]; // q[j] = sum of j largest = suffix sums
    let mut st = Stats { probes: 0, accepts: 0, rejects: 0 };
    let mut x = 1u64;
    while x <= n {
        let k = a.len();
        let mut hit = false;
        for j in 0..=k {
            st.probes += 1;
            if t.contains(x + q[j]) {
                hit = true;
                break;
            }
        }
        if !hit {
            for j in 0..=k {
                t.insert(x + q[j]);
            }
            let mut nq = Vec::with_capacity(k + 2);
            nq.push(0);
            for j in 0..=k {
                nq.push(x + q[j]);
            }
            q = nq;
            a.push(x);
            st.accepts += 1;
        } else {
            st.rejects += 1;
        }
        x += 1;
    }
    (a, st, t)
}

#[derive(Clone)]
struct State {
    t: Table,
    c: Vec<u64>,
    acc: Vec<u64>,
    x: u64, // next candidate to test (scanning downward); 0 = finished
}

impl State {
    fn new(n: u64, bits: u32) -> State {
        State { t: Table::new(bits), c: vec![0], acc: Vec::new(), x: n }
    }
    /// is x admissible as the new minimum?
    #[inline]
    fn admissible(&self, x: u64) -> bool {
        let k = self.c.len() - 1;
        let base = x + self.c[k];
        let mut m = k as i64;
        while m >= 0 {
            let lo = (m - 7).max(0);
            for mm in lo..=m {
                self.t.prefetch(base - self.c[mm as usize]);
            }
            for mm in (lo..=m).rev() {
                if self.t.contains(base - self.c[mm as usize]) {
                    return false;
                }
            }
            m = lo - 1;
        }
        true
    }
    fn accept(&mut self, x: u64) {
        let k = self.c.len() - 1;
        let base = x + self.c[k];
        for mm in 0..=k {
            self.t.insert(base - self.c[mm]);
        }
        self.c.push(base);
        self.acc.push(x);
        if self.t.count * 10 > (1u64 << self.t.bits) * 9 {
            eprintln!("table nearly full; rerun with larger --bits");
            std::process::exit(3);
        }
    }
    fn finish(&mut self) -> usize {
        while self.x >= 1 {
            let x = self.x;
            if self.admissible(x) {
                self.accept(x);
            }
            self.x -= 1;
        }
        self.acc.len()
    }
}

/// one-step lookahead: among the first `b` admissible candidates, accept the one whose greedy completion is largest.
fn run_look(n: u64, b: usize, bits: u32, verbose: bool) -> Vec<u64> {
    let mut st = State::new(n, bits);
    let mut rolled = 0u64;
    loop {
        // gather up to b admissible candidates from st.x downward
        let mut cands: Vec<u64> = Vec::new();
        let mut x = st.x;
        while x >= 1 && cands.len() < b {
            if st.admissible(x) {
                cands.push(x);
            }
            x -= 1;
        }
        if cands.is_empty() {
            break;
        }
        let mut best = (0usize, cands[0]);
        if cands.len() == 1 {
            best = (0, cands[0]);
        } else {
            for &cx in &cands {
                let mut s2 = st.clone();
                s2.accept(cx);
                s2.x = cx - 1;
                let kk = s2.finish();
                rolled += 1;
                if kk > best.0 || (kk == best.0 && cx > best.1) {
                    best = (kk, cx);
                }
            }
        }
        st.accept(best.1);
        st.x = best.1 - 1;
        if verbose && st.acc.len() % 50 == 0 {
            eprintln!("  look: accepted {} (best completion {}), rollouts {}", st.acc.len(), best.0, rolled);
        }
        if st.x < 1 {
            break;
        }
    }
    let mut a = st.acc;
    a.reverse();
    a
}

fn brute(n: u64) -> usize {
    // exhaustive max k over subsets of [1..n] (tiny n only)
    fn ok_last(cur: &Vec<u64>) -> bool {
        let k = cur.len();
        let mut sums: Vec<u64> = Vec::new();
        for i in 0..k {
            let mut s = 0;
            for j in i..k {
                s += cur[j];
                sums.push(s);
            }
        }
        sums.sort_unstable();
        sums.windows(2).all(|w| w[0] != w[1])
    }
    fn rec(next: u64, n: u64, cur: &mut Vec<u64>, best: &mut usize) {
        if cur.len() > *best {
            *best = cur.len();
        }
        for x in next..=n {
            cur.push(x);
            if ok_last(cur) {
                rec(x + 1, n, cur, best);
            }
            cur.pop();
        }
    }
    let mut best = 0;
    let mut cur = Vec::new();
    rec(1, n, &mut cur, &mut best);
    best
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: rgreedy rev|fwd|verify|brute n|file [--bits b] [--cmax c] [--mod q --res r,..] [--dump f]");
        std::process::exit(1);
    }
    let mode = args[1].as_str();
    match mode {
        "verify" => {
            let s = read_set(&args[2]);
            let t = Instant::now();
            let ok = verify(&s);
            println!("verify {} k={} ok={} ({:.1}s)", args[2], s.len(), ok, t.elapsed().as_secs_f64());
            if !ok {
                std::process::exit(2);
            }
        }
        "brute" => {
            let n: u64 = args[2].parse().unwrap();
            println!("brute n={} f={}", n, brute(n));
        }
        "look" => {
            let n: u64 = args[2].parse().unwrap();
            let b: usize = arg_val(&args, "--b").map(|s| s.parse().unwrap()).unwrap_or(2);
            let cmax: f64 = arg_val(&args, "--cmax").map(|s| s.parse().unwrap()).unwrap_or(7.0);
            let bits: u32 = arg_val(&args, "--bits").map(|s| s.parse().unwrap()).unwrap_or_else(|| auto_bits(n, cmax));
            let t0 = Instant::now();
            let set = run_look(n, b, bits, arg_val(&args, "--verbose").is_some());
            println!(
                "look n={} b={} k={} k/sqrt(n)={:.4} sum={} table_bits={} fnv={:016x} time={:.1}s",
                n, b, set.len(), set.len() as f64 / (n as f64).sqrt(), set.iter().sum::<u64>(), bits, fnv(&set), t0.elapsed().as_secs_f64()
            );
            if let Some(p) = arg_val(&args, "--dump") {
                dump(&p, &set);
            }
        }
        "rev" | "fwd" => {
            let n: u64 = args[2].parse().unwrap();
            let cmax: f64 = arg_val(&args, "--cmax").map(|s| s.parse().unwrap()).unwrap_or(7.0);
            let bits: u32 = arg_val(&args, "--bits").map(|s| s.parse().unwrap()).unwrap_or_else(|| auto_bits(n, cmax));
            let filt = match (arg_val(&args, "--mod"), arg_val(&args, "--res")) {
                (Some(q), Some(r)) => {
                    let q: u64 = q.parse().unwrap();
                    let mut ok = vec![false; q as usize];
                    for t in r.split(',') {
                        ok[t.parse::<usize>().unwrap() % (q as usize)] = true;
                    }
                    Some((q, ok))
                }
                _ => None,
            };
            // --forbid lo-hi[,lo-hi..]: candidates x in [lo,hi] are never offered (rev mode only)
            let forbid: Vec<(u64, u64)> = match arg_val(&args, "--forbid") {
                Some(f) => f
                    .split(',')
                    .map(|t| {
                        let mut it = t.split('-');
                        let lo: u64 = it.next().unwrap().parse().unwrap();
                        let hi: u64 = it.next().unwrap().parse().unwrap();
                        (lo, hi)
                    })
                    .collect(),
                None => Vec::new(),
            };
            let skip: f64 = arg_val(&args, "--skip").map(|s| s.parse().unwrap()).unwrap_or(0.0);
            let seed: u64 = arg_val(&args, "--seed").map(|s| s.parse().unwrap()).unwrap_or(1);
            let t0 = Instant::now();
            let (set, st, t) = if mode == "rev" { run_rev(n, filt, &forbid, skip, seed, bits) } else { run_fwd(n, bits) };
            let el = t0.elapsed().as_secs_f64();
            let k = set.len();
            let total: u64 = set.iter().sum();
            println!(
                "{} n={} k={} k/sqrt(n)={:.4} sum={} table_bits={} load={:.3} probes={} accepts={} rejects={} fnv={:016x} time={:.1}s",
                mode,
                n,
                k,
                k as f64 / (n as f64).sqrt(),
                total,
                bits,
                t.count as f64 / (1u64 << bits) as f64,
                st.probes,
                st.accepts,
                st.rejects,
                fnv(&set),
                el
            );
            if let Some(p) = arg_val(&args, "--dump") {
                dump(&p, &set);
            }
        }
        _ => {
            eprintln!("unknown mode");
            std::process::exit(1);
        }
    }
}
