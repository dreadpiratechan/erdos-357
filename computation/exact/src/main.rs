// Independent exhaustive solver for Erdos Problem 357 (reproducibility package).
//
// Definition (the only input): a_1 < ... < a_k, all in [1, n], is admissible when the
// k(k+1)/2 block sums a_u + ... + a_v (1 <= u <= v <= k) are pairwise distinct.
//
// Search: depth-first, left to right.  Appending a_{j+1} = x creates exactly the j+1
// new block sums  x, x + a_j, x + a_j + a_{j-1}, ..., x + a_j + ... + a_1  (the sums that
// end at position j+1); the sequence stays admissible iff none of them is already
// used.  "Used" is a bitset indexed by sum.  See README.md for the pruning rules
// (all of them are proved sound there) and for what each --prune level switches on.
//
//   exact raw  N                      prune level 0: every admissible set inside 1..N (histogram)
//   exact count K N [opts]            number of admissible K-sets with max <= N
//   exact table KMAX [opts]           M(k) and all optimal sets for k = 1..KMAX
//   exact grid N [opts]               count(K, n) for every 1 <= K <= n <= N
//   exact ftable MTABLE NMAX [opts]   direct negative decision count(f(n)+1, n) = 0 for n = 1..NMAX
//
//   opts:  --prune 1|2 (default 2)   --threads T (default 8, max 8)   --split D
//          --first (stop at first solution; count is then a lower bound)
//          --audit R (naive re-derivation of the candidate set at every R-th node)
//          --sets FILE (write the sets found)   --ckpt FILE (resumable task log)
use std::collections::BTreeMap;
use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

const W: usize = 72; // words of the used-sum bitset (4608 bits)
const MAXK: usize = 64;
static DEPTH: [AtomicU64; MAXK + 2] = [const { AtomicU64::new(0) }; MAXK + 2];
static AUDITED: AtomicU64 = AtomicU64::new(0);

#[inline(always)]
fn window(u: &[u64; W + 4], pos: usize) -> u128 {
    // bits pos .. pos+127 of the bitset as a u128 (bit 0 = sum `pos`)
    let wi = pos >> 6;
    let o = (pos & 63) as u32;
    let lo = (u[wi] as u128) | ((u[wi + 1] as u128) << 64);
    if o == 0 {
        lo
    } else {
        (lo >> o) | ((u[wi + 2] as u128) << (128 - o))
    }
}
#[inline(always)]
fn set_bit(u: &mut [u64; W + 4], s: usize) {
    u[s >> 6] |= 1u64 << (s & 63);
}
#[inline(always)]
fn clr_bit(u: &mut [u64; W + 4], s: usize) {
    u[s >> 6] &= !(1u64 << (s & 63));
}
#[inline(always)]
fn low_mask(w: u32) -> u128 {
    if w >= 128 {
        !0u128
    } else {
        (1u128 << w) - 1
    }
}

#[derive(Clone, Copy)]
struct Cfg {
    k: usize,
    n: u32,
    prune: u8, // 0 = none (raw), 1 = room bound, 2 = room bound + free-slot count
    first: bool,
    audit: u64, // if > 0: re-derive the Lemma-1 candidate set by the naive definition at every audit-th node
}

struct Worker {
    cfg: Cfg,
    a: [u32; MAXK + 1],
    p: [u32; MAXK + 1],
    u: [u64; W + 4],
    nodes: u64,
    count: u64,
    sols: Vec<Vec<u8>>,
    keep_sols: bool,
    hist: Vec<u64>, // raw mode: hist[k * 128 + last]
    depth_nodes: [u64; MAXK + 2],
    audited: u64,
    stop: Arc<AtomicBool>,
}

impl Worker {
    fn new(cfg: Cfg, keep_sols: bool, stop: Arc<AtomicBool>) -> Self {
        Worker {
            cfg,
            a: [0; MAXK + 1],
            p: [0; MAXK + 1],
            u: [0; W + 4],
            nodes: 0,
            count: 0,
            sols: vec![],
            keep_sols,
            hist: if cfg.prune == 0 { vec![0; 128 * 128] } else { vec![] },
            depth_nodes: [0; MAXK + 2],
            audited: 0,
            stop,
        }
    }

    // append x as the (j+1)-th term; caller guarantees admissibility
    #[inline(always)]
    fn push(&mut self, j: usize, x: u32) {
        self.a[j + 1] = x;
        self.p[j + 1] = self.p[j] + x;
        let pj1 = self.p[j + 1];
        for i in 0..=j {
            set_bit(&mut self.u, (pj1 - self.p[i]) as usize);
        }
    }
    #[inline(always)]
    fn pop(&mut self, j: usize) {
        let pj1 = self.p[j + 1];
        for i in 0..=j {
            clr_bit(&mut self.u, (pj1 - self.p[i]) as usize);
        }
    }

    // candidate set for the next term, as a bitmask over x = lo + t  (t = bit index)
    // returns (lo, cand); cand == 0 means: prune this node.
    #[inline(always)]
    fn candidates(&self, j: usize) -> (u32, u128, u128) {
        let cfg = self.cfg;
        let n = cfg.n;
        let lo = if j == 0 { 1 } else { self.a[j] + 1 };
        if lo > n {
            return (lo, 0, 0);
        }
        let wall = n - lo + 1;
        // x itself must not be a used sum (shift 0)
        let mut cand = !window(&self.u, lo as usize) & low_mask(wall);
        let mut free = 0u128; // free singles in [lo, n] (prune >= 2)
        if cfg.prune >= 1 {
            let need = (cfg.k - j) as u32; // terms still to place, including x
            // R1 (room): x <= n - (need - 1)
            if need > wall {
                return (lo, 0, 0);
            }
            if cfg.prune >= 2 {
                // R3 (free slots): the `need` terms from here on are distinct unused
                // integers in [lo, n]; so at least `need` free singles must exist, and x
                // must have at least need-1 free singles above it.
                if cand.count_ones() < need {
                    return (lo, 0, 0);
                }
                free = cand;
                let mut tmp = cand;
                for _ in 0..need - 1 {
                    tmp &= !(1u128 << (127 - tmp.leading_zeros()));
                }
                let top = 127 - tmp.leading_zeros();
                cand &= low_mask(top + 1);
            } else {
                cand &= low_mask(wall - (need - 1));
            }
        }
        // x + (a_j + ... + a_{i+1}) must not be a used sum, i = j-1 .. 0
        let pj = self.p[j];
        let mut i = j;
        while i > 0 {
            i -= 1;
            let s = (pj - self.p[i]) as usize;
            cand &= !window(&self.u, lo as usize + s);
            if cand == 0 {
                return (lo, 0, 0);
            }
        }
        (lo, cand, free)
    }

    // R3 applied to the children ahead of time.  Pushing x adds the block sums x + (suffix sums of
    // the prefix); those that are <= n are all unused singles above x (they passed the candidate
    // test), so they are removed from the free set.  The child therefore has exactly
    // popcount(free above x) - #{suffix sums s : x + s <= n} free singles above its own last term,
    // and the child is dead on arrival (R3(i) with k - j - 1 terms still to place) unless that is
    // >= k - j - 1.  Dropping such x here saves the push/pop and the node visit; the set of nodes
    // that can lead to a solution is untouched.
    #[inline(always)]
    fn precheck(&self, j: usize, lo: u32, cand: u128, free: u128) -> u128 {
        let cfg = self.cfg;
        if cfg.prune < 2 || cand == 0 || cfg.k <= j + 1 {
            return cand;
        }
        let need1 = (cfg.k - j - 1) as u32;
        let n = cfg.n;
        let pj = self.p[j];
        let mut out = 0u128;
        let mut c = cand;
        let mut r = j; // number of suffix sums (a_j, a_j+a_{j-1}, ...) still <= n - x
        while c != 0 {
            let t = c.trailing_zeros();
            c &= c - 1;
            let lim = n - (lo + t);
            while r > 0 && pj - self.p[j - r] > lim {
                r -= 1;
            }
            let above = if t + 1 >= 128 { 0 } else { (free >> (t + 1)).count_ones() };
            if above >= need1 + r as u32 {
                out |= 1u128 << t;
            }
        }
        out
    }

    // Naive re-derivation of the Lemma-1 candidate set of the current node: x in [lo, n] is a
    // candidate iff a_1..a_j, x is admissible, decided from the definition with a HashSet.
    // Compared with the bitset-window mask; panics on any difference.
    fn audit_node(&mut self, j: usize) {
        let n = self.cfg.n;
        let lo = if j == 0 { 1 } else { self.a[j] + 1 };
        if lo > n {
            return;
        }
        let wall = n - lo + 1;
        let mut mask = low_mask(wall);
        let mut i = j + 1;
        while i > 0 {
            i -= 1;
            let s = (self.p[j] - self.p[i]) as usize;
            mask &= !window(&self.u, lo as usize + s);
        }
        let mut seq: Vec<u8> = (1..=j).map(|i| self.a[i] as u8).collect();
        for x in lo..=n {
            seq.push(x as u8);
            let naive = naive_admissible(&seq);
            seq.pop();
            let bit = (mask >> (x - lo)) & 1 == 1;
            assert_eq!(naive, bit, "AUDIT FAILURE at prefix {:?}, x = {}: naive {} window {}", seq, x, naive, bit);
        }
        self.audited += 1;
    }

    fn dfs(&mut self, j: usize) {
        self.nodes += 1;
        if self.cfg.audit > 0 && self.nodes % self.cfg.audit == 0 {
            self.audit_node(j);
        }
        self.depth_nodes[j.min(MAXK + 1)] += 1;
        let cfg = self.cfg;
        if cfg.prune == 0 {
            if j >= 1 {
                self.hist[j * 128 + self.a[j] as usize] += 1;
            }
        } else if j == cfg.k {
            self.count += 1;
            if self.keep_sols {
                self.sols.push((1..=j).map(|i| self.a[i] as u8).collect());
            }
            if cfg.first {
                self.stop.store(true, Ordering::Relaxed);
            }
            return;
        }
        let (lo, cand0, free) = self.candidates(j);
        let mut cand = self.precheck(j, lo, cand0, free);
        while cand != 0 {
            let t = cand.trailing_zeros();
            cand &= cand - 1;
            self.push(j, lo + t);
            self.dfs(j + 1);
            self.pop(j);
            if cfg.first && self.stop.load(Ordering::Relaxed) {
                return;
            }
        }
    }

    // generate all nodes at depth d (same pruning as dfs) into out
    fn gen_prefixes(&mut self, j: usize, d: usize, out: &mut Vec<Vec<u8>>) {
        self.nodes += 1;
        if j == d {
            out.push((1..=j).map(|i| self.a[i] as u8).collect());
            return;
        }
        let (lo, cand0, free) = self.candidates(j);
        let mut cand = self.precheck(j, lo, cand0, free);
        while cand != 0 {
            let t = cand.trailing_zeros();
            cand &= cand - 1;
            self.push(j, lo + t);
            self.gen_prefixes(j + 1, d, out);
            self.pop(j);
        }
    }

    fn load_prefix(&mut self, pre: &[u8]) {
        // reset and replay a prefix (prefixes come from gen_prefixes, hence admissible)
        self.u = [0; W + 4];
        self.p[0] = 0;
        for (j, &x) in pre.iter().enumerate() {
            self.push(j, x as u32);
        }
    }
}

struct RunResult {
    count: u64,
    nodes: u64,
    sols: Vec<Vec<u8>>,
    hist: Vec<u64>,
    secs: f64,
    tasks: usize,
}

fn run(
    cfg: Cfg,
    threads: usize,
    split: Option<usize>,
    keep_sols: bool,
    ckpt: Option<&str>,
    verbose: bool,
) -> RunResult {
    let t0 = Instant::now();
    let stop = Arc::new(AtomicBool::new(false));
    // sanity: bitset capacity.  Largest possible block sum is the total of the last k terms.
    let kk = if cfg.prune == 0 { cfg.n as u64 } else { cfg.k as u64 };
    let maxsum = kk * cfg.n as u64 - kk * (kk.saturating_sub(1)) / 2;
    assert!(maxsum + 130 < (W as u64) * 64, "bitset too small: maxsum {}", maxsum);
    assert!(cfg.n <= 120 && cfg.k <= MAXK);

    // choose prefix depth
    let mut master = Worker::new(cfg, false, stop.clone());
    let maxd = if cfg.prune == 0 { cfg.n as usize } else { cfg.k };
    let mut d = split.unwrap_or(0);
    let mut prefixes: Vec<Vec<u8>> = vec![];
    if split.is_none() {
        d = 1;
        loop {
            prefixes.clear();
            master.nodes = 0;
            master.gen_prefixes(0, d, &mut prefixes);
            if prefixes.len() >= 3000 || d >= maxd.min(12) {
                break;
            }
            d += 1;
        }
    } else {
        master.nodes = 0;
        master.gen_prefixes(0, d, &mut prefixes);
    }
    let ntasks = prefixes.len();
    // nodes strictly above the split depth (the root included); the depth-d nodes themselves
    // are counted once, by the tasks.
    let upper_nodes = master.nodes - ntasks as u64;
    // checkpoint: a text log "T idx nodes count" and "S idx a1,a2,.."  (header identifies the run)
    let header = format!("# k={} n={} prune={} split={} tasks={}", cfg.k, cfg.n, cfg.prune, d, ntasks);
    let mut done: BTreeMap<usize, (u64, u64)> = BTreeMap::new();
    let mut sols_done: Vec<Vec<u8>> = vec![];
    if let Some(path) = ckpt {
        if let Ok(txt) = std::fs::read_to_string(path) {
            let mut lines = txt.lines();
            if lines.next() == Some(header.as_str()) {
                for l in lines {
                    let f: Vec<&str> = l.split_whitespace().collect();
                    if f.len() == 4 && f[0] == "T" {
                        done.insert(f[1].parse().unwrap(), (f[2].parse().unwrap(), f[3].parse().unwrap()));
                    } else if f.len() == 3 && f[0] == "S" {
                        sols_done.push(f[2].split(',').map(|v| v.parse().unwrap()).collect());
                    }
                }
            } else {
                panic!("checkpoint {} belongs to a different run (header mismatch); delete it", path);
            }
        } else {
            std::fs::write(path, format!("{}\n", header)).unwrap();
        }
    }
    let ck_file = ckpt.map(|p| Mutex::new(std::fs::OpenOptions::new().append(true).open(p).unwrap()));
    let ck_file = Arc::new(ck_file);
    let prefixes = Arc::new(prefixes);
    let next = Arc::new(AtomicUsize::new(0));
    let finished = Arc::new(AtomicUsize::new(done.len()));
    let tot_nodes = Arc::new(AtomicU64::new(0));
    let resumed_nodes: u64 = done.values().map(|v| v.0).sum();
    let resumed_count: u64 = done.values().map(|v| v.1).sum();
    let done = Arc::new(done);
    // (count, nodes, sols, hist)
    let results: Arc<Mutex<(u64, u64, Vec<Vec<u8>>, Vec<u64>)>> = Arc::new(Mutex::new((
        resumed_count,
        resumed_nodes,
        sols_done,
        if cfg.prune == 0 { vec![0; 128 * 128] } else { vec![] },
    )));
    let mut hs = vec![];
    for _ in 0..threads {
        let (prefixes, next, finished, results, stop, done, ck_file, tot_nodes) = (
            prefixes.clone(),
            next.clone(),
            finished.clone(),
            results.clone(),
            stop.clone(),
            done.clone(),
            ck_file.clone(),
            tot_nodes.clone(),
        );
        hs.push(std::thread::spawn(move || {
            let mut w = Worker::new(cfg, keep_sols, stop.clone());
            loop {
                if cfg.first && stop.load(Ordering::Relaxed) {
                    break;
                }
                let idx = next.fetch_add(1, Ordering::Relaxed);
                if idx >= prefixes.len() {
                    break;
                }
                if done.contains_key(&idx) {
                    continue;
                }
                w.load_prefix(&prefixes[idx]);
                let (n0, c0, s0) = (w.nodes, w.count, w.sols.len());
                w.dfs(prefixes[idx].len());
                let (dn, dc) = (w.nodes - n0, w.count - c0);
                if let Some(f) = ck_file.as_ref() {
                    let mut f = f.lock().unwrap();
                    writeln!(f, "T {} {} {}", idx, dn, dc).unwrap();
                    for s in &w.sols[s0..] {
                        let v: Vec<String> = s.iter().map(|x| x.to_string()).collect();
                        writeln!(f, "S {} {}", idx, v.join(",")).unwrap();
                    }
                }
                tot_nodes.fetch_add(dn, Ordering::Relaxed);
                let fin = finished.fetch_add(1, Ordering::Relaxed) + 1;
                if verbose && (fin % 200 == 0 || fin == prefixes.len()) {
                    eprintln!("  [{}/{} tasks, {} nodes]", fin, prefixes.len(), tot_nodes.load(Ordering::Relaxed));
                }
            }
            AUDITED.fetch_add(w.audited, Ordering::Relaxed);
            for (i, v) in w.depth_nodes.iter().enumerate() {
                DEPTH[i].fetch_add(*v, Ordering::Relaxed);
            }
            let mut r = results.lock().unwrap();
            r.0 += w.count;
            r.1 += w.nodes;
            r.2.extend(w.sols.drain(..));
            for (i, v) in w.hist.iter().enumerate() {
                r.3[i] += v;
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let mut r = results.lock().unwrap();
    let mut sols = std::mem::take(&mut r.2);
    sols.sort();
    // raw mode: the master's own nodes above depth d are not counted in hist; add them
    let mut hist = std::mem::take(&mut r.3);
    if cfg.prune == 0 {
        // nodes at depth 1..d-1 (depth 0 is the empty set and is not recorded)
        let mut shallow = Worker::new(cfg, false, stop.clone());
        for dd in 1..d {
            let mut pre = vec![];
            shallow.gen_prefixes(0, dd, &mut pre);
            for p in pre {
                hist[dd * 128 + *p.last().unwrap() as usize] += 1;
            }
        }
    }
    RunResult { count: r.0, nodes: r.1 + upper_nodes, sols, hist, secs: t0.elapsed().as_secs_f64(), tasks: ntasks }
}

struct Opts {
    prune: u8,
    threads: usize,
    split: Option<usize>,
    first: bool,
    sets: Option<String>,
    ckpt: Option<String>,
    out: Option<String>,
    audit: u64,
    pos: Vec<String>,
}

fn parse(args: &[String]) -> Opts {
    let mut o = Opts {
        prune: 2,
        threads: 8,
        split: None,
        first: false,
        sets: None,
        ckpt: None,
        out: None,
        audit: 0,
        pos: vec![],
    };
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--prune" => {
                o.prune = args[i + 1].parse().unwrap();
                i += 1
            }
            "--threads" => {
                o.threads = args[i + 1].parse().unwrap();
                i += 1
            }
            "--split" => {
                o.split = Some(args[i + 1].parse().unwrap());
                i += 1
            }
            "--first" => o.first = true,
            "--sets" => {
                o.sets = Some(args[i + 1].clone());
                i += 1
            }
            "--ckpt" => {
                o.ckpt = Some(args[i + 1].clone());
                i += 1
            }
            "--audit" => {
                o.audit = args[i + 1].parse().unwrap();
                i += 1
            }
            "--out" => {
                o.out = Some(args[i + 1].clone());
                i += 1
            }
            s => o.pos.push(s.to_string()),
        }
        i += 1;
    }
    assert!(o.threads >= 1 && o.threads <= 8, "at most 8 threads (shared machine)");
    o
}

// Check straight from the definition (HashSet of all block sums), used to re-verify every set the
// search reports; independent of the incremental bitset logic.
fn naive_admissible(s: &[u8]) -> bool {
    let mut seen = std::collections::HashSet::new();
    for u in 0..s.len() {
        let mut sum = 0u32;
        for v in u..s.len() {
            sum += s[v] as u32;
            if !seen.insert(sum) {
                return false;
            }
        }
    }
    s.windows(2).all(|w| w[0] < w[1]) && s.first().map_or(true, |&x| x >= 1)
}

fn fmt_set(s: &[u8]) -> String {
    s.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(|s| s.as_str()).unwrap_or("");
    let o = parse(&args[2.min(args.len())..]);
    match cmd {
        "raw" => {
            let n: u32 = o.pos[0].parse().unwrap();
            let cfg = Cfg { k: 0, n, prune: 0, first: false, audit: 0 };
            let r = run(cfg, o.threads, o.split, false, None, false);
            println!("# exact raw: all admissible subsets of 1..{} ({} tree nodes, {:.2}s)", n, r.nodes, r.secs);
            let mut mk: BTreeMap<usize, (usize, u64)> = BTreeMap::new();
            for k in 1..=n as usize {
                for last in 1..=n as usize {
                    let c = r.hist[k * 128 + last];
                    if c > 0 {
                        println!("H {} {} {}", k, last, c);
                        mk.entry(k).or_insert((last, c));
                    }
                }
            }
            for (k, (m, c)) in &mk {
                println!("M {} {} {}", k, m, c);
            }
            for nv in 1..=n as usize {
                let f = mk.iter().filter(|(_, (m, _))| *m <= nv).map(|(k, _)| *k).max().unwrap_or(0);
                println!("F {} {}", nv, f);
            }
        }
        "count" => {
            let k: usize = o.pos[0].parse().unwrap();
            let n: u32 = o.pos[1].parse().unwrap();
            let cfg = Cfg { k, n, prune: o.prune, first: o.first, audit: o.audit };
            let r = run(cfg, o.threads, o.split, o.sets.is_some(), o.ckpt.as_deref(), true);
            println!(
                "count k={} n={} prune={} threads={}: {} admissible {}-sets with max <= {}  [{} nodes, {} tasks, {:.2}s]{}",
                k, n, o.prune, o.threads, r.count, k, n, r.nodes, r.tasks, r.secs,
                if o.first { "  (--first: lower bound only)" } else { "" }
            );
            if o.audit > 0 {
                println!("audit: {} sampled nodes had their candidate sets re-derived naively, all identical", AUDITED.load(Ordering::Relaxed));
            }
            if std::env::var("ERDOS_DEPTHS").is_ok() {
                let v: Vec<String> = (0..=k).map(|i| format!("{}:{}", i, DEPTH[i].load(Ordering::Relaxed))).collect();
                println!("nodes per depth (below the split depth only): {}", v.join(" "));
            }
            if let Some(path) = &o.sets {
                let mut f = std::fs::File::create(path).unwrap();
                for s in &r.sols {
                    writeln!(f, "{}", fmt_set(s)).unwrap();
                }
            }
        }
        "grid" => {
            let nmax: u32 = o.pos[0].parse().unwrap();
            for n in 1..=nmax {
                for k in 1..=n as usize {
                    let cfg = Cfg { k, n, prune: o.prune, first: false, audit: o.audit };
                    let r = run(cfg, o.threads, o.split, false, None, false);
                    println!("G {} {} {}", k, n, r.count);
                }
            }
        }
        "table" => {
            let kmax: usize = o.pos[0].parse().unwrap();
            let outdir = o.out.clone().unwrap_or_else(|| ".".to_string());
            std::fs::create_dir_all(&outdir).unwrap();
            let mut mtab: Vec<(usize, u32, u64)> = vec![];
            let mut prev_m: u32 = 0;
            let mut sets_all = String::new();
            let tstart = Instant::now();
            for k in 1..=kmax {
                let mut n = prev_m + 1;
                loop {
                    let cfg = Cfg { k, n, prune: o.prune, first: false, audit: o.audit };
                    let ck = o.ckpt.as_ref().map(|d| format!("{}/ck_k{}_n{}.txt", d, k, n));
                    let r = run(cfg, o.threads, o.split, true, ck.as_deref(), false);
                    println!(
                        "k={:2} n={:3}: {} sets  [{} nodes, {} tasks, {:.2}s]  (elapsed {:.1}s)",
                        k, n, r.count, r.nodes, r.tasks, r.secs, tstart.elapsed().as_secs_f64()
                    );
                    std::io::stdout().flush().unwrap();
                    if r.count > 0 {
                        mtab.push((k, n, r.count));
                        for s in &r.sols {
                            assert_eq!(*s.last().unwrap() as u32, n);
                            assert_eq!(s.len(), k);
                            assert!(naive_admissible(s), "engine reported a non-admissible set {:?}", s);
                            sets_all.push_str(&format!("{} {} {}\n", k, n, fmt_set(s)));
                        }
                        prev_m = n;
                        break;
                    }
                    n += 1;
                }
            }
            let mut f = std::fs::File::create(format!("{}/M_table.txt", outdir)).unwrap();
            writeln!(f, "# k M(k) optimal_set_count").unwrap();
            for (k, m, c) in &mtab {
                writeln!(f, "{} {} {}", k, m, c).unwrap();
            }
            std::fs::write(format!("{}/optimal_sets.txt", outdir), sets_all).unwrap();
        }
        "ftable" => {
            // ftable MTABLE NMAX : for every n = 1..NMAX decide directly that no (f(n)+1)-set fits in
            // [1,n], where f(n) = max{k : M(k) <= n} is read from the M table produced by `table`.
            let mt = std::fs::read_to_string(&o.pos[0]).unwrap();
            let nmax: u32 = o.pos[1].parse().unwrap();
            let ms: Vec<u32> = mt
                .lines()
                .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
                .map(|l| l.split_whitespace().nth(1).unwrap().parse().unwrap())
                .collect();
            let outdir = o.out.clone().unwrap_or_else(|| ".".to_string());
            std::fs::create_dir_all(&outdir).unwrap();
            let mut lines = String::from("# n f(n) | decision: count of admissible (f(n)+1)-sets with max <= n (must be 0) | nodes | seconds\n");
            let tstart = Instant::now();
            for n in 1..=nmax {
                let f = ms.iter().filter(|&&m| m <= n).count();
                let cfg = Cfg { k: f + 1, n, prune: o.prune, first: false, audit: o.audit };
                let ck = o.ckpt.as_ref().map(|d| format!("{}/fck_k{}_n{}.txt", d, f + 1, n));
                let r = run(cfg, o.threads, o.split, false, ck.as_deref(), false);
                let line = format!("{} {} | count({},{}) = {} | {} | {:.2}", n, f, f + 1, n, r.count, r.nodes, r.secs);
                println!("{}  (elapsed {:.1}s)", line, tstart.elapsed().as_secs_f64());
                std::io::stdout().flush().unwrap();
                assert_eq!(r.count, 0, "an (f(n)+1)-set exists at n={}: the M table is wrong", n);
                lines.push_str(&line);
                lines.push('\n');
            }
            std::fs::write(format!("{}/f_table_decisions.txt", outdir), lines).unwrap();
        }
        _ => {
            eprintln!("usage: exact raw N | count K N | grid N | table KMAX   [--prune p --threads t --split d --first --sets f --ckpt f --out dir]");
            std::process::exit(2);
        }
    }
}
