// All-subsets brute force for Erdos 357, written straight from the definition.
//
// For every non-empty subset S of {1..N} (as a bitmask), list its elements in
// increasing order a_1 < ... < a_k, form ALL sums a_u + ... + a_v (1<=u<=v<=k),
// and test that they are pairwise distinct.  No pruning, no incremental state,
// no use of any other part of this package.
//
// Output (stdout): one line per (k, last) with the number of admissible k-subsets
// whose maximum element is `last`:   "H k last count"
// plus the derived tables.  Usage: brute N [threads]
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

fn admissible(mask: u64, buf: &mut [u32; 64]) -> (usize, u32) {
    // collect elements
    let mut k = 0usize;
    let mut m = mask;
    while m != 0 {
        let b = m.trailing_zeros();
        buf[k] = b + 1;
        k += 1;
        m &= m - 1;
    }
    let mut seen = [0u64; 16]; // 1024 bits; N <= 40 gives sums <= 820
    for u in 0..k {
        let mut s = 0u32;
        for v in u..k {
            s += buf[v];
            let (w, b) = ((s >> 6) as usize, s & 63);
            if (seen[w] >> b) & 1 == 1 {
                return (0, 0);
            }
            seen[w] |= 1u64 << b;
        }
    }
    (k, buf[k - 1])
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: u32 = args.get(1).expect("usage: brute N [threads]").parse().unwrap();
    let threads: usize = args.get(2).map(|s| s.parse().unwrap()).unwrap_or(8);
    assert!(n >= 1 && n <= 40);
    let total: u64 = 1u64 << n;
    let hist: Arc<Vec<AtomicU64>> =
        Arc::new((0..(n as usize + 2) * (n as usize + 2)).map(|_| AtomicU64::new(0)).collect());
    let next = Arc::new(AtomicU64::new(1));
    let chunk: u64 = 1 << 16;
    let w = n as usize + 2;
    let mut hs = vec![];
    for _ in 0..threads {
        let hist = hist.clone();
        let next = next.clone();
        hs.push(std::thread::spawn(move || {
            let mut buf = [0u32; 64];
            let mut local = vec![0u64; w * w];
            loop {
                let start = next.fetch_add(chunk, Ordering::Relaxed);
                if start >= total {
                    break;
                }
                let end = (start + chunk).min(total);
                for mask in start..end {
                    if mask == 0 {
                        continue;
                    }
                    let (k, last) = admissible(mask, &mut buf);
                    if k > 0 {
                        local[k * w + last as usize] += 1;
                    }
                }
            }
            for i in 0..local.len() {
                if local[i] != 0 {
                    hist[i].fetch_add(local[i], Ordering::Relaxed);
                }
            }
        }));
    }
    for h in hs {
        h.join().unwrap();
    }
    let nn = n as usize;
    println!("# brute force over all non-empty subsets of 1..{}  ({} subsets)", n, total - 1);
    let mut mk: Vec<Option<(usize, u64)>> = vec![None; nn + 2];
    for k in 1..=nn {
        for last in 1..=nn {
            let c = hist[k * w + last].load(Ordering::Relaxed);
            if c > 0 {
                println!("H {} {} {}", k, last, c);
                if mk[k].is_none() {
                    mk[k] = Some((last, c));
                }
            }
        }
    }
    println!("# k  M(k)  optimal_count   (only k with M(k) <= {})", n);
    for k in 1..=nn {
        if let Some((m, c)) = mk[k] {
            println!("M {} {} {}", k, m, c);
        }
    }
    println!("# n  f(n)");
    for nv in 1..=nn {
        let mut f = 0;
        for k in 1..=nn {
            if let Some((m, _)) = mk[k] {
                if m <= nv {
                    f = k;
                }
            }
        }
        println!("F {} {}", nv, f);
    }
}
