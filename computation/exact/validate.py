#!/usr/bin/env python3
"""Validation driver for the exact solver.
usage: validate.py [BIN_DIR [BRUTE_FILE [NGRID [RAWN]]]]

  BIN_DIR     directory with the compiled `exact` binary (exact.exe on Windows).  Default: $EXACT_BIN_DIR if set,
              else target/release next to this script (where `cargo build --release` puts it).
  BRUTE_FILE  output of `brute NMAX`.  Default: results/brute_N34.txt next to this script.
  NGRID       largest n of the grid comparison (default 28; the recorded runs used 34, or 30 for the quick run).
  RAWN        optional; also compare against the unpruned `exact raw RAWN` (the recorded run used 52, about 90 s).

Compares, against the all-subsets brute force (results/brute_N<NMAX>.txt, produced by
`brute NMAX`):
  1. the full histogram  H[k][last] = #admissible k-subsets of {1..N} with maximum `last`
     computed by `exact raw N` (prune level 0: no pruning at all) -- for N = NMAX;
  2. the whole table count(k, n) = #admissible k-subsets with max <= n for every
     1 <= k <= n <= NGRID, as computed by `exact grid NGRID --prune 1` (room bound only)
     and `--prune 2` (room bound + free-slot count), against the brute force cumulative sums;
  3. M(k) and the optimal-set counts implied by the brute force, against the OEIS A364132 terms
     (reference/oeis_A364132.txt, 22 terms);
  4. (optional RAWN > N) the same grid comparison for n up to RAWN, with `exact raw RAWN`
     (no pruning at all) as the reference instead of the brute force: count(k, n) from the
     pruned engine at --prune 2 against the cumulative histogram of the unpruned enumeration.
"""
import os
import subprocess
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
bin_dir = sys.argv[1] if len(sys.argv) > 1 else os.environ.get("EXACT_BIN_DIR", os.path.join(HERE, "target", "release"))
brute_file = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "results", "brute_N34.txt")
ngrid = int(sys.argv[3]) if len(sys.argv) > 3 else 28
rawn = int(sys.argv[4]) if len(sys.argv) > 4 else 0
OEIS = os.path.join(HERE, "..", "reference", "oeis_A364132.txt")

fail = 0


def exact_binary():
    for name in ("exact.exe", "exact"):
        p = os.path.join(bin_dir, name)
        if os.path.isfile(p):
            return p
    sys.exit(f"no `exact` binary in {bin_dir} (build it with: cargo build --release)")


def show_path(p):
    try:
        return os.path.relpath(p, HERE).replace(os.sep, "/")
    except ValueError:  # different drive on Windows
        return p


def read_oeis_terms(path):
    terms = []
    for ln in open(path, encoding="utf-8"):
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            n, a = ln.split()
            assert int(n) == len(terms) + 1, f"{path}: term index {n} out of order"
            terms.append(int(a))
    return terms


def run(args):
    r = subprocess.run([exact_binary()] + args, capture_output=True, text=True, check=True)
    return r.stdout


# brute-force histogram
H = {}
nbrute = None
for ln in open(brute_file):
    t = ln.split()
    if ln.startswith("# brute force"):
        nbrute = int(ln.split("1..")[1].split()[0])
    if t and t[0] == "H":
        H[(int(t[1]), int(t[2]))] = int(t[3])
print(f"brute force file {show_path(brute_file)}: N={nbrute}, {len(H)} nonzero (k,last) cells, {sum(H.values())} admissible non-empty subsets")

# 1. raw histogram
out = run(["raw", str(nbrute), "--threads", "8"])
Hr = {}
for ln in out.splitlines():
    t = ln.split()
    if t and t[0] == "H":
        Hr[(int(t[1]), int(t[2]))] = int(t[3])
print(out.splitlines()[0])
ok = Hr == H
print(f"[1] raw (no pruning) histogram == brute-force histogram over all subsets of 1..{nbrute}: {ok}"
      f"   ({sum(Hr.values())} sets in both)")
fail += not ok


# 2. grid
def cum(k, n):
    return sum(c for (kk, last), c in H.items() if kk == k and last <= n)


for prune in (1, 2):
    out = run(["grid", str(ngrid), "--prune", str(prune), "--threads", "8"])
    cells = 0
    bad = []
    nonzero = 0
    for ln in out.splitlines():
        t = ln.split()
        if t and t[0] == "G":
            k, n, c = int(t[1]), int(t[2]), int(t[3])
            cells += 1
            nonzero += c > 0
            if c != cum(k, n):
                bad.append((k, n, c, cum(k, n)))
    ok = not bad and cells == ngrid * (ngrid + 1) // 2
    print(f"[2] grid --prune {prune}: count(k,n) for all 1<=k<=n<={ngrid}: {cells} cells ({nonzero} nonzero), "
          f"mismatches vs brute force: {bad[:5]}  -> {'PASS' if ok else 'FAIL'}")
    fail += not ok

# 3. M(k), counts from brute force, vs OEIS
Mk = {}
for k in range(1, nbrute + 1):
    lasts = sorted(l for (kk, l) in H if kk == k)
    if lasts:
        Mk[k] = (lasts[0], H[(k, lasts[0])])
oeis = read_oeis_terms(OEIS)
cmp = [(k, Mk[k][0], oeis[k - 1]) for k in Mk if k <= len(oeis) and Mk[k][0] != oeis[k - 1]]
print(f"[3] brute-force M(k) for k = 1..{max(Mk)}: {[Mk[k][0] for k in sorted(Mk)]}")
print(f"    brute-force optimal-set counts:       {[Mk[k][1] for k in sorted(Mk)]}")
print(f"    mismatches against OEIS A364132 (cache, {len(oeis)} terms): {cmp}")
fail += bool(cmp)
# 4. pruned grid against the unpruned enumeration beyond the brute-force range
if rawn:
    out = run(["raw", str(rawn), "--threads", "8"])
    print(out.splitlines()[0])
    Hq = defaultdict(int)
    for ln in out.splitlines():
        t = ln.split()
        if t and t[0] == "H":
            Hq[(int(t[1]), int(t[2]))] = int(t[3])
    cq = {}
    for k in range(1, rawn + 1):
        run_tot = 0
        for n in range(1, rawn + 1):
            run_tot += Hq.get((k, n), 0)
            cq[(k, n)] = run_tot
    for prune in (2,):
        out = run(["grid", str(rawn), "--prune", str(prune), "--threads", "8"])
        cells = 0
        bad = []
        nonzero = 0
        for ln in out.splitlines():
            t = ln.split()
            if t and t[0] == "G":
                k, n, c = int(t[1]), int(t[2]), int(t[3])
                cells += 1
                nonzero += c > 0
                if c != cq[(k, n)]:
                    bad.append((k, n, c, cq[(k, n)]))
        ok = not bad and cells == rawn * (rawn + 1) // 2
        print(f"[4] grid --prune {prune} vs unpruned `raw {rawn}` ({sum(Hq.values())} admissible sets): "
              f"{cells} cells ({nonzero} nonzero), mismatches: {bad[:5]} -> {'PASS' if ok else 'FAIL'}")
        fail += not ok
print("VALIDATION", "PASSED" if fail == 0 else f"FAILED ({fail})")
sys.exit(1 if fail else 0)
