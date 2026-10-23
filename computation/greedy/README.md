# Reverse-greedy sets: regeneration and independent verification

Section 8 of the paper ("Greedy sequences") reports a reverse greedy construction giving a valid sequence of
26813 terms in {1, ..., 2*10^7}.  This directory holds the generator (`rgreedy/`, Rust source), the 18 sets it
produces for n = 10^3 ... 2*10^7 (sizes k = 115 ... 26813), and an independent checker (`check_sets.py`).  The sets
were **re-generated from source** with the documented command

    rgreedy rev N --cmax 6.5 --dump rev_N.txt

and then every set was **verified by code written separately from the generator** (`check_sets.py`), not by the
tool's own `verify` mode or hash.  This is a computational check, not a proof; it says that these 18 finite
sequences have the stated properties, and nothing about the growth of f(n).

## Contents

| file | what |
|---|---|
| `rgreedy/` | the generator: `Cargo.toml`, `Cargo.lock`, `src/main.rs` (the tool `rgreedy`: modes `rev`, `fwd`, `verify`, `brute`, `look`), `src/bin/parab.rs` (a separate exploratory annealing search for Sidon sets of the form parabola plus bounded noise, built with it; not used for the 18 sets) |
| `run_greedy.sh` | regenerates the 18 sets with the documented command; refuses to start a run that would leave too little free RAM (see below) |
| `check_sets.py` | independent checker (parses sets, FNV-1a-64 digest, two admissibility methods A/B, self-test) |
| `expected.tsv` | expected n, k and FNV-1a-64 digest of each set, plus the table bits and wall time, taken from the table of an earlier run of the same tool (recorded in the research notes, which are not part of this release); `check_sets.py` compares with it (the "doc" columns in its output) |
| `sets/rev_N.txt` | the 18 regenerated sets (one line, `a_1,...,a_k`; 789 KB in total) |
| `digests.tsv` | per set: k, FNV-1a-64 recomputed here / from `expected.tsv` / printed by the tool, sha256 of the file, A/B verdicts, checker seconds (written by `check_sets.py --digests`) |
| `logs/run_greedy.log` | the tool's own output lines for all 18 runs (`table_bits`, `load`, `probes`, `fnv`, `time`) and free RAM before each; `logs/run_greedy.stdout` is the same text |
| `logs/check_sets.log` | the checker's output (self-test, then one line per set, `ALL 18 ROWS OK`) |
| `logs/rev_20000000_bits29.log` | side run of the n = 2*10^7 row with `--bits 29` (see "Table-size discrepancy") |

## Commands

Requirements: a Rust toolchain (the recorded runs used rustc/cargo 1.98.1; no dependencies), Python 3 with numpy
(recorded: Python 3.13.3, numpy 2.2.6).

```
# build the tool (about 3 s); the binary is rgreedy/target/release/rgreedy (rgreedy.exe on Windows)
cd rgreedy
cargo build --release --locked
cd ..

# quick regeneration: the 13 sets with n <= 10^6, into ./regen (about 15 s), compared byte for byte with sets/
MAXN=1000000 bash run_greedy.sh
for f in regen/sets/*.txt; do cmp "$f" "sets/$(basename $f)" && echo "identical: $f"; done
python check_sets.py regen expected.tsv --upto 1000000

# full regeneration of all 18 sets into ./regen (single thread per run, about 25 minutes; the last two runs need
# 2.7 GB (n = 10^7) and 5.4 GB (n = 2*10^7) of RAM for the hash table)
bash run_greedy.sh

# verify the committed sets without regenerating (about 2 minutes, mostly the n = 2*10^7 row)
python check_sets.py
```

`run_greedy.sh [RGREEDY_EXE [OUTDIR]]` writes `OUTDIR/sets/rev_N.txt` and `OUTDIR/logs/run_greedy.log` (default
`OUTDIR=./regen`); it never touches the committed `sets/` and `logs/` unless you pass this directory itself.  Before
every run it checks the free RAM and refuses to start if less than 3 GB (6 GB for n >= 5*10^6, 9 GB for
n >= 1.5*10^7, the default table of that size being 5.4 GB) would be free; if the free RAM cannot be determined it
says so and continues.  The recorded `logs/run_greedy.log` was produced by an earlier version of the script with
slightly different thresholds (for example `need >= 6.0` for n = 2*10^7); the commands passed to `rgreedy` are the
same.  `check_sets.py [GREEDY_DIR [EXPECTED_TSV]] [--upto N] [--digests OUT] [--log RUN_LOG]` exits with status 0
iff every row is OK; without `--digests` it writes nothing.

Hashes.  The recorded runs used an `rgreedy.exe` with sha256
7c50c51a15af24deeb283dcd618bbb0190f1f508c40757818e26cefb2c495fcf, built from a `src/main.rs` whose sha256 was
77dc7ca87605fc765123dad360b774855208d2482baff1d8ff77672ef89265e2.  The copy in this release has LF line endings
instead of the original CRLF; apart from that conversion the file is the same (verified by comparing the two after
removing carriage returns), and its sha256 is 91c4eae43914c3bea56bc6a2750388a60b76db5e28fe833bb4918083ec6b5fa9.
(`Cargo.lock` 1747403e40bcaf2370b82f380da0ba3453ca29407ce3cee6638fc317ecd3f6be, `src/bin/parab.rs`
1c0d320a92b7ab21444e6e12d71a1d7be9c8b3e263c1821774951d55604905ff.)  A rebuild from this release with the same
toolchain gave an `rgreedy.exe` with sha256 2aa2ae617f0e0a8f75d58bf2f8c5b625d5a52eab3f9817377c27c4b68a81d074, which
differs from the recorded one, as is usual for executables that embed build paths; binaries are not claimed to be
bit-reproducible.  What the rebuilt binary does reproduce is the output: the 13 sets with n <= 10^6 are
byte-identical to `sets/`, and the lines printed by the tool (`k`, `sum`, `table_bits`, `load`, `probes`, `accepts`,
`rejects`, `fnv`; not `time`) are identical to the corresponding lines of `logs/run_greedy.log`.  The five largest
sets (n >= 1.7*10^6) were not regenerated again for this release (they take about 25 minutes together and up to
5.4 GB of RAM); they were checked in place by `check_sets.py` against the recorded digests.

## Results

All 18 rows: size k equals the `expected.tsv` value; the FNV-1a-64 digest recomputed by the checker (over the decimal
text `a_1,a_2,...,a_k`) equals the `expected.tsv` value **and** the tool's printed value; the set is strictly
increasing with a_k <= n; and the k(k+1)/2 block sums are pairwise distinct by **both** methods:

* method A: build every block sum from the definition (for each length l, `P[l:] - P[:-l]` for the prefix-sum array P), sort, require strict increase. It ran for every row, including n = 2*10^7 (k(k+1)/2 = 359,481,891 block sums; 30.3 s) because enough RAM was free.  If less than the needed RAM is free the checker skips method A for that row and says so.
* method B: a different mechanism that never holds all sums at once: the pairwise differences P_j - P_i are generated in consecutive *value intervals* (<= 12,000,000 pairs each, boundaries found by bisection), sorted and checked chunk by chunk; the checker asserts that the chunks together contain exactly k(k+1)/2 pairs.

Checker self-test (before any set): both methods and a naive Python `set` check agree on {1,2,3,4}
(inadmissible), {1,2,4,8} (admissible), on 3000 random sequences (1180 admissible, 1820 not), and
on all 11 single-element +-1 perturbations of the n = 1000 set (all inadmissible), so a failing
verdict is attainable.

`digests.tsv` has the full table; excerpt:

| n | k | FNV-1a-64 (recomputed = expected = tool) |
|--:|--:|:--|
| 1000 | 115 | d0bf5bcee463a356 |
| 10000 | 435 | 6729f65791456e68 |
| 100000 | 1556 | cca93c9881fa0ce3 |
| 1000000 | 5424 | 31b66e12b2b122ae |
| 10000000 | 18550 | 60dcc239a58687e8 |
| 20000000 | 26813 | 4031502380f50c87 |

The independent second check of the n = 2*10^7 set quoted in the paper is `../review-checks/greedy_valid.py` (a
different program: block sums bucketed by residue, each bucket sorted); its recorded output is
`../review-checks/greedy_valid_2e7.out`.

Differences between a re-run of `check_sets.py` and the recorded `logs/check_sets.log`: the times in brackets, the
final `wall=` line, and the first line, which in the recorded log reads "parsed 18 rows of the research notes (not
public) Section 4 table" (the name of the internal file was replaced) and now reads "parsed 18 expected rows from
expected.tsv".  The recorded `digests.tsv` has its two column names renamed (`fnv1a64_expected`, `k_expected`, from
names that referred to the internal file); the data are unchanged.

## Table-size discrepancy for the n = 2*10^7 row (reported, not explained away)

The earlier run whose table is in `expected.tsv` used `table_bits 29` (2.7 GB, load 0.67, 1039.9 s) for the last
row.  With the documented command (`--cmax 6.5`, no `--bits`) the tool in this release chose
`table_bits=30` (5.4 GB, load 0.335, 955.3 s) for n = 2*10^7.  The *output* is the same either way:
the side run with an explicit `--bits 29` gave `table_bits=29 load=0.670 ... time=1029.2 s`
(matching the earlier load figure and approximately its time) and a file that is
**byte-for-byte identical** to `sets/rev_20000000.txt` (`cmp`; same k = 26813, same
fnv 4031502380f50c87). So the sets and digests reproduce exactly; only the earlier memory
figure corresponds to an explicit `--bits 29`, not to the default of the documented command in the
current source. The other 17 rows used exactly the table bits listed in `expected.tsv` (compare `table_bits=`
in `logs/run_greedy.log` with the table). The tool's table-size rule is not what the remark in the earlier notes
(that the `--cmax` default only sizes the table) suggests for this one row; we did not investigate whether the
source changed after that run.

Runtimes are wall-clock on a shared machine (load 77-100 % from other jobs) and are noisy.
