# Independent exhaustive solver for Erdos Problem 357

Independent re-computation of the finite claims of the paper (Section 8, "Exact values for small n"):
M(1..28), f(77) = 28 and the 67 optimal sets.  Written from the definition only; none of the earlier
search programs of the research repository (they are not part of this release) was read until all
results in this directory were final (../COMPARISON.md says what was compared afterwards and what that
comparison found).  Everything here is computational evidence, not a formal proof: the "no sequence
exists" statements rest on the correctness of the program and of the pruning proofs of section 3.

**Quick start** (from this directory; Python 3 and a Rust toolchain; the whole list takes about two minutes):

```
cargo build --release --locked                  # bins target/release/exact and brute (about 5 s, no dependencies)
python compare_results.py                       # recorded results vs ../reference tables: ALL AGREE (< 1 s)
python validate.py target/release results/brute_N34.txt 30     # quick validation, grids up to 30 (seconds)
target/release/exact count 26 66 --threads 7    # 0 sets, 2563131703 nodes (about a minute)
```

On Windows use `py` for `python` and `target\release\exact.exe`.  `compare_results.py` and `validate.py`
default to the files of this release (`results/`, `../reference/exact_f_table_research.txt`,
`../reference/oeis_A364132.txt`); the arguments in their docstrings override them.  The full runs of
section 6 take hours and are not needed to read the results.

## Results (all with pruning R1 + R3 only, no M-bound; 7 threads)

* **M(k), k = 1..28** (= OEIS A364132 for k <= 22; k = 23..28 beyond the 22-term cache):

      k= 1..14:  1  2  4  5  7 10 12 13 15 18 21 24 25 29
      k=15..28: 30 33 36 38 41 47 50 52 56 60 63 67 69 75

* **Number of optimal sets at n = M(k)**, every one found by exhaustive enumeration (total **67**):
  1 1 2 1 1 7 5 1 1 2 1 13 1 5 1 1 1 1 1 3 5 1 2 2 2 2 1 2.  The sets are in `results/optimal_sets.txt`
  (`k M(k) a_1,...,a_k`, one line each).
* **f(n), n = 1..77** (`results/f_table.txt`; every row lists the log line that proves count(f(n)+1, n) = 0):

      n= 1..10:  1  2  2  3  4  4  5  5  5  6
      n=11..20:  6  7  8  8  9  9  9 10 10 10
      n=21..30: 11 11 11 12 13 13 13 13 14 15
      n=31..40: 15 15 16 16 16 17 17 18 18 18
      n=41..50: 19 19 19 19 19 19 20 20 20 21
      n=51..60: 21 22 22 22 22 23 23 23 23 24
      n=61..70: 24 24 25 25 25 25 26 26 27 27
      n=71..77: 27 27 27 27 28 28 28

* **The decisive searches** (exhaustive; "nodes" as defined in section 3):

  | (k, n) | result | nodes | wall s (7 threads, shared machine) |
  |---|---|--:|--:|
  | (27, 68) | **0** admissible 27-sequences with a_27 <= 68 (none in [1, 68]) | 3,511,032,181 | 72 |
  | (27, 69) | **1** (the unique optimal set for k = 27) | 5,552,300,898 | 117 |
  | (28, 69) | 0 | 2,921,438,674 | 59 |
  | (28, 70) | 0 | 4,795,998,821 | 105 |
  | (28, 71) | 0 | 7,584,119,692 | 171 |
  | (28, 72) | 0 | 12,220,133,884 | 281 |
  | (28, 73) | 0 | 19,113,213,033 | 427 |
  | (28, 74) | 0 | 30,445,560,524 | 688 |
  | (28, 75) | **2** (both optimal sets for k = 28) | 47,089,805,773 | 1044 |
  | (29, 77) | **0** admissible 29-sequences with a_29 <= 77, i.e. **f(77) = 28** | 63,850,867,140 | 1351 |

  All of these use R1 and R3 only.  In particular **the decisions at n = 71..77 do not use any M-value
  as a pruning bound**: the dependency "a_r >= M(r)" of the earlier programs is absent from this program
  (the only M-dependent code is the start value `prev_m + 1` of `table` and the way `ftable` picks k = f(n)+1; neither is part of the search below that node), so the n = 69 point (M(27) = 69,
  none in [1, 68]) and n = 71..77 are covered by a search whose pruning is the trivial room/free-slot
  counting of section 3.
* Totals: `table 28`: 75 (k, n) searches, 143,260,467,161 nodes, 3169 s; `ftable 68`: 68 searches,
  13,615,697,785 nodes, 271 s; `count 28 69`: 59 s; `count 29 77`: 1351 s.  Repeated (k, n) have identical
  node counts in every log (e.g. (27, 68): 3,511,032,181 in the table, in `ftable` and in the audit run).
* Everything agrees with the reference table `../reference/exact_f_table_research.txt` (a snapshot, n <= 77, of the
  table produced by the earlier programs of the research repository) and with OEIS A364132 (22 terms,
  `../reference/oeis_A364132.txt`): `logs/compare_results.log`, ../COMPARISON.md.
* Deep-state audit: at every 20000th node of the runs (26, 66), (27, 68), (28, 70) (1 thread each) the
  candidate set was re-derived from the definition: 128,156 + 175,551 + 239,799 sampled nodes, all identical.


## 1. Definition and notation

A sequence of integers 1 <= a_1 < a_2 < ... < a_k is *admissible* if the k(k+1)/2 block sums
a_u + ... + a_v (1 <= u <= v <= k) are pairwise distinct.  M(k) is the least n for which an
admissible k-term sequence with a_k <= n exists (OEIS A364132) and f(n) = max{k : M(k) <= n}.
Write P_i = a_1 + ... + a_i (P_0 = 0); the block sums are the differences P_v - P_{u-1}.
`count(k, n)` below is the number of admissible k-term sequences with a_k <= n.

## 2. Algorithm

Depth-first search, left to right.  A node is an admissible prefix a_1 < ... < a_j together with
the bitset U of its block sums (indexed by the sum, 4608 bits).

**Lemma 1 (extension criterion).**  Let a_1..a_j be admissible with block-sum set U and let
x > a_j.  Then a_1..a_j, x is admissible iff none of the j+1 numbers
`x + (P_j - P_i)`, i = j, j-1, ..., 0 (that is x, x+a_j, x+a_j+a_{j-1}, ..., x+a_j+...+a_1)
lies in U.

*Proof.* The block sums of the extended sequence are the old ones (U, pairwise distinct by
hypothesis) together with the j+1 block sums that end at the new last position, which are exactly
the listed numbers.  They are strictly increasing in i (all terms positive), hence pairwise
distinct among themselves.  So the whole family is pairwise distinct iff the new numbers avoid U. []

**Lemma 2 (heredity).**  Every prefix of an admissible sequence is admissible (its block sums are a
subset of the block sums of the whole sequence).  Consequently the search tree whose root is the
empty sequence and whose children of a_1..a_j are the admissible extensions a_1..a_j, x
(x > a_j) contains every admissible sequence exactly once, as the path a_1, a_2, ..., a_k.

**Candidate generation.**  For a node of depth j let lo = a_j + 1 (lo = 1 at the root).  The
candidates x in [lo, n] satisfying Lemma 1 are computed in one pass as a 128-bit mask
`cand = AND_{i=j..0}  NOT window(U, lo + P_j - P_i)` where `window(U, s)` is the 128 bits of U
starting at bit s (bit t of the mask stands for x = lo + t; the program asserts n <= 120 so the mask
covers [lo, n]).  Every candidate is a child; pushing it sets the j+1 new bits of U, popping clears them.
The bitset capacity is asserted at run time (largest possible block sum + 130 < 4608).

## 3. Pruning levels (`--prune`), their proofs, and the no-pruning mode

* **level 0 (`exact raw N`)**: *no pruning at all*.  Only Lemma 1 / Lemma 2: every admissible
  sequence with all terms <= N is visited (this is the whole search tree) and the program records
  the histogram `H[k][last]` of sizes and largest elements.  There is no target length, no room
  bound, no free-slot bound, nothing derived from any other computation.
* **level 1**: for a target (k, n) ("how many admissible k-sequences with a_k <= n exist, and which?")
  rule R1.
* **level 2 (default, used for every big run)**: level 1 plus rule R3 and its child form `precheck`.

None of the rules uses any M(r) or f(m), nor anything else computed by a previous search: the only
inputs are the node's own prefix, k and n.  **There is no "a_r >= M(r)" rule anywhere in this program,
so the n = 71..77 results do not depend on the table of M-values** (in particular the decisions
count(28, 71..74) = 0 and count(29, 75..77) = 0 are obtained with R1 + R3 only).  The only places
where an M-value is read at all are the *order of the table search* (the start point n = M(k-1)+1 for
k, which is covered by direct runs, see section 4) and `ftable` (which reads f(n) from the table to know
which k = f(n)+1 to test).

**R1 (room).**  If a prefix a_1..a_j extends to an admissible k-sequence with all terms <= n, then
x = a_{j+1} <= n - (k - j - 1).
*Proof.* a_{j+1} < a_{j+2} < ... < a_k <= n are integers, so a_k >= a_{j+1} + (k - j - 1). []

**R3 (free slots).**  Let F = { y : a_j < y <= n, y not in U } (U = block sums of the prefix).  If the
prefix extends to an admissible k-sequence with all terms <= n, then (i) |F| >= k - j, and
(ii) x = a_{j+1} is at most the (k-j)-th largest element of F.
*Proof.* Each of a_{j+1} < ... < a_k is an integer in (a_j, n]; and each is a block sum (of length 1)
of the extended sequence, whereas every element of U is also a block sum of the extended sequence, in
a different position; by admissibility of the extended sequence they differ.  So a_{j+1}, ..., a_k are
k - j distinct elements of F, which gives (i).  For (ii): a_{j+1} is in F and a_{j+2} < ... < a_k are
k-j-1 elements of F larger than it, so at least k-j elements of F are >= a_{j+1}, i.e. a_{j+1} is at most the
(k-j)-th largest element of F.  []
(R3(ii) implies R1 because F is contained in (a_j, n].)  In the code F is the mask `!window(U, lo)` cut
to [lo, n] *before* the Lemma-1 shifts are applied, which is exactly this F.

**R3 at the child (`precheck`).**  Before pushing a candidate x (so it is already known that x passes
Lemma 1) the program applies R3(i) to the child a_1..a_j, x, which has k-j-1 terms still to place:
the child is discarded unless it has at least k-j-1 free singles.
*Proof of the count.*  Let F be the free set of the parent (as above) and F' the free set of the child, F' = {y : x < y <= n,
y not in U'} with U' = U together with the j+1 new sums x + s, s in S = {0, a_j, a_j+a_{j-1}, ..., P_j}.
The new sums are pairwise distinct (S is strictly increasing).  The new sums that are <= n and larger
than x (those with s > 0, x+s <= n) were checked to be outside U (Lemma 1), and they lie in (a_j, n], so
they are elements of F above x.  Hence |F'| = |{y in F : y > x}| - |{s in S, s > 0 : x + s <= n}|.
The program evaluates exactly this (`above` = popcount of the parent's free mask above x, `r` = number of
nonzero s with s <= n - x, maintained incrementally as x increases) and requires
`above - r >= k - j - 1`.  By R3(i) applied to the child (which has j+1 terms and k-j-1 to place) a child
violating it has no completion, so discarding it never loses a solution.  []
(Only used when k > j+1; for the last term the check is vacuous.)

All three rules only discard nodes that have no completion, so the leaves reached at depth k are
exactly the admissible k-sequences with a_k <= n.  `count K N` returns their number; `--first`
(stop at the first leaf, count is then only a lower bound) is a debugging flag and is **not** used in
any reported result.

**Audit mode (`--audit R`).**  At every R-th visited node the engine recomputes the candidate set of
that node from the definition (a `HashSet` of all block sums, every x in [lo, n] tried) and compares
it with the bitset-window mask; any difference panics.  This tests Lemma 1's implementation on real
deep states, independently of the pruning.

**Parallelism and determinism.**  The tree is cut at the smallest depth d with >= 3000 nodes (same
pruning), the depth-d nodes are tasks handed out through an atomic counter to <= 8 worker threads
(7 for the main runs: the machine is shared); counts and node totals do not depend on the schedule
(the repeated runs of identical (k,n) in the logs show identical node counts).  `--ckpt` logs finished
tasks so an interrupted run resumes without changing any total.  "nodes" = DFS nodes pushed (leaves
included) plus the nodes above the split depth.

## 4. Determining M(k), the optimal sets and f(n)

**Searching for M(k).**  `table` runs, for k = 1, 2, ..., n = M(k-1)+1, M(k-1)+2, ... (M(0) := 0) and
stops at the first n with count(k, n) > 0; that n is M(k) and every set found has maximum exactly n
(no k-set has a_k < n; see below for why the skipped values n <= M(k-1) are covered), so the reported
sets are *all* the optimal sets.  Each reported set is re-checked from the definition inside the program
(`naive_admissible`, a HashSet of all block sums), again by `../witness_check.py`, and the whole set list
is compared with the reference table in ../COMPARISON.md.

**Why starting at n = M(k-1)+1 is not an assumption.**  "a_k <= n" is monotone in n, so count(k, n') = 0
for one n' implies count(k, n) = 0 for all n <= n'.  Hence M(k) is the least n with count(k, n) > 0 as soon as
count(k, M(k)-1) = 0 has been *computed directly*.  For 22 of the 28 values k the table itself computed
(k, M(k)-1) (because M(k)-1 >= M(k-1)+1); for k = 1 the claim is trivial (a_1 >= 1, so count(1, 0) = 0); for
the five k with M(k) = M(k-1)+1 (k = 2, 4, 8, 13, 15) the value count(k, M(k-1)) = count(k, M(k)-1) was
computed by `ftable` (it is the row n = M(k-1) of `logs/ftable_n68.log`).  So no prefix argument
(M(k) >= M(k-1)+1) is needed.

**f(n).**  f(n) >= k iff M(k) <= n.  For each n the claim f(n) = k needs, besides the set of size k,
count(k+1, n) = 0 (then no longer sequence exists either, because an admissible sequence with k+j terms
has an admissible (k+1)-term prefix with a_{k+1} <= n, Lemma 2).  Those zeros are established as follows:

* `ftable M_table.txt 68`: for **each** n = 1..68 separately, count(f(n)+1, n) = 0 (f(n) read from the M table);
* n = 69: `count 28 69` = 0 (28 terms, n = 69 = M(27));
* n = 70..74: the table's own runs (28, 70..74) = 0 (these have f(n) = 27, k = 28);
* n = 75, 76, 77 (f = 28, k = 29): the single run `count 29 77` = 0, which gives 75 and 76 by
  monotonicity in n (a 29-term sequence with a_29 <= 75 has a_29 <= 77).

`make_f_table.py` assembles `results/f_table.txt` from those logs and states, row by row, whether the
zero was obtained directly at that n or via a larger n' (it refuses to write a row without evidence).
A literal per-n run of `ftable` up to 77 was started in the first draft of `run_main.sh` and replaced by the
above because it would have repeated the table's computations (about 3 hours) for no new content.

**M(27) = 69.**  The table log has `k=27 n=68: 0 sets` (count(27, 68) = 0, 3,511,032,181 nodes, so there is
no admissible 27-term sequence with a_27 <= 68; by monotonicity none with a_27 <= n for any n <= 68, in
particular none in [1, 68]) and `k=27 n=69: 1 sets`.  `ftable` re-ran (27, 68) independently (n = 68 row of
`logs/ftable_n68.log`) with the identical node count.  The unique set is
7,14,15,19,24,33,37,38,39,41,44,49,50,51,53,54,56,59,60,62,63,64,65,66,67,68,69.

## 5. Validation (what makes the results trustworthy)

Everything is checked against procedures that share no code with the pruned engine.

1. **All-subsets brute force** (`src/bin/brute.rs`, from the definition, no pruning, no incremental state):
   all 2^34 - 1 = 17,179,869,183 non-empty subsets of {1..34}; 13,286,737 are admissible.  The unpruned
   tree enumeration `exact raw 34` reproduces the full histogram H[k][last] exactly.  (306 s on 6 threads.)
2. `exact grid 34 --prune 1` and `--prune 2` (the pruned search, every cell 1 <= k <= n <= 34) equal the brute force
   cumulative counts in all 595 cells (311 nonzero): zero mismatches for each pruning level.
3. `exact raw 52` (still no pruning, 10,528,138,219 admissible subsets of {1..52}, 90 s) against
   `exact grid 52 --prune 2`: all 1378 cells (653 nonzero), zero mismatches.
4. Brute-force M(k) for k = 1..16 and optimal-set counts (1,1,2,1,1,7,5,1,1,2,1,13,1,5,1,1) agree with the
   OEIS A364132 cache (22 terms; compared for all of them at the end, see COMPARISON.md).
5. In-engine and external re-check of every reported set: `naive_admissible` on each of the 67 sets; the
   stand-alone `../witness_check.py` (different code, different language) on every set of the reference
   table `../reference/exact_f_table_research.txt`.
6. Deep-state audit (`run_audits.sh`, `logs/audit_deep.log`): 543,506 sampled nodes of the real (26,66), (27,68), (28,70) trees, candidate sets identical to the naive derivation.
7. Level-1 (R1 only) repeats at depth (`run_prune1_checks.sh`, `logs/prune1_deep.log`): (26,66) = 0, (27,68) = 0,
   (27,69) = 1 (same set as with R1+R3), (28,70) = 0, (28,72) = 0 - same answers as level 2, 6-7 times the nodes
   (14.1e9, 21.4e9, 32.3e9, 32.3e9, 72.7e9; the last two cases (27,69) and (28,70) have identical trees, as they must when
   there is no admissible 28-term prefix).  This tests R3 / `precheck` (the code, not the proof) on the real deep states.

`validate.py` runs steps 1-4 (`validate.py BIN_DIR results/brute_N34.txt 34 52`); logs in `logs/validate_*.log`.

## 6. Exact commands

Toolchain: rustc 1.98.1, cargo 1.98.1, Windows 10 x64 (the recorded runs); Python 3.13.3.  No Rust or
Python dependencies beyond the standard libraries.  Build (`target/` is git-ignored; a build directory outside
the repository works as well, `CARGO_TARGET_DIR=<build-dir>`):

```
cd exact
cargo build --release --locked        # bins: target/release/exact, target/release/brute (exact.exe, brute.exe on Windows)
```

Hashes.  `logs/binary_sha256_validation.txt` records the sha256 of the two binaries used for the recorded runs
(`<build-dir>/exact.exe` 17399b1c943665bd75469510f52bedc64d7ffd9c6bb2606fb7ef382c125ace79, `<build-dir>/brute.exe`
331cf40c4b1821284eae8ee87f64b23b3b654aa4e883cb7a71a99039d88d8db9).  A rebuild from the files of this release with
the same toolchain gave different bytes (exact.exe 9beec440a38f41bb5bc74d75af98214628a8d7c9cf54744b0b92f617131ead46,
brute.exe c79198bf7ca97e4d054af955210038daaaab8e989fa86ba42eaf9ed5f90ef610), as is usual for executables that
embed build paths; the binaries are therefore not claimed to be bit-reproducible.  What identifies the program
is its source, with LF line endings as in this release (hashes in the table at the end of this section).  The
rebuilt binaries reproduce the recorded results; see "Re-run before release" in ../README.md.

Validation:

```
target/release/brute 34 6 > results/brute_N34.txt        # 306 s
python validate.py target/release results/brute_N34.txt 34 52    # logs/validate_final.log, 1100 s wall
```

Main run (`THREADS=7`, i.e. 7 worker threads; `<ckpt>` is a scratch directory for resumable task logs):

```
THREADS=7 bash run_main.sh target/release/exact . <ckpt>
#   = exact table 28                       --threads 7 --out results --ckpt <ckpt>     (logs/table_k28.log)
#     exact ftable results/M_table.txt 68  --threads 7 --out results --ckpt <ckpt>     (logs/ftable_n68.log)
#     exact count 28 69                    --threads 7                                  (logs/decisions_n69_77.log)
#     exact count 29 77                    --threads 7                                  (same)
python make_f_table.py .                   # results/f_table.txt
python compare_results.py                  # vs the reference table; see ../COMPARISON.md
bash run_audits.sh target/release/exact .  # logs/audit_deep.log, 1 thread
bash run_prune1_checks.sh target/release/exact .   # logs/prune1_deep.log, level-1 repeats, 8 threads
```

`run_main.sh`, `run_audits.sh` and `run_prune1_checks.sh` write into `logs/` and `results/` of the directory
given as second argument (they append to existing logs): to repeat them without touching the recorded logs, copy
this directory to a scratch location first and pass that.  Each of the two audit scripts takes about 25 minutes.

Files: `src/main.rs` (engine: `raw`, `count`, `table`, `ftable`, `grid`), `src/bin/brute.rs`,
`validate.py`, `compare_results.py`, `make_f_table.py`, `run_main.sh`,
`run_audits.sh`, `run_prune1_checks.sh`, `results/` (`M_table.txt`, `optimal_sets.txt` = the 67 sets with k and M(k),
`f_table.txt`, `f_table_decisions.txt`, `brute_N34.txt`), `logs/`.

| file | sha256 (LF line endings) |
|---|---|
| `src/main.rs` | cbf669ff8ca49aceb775fdc7c2cab7c79b79168b5d7e57ce65fe4b2c2605ee6e |
| `src/bin/brute.rs` | 8bdbe15fb1064546a65e4acf8f7937e44c541bf8992625863738ff3bf1f87f70 |
| `Cargo.lock` | 276ac00b4ab91e939183ec995f32d07c513fcaeebf266471a1607a8571ba4a13 |


## Machine and runtimes

AMD Ryzen 7 8700F (8 cores / 16 logical, 4.1 GHz max), 31.7 GB RAM, Windows 10 Home; the machine was shared with
other jobs (processor load 77-100 % throughout, of which these runs were a part), so wall times are
inflated and noisy; the engine ran with 7 worker threads (+ 1 for the audits / the side greedy run, never more
than 8 in total).  About 45-50 M nodes/s in aggregate.

| step | wall |
|---|--:|
| `brute 34` (6 threads) | 306 s |
| `validate.py ... 34 52` (grids + `raw 52` etc.) | 1100 s |
| `table 28` (M(1..28) + all sets) | 3169 s (52.8 min) |
| `ftable ... 68` | 271 s |
| `count 28 69` / `count 29 77` | 59 s / 1351 s |
| audits (3 runs, 1 thread each) | 356 s + 488 s + 701 s |
| level-1 repeats (8 threads) | 143 s + 216 s + 314 s + 303 s + 686 s |
| `witness_check.py` | a few seconds |

Everything above, from scratch with the committed sources, takes about 1.7 h on this machine.


## 7. Things to know

* `logs/after_table.out` holds the progress lines (stderr) of the `ftable` / `count` steps; `logs/run_main.stdout`
  is the stdout of the first wrapper (a duplicate of `logs/table_k28.log`).
* The first draft of `run_main.sh` was going to run `ftable ... 77` right after the table; the wrapper
  was stopped (the running `table` process was not touched) and replaced by the sequence in section 6.
  `logs/table_k28.log` therefore has a "wrapper script was replaced" note on its last line.
* `--ckpt` task logs live in a scratch directory and are not part of this release; they only make
  interrupted runs resumable.  No run reported here was interrupted.
* Run times are wall clock on a shared 16-thread machine at 77-100 % load from other jobs; absolute times
  carry no precision, the node counts are the reproducible quantity.
