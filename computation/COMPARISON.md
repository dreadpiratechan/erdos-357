# Comparison of the independent reproduction with the claims of the research repository

Reproduction by an independent solver (`exact/`), an independent set checker (`witness_check.py`) and a
re-generation + independent verification of the reverse-greedy sets (`greedy/`).  Everything below is a
plain comparison.  No disagreement was found in the finite exact claims; one documentation discrepancy in
the greedy table was found and is reported in section 3 as found.  This is a comparison of computations;
it is computational evidence, not a proof.

The programs, the runs and this comparison were written and carried out by AI sessions (see
`../docs/PROVENANCE.md`); no person has repeated them. "Independent" below means written without access to the
earlier programs of the research repository, not done by a different person. "Here" means this reproduction; the
columns headed "mine" in `exact/logs/compare_results.log` are the same as the columns headed "here" below.

"The repository" (columns "repo" and "doc" below) is the research repository in which the paper's results were
found; it is not part of this release.  Its claims enter here only through two files that are included:
`reference/exact_f_table_research.txt` (its table of M(k), f(n) and the optimal sets, snapshot for n <= 77; the
"repo" columns) and `greedy/expected.tsv` (the table of the reverse-greedy sets; the "doc" columns).  The research
notes that state the other claims quoted below (called note E and note V below; the greedy table is in a third note) are not
included, so those claims can be compared with the computation but not traced to their source from this release.

## 0. Independence log (what was read and when)

* Before the results below were final, the session that wrote them did **not** open any of the six earlier search programs of the research
  repository (four Rust programs and two Python programs; not part of this release), nor the two research notes
  that describe them (notes E and V).  Inputs read earlier: the problem definition; the
  repository's table of M(k), f(n) and optimal sets (only as the thing to compare with: `witness_check.py` and
  `compare_results.py` read it, the solver does not; snapshot in `reference/exact_f_table_research.txt`); the
  cached OEIS A364132 terms (`reference/oeis_A364132.txt`); the sections of the research notes that give the
  greedy commands and table (now `greedy/expected.tsv`); a grep of the repository's problem README; the
  command-line, FNV and dump code of the `rgreedy` tool (`greedy/rgreedy/src/main.rs`; the tool itself is the
  object being regenerated).
* After the results were final (all runs finished, `f_table.txt` written, `compare_results.py` run) the session read the
  two research notes and the header/pruning comments of two of the earlier programs to compare the methods (section 4).  It did not run those programs and did not
  read their code bodies.

## 1. Exact claims, line by line

Compared by `exact/compare_results.py` (reads `exact/results/*` and the reference table
`reference/exact_f_table_research.txt`; output saved in `exact/logs/compare_results.log`):

| k | M(k) here | M(k) repo | OEIS A364132 | sets here | sets repo | identical set lists | verdict |
|--:|--:|--:|--:|--:|--:|:-:|:-:|
| 1 | 1 | 1 | 1 | 1 | 1 | yes | agree |
| 2 | 2 | 2 | 2 | 1 | 1 | yes | agree |
| 3 | 4 | 4 | 4 | 2 | 2 | yes | agree |
| 4 | 5 | 5 | 5 | 1 | 1 | yes | agree |
| 5 | 7 | 7 | 7 | 1 | 1 | yes | agree |
| 6 | 10 | 10 | 10 | 7 | 7 | yes | agree |
| 7 | 12 | 12 | 12 | 5 | 5 | yes | agree |
| 8 | 13 | 13 | 13 | 1 | 1 | yes | agree |
| 9 | 15 | 15 | 15 | 1 | 1 | yes | agree |
| 10 | 18 | 18 | 18 | 2 | 2 | yes | agree |
| 11 | 21 | 21 | 21 | 1 | 1 | yes | agree |
| 12 | 24 | 24 | 24 | 13 | 13 | yes | agree |
| 13 | 25 | 25 | 25 | 1 | 1 | yes | agree |
| 14 | 29 | 29 | 29 | 5 | 5 | yes | agree |
| 15 | 30 | 30 | 30 | 1 | 1 | yes | agree |
| 16 | 33 | 33 | 33 | 1 | 1 | yes | agree |
| 17 | 36 | 36 | 36 | 1 | 1 | yes | agree |
| 18 | 38 | 38 | 38 | 1 | 1 | yes | agree |
| 19 | 41 | 41 | 41 | 1 | 1 | yes | agree |
| 20 | 47 | 47 | 47 | 3 | 3 | yes | agree |
| 21 | 50 | 50 | 50 | 5 | 5 | yes | agree |
| 22 | 52 | 52 | 52 | 1 | 1 | yes | agree |
| 23 | 56 | 56 | - | 2 | 2 | yes | agree |
| 24 | 60 | 60 | - | 2 | 2 | yes | agree |
| 25 | 63 | 63 | - | 2 | 2 | yes | agree |
| 26 | 67 | 67 | - | 2 | 2 | yes | agree |
| 27 | 69 | 69 | - | 1 | 1 | yes | agree |
| 28 | 75 | 75 | - | 2 | 2 | yes | agree |

Total optimal sets: here 67, repo 67.  f(n) for n = 1..77: 77 values here, 77 repo; disagreements at
n = none.  f(77): here 28, repo 28.  `RESULT: ALL AGREE`.  (OEIS column: the 22 cached terms of A364132;
`-` = beyond the cache.)

| claim (source) | repository | this reproduction | status |
|---|---|---|---|
| M(1..28) = 1,2,4,5,7,10,12,13,15,18,21,24,25,29,30,33,36,38,41,47,50,52,56,60,63,67,69,75 (notes E Sect. 4 and V; the table) | as listed | identical, all 28 values | agree |
| M(1..22) = OEIS A364132 | 22 terms | identical, 22 terms (brute force also agrees for k <= 16) | agree |
| f(n), n = 1..77 (reference table, section f) | 77 values | 77/77 identical (`exact/results/f_table.txt`, every row backed by a logged zero count) | agree |
| f(77) = 28, i.e. no admissible 29-term sequence with a_29 <= 77 | claimed | count(29, 77) = **0**, 63,850,867,140 nodes, R1+R3 only (n = 75, 76 follow by monotonicity in n) | agree |
| M(29) >= 78 (note V: E(29,76), E(29,77) false) | claimed | the same statement (a_29 <= 77 impossible) | agree |
| optimal-set counts at n = M(k): 1,1,2,1,1,7,5,1,1,2,1,13,1,5,1,1,1,1,1,3,5,1,2,2,2,2,1,2 (total 67) | claimed | identical, total 67 | agree |
| the 67 optimal sets themselves (reference table, section M) | 67 sets | set lists identical for every k (sorted comparison); each set also re-checked by the engine's naive checker and by `witness_check.py` | agree |
| M(27) = 69, none in [1, 68] | claimed | count(27, 68) = **0** (3,511,032,181 nodes), hence none in [1, 68] ("a_27 <= n" is monotone in n); count(27, 69) = 1, the unique set 7,14,15,19,24,33,37,38,39,41,44,49,50,51,53,54,56,59,60,62,63,64,65,66,67,68,69 | agree |
| negatives E(28,71..74), E(29,76), E(29,77) (note V lists these as "Not done without the M-bound"; the second earlier program used a_r >= M(r)) | negatives, with the M-bound | count(28, 71..74) = 0 and count(29, 77) = 0 with **no M-bound** (R1+R3 only); count(28, 75) = 2 | agree, now also without the M-bound |
| f(n) <= f(n-1) + 1 (note E Sect. 2) | claimed | increments of the f table here are 0 or 1 for n = 1..77 | agree |
| (note E Sect. 6) unique optimum for k = 1,2,4,5,8,9,11,13,15,16,17,18,19,22 and k = 27; largest count 13 at k = 12; M(k+1)-M(k) in 1..4 except 6 at k = 19->20 and 27->28 | claimed | follows from the M(k) and counts here (count = 1 exactly at these k and 27; differences as stated) | agree |

Not reproduced (outside the scope of this reproduction): the bridge from the Lean `Erdos357.f` to the finite search
predicate (note E Sect. 1), the run-time / node statements of note E Sect. 9, and the structural
observations of note E Sect. 6 other than the last row above.

## 2. Checks on the engine itself

Details and logs: `exact/README.md` section 5, `exact/logs/`.

* All-subsets brute force over {1..34} (17,179,869,183 subsets, 13,286,737 admissible) vs the unpruned tree
  enumeration (`raw`): identical histogram.  vs the pruned search at prune levels 1 and 2 for every (k, n),
  1 <= k <= n <= 34: 0 mismatches in 595 cells each.
* Pruned search (level 2) vs the unpruned enumeration `raw 52` (10,528,138,219 sets): 0 mismatches in 1378 cells.
* Audit of the Lemma-1 candidate masks against a naive HashSet derivation at 543,506 sampled nodes of the real
  (26,66), (27,68), (28,70) trees: all identical.
* Pruning level 1 (room bound R1 only, one-line proof; no free-slot counting) repeated at depth, 8 threads:
  (26,66) = 0 (14,143,925,202 nodes), (27,68) = 0 (21,390,565,977), (27,69) = 1 with the same set
  (32,253,751,315), (28,70) = 0 (32,253,751,315 - identical to the (27,69) tree, as it must be when no admissible
  28-term prefix exists), (28,72) = 0 (72,701,801,709 nodes): the same answers as with R1+R3
  (`exact/logs/prune1_deep.log`).  So the n = 68 / 69 / 70 / 72 decisions also hold with the weakest prune.
* Repeated (k, n) have identical node counts across the table, `ftable`, `count` and audit runs.
* `witness_check.py` (separate language, no shared code) on all 67 sets of the reference table and its M /
  count claims: ALL CHECKS PASSED.

## 3. Reverse-greedy sets (table of the research notes, now `greedy/expected.tsv`)

Regenerated with the documented command `rgreedy rev N --cmax 6.5 --dump rev_N.txt` (tool built from the
unmodified source, `src/main.rs` sha256 77dc7ca8... for the original CRLF file, 91c4eae4... for the LF copy in
`greedy/rgreedy/`; see `greedy/README.md`) and verified by `greedy/check_sets.py` (own FNV-1a-64, two
admissibility methods).  "doc" in the table is `greedy/expected.tsv`:

| n | k here / doc | FNV-1a-64 here = doc = tool | checker A (sort all) | checker B (chunked) | table bits here / doc | tool time s here / doc |
|--:|:-:|:-:|:-:|:-:|:-:|:-:|
| 1,000 | 115 / 115 | d0bf5bcee463a356 | True | True | 16 / 16 | 0.0 / 0.0 |
| 1,778 | 156 / 156 | 77e575aed5c8cb64 | True | True | 17 / 17 | 0.0 / 0.0 |
| 3,162 | 227 / 227 | 829e6e83a2f68409 | True | True | 17 / 17 | 0.0 / 0.0 |
| 5,623 | 313 / 313 | 464294faa0949d69 | True | True | 18 / 18 | 0.0 / 0.0 |
| 10,000 | 435 / 435 | 6729f65791456e68 | True | True | 19 / 19 | 0.0 / 0.0 |
| 17,783 | 610 / 610 | af903255612a065b | True | True | 20 / 20 | 0.0 / 0.0 |
| 31,623 | 821 / 821 | b06227fa30d7c41f | True | True | 21 / 21 | 0.0 / 0.0 |
| 56,234 | 1136 / 1136 | f5d03266b113d1cb | True | True | 22 / 22 | 0.1 / 0.1 |
| 100,000 | 1556 / 1556 | cca93c9881fa0ce3 | True | True | 22 / 22 | 0.3 / 0.2 |
| 177,828 | 2128 / 2128 | b8d2ef1211d9e5c1 | True | True | 23 / 23 | 0.6 / 0.5 |
| 316,228 | 2914 / 2914 | 853986e2a0e328b2 | True | True | 24 / 24 | 1.2 / 1.1 |
| 562,341 | 3993 / 3993 | bfe6fce42ee30c4e | True | True | 25 / 25 | 2.5 / 2.5 |
| 1,000,000 | 5424 / 5424 | 31b66e12b2b122ae | True | True | 26 / 26 | 6.6 / 6.2 |
| 1,778,279 | 7401 / 7401 | 73f873079e274567 | True | True | 27 / 27 | 16.1 / 16.1 |
| 3,162,278 | 10054 / 10054 | 860c590f423ebe61 | True | True | 27 / 27 | 34.0 / 37.0 |
| 5,623,413 | 13673 / 13673 | f3400e3ff71f0df6 | True | True | 28 / 28 | 84.5 / 100.6 |
| 10,000,000 | 18550 / 18550 | 60dcc239a58687e8 | True | True | 29 / 29 | 260.2 / 272.8 |
| 20,000,000 | 26813 / 26813 | 4031502380f50c87 | True | True | **30 != 29** | 955.3 / 1039.9 |

* All 18 sets: size equal to the table, FNV-1a-64 equal to the table and to the tool's own output, strictly
  increasing with a_k <= n, and all k(k+1)/2 block sums pairwise distinct by **both** checker methods (method A
  sorts every block sum, including the 359,481,891 sums of the n = 2*10^7 set).
* **Documentation discrepancy (reported, not explained away):** for n = 20,000,000 the table in the research
  notes (= `greedy/expected.tsv`) says `table bits 29` (and the notes' Sect. 3 says: 2^29 slots = 2.7 GB at load
  0.67, 1039.9 s).  With the documented command the tool's current source used `table_bits=30`
  (5.4 GB, load 0.335, 955.3 s).  The output is
  identical either way: a side run with an explicit `--bits 29` gave table_bits=29, load 0.670, 1029.2 s and a file
  byte-for-byte equal to the first (`greedy/logs/rev_20000000_bits29.log`).  So the sets and digests reproduce
  exactly; the memory / load figures in the notes correspond to an explicit `--bits 29`, not to the default of the
  stated command with the current source.  The other 17 rows have exactly the documented table bits.

## 4. Method comparison with the earlier programs of the repository (read after the results were final)

"Program A" and "program B" are two of the earlier Rust search programs of the research repository (not part of
this release).

| | this reproduction (`exact/`) | program A | program B |
|---|---|---|---|
| question per run | count(k, n): number of admissible k-sequences with **a_k <= n** | E(k, n): exists a_k = n exactly | E(K, N): a_K = N pinned |
| order | bottom-up | bottom-up | top-down (Golomb ruler, decreasing) |
| prunes | R1 (room), R3 (free singles; also at the child); one-line counting proofs | P0 range + P1 chain DP (pair sums of the remaining terms) | only the bound a_r >= M(r) (none with `--nomb`) |
| uses M-values to prune | **never** | no | yes (its own earlier M); `--nomb` only for n <= 68 and n = 70 |
| unpruned mode | `raw N` enumerates every admissible set in {1..N} | `--noprune` (P1 off) | `--nomb` |
| (27,68) nodes | 3.51e9 | n/a | 7.9e8 (M-bound), 6.07e10 (`--nomb`) |
| (28,70) nodes | 4.80e9 | n/a | 7.0e8 (M-bound), 1.04e11 (`--nomb`) |
| (28,74) nodes | 3.04e10 | 3.2e9 (note E) | 1.7e10 (M-bound) |

Node counts answer different questions with different node definitions; they show orders of magnitude only.

* The prunes here are the weakest of the three in the sense that each is a one-line counting argument; the price is more
  nodes than the chain-DP engine at the largest n, and the gain is that no previous M-value and no deep
  argument is needed.
* The research notes (note V Sect. 3.2) could not remove the M-bound for E(28,71..74), E(29,76), E(29,77)
  (cost).  This reproduction does, with a different tree (a_k <= n instead of the pinned top term), a different
  search direction than program B and different pruning than program A.

## 5. What is not independent / residual risks

* The problem definition is the same text for everybody; all programs implement it the same way (block sums of
  consecutive terms pairwise distinct).  OEIS A364132 agrees for k <= 22 only.
* The three solvers (this one and programs A and B) share the language (Rust), the compiler family and the machine
  type.  The brute force and the Python witness checker are the only code outside that family.
* Pruned counts beyond n = 52 are validated against the unpruned enumeration only up to n = 52; R3 and
  `precheck` rely on their proofs (README section 3) and on the cross-checks of section 2 at larger n.
* The comparison with the repository's table was made only after the results here were final (section 0), so no
  repository value influenced the search.
