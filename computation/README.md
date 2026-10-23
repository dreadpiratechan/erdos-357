# Computation: programs, data and logs for Section 8

This directory holds the programs, data and recorded outputs behind the finite computations of the paper
(Section 8, "Finite computations"): an exhaustive solver for the exact values of M(k) and f(n) for small
arguments, the reverse greedy sets with a generator and a checker, finite checks of the lower- and upper-bound
constructions, and the recomputations of an adversarial review.

**What these are.**  Computational checks and data.  They are evidence, not proofs.  The programs were written and
run, and this directory was prepared, by AI sessions (see `../docs/PROVENANCE.md`); no person has repeated the runs.  The proofs of Theorems 1.1 to 1.3
are the written proofs of the paper and the Lean development in `../lean/`; none of the computations here is used in
them (Section 8 says the same).  The "no sequence exists" statements of the exhaustive search rest on the correctness
of the search programs and of the pruning proofs, which are written out in `exact/README.md`; the programs were
cross-checked against brute force on small ranges and against each other, as described there, but nothing here is a
formal verification.  Finite data do not decide whether f(n)/sqrt(n) is bounded.

## Layout

| path | contents | paper |
|---|---|---|
| `witness_check.py`, `witness_check.log` | stand-alone checker for the table of exact values: every listed sequence is re-checked from the definition, and the M and f columns are checked for consistency and against OEIS A364132 | Section 8, exact values |
| `exact/` | the exhaustive solver (Rust), validation against brute force, the results (`M_table.txt`, `optimal_sets.txt`, `f_table.txt`) and logs; see `exact/README.md` | Section 8, exact values |
| `COMPARISON.md` | comparison of the solver's results with the earlier computations of the research repository, line by line, and of the greedy sets with their expected values | Section 8 |
| `greedy/` | the reverse greedy generator (`rgreedy/`, Rust), the 18 sets, an independent checker, and logs; see `greedy/README.md` | Section 8, greedy sequences |
| `lower-bound-checks/` | independent checks of the modulus-42 family, the skip construction and the arithmetic of the upper bound | Sections 4 to 6; Section 8, "Checks of the proofs" |
| `review-checks/` | recomputations by an adversarial review, with their recorded outputs; see `review-checks/README.md` | Sections 4 to 6, 8; `../docs/REVIEWS.md` |
| `reference/` | the inputs the scripts compare with: `exact_f_table_research.txt` (table of M(k), f(n) for n <= 77 and the optimal sets, from the research repository's earlier programs) and `oeis_A364132.txt` (the 22 terms of OEIS A364132, CC BY-SA 4.0, see `../NOTICE`) | |

## Requirements

* Python 3 (recorded runs: 3.13.3).  `witness_check.py`, `exact/compare_results.py`, `exact/validate.py` and
  `exact/make_f_table.py` need only the standard library.
* numpy (2.2.6) for `greedy/check_sets.py` and most of `review-checks/`; numba (0.62.1) for
  `lower-bound-checks/`, `review-checks/exact_small.py`, `review-checks/greedy_valid.py` and `review-checks/s6_count.py`;
  sympy (1.14.0) for `review-checks/s6_check.py` and `s6_check_only.py`.
* Rust, rustc/cargo 1.98.1 (recorded), for `exact/` and `greedy/rgreedy/`; no crates are downloaded (no dependencies).
* The numba scripts must not be run with `python -I`.  numba writes a cache into `__pycache__` next to each script; set
  `NUMBA_CACHE_DIR` (and `PYTHONDONTWRITEBYTECODE=1`) to a scratch directory to keep the repository clean.  `.gitignore`
  excludes `target/`, `__pycache__/` and `greedy/regen/`.
* All scripts locate their inputs relative to their own location, so they can be run from any directory.  On Windows
  use `py` for `python`; the shell scripts (`*.sh`) need Bash.
* Recorded machine: Windows 10, 16 logical processors, 31.7 GB RAM, shared with other jobs.

## Quick start

From this directory.  Runtime classes: *seconds* (under a minute), *minutes* (1 to 15 minutes), *long* (over 15 minutes).

```
python witness_check.py                                  # seconds: ALL CHECKS PASSED
python exact/compare_results.py                          # seconds: ALL AGREE
(cd exact && cargo build --release --locked)             # seconds
python exact/validate.py exact/target/release exact/results/brute_N34.txt 30   # seconds
exact/target/release/exact count 26 66 --threads 7       # about 1 minute: 0 sets, 2563131703 nodes
(cd greedy/rgreedy && cargo build --release --locked)    # seconds
(cd greedy && MAXN=1000000 bash run_greedy.sh)           # seconds: regenerates 13 of the 18 sets into greedy/regen
(cd greedy && python check_sets.py)                      # minutes: checks the 18 committed sets
python lower-bound-checks/check_lower.py quick           # seconds
python lower-bound-checks/spectra_table.py               # seconds
```

Longer runs, from the per-directory READMEs: `exact/validate.py ... 34 52` (about 15 to 20 minutes), the full
`greedy/run_greedy.sh` (about 25 minutes, up to 5.4 GB of RAM), `lower-bound-checks/check_lower.py full` (about 15
minutes), and the exhaustive searches of `exact/` (hours; `exact/README.md` section 6).

## Lower-bound and upper-bound checks (`lower-bound-checks/`)

Run these from any directory without `-I`.  "Recorded log" is the output of the original run (in `logs/`).

| script | what it recomputes | paper | command | runtime | recorded log |
|---|---|---|---|---|---|
| `check_lower.py` | L1 pattern facts for R = (2,7,11,25,26,34) mod 42 (the residue spectra of window lengths 0..11 partition Z/42); L2 the modulus-42 family for m = 1..60 (all window sums distinct, maximal term, negative controls); L3 the window formula on random windows; L4 the phase filter over all 216 triples; L5 the skip sequence for j = 1..4 and every u in the window (all equal-sum pairs of windows found by brute force, each of the predicted type); L6 larger rows j = 10, 25, 50 (including a negative control); L7 exact counts of bad u for j = 500, 501, 1000, 2000; L8 the assembly arithmetic | Sections 5 and 6; Section 8, "Checks of the proofs", items 2, 3, 5 | `python check_lower.py quick` or `full` | quick: seconds; full: about 15 minutes (recorded: 870 s) | `check_lower_full.log` |
| `check_upper.py [NMAX]` | U1 to U6: the side conditions of the (5, 9) design of the 797/1620 bound for 12 <= n <= NMAX, fiber degree at most 2, the closing arithmetic, the real-form step, the intermediate inequalities on concrete admissible sets (n up to 3000), and an exhaustive pass over all admissible sets for n <= 21 | Section 4 and its remark on the 797/1620 bound (Lean: `f_le_real2`); Section 8, item 1 | `python check_upper.py` (NMAX = 10^7) | seconds (about 30 s) | `check_upper_default.log` (produced when this release was assembled) |
| `check_lower_extra.py` | E1 the four modulus-42 patterns are R, -R, R+21, -R+21; E2 for every j = 1..499 the window contains a u with no divisor pair; E3 the thresholds for j = 2, 3 below the left end of the window | Sections 5 and 6; Section 8, item 4; remarks on j < 500 and on 15/sqrt(21) | `python check_lower_extra.py` | minutes (about 3.5 min) | `check_lower_extra.log` |
| `check_referee_claims.py` | R1 the largest offset 42t below the proof's offset that still gives coincidences, for m = 20, 60, 100; R2 Pickhardt's construction is valid for k = 40, 100, 200, 400 | Section 5, remark on the offset (R1); Pickhardt's construction cited in Section 2 (R2) | `python check_referee_claims.py` | seconds | `check_referee_claims.log` |
| `check_small_facts.py` | the smallest valid offset u for j = 2, 3; the reverse greedy length at n = 1000, 2000, 3000 | Section 6, remark on 15/sqrt(21) | `python check_small_facts.py` | about 1.5 minutes (mostly numba compilation) | `check_small_facts.log` |
| `spectra_table.py` | the residue spectra D_0..D_11 of the modulus-42 pattern (the table of the paper) and that they partition Z/42 | Section 5 | `python spectra_table.py` | seconds | `spectra_table.log` |

`check_lower.py full` wrote a first line with the date and a truncated sha256 of the script that was run
(`ffba058f5680045b`).  The script in this release differs from that one in its docstring only (private names removed),
so the hash of the file differs.

## Recorded logs and what differs when you re-run

The `logs/` and `*.out`/`*.log` files are the outputs of the original runs and were not regenerated.  They were edited
only to remove machine-specific paths and names of internal files; no number, count, hash or result line was changed.
The edits are:

| file | edit |
|---|---|
| `witness_check.log`, line 1 | the absolute path of the table on the author's machine (ending in `problems\0357\exact_f_table.txt`) was replaced by `<research-repo>\problems\0357\exact_f_table.txt`; a re-run prints `table: reference/exact_f_table_research.txt` |
| `exact/logs/binary_sha256_validation.txt` | the temporary directory of the binaries was replaced by `<build-dir>` |
| `greedy/logs/check_sets.log`, line 1 | the name of an internal notes file was replaced by "the research notes (not public)"; a re-run prints "parsed 18 expected rows from expected.tsv" |
| `greedy/digests.tsv`, header | two column names that contained the name of an internal notes file were renamed to `fnv1a64_expected` and `k_expected` |
| `lower-bound-checks/logs/spectra_table.log` | the name of an internal notes file was replaced by "= listed table" in 12 lines; `spectra_table.py` prints the same words |
| `reference/exact_f_table_research.txt`, comment lines 2 and 4 | the names of internal programs were replaced by a description; the data lines are unchanged |

In the output of the scripts, "repo" (or "research table") means `reference/exact_f_table_research.txt` and "doc"
means `greedy/expected.tsv`; "cache" in `validate.py` means `reference/oeis_A364132.txt`.

When a script is re-run its output equals the recorded log except for: timings, the lines named above, the shell's
`time` output at the end of two review outputs, and the thread-dependent progress lines of `exact` (printed to
standard error).  Node counts, set counts, digests and verdicts are deterministic.  The Python scripts under Windows
write CRLF line endings when their output is redirected; the logs here have LF.

Binaries are not bit-reproducible: the sha256 values recorded for `exact.exe`, `brute.exe` and `rgreedy.exe` are those
of the binaries used for the recorded runs, and a rebuild gives different bytes (see `exact/README.md` section 6 and
`greedy/README.md`).  The sources in this release have LF line endings; the `rgreedy` source recorded in
`greedy/README.md` was hashed with CRLF endings before conversion.

## Re-run before release

The scripts below were re-run from this directory when it was prepared for release (binaries rebuilt in a scratch build
directory, outputs written outside the repository), on the machine of the recorded runs, with several of these jobs
and other work running at the same time, so the times are indicative only.  The quick-start commands were also
repeated on a separate copy of this directory.  Every result agrees with the recorded logs; the only differences are
the ones listed in the previous section (timings and the named lines).

| check | command | wall time | result |
|---|---|--:|---|
| `witness_check.py` | `python witness_check.py` | 0.1 s | ALL CHECKS PASSED (28 M blocks, 67 sets, 77 f rows, 22 OEIS terms); output equal to `witness_check.log` except line 1 |
| `exact/compare_results.py` | `python exact/compare_results.py` | 0.4 s | ALL AGREE; output byte-identical to `exact/logs/compare_results.log` |
| `exact` build | `cargo build --release --locked` | 4 s | binaries build; hashes differ from the recorded ones (see above) |
| `exact/validate.py` (grid 30) | `validate.py <bindir> results/brute_N34.txt 30` | 1 s | VALIDATION PASSED; equal to `logs/validate_N34_grid30.log` except one timing |
| `exact/validate.py` (full) | `validate.py <bindir> results/brute_N34.txt 34 52` | 873 s | VALIDATION PASSED; 1378 cells (653 nonzero) with zero mismatches against the unpruned enumeration of 10528138219 sets; equal to `logs/validate_final.log` except timings |
| `exact count 26 66` | `exact count 26 66 --threads 7` | 56 s | 0 admissible 26-sets with max <= 66, 2563131703 nodes, 11171 tasks: the node count equals those in `logs/ftable_n68.log` and `logs/audit_deep.log` |
| `greedy/check_sets.py` | `python check_sets.py --digests <scratch>/digests.tsv` | 126 s | ALL 18 ROWS OK; digests (columns 1 to 11) identical to `digests.tsv` |
| `rgreedy` build and regeneration | `cargo build --release --locked`, `MAXN=1000000 bash run_greedy.sh` | 3 s, 14 s | the 13 sets with n <= 10^6 are byte-identical to `sets/`; the tool's lines (without time) equal those of `logs/run_greedy.log` |
| `lower-bound-checks/check_lower.py quick` | `python check_lower.py quick` | 7 s | ALL CHECKS PASSED; the numbers it prints equal those of the corresponding lines of `check_lower_full.log` (quick mode covers a subset of the cases) |
| `lower-bound-checks/check_upper.py` | `python check_upper.py` | 30 s | ALL CHECKS PASSED |
| `lower-bound-checks/check_lower_extra.py` | `python check_lower_extra.py` | 211 s | output equal to `check_lower_extra.log` except timing |
| `lower-bound-checks/check_referee_claims.py`, `check_small_facts.py`, `spectra_table.py` | as above | 8 s, 87 s, under 1 s | output identical to the recorded logs |
| `review-checks/` fast scripts | `ex28.py`, `s4_check.py`, `s4_rem797.py`, `s5_check.py`, `s6_count.py` | 0 to 12 s each | output equal to the recorded `.out` files except timings |
| `review-checks/s4_bruteforce.py` | `python s4_bruteforce.py 22`; `python s4_bruteforce.py 32 13` | 63 s, 35 s | output equal to the recorded `.out` files except timings |
| `review-checks/s6_remark66.py` | `python s6_remark66.py 2 3` | 182 s | output equal to `s6_remark66.out` except timings |
| `review-checks/greedy_valid.py` | `python greedy_valid.py ../greedy/sets/rev_20000000.txt 16` | 95 s | 359481891 block sums, 0 duplicates, VALID; equal to `greedy_valid_2e7.out` except timings |
| `review-checks/exact_small.py` | `python exact_small.py 24` | 235 s | M(1..24) and the node counts equal the lines of `exact_small_k26.out` |
| `review-checks/s6_check.py` | `python s6_check.py 3` | 278 s | ALL PASS (brute force of the reduction for every u in U, j = 1, 2, 3); output equal to `s6_check_j3.out` except timings |

Not repeated for this release, because of their running time (the recorded outputs are included):
`exact_small.py` with KMAX = 25 and 26 (about 7 and 26 more minutes), `s6_check_only.py 4` (about 14 minutes),
`check_lower.py full` (about 15 minutes; its quick mode and the pieces repeated in `check_lower_extra.py` were run),
the full regeneration of the five largest greedy sets (about 25 minutes, up to 5.4 GB of RAM), and the exhaustive
searches of `exact/` (`table 28`, `ftable`, `count 29 77` and the audits: about 1.7 hours in total; of these only
`count 26 66` was repeated).  A repetition of these would be expected to reproduce the recorded node counts and
verdicts, but that has not been checked.

## Edits made when preparing this release

Besides the log edits above: absolute paths and names of internal tools and working copies were removed from
the scripts and READMEs, and internal research notes are referred to by neutral labels (`COMPARISON.md` calls two of them
note E and note V); the scripts read their inputs from `reference/` and from their own directory instead of from
the research repository; `reference/oeis_A364132.txt`, `greedy/expected.tsv`, `.gitignore`, this file and
`review-checks/README.md` were added; `greedy/run_greedy.sh` and `exact/run_*.sh` were made portable and
`greedy/check_sets.py` reads `expected.tsv`; the result-producing logic, including both validity methods of
`check_sets.py` and all printed result lines, was not changed.  A script of the original package that recorded the search range in the research repository is not included.
