# Review recomputations

Scripts and recorded outputs of an adversarial review of the manuscript (see `../../docs/REVIEWS.md`, section 2).
The reviewer was asked to find errors, not to confirm the paper, and to recompute with its own code (the docstring of
`s4_check.py` says that it was written from the text of the manuscript alone and reads no other script of this
repository).  Each script recomputes a group of numerical statements or finite case analyses with exact integer or
rational arithmetic, or by brute force.

These are computational checks of the stated finite facts.  They are evidence, not proofs: the proofs are the written
proofs of the paper and the Lean development in `../../lean/`, and none of these computations is used in them
(Section 8 of the paper says the same).  A passing script shows that the statement holds on the cases it covers.

## Requirements

Python 3 (recorded: 3.13.3) with numpy (2.2.6); numba (0.62.1) for `exact_small.py`, `greedy_valid.py` and
`s6_count.py`; sympy (1.14.0) for `s6_check.py` and `s6_check_only.py`.  Run the scripts from this directory.  Do not
use `python -I` for the numba scripts.  numba caches its compiled code in a `__pycache__` directory next to the script;
set `NUMBA_CACHE_DIR` to a scratch directory (and `PYTHONDONTWRITEBYTECODE=1`) to keep the repository clean.

## Scripts

Runtime classes: *seconds* (under a minute), *minutes* (1 to 15 minutes), *long* (over 15 minutes).  Times are
wall-clock on a 16-thread Windows machine shared with other jobs, so they are only indicative; each script is single
threaded.  "Recorded output" is the output of the original run; where a script's output contains timings they differ
from run to run, everything else is deterministic.

| script | what it recomputes | paper | command | runtime | recorded output |
|---|---|---|---|---|---|
| `ex28.py` | the 28-term sequence with largest term 75 quoted as an example: 406 block sums, all distinct | Section 8, exact values | `python ex28.py` | seconds | `ex28.out` |
| `count_valid.py` | the number of valid sequences (including the empty one) with terms in {1..N}, N = 12, 16, 18, 20, 22, by plain depth-first search | cross-check of `s4_bruteforce.py` and of `../lower-bound-checks/check_upper.py` (U6) | `python count_valid.py` | seconds | `count_valid.out` |
| `s4_check.py` | the numbers of Section 4: band sizes 687, 949, 479, 1924, 1777 (sum 5816), 44273/90000, the additive constant 177792, the zone table, the degree bound by direct incidence counts for j = 2, 3, 4, 5, 6, 12, 13, 17, 30, the sum identities of the patterns, the closing inequalities of Theorem 1.1 | Section 4 (design with five bands, proof of the upper bound) | `python s4_check.py` | seconds | `s4_check.out` |
| `s4_rem797.py` | the simpler two-band design: ranges of w, degree at most 2 and supports inside (t, theta] for 12 <= n <= 6000, and the closing arithmetic 1620(n - t) - 810 P - 797 n <= 8000 for 12 <= n < 2*10^6 | Section 4, remark on the 797/1620 design | `python s4_rem797.py` | seconds | `s4_rem797.out` |
| `s4_bruteforce.py N [MINLEN]` | the lemmas of Section 4 listed in the script's docstring (Cor 4.2, Lemmas 4.1, 4.3, 4.5, Prop 4.6, Lemma 4.7(b), in the numbering used by the script) on every valid sequence in {1..N} and several values of n >= max a | Section 4; Section 8, "Checks of the proofs", item 1 | `python s4_bruteforce.py 22` and `python s4_bruteforce.py 32 13` | minutes (N = 22: about 100 s; N = 32 with MINLEN = 13: about 1 min) | `s4_bruteforce_N22.out`, `s4_bruteforce_N32_minlen13.out` |
| `s5_check.py` | Section 5: the sequence of Theorem 1.2 is valid for m = 1..60 with last term 21m^2 + 105m + 34, the real-form derivation of the theorem, and the numerics of the remark on the offset (the largest colliding offset 42t for m = 20, 60, 100: 0.8436, 0.9432, 0.9683 of the paper's offset) | Section 5; Section 8, item 2 | `python s5_check.py` | seconds (about 15 s) | `s5_check.out` (ends with the shell's `time` output) |
| `s6_check.py [JMAX]` | Section 6: the window identity (3000 random windows), the 216 phase triples, the constants of the four cases, the threshold arithmetic of Theorem 1.3, and an exhaustive brute force of the reduction for every offset u in U, for j = 1..JMAX (default 3) | Section 6; Section 8, item 3 | `python s6_check.py 3` | minutes (JMAX = 3: about 8 min) | `s6_check_j3.out` |
| `s6_check_only.py J` | the same, for the single value j = J | Section 6; Section 8, item 3 | `python s6_check_only.py 4` | long (J = 4: about 14 min) | `s6_check_j4.out` |
| `s6_count.py [JMAX]` | the exact number of bad offsets u in U for every j (u is bad iff 14 <= L <= delta <= 288j - 1 with L*delta = 72u + 66 + 3456j): a good u exists for every j = 1..499 (smallest proportion 0.6384 at j = 16), and the counts for j = 500, 230, 229, 1000 against the bound 1944.4j + 12768 | Section 6; Section 8, items 4 and 5 | `python s6_count.py` | seconds (recorded 34 s, 3 s with a warm numba cache) | `s6_count.out` (ends with the shell's `time` output) |
| `s6_remark66.py J...` | the numerics of the remark on the constant 15/sqrt(21): for j = 2, 3 the largest offset below the left end of U with a collision not of divisor type, the smallest valid offset, and the number of valid offsets below the left end | Section 6, remark on where 15/sqrt(21) comes from | `python s6_remark66.py 2 3` | minutes (j = 2: about 50 s; j = 3: about 3 min) | `s6_remark66.out` |
| `exact_small.py KMAX` | an independent exhaustive computation of M(k) for k <= KMAX: depth-first search with a table of block sums, whose only pruning is a_r >= M(r) and a_r <= n - (k - r) | Section 8, exact values | `python exact_small.py 24` | minutes for KMAX <= 24 (about 4 min); KMAX = 25 adds about 7 min and KMAX = 26 about 26 min more (long) | `exact_small_k26.out` (KMAX = 26) |
| `greedy_valid.py FILE [NB]` | validity of the 2*10^7 reverse-greedy set (26813 terms): all 359,481,891 block sums, bucketed by residue (NB buckets, default 8) so that memory stays small, each bucket sorted and tested for duplicates | Section 8, greedy sequences (second, separately written check; the first is `../greedy/check_sets.py`) | `python greedy_valid.py ../greedy/sets/rev_20000000.txt 16` | minutes (about 1.5 min) | `greedy_valid_2e7.out` |

`s6_check.py` and `s6_check_only.py` differ in one line (the loop over j).  `s5_check.out` and `s6_count.out` end
with the output of the shell's `time` command, a leftover of how they were produced.  `count_valid.out` was produced
when this release was assembled (the script had no recorded output before); its values for N = 18 and N = 22 agree
with `../lower-bound-checks/check_upper.py` (U6) and with `s4_bruteforce_N22.out` respectively.

## Long runs

The large searches (`exact_small.py` with KMAX = 25 or 26, and `s6_check_only.py 4`) are included with their recorded
outputs but take a long time and were not repeated for this release; KMAX <= 24 and `s6_check.py 3` were repeated
and reproduce the recorded lines.  Further finite checks (the modulus-42 family, the skip construction, the
upper-bound arithmetic) are in `../lower-bound-checks/`.
