# Erdős Problem 357: bounds for increasing sequences with distinct consecutive sums

This repository accompanies the paper *Bounds for increasing sequences with distinct consecutive sums (Erdős Problem 357)* by Chandler
Snively (Quana Labs, 2026). It contains:

- the manuscript;
- the Lean 4 formalization of its theorems, pinned to an exact toolchain;
- a script that repeats every formal check from a clean build;
- the programs and data behind the paper's finite computations.

**The question.** Let f(n) be the largest k for which there are integers 1 ≤ a₁ < a₂ < … < a_k ≤ n whose consecutive sums
a_i + a_{i+1} + … + a_j (1 ≤ i ≤ j ≤ k) are pairwise distinct. Erdős and Harzheim asked how f(n) grows, and whether f(n) = o(n)
([erdosproblems.com/357](https://www.erdosproblems.com/357)). That question remains open, and nothing here settles it.

> **How this work was done.** The theorems, their proofs and the Lean formalization were produced by AI systems in a research
> project directed by the author. The paper and the verification were also prepared with AI. No independent human mathematician has
> checked the proofs, and the paper has not been peer reviewed. The formal verification below is the main evidence for
> correctness. See [docs/PROVENANCE.md](docs/PROVENANCE.md) and the statement on AI use at the end of the paper.

## Results and their status

| Result | Statement | Status |
|---|---|---|
| Theorem 1.1 (upper bound) | 720000·f(n) ≤ 354184·n + 1440000·⌊√n⌋ + 128010240000 for all n; hence f(n) ≤ (44273/90000)·n + 2√n + 177792 | **Formally verified** in Lean; complete written proof in the paper |
| Theorem 1.2 (lower bound, modulus 42) | f(21m² + 105m + 46) ≥ 12m for all m ≥ 0; hence f(n) ≥ (12/√21)·√n − 48 for all n | **Formally verified**; complete written proof |
| Theorem 1.3 (lower bound, one skip) | f(12096j² + 87024j + 81) ≥ 360j for all j ≥ 500; hence f(n) ≥ (15/√21)·√n − 1800 for n ≥ 12096·504², and f(n) ≥ (15/√21)·√n − 181440 for all n | **Formally verified**; complete written proof |
| Remark 4.9 (a simpler upper bound) | f(n) ≤ (797/1620)·n + 2√n + 7 for all n | **Formally verified**; the paper gives only an outline |
| Exact values | f(n) for every n ≤ 77, and M(k), the least n with f(n) ≥ k, for k ≤ 28 | **Computational evidence**: exhaustive searches by independently written programs, not proofs |
| Greedy sequences | A valid sequence of 26813 terms in [1, 2·10⁷] | **Computational evidence**: the sequence is checkable from the definition |

The constants are exact. Decimal expansions such as 44273/90000 = 0.4919222… and 15/√21 = 3.273268… are truncated, never rounded.

Some parts of the written proofs cover more cases than Lean does. These cases are used by no headline theorem, and the paper marks them:
- Proposition 4.8 is proved by hand for 2 ≤ j < 12; Lean covers j ≥ 12.
- Proposition 6.4 is proved by hand for 230 ≤ j < 500; Lean covers j ≥ 500.

**Novelty is not established.** To our knowledge:
- Theorem 1.1 is the first bound f(n) ≤ (c + o(1))·n with c < 1/2;
- the constants 12/√21 and 15/√21 are new.

This rests on literature searches, which cannot prove novelty. Two relevant papers could be consulted only through abstracts and reviews:
Hegyvári (1986) and Coppersmith–Phillips (1996). See [docs/LITERATURE.md](docs/LITERATURE.md).

## What the formal verification establishes

The Lean development proves the theorems above for a function `f` whose definition is checked, by `rfl`, to be **definitionally
equal** to the definition in the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project
(`FormalConjectures/ErdosProblems/357.lean`, at commits `d16e05a` and `4b5e5275a2`).

The last recorded run (`verification/logs/`) shows:
- **Build.** A clean build of the six proof files succeeds with Lean `v4.27.0` and Mathlib `a3a10db` (tag `v4.27.0`).
- **Axioms.** All 1023 declarations of the six files depend only on Lean's standard axioms `propext`, `Classical.choice` and
  `Quot.sound`. There is no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`) and no added axiom.
- **Kernel replay.** [lean4checker](https://github.com/leanprover/lean4checker) `v4.27.0` replays every module with exit code 0.
- **Exact arithmetic.** `verification/paper_checks.py` checks every number and finite case analysis in the written proofs with exact
  integer and rational arithmetic: 15 checks.

What it does **not** establish:
- that these are the right statements (§7.2 of the paper argues that they are);
- that the results are new;
- anything about the open question f(n) = o(n).

The trust base is the standard one for Lean: the kernel, Mathlib's definitions, and the three axioms.

**A known error in the Lean comments.** The docstrings at `P0357Upper.lean:520`, `P0357Upper2.lean:252` and `P0357Upper4.lean:268`
(and the generator's matching line) say that the definition of `f` is copied from Formal Conjectures "commit c83a94d". No such
commit exists in the upstream history available to us. The upstream commits are `d16e05a` and `4b5e5275a2`, and the `rfl` pin
checks both mechanically. The text is a comment, so no proof depends on it. The proof files are left unchanged, so that they stay
identical to the research version described in [docs/PROVENANCE.md](docs/PROVENANCE.md).

## Layout

| Path | Contents |
|---|---|
| `manuscript/` | `main.tex`, `refs.bib`, `main.bbl`, and the compiled `main.pdf` |
| `lean/` | A standalone Lake project with the six proof files under `Erdos/Proofs/`, unchanged from the research repository, and `Erdos357.lean`, which imports them. `generator/` holds the script and data that generated `P0357Upper4.lean`; `python3 lean/generator/gen_design4.py lean/generator/design_M360000_4fam.json out.lean` re-checks the design and writes a file identical to it. Comments in the proof files mention research notes that are not part of this release; the proofs do not depend on them. |
| `verification/` | `run_all.sh`, which repeats every check; `Headline.lean`, which prints every statement the paper uses; `AxiomAudit.lean`; the upstream definition pin (`make_upstream_pin.py`, `upstream/`); `paper_checks.py`; and `logs/` from the last run |
| `computation/` | Programs, data and logs for Section 8 of the paper: an exhaustive solver for exact values, the greedy sets with a checker and the generator, checks of the lower-bound constructions, and the review recomputations. See [computation/README.md](computation/README.md). |
| `docs/` | [PROVENANCE.md](docs/PROVENANCE.md) (who and what produced the work), [LITERATURE.md](docs/LITERATURE.md) (literature search and novelty), [REVIEWS.md](docs/REVIEWS.md) (internal AI reviews and how each finding was resolved) |
| `MANIFEST.sha256` | SHA-256 of every file, with LF line endings. Check it on a fresh checkout with `python3 verification/make_manifest.py --check` (on Windows, `py` instead of `python3`). Running the verification rewrites the logs, so they will then differ. |

## Reproducing the formal verification

Requirements:
- [elan](https://github.com/leanprover/elan), the Lean toolchain installer. It reads `lean/lean-toolchain`.
- Git, Bash and Python 3.
- About 8 GB of disk for Mathlib and its build cache.
- Network access for the first run.

```bash
FETCH_CACHE=1 bash verification/run_all.sh
```

`FETCH_CACHE=1` downloads Mathlib (pinned in `lean/lake-manifest.json`) and its prebuilt cache. Later runs can omit it. The script
deletes `lean/.lake/build`, builds the six files from scratch, runs every check, and writes `verification/logs/SUMMARY.txt`.

To include the kernel replay, build lean4checker and pass its path:

```bash
git clone --branch v4.27.0 https://github.com/leanprover/lean4checker /tmp/lean4checker
(cd /tmp/lean4checker && lake build)
LEAN4CHECKER=/tmp/lean4checker/.lake/build/bin/lean4checker bash verification/run_all.sh
```

A successful run with `LEAN4CHECKER` set prints the summary below. Times and dates differ. Without `LEAN4CHECKER`, the
lean4checker line reads `SKIPPED (LEAN4CHECKER not set)` and the last line `RESULT: PASS (kernel replay skipped)`.

```
build:        Build completed successfully (7892 jobs). [exit=0]
headline:     13 axiom lines, 0 error lines [exit=0]
axioms:       TOTAL: 1023 constants (977 theorems) in 6 modules AXIOM AUDIT PASSED: every constant depends only on propext, Classical.choice, Quot.sound  [exit=0]
upstream pin: 4 axiom lines, 0 error lines [exit=0]
lean4checker: 6 of 6 modules exit 0
paper checks: ALL 15 CHECKS PASSED  [exit=0]
RESULT: PASS
```

The script exits with status 0 only if every step it ran passed; otherwise the summary ends with `RESULT: FAIL`.

On Windows, run the script from Git Bash; it uses `py` if present. **Clone to a short path**, such as `C:\erdos-357`. Mathlib's build
cache contains deep paths, and under a long parent folder some of them exceed Windows' 260-character limit. The cache then unpacks
without reporting an error, but the build fails on missing `.olean.server.hash` files. The workflow in `.github/workflows/verify.yml`
runs the same script on Linux.

## Citing

Please cite the paper; see [CITATION.cff](CITATION.cff). Until an arXiv identifier exists, cite this repository and its release tag.

## Licence

- **Code**: Lean files, scripts and programs, under the [Apache License 2.0](LICENSE).
- **Text and data**: the manuscript, the documentation, and the data and logs, under [CC BY 4.0](LICENSE-CC-BY-4.0.md).
- **Third-party material**: `verification/upstream/` contains verbatim copies of a Formal Conjectures file, under its own Apache 2.0
  licence. `computation/reference/oeis_A364132.txt` contains terms of OEIS A364132 (CC BY-SA 4.0). See [NOTICE](NOTICE).

## Contact

Quana Labs: [lab@quanalabs.com](mailto:lab@quanalabs.com), [quanalabs.com](https://quanalabs.com). Reports of errors are welcome. A
confirmed error is corrected in a new release, recorded in the release notes, and noted in a replacement version of the paper.
