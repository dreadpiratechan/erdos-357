# Internal reviews and how their findings were resolved

Before release the work was reviewed three times. All three reviews were done by **AI systems** (Claude, Anthropic); none is a human
or journal review. They are recorded here so that readers can see what was checked, what was found and what changed. The paper has
not been peer reviewed.

## 1. Referee review of the first internal draft (23 October 2026)

A separate AI agent, with read-only access, was asked to referee an internal draft of the paper. It raised 15 findings, all about
how the text stated or presented the results; none affected a theorem as formalized in Lean. The findings were:
- 3 errors in the text;
- 7 overclaims;
- 2 unclear points;
- 3 minor issues.

All were resolved before the present manuscript was written.

| # | Finding | Resolution |
|---|---|---|
| 1 | The abstract rounded the threshold of Theorem 1.3 down to 3.07·10⁹, which admitted values of n the theorem does not cover. | The threshold is stated exactly: n ≥ 12096·504² = 3,072,577,536. |
| 2 | Two constants were rounded in the direction that strengthens the inequality (3.2733 and 0.491922). | Every inequality uses the exact constants. Decimals are marked truncations. |
| 3 | The draft said every step was formalized "against the Formal Conjectures statement", and its definitional check compared a retyped copy. | The paper states exactly what is formal. The definitional check is now mechanical: the upstream definitions are copied verbatim by a script and proved equal by `rfl` (`verification/make_upstream_pin.py`). |
| 4 | The upper constant was called "the first below 1/2", although 125/252 and 797/1620 come from the same development. | The paper states the crossover with the 797/1620 bound exactly (n ≥ 3,348,973,256) and records the history in §9. |
| 5 | A threshold confused the real and integer forms of the 797/1620 bound. | Both thresholds are decided exactly in `verification/paper_checks.py`. The paper quotes the real form. |
| 6 | The 2·10⁷ greedy set was said to have two checkers but had one, and was not archived. | The set is archived (`computation/greedy/sets/`) and was checked by two separately written programs. |
| 7 | "15/√21 is the exact limit of the one-skip family" was not proved. | Remark 6.6 now says that the constant optimizes the paper's sufficient conditions and is not a proof of a limit. |
| 8 | Linear-programming experiments were stated as caps. | Remark 4.10 labels them as exploratory experiments that do not prove any limit. |
| 9 | A growth statistic was presented as exact beyond its exact range. | The statistic was removed from the paper. |
| 10 | Growth fits of greedy data were overinterpreted. | §8 says only that finite data do not decide whether f(n)/√n is bounded. |
| 11 | Two steps of the upper bound needed explaining. | Added to the proofs of Proposition 4.6 and Theorem 1.1. |
| 12 | Three steps of the lower bounds needed explaining. | Added to §5 and §6, with all variables defined before use. |
| 13 | Several minor points: the n = 69 search, module counts, a missing axioms line, and 11663 instead of 11676. | All corrected. The n = 69 value is a witness, checked from the definition; the nonexistence claim at n = 68 was searched without pruning. |
| 14 | Citation gaps. | The cited sources were added. The Erdős–Graham reference cites the page that was read (p. 58). |
| 15 | Symbol clashes. | The notation was made unique. |

## 2. Adversarial review of the manuscript (23 October 2026)

A second AI agent was asked to find errors, not to confirm the paper, and to recompute everything with its own code. Its scripts and
outputs are in `computation/review-checks/`.

**Result: no mathematical error was found** in Sections 3–6, and no mismatch was found between the Lean statements and Section 7.

What it recomputed:
- every constant of §4;
- the zone table and the degree bound of Proposition 4.8, by direct incidence counts for j = 2, 3, 4, 5, 6, 12, 13, 17 and 30;
- the thresholds;
- the lemmas of §§3–4, tested on every valid sequence in {1, …, 22};
- the §5 spectra, and Theorem 1.2 for m ≤ 60;
- the phase filter of §6, Proposition 6.3 for every offset at j = 1 to 4, and the counting constants;
- M(1), …, M(26), with a separate naive program;
- the validity of the 2·10⁷ greedy set.

It reported 10 findings about completeness, wording, ranges and rounding. All were fixed.

| # | Finding | Resolution |
|---|---|---|
| 1 | Remark 4.9 (the 797/1620 bound) was only sketched, while the paper said all its written proofs were complete. | Remark 4.9 now says that it is proved in Lean and gives an outline. "Complete written proofs" now covers Theorems 1.1–1.3 only. |
| 2 | The abstract could be read as saying that the formal conjecture was settled. | The abstract says the theorems are verified for a function definitionally equal to the Formal Conjectures f, and that they do not settle f(n) = o(n). |
| 3 | Bracketed draft placeholders remained. | Filled in. The release version contains no draft text. |
| 4 | Propositions 4.8 and 6.4 are proved by hand for more cases than Lean covers. | Each proposition now says which case is used and formalized. |
| 5 | Coppersmith–Phillips (abstract only) was missing from the list of unread sources. | Both unread texts are named in §2 and in the Limitations. |
| 6 | Remark 4.10 drew an asymptotic conclusion from a computation at n = 3000. | Reworded. No limit is claimed. |
| 7 | The example in Remark 4.4 fails for m = 3, since 2 + 3 = 5. | It now reads m ≥ 4. |
| 8 | Three decimals were rounded in the strengthening direction: 0.0081, 3.2508… and 0.97. | Corrected to 727/90000 = 0.00807…, 3.2507… and 0.96. |
| 9 | A weaker bound in Table 1 was not marked as weaker. | Marked. |
| 10 | Unused content of `P0357.lean` was not mentioned. | §7 now lists it. |

## 3. Independent recomputation of the exact values (23 October 2026)

A third exhaustive solver was written from the definition alone; the original programs were not consulted. Its only pruning rules
have one-line proofs, and it uses no previously computed value. It reproduced:
- M(1), …, M(28);
- all 67 optimal sequences;
- f(n) for every n ≤ 77, including the claims that previously relied on a pruning rule based on earlier values.

Its pruned search agrees with a complete unpruned enumeration of all valid sequences in {1, …, 52}. Details are in
`computation/exact/README.md` and `computation/COMPARISON.md`. These remain computational evidence.

## 4. Release review (23 October 2026)

Before this release, a separate AI session reviewed the whole repository, the website entry, the announcement drafts and the arXiv
bundle. It had read-only access and was given no conclusions to confirm. It re-derived the arithmetic of Sections 3–6 exactly and
compared every stated theorem with the Lean statements. It found no mathematical error, no statement stronger than the Lean theorem,
and no decimal rounded in the unsafe direction. Its other findings, and what was done:

| Finding | Resolution |
|---|---|
| `computation/COMPARISON.md` was written in the first person and named unreleased notes. | Rewritten in a neutral voice; it now states that AI sessions wrote and ran the computations; the notes are labelled E and V. |
| README: `python3` does not exist in Git Bash on Windows; the expected output showed the kernel-replay line for a command that skips it; `run_all.sh` reported a pass with the replay skipped. | README corrected; `run_all.sh` prints `SKIPPED` and `RESULT: PASS (kernel replay skipped)` in that case, and exits 1 on any failure. |
| Comments in three Lean files cite a Formal Conjectures commit `c83a94d`, which is not in the upstream history available to us and is documented nowhere else. | Documented in the README. The files stay byte-identical to the research version; the `rfl` pin checks the real upstream commits. |
| The literature table labelled forum deductions "peer reviewed". | Relabelled: published source, deduction for f in a forum comment. |
| `verification/paper_checks.py` named old section and theorem numbers. | Labels corrected; the checks are unchanged. |
| √tanh 1 was written 0.8727…, a rounded value with a truncation ellipsis. | Now 0.87269… (truncated). |
| The generator of `P0357Upper4.lean` had no documented command. | Command added to the README; its output is byte-identical to the file. |
| Licence coverage of data and logs was unstated. | Data and logs are under CC BY 4.0, except the OEIS terms (CC BY-SA 4.0). |

A further error was found while the bibliography was rebuilt after these fixes. The bibliography style lowercased a title, so the
reference to the Lenthall-Cleary claim printed n/2 + o(n^{2/3}) instead of n/2 + O(n^{2/3}). This was fixed. The same reference no
longer attributes the matching GitHub draft to that author: the draft names no author, and the match rests on the bound and the date.

## What none of the reviews did

None of them was done by a human, none read the full texts of Hegyvári (1986) or Coppersmith–Phillips (1996), and none replaced
journal peer review.
