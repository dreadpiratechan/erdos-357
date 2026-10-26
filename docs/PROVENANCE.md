# Provenance: how the results were produced

This file records who and what produced the results in this repository, in more detail than the paper's statement on the use of AI
tools. It contains the same facts as that statement and adds nothing to them.

## Summary

The mathematics was found, proved and formalized by AI systems. The written proofs, the audits and the manuscript were also produced
with AI. The author, Chandler Snively, set up and directed the research project at Quana Labs, a one-person independent research
lab. That work consisted of:
- choosing Problem 357;
- commissioning the runs described below;
- deciding what to publish.

The records show no human mathematical contribution to the constructions, the proofs or the formalization.

No independent human mathematician has checked the proofs, and the paper has not been peer reviewed. The author takes full
responsibility for the paper and this repository, including the accuracy of this account, and for correcting or withdrawing any result
that is found to be wrong.

## Timeline

| Date (2026) | What was produced | By |
|---|---|---|
| 9 September | The modulus-22 residue pattern (2, 6, 9, 12, 18, 19), found by an exhaustive search over residue patterns modulo q ≤ 22, and a Lean proof of f(n) ≥ (12/√22)·√n − 36. This is the predecessor of Theorem 1.2; it is not a theorem of the paper. | An autonomous coding agent: OpenAI Codex, model identifier `gpt-6-astra` |
| 23 October | The modulus-42 pattern and Theorem 1.2; the skip construction and Theorem 1.3; the first two upper bounds, with constants 125/252 and 797/1620 (Remark 4.9); their Lean proofs; exact values of f(n) for n ≤ 77, from two exhaustive programs | Autonomous AI agents built on Claude models (Anthropic; Claude Sonnet 5.5 and Claude Opus 5.5) |
| 23 October (day) | Theorem 1.1: the five-band design, the generated Lean module `P0357Upper4.lean` and its proof | A further Claude agent (Claude Sonnet 5.5) |
| 23 October | The independent audits: clean rebuilds, axiom audits, kernel replay, the upstream definition pin, exact-arithmetic checks and the literature searches. Also: the written proofs in their present form; the manuscript; two AI referee reviews; the independent recomputation of the exact values; and this release | Claude (Anthropic), model Claude Opus 5.5 |
| 26 October | Release v1.1: Hegyvári (1986) read in full, the literature searches repeated, the manuscript's literature discussion and statement on AI use revised, fresh adversarial reviews of the proofs, and the verification reproduced from a fresh clone | Claude (Anthropic), model Claude Opus 5.5 |

## What is in this repository, and where it came from

- **`lean/Erdos/Proofs/*.lean`.** The six proof files are byte-identical, line endings aside, to the files in the research repository
  at its frozen commit `6dadb49`. Their SHA-256 values over the LF form are:

  | File | SHA-256 |
  |---|---|
  | `P0357.lean` | `00ed7d57beaa2944d54972fb9e062e02606d34a61ede618518fa53613d434819` |
  | `P0357Skip.lean` | `66361ccf61b1bac1487232d604e313b0efabdbb5414e26ecf59b13cb20993a1b` |
  | `P0357Upper.lean` | `6ab3ce32b87139b45c0aa6dbc693765c41a85e09f308b70a80eb84037e58d882` |
  | `P0357Upper2.lean` | `523eaf2d2ab017dbc8eec0974fd8477eba67e62f56032b3cc7ea905a895dc202` |
  | `P0357Upper4.lean` | `615df552a7aeddf9c958ed0ef967c153f6b43334a748456f9ce76a5f56de80d8` |
  | `P0357Upper4Gen.lean` | `de2a19ca5a040746ef8076bf13062551a753229d5dc19290c1d3126d1e96a176` |

  Comments in these files mention research notes and helper scripts of the research repository. Those are not part of this release.
  The proofs do not depend on them.
- **`manuscript/`.** The release version of the paper. It differs from the frozen internal draft only editorially:
  - the affiliation and contact lines;
  - citations of this repository in place of "supplementary material";
  - the removal of the draft-status box and the bracketed draft sentences;
  - the final sentence of the responsibility statement;
  - bibliography comments.

  The theorems, proofs and computations are unchanged. Release v1.1 revises the account of Hegyvári (1986), cites release v1.1 of this
  repository, qualifies the reported residue-pattern searches, corrects the expository statements listed in
  [REVIEWS.md](REVIEWS.md), Section 5, and shortens the statement on AI use. The theorems and computations are unchanged; Proposition 4.6
  now states the hypothesis t ≥ 0, which its proof uses and its Lean form assumes.
- **`verification/`.** The verification scripts from the frozen package, made portable, with the logs of a run on a fresh clone of
  this repository (Windows 10, Git Bash, 23 October 2026). On that machine the Mathlib build cache was already downloaded, so the
  download from scratch was not part of the run.
- **`computation/`.** The programs and data of the paper's Section 8. They were cleaned for publication: local paths were removed and
  the scripts read in-repository data. No result was changed. See `computation/README.md`.

## Records not included

The research repository is kept privately by Quana Labs. Its commit history, its research notes and the agents' reports are frozen
there at the commit above. Those records include:
- the provenance records of the September and October runs;
- the session logs;
- the full literature report;
- the internal reviews.

This release summarizes them in this file, in [LITERATURE.md](LITERATURE.md) and in [REVIEWS.md](REVIEWS.md). The prompts, agent
configuration and internal infrastructure of the research project are not part of this release.

## Later work

Research on Problem 357 continued after the frozen commit. Results obtained after it, for example exact values beyond n = 77, are not
part of this release. They will appear, if at all, in later releases with their own records.
