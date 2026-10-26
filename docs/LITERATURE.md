# Literature search and novelty

This file describes the literature search behind the paper's statements on prior work (§2 and the Limitations). The search was done
with AI on 23 October 2026, and the main sources were re-checked the same day before release. For release v1.1 the searches were
repeated on 26 October 2026, which found nothing new, and Hegyvári (1986) was read in full.

**Novelty has not been established.** A search can find prior work; it cannot show that none exists. The paper therefore states
novelty only as "to our knowledge". The gaps in coverage are listed below.

## What was found

| Bound | Best earlier result found | Source and status |
|---|---|---|
| Upper, published source; transfer to f in a forum comment | f(n) ≤ (2/3 − 1/512)·n + O(log n) | Coppersmith and Phillips, SIAM J. Discrete Math. 9 (1996) 173–177, for the weaker property that no term is a sum of two or more consecutive earlier terms. A valid sequence has this property, so the bound applies to f. The transfer was observed by D. Weisenberg on the erdosproblems.com forum (9 Dec 2025). |
| Upper, published source (for g; f ≤ g by definition) | g(n) ≤ (2/3 + o(1))·n for the non-monotone variant g ≥ f | Hegyvári, Acta Math. Hungar. 48 (1986) 193–200, Theorem 1, read in full. The upper bound counts the sums of short blocks and applies to increasing sequences as well. |
| Upper, published source; deduction for f in a forum comment | f(n) ≤ (√tanh 1 + o(1))·n, √tanh 1 = 0.87269… | Deduced by Q. Tang (forum, 8 Dec 2025) from Beker, Bull. Lond. Math. Soc. 56 (2024), Prop. 1.5. Weaker than the two rows above. |
| Upper, informal | f(n) ≤ n/2 + O(√n) | Erdős Problem a Day, "Erdős #357: how many strictly increasing numbers can you pick with every run-sum distinct? A clean new ceiling." (24 July 2026). A version of its crossing argument is Corollary 4.2 of the paper, credited there. |
| Upper, informal | f(n) ≤ n/2 + O(n^{2/3}) | J. Pickhardt's web manuscript (Paratelligent, 2026), and C. Lenthall-Cleary's proof claim on erdosproblems.com (27 July 2026; unrefereed). A draft with the same bound, pushed the same day, is in the GitHub repository chapinalc/chapinerdos. It calls itself a draft, and its files name no author. |
| Lower | f(n) ≥ (2 − o(1))·√n | Hegyvári (1986), §2, Theorem 2: the interval {t+1, …, t+k} with t = ⌊k²/4⌋ has distinct consecutive sums. It is stated there for shifts of {1, …, k}, not as a bound on f. This is the earliest bound of order √n found. |
| Lower | f(n) ≥ (2 + o(1))·√n | Straus (1966), through Weisenberg's observation on the forum (24 Aug 2025): admissible sets have distinct consecutive sums |
| Lower | f(n) ≥ (4/√3 − o(1))·√n ≈ 2.309·√n | Pickhardt's web manuscript (2026): a residue construction modulo 3. The paper's lower-bound method is this framework with a different pattern and an added skip. |
| Exact values | M(k) for k ≤ 22 (OEIS A364132); f(n) for n ≤ 53 | OEIS A364132 (22 terms); the GitHub repository chy4pro/erdos-357-distinct-block-sums (2 Sep 2026). The paper's values agree with both on their overlap. |

No source found states a bound f(n) ≤ (c + o(1))·n with c < 1/2, a lower-bound constant above 4/√3, or exact values beyond n = 53 and
k = 22. The constants 44273/90000, 797/1620, 12/√21 and 15/√21 do not appear in any source found.

What earlier work already contains:
- **The crossing step.** The bound k ≤ n/2 + O(√n) appeared independently in three informal, AI-assisted sources in July–August
  2026. The paper treats it as background and claims no priority for it.
- **Equal sums of runs of different lengths.** Hegyvári (1986, §3, Theorem 3; see also erdosproblems.com/1213) proves that an increasing
  sequence with gaps at most K and large enough terms contains two different blocks with equal sums. The paper's Lemma 4.7(b), which
  compares runs of ℓ+1 and ℓ consecutive integers, is the simplest instance of that principle. Hegyvári does not use it to bound f or g.
- **The large-offset idea.** Hegyvári's §2 ("translating problem") separates blocks of different lengths by a large common shift.
  Pickhardt's construction and Theorems 1.2–1.3 combine that idea with congruence conditions.
- **The lower-bound framework** (periodic residue patterns plus a size argument) is Pickhardt's.

Why the upper bound does not follow from Coppersmith–Phillips: their weaker property admits sequences of length (13/24)·n − O(1), and
13/24 > 1/2. So no bound below 13/24 can use that property alone.

## Sources and how much of each was read

| Source | How much was read |
|---|---|
| Hegyvári (1986) | **Full text** (read 26 October 2026), pp. 193–200 of the scanned volume 48 in REAL-J, the open repository of the Library of the Hungarian Academy of Sciences (https://real-j.mtak.hu/7472/). The 23 October search had not found it there. |
| Hegyvári (2017), DSc dissertation *Topics in Combinatorial Number Theory* (REAL-D) | Contents and a full-text search: nothing on consecutive sums. |
| Coppersmith and Phillips (1996) | **Abstract only.** The paper is not open access. |
| Beker (2024), arXiv:2311.10087 | Full text |
| Konieczny (2021), arXiv:1504.07156 | §1.5 and the references |
| Erdős and Graham (1980), *Old and new problems and results in combinatorial number theory*, p. 58 | Read in a scan from R. Graham's publications page |
| Erdős (1977), *Problems and results on combinatorial number theory III*, in *Number Theory Day*, LNM 626, pp. 43–72 | p. 70, the source of the infinite-set question. The volume number was confirmed against Crossref (container and ISBN) and a library series listing. |
| Straus (1966); Erdős, Nicolas and Sárközy (1991); Deshouillers and Freiman (1995, 1999) | Straus's theorems were read through ENS (1991) and DF (1999), which are open on Numdam. DF (1995): abstract. |
| erdosproblems.com/357, its forum thread (11 comments, commenting suspended) and its proof-claims page (one claim) | Full. First read on 23 October 2026; re-read before release the same day, with no change. |
| erdosproblems.com/1213 | Full |
| Pickhardt's manuscript | Full text (the PDF was read again on 26 October 2026) |
| Erdős Problem a Day, entry for Problem 357 (24 July 2026) | Full |
| The repository chapinalc/chapinerdos, 357_partial (matched to the claim by bound and date) | README and literature review. The Lean file and the manuscript were not read. |
| Formal Conjectures `ErdosProblems/357.lean`, with its issues and pull requests | Full |
| OEIS A364132, A364153, A363446 | Full |
| Hegyvári's talk at CANT 2026, "Consecutive sums, Sidon sets, convex sequences" | Abstract only. No slides or preprint were found. |

## Searches run

All searches were run on 23 October 2026:
- **arXiv:** about 30 queries on consecutive or block sums, Erdős–Harzheim, Problem 357, and the authors above.
- **OpenAlex and Semantic Scholar:** works citing Hegyvári (1986), Coppersmith–Phillips, Beker and Konieczny; contexts were read for
  the first 100 citations of Hegyvári.
- **zbMATH Open:** the Hegyvári, Straus and Freud records.
- **Web search:** about 20 queries, including the constants 797/1620, 44273/90000, 12/√21 and 15/√21.
- **Other databases:** GitHub repository search, Zenodo, OEIS, and the Formal Conjectures issues and pull requests.

None of these found any of the paper's constants or constructions. On 26 October 2026 the searches were repeated on arXiv (including
Hegyvári's recent preprints), OpenAlex (from 2024), aiXiv, and the erdosproblems.com page, forum and proof claims. They found nothing
new; the forum's last comment is from 31 August 2026.

## Coverage gaps and residual risks

- **Hegyvári (1986)** (resolved in v1.1). Read in full. It contains the (2 − o(1))·√n lower bound implicitly, the bounded-gap theorem,
  and nothing on upper bounds below 2n/3, on hole counting or on residue patterns.
- **Coppersmith–Phillips (1996), full text.** Their improvement 1/512 below 2/3 counts something beyond the trivial bound. A
  methodological overlap with the left-extension lemma (Lemma 4.3) cannot be ruled out without the text.
- **Activity.** AI-assisted work on this problem was active in July–August 2026, and the forum no longer accepts comments. Claims
  could exist in places not indexed by these searches.
- **Not searched:** MathSciNet, Google Scholar, GitHub code search (needs an account), and ResearchGate.

Readers who know of relevant work are asked to write to lab@quanalabs.com. A missed reference will be added and acknowledged in a new
release and a replacement version of the paper.
