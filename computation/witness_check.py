#!/usr/bin/env python3
"""Independent witness checker for reference/exact_f_table_research.txt (Erdos Problem 357).

Checks every set listed in the table straight from the definition and checks the table's
internal consistency.  It imports nothing from this repository and uses none of the search programs.

Definition: a_1 < ... < a_k is admissible iff the k(k+1)/2 block sums a_u + ... + a_v
(1 <= u <= v <= k) are pairwise distinct.  M(k) = least n such that an admissible k-term
sequence with a_k <= n exists; f(n) = max k with M(k) <= n.

For each 'M k n count' block the checker verifies
  * the listed sets are strictly increasing sequences of positive integers, of length k,
    with maximum exactly n, pairwise different, and the number of them equals `count`;
  * each set is admissible (checked by two different formulations: (a) all block sums
    pairwise distinct; (b) the prefix sums 0=P_0<P_1<..<P_k have pairwise distinct positive
    differences P_i - P_j);
and for the table as a whole
  * the M column is strictly increasing and agrees with the OEIS A364132 terms in reference/oeis_A364132.txt;
  * Section f is exactly f(n) = max{k : M(k) <= n} for n = 1..(last n listed), n up to 77;
  * (what it cannot check: minimality of M(k) and completeness of the listed sets --
    that is the exhaustive solver's job.)

usage: python witness_check.py [table] [oeis_terms]
  table       default: reference/exact_f_table_research.txt   (relative to this script)
  oeis_terms  default: reference/oeis_A364132.txt             (OEIS b-file style lines "n a(n)")
Exit status 0 iff every check passed.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TABLE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "reference", "exact_f_table_research.txt")
OEIS = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "reference", "oeis_A364132.txt")


def read_oeis_terms(path):
    """Terms a(1), a(2), ... from a file of '#' comment lines and 'n a(n)' lines."""
    terms = []
    with open(path, encoding="utf-8") as fh:
        for ln in fh:
            ln = ln.strip()
            if ln and not ln.startswith("#"):
                n, a = ln.split()
                assert int(n) == len(terms) + 1, f"{path}: term index {n} out of order"
                terms.append(int(a))
    return terms


def show_path(p):
    """Path relative to this script's directory when possible (keeps the printed output machine independent)."""
    try:
        return os.path.relpath(p, HERE).replace(os.sep, "/")
    except ValueError:  # different drive on Windows
        return p


def admissible_blocksums(a):
    sums = []
    for u in range(len(a)):
        s = 0
        for v in range(u, len(a)):
            s += a[v]
            sums.append(s)
    return len(sums) == len(set(sums))


def admissible_prefix_diffs(a):
    p = [0]
    for x in a:
        p.append(p[-1] + x)
    diffs = [p[j] - p[i] for i in range(len(p)) for j in range(i + 1, len(p))]
    return len(diffs) == len(set(diffs))


def main():
    f_rows = {}
    blocks = []  # (k, n, count_field, [sets])
    section = None
    with open(TABLE, encoding="utf-8") as fh:
        for ln in fh:
            ln = ln.strip()
            if not ln:
                continue
            if ln.startswith("#"):
                if "SECTION f" in ln:
                    section = "f"
                elif "SECTION M" in ln:
                    section = "M"
                continue
            tok = ln.split()
            if section == "f":
                f_rows[int(tok[0])] = int(tok[1])
            elif tok[0] == "M":
                blocks.append((int(tok[1]), int(tok[2]), tok[3], []))
            else:
                blocks[-1][3].append([int(x) for x in tok])

    bad = 0
    total_sets = 0
    counts = []
    print(f"table: {show_path(TABLE)}")
    print(f"Section f rows: {len(f_rows)} (n = {min(f_rows)}..{max(f_rows)});  Section M blocks: {len(blocks)}")
    for k, n, cnt, sets in blocks:
        problems = []
        if cnt != "witness-only" and int(cnt) != len(sets):
            problems.append(f"count field {cnt} != {len(sets)} sets listed")
        if len({tuple(s) for s in sets}) != len(sets):
            problems.append("duplicate sets")
        for s in sets:
            if len(s) != k:
                problems.append(f"{s}: length {len(s)} != k={k}")
            if any(x < 1 for x in s) or any(s[i] >= s[i + 1] for i in range(len(s) - 1)):
                problems.append(f"{s}: not strictly increasing positive")
            if s[-1] != n:
                problems.append(f"{s}: max {s[-1]} != n={n}")
            if not admissible_blocksums(s):
                problems.append(f"{s}: block sums NOT distinct")
            if not admissible_prefix_diffs(s):
                problems.append(f"{s}: prefix-sum differences NOT distinct (formulation b)")
        total_sets += len(sets)
        counts.append(len(sets))
        status = "OK " if not problems else "FAIL"
        print(f"  {status} k={k:2d} M={n:3d}  sets listed={len(sets):2d}  count field={cnt}")
        for p in problems:
            print("      !!", p)
        bad += len(problems)

    ks = [b[0] for b in blocks]
    ms = [b[1] for b in blocks]
    if ks != list(range(1, len(ks) + 1)):
        print("!! k column is not 1..K consecutive:", ks)
        bad += 1
    if any(ms[i] >= ms[i + 1] for i in range(len(ms) - 1)):
        print("!! M column not strictly increasing")
        bad += 1
    # Section f consistency with M
    K = len(blocks)
    f_bad = 0
    for n, fv in sorted(f_rows.items()):
        expect = max([k for k, m in zip(ks, ms) if m <= n] or [0])
        if fv != expect:
            f_bad += 1
            print(f"  !! f({n}) = {fv} in table but max{{k: M(k)<=n}} = {expect}")
    # coverage: f rows must be exactly 1..77 and the top value f(77)=K
    if sorted(f_rows) != list(range(1, 78)):
        print("!! Section f does not cover exactly n = 1..77")
        f_bad += 1
    if f_rows.get(77) != K:
        print(f"!! f(77) = {f_rows.get(77)} but last M-block has k = {K}")
        f_bad += 1
    bad += f_bad
    print(f"Section f vs M: {len(f_rows)} rows checked, {f_bad} inconsistencies")

    # OEIS cross-check (A364132; the entry lists 22 terms)
    try:
        oeis = read_oeis_terms(OEIS)
        mism = [(i + 1, t, ms[i]) for i, t in enumerate(oeis) if i < len(ms) and ms[i] != t]
        print(f"OEIS A364132 cached terms: {len(oeis)}; compared with M(1..{min(len(oeis), len(ms))}); mismatches: {mism}")
        bad += len(mism)
    except Exception as e:  # pragma: no cover
        print("OEIS terms not readable:", e)
        bad += 1  # a check that could not run is not a pass

    print("M(k):", ms)
    print("optimal set counts:", counts, "total", total_sets)
    claim_m = [1, 2, 4, 5, 7, 10, 12, 13, 15, 18, 21, 24, 25, 29, 30, 33, 36, 38, 41, 47, 50, 52, 56, 60, 63, 67, 69, 75]
    claim_c = [1, 1, 2, 1, 1, 7, 5, 1, 1, 2, 1, 13, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 2]
    print("M(k) equals the 28 claimed values:", ms == claim_m)
    print("counts equal the 28 claimed counts (total 67):", counts == claim_c and total_sets == 67)
    if ms != claim_m or counts != claim_c or total_sets != 67:
        bad += 1
    print("RESULT:", "ALL CHECKS PASSED" if bad == 0 else f"{bad} PROBLEM(S) FOUND")
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()
