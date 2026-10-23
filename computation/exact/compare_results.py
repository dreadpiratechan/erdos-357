#!/usr/bin/env python3
"""Compare this package's results with the research table (reference/exact_f_table_research.txt), line by line.

usage: compare_results.py [RESULTS_DIR [RESEARCH_TABLE [OEIS_TERMS]]]

RESULTS_DIR holds M_table.txt ("k M count"), optimal_sets.txt ("k M a1,a2,..."), and f_table.txt
("n f(n)").  Defaults (all relative to this script): RESULTS_DIR = results, RESEARCH_TABLE =
../reference/exact_f_table_research.txt, OEIS_TERMS = ../reference/oeis_A364132.txt.
In the printed table "repo" means that research table.  Prints a markdown table; exits 1 on any disagreement.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
rdir = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "results")
repo = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "..", "reference", "exact_f_table_research.txt")
OEIS = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "..", "reference", "oeis_A364132.txt")


def read_oeis_terms(path):
    terms = []
    for ln in open(path, encoding="utf-8"):
        ln = ln.strip()
        if ln and not ln.startswith("#"):
            n, a = ln.split()
            assert int(n) == len(terms) + 1, f"{path}: term index {n} out of order"
            terms.append(int(a))
    return terms


# research table
f_repo, blocks, section = {}, {}, None
cur = None
for ln in open(repo, encoding="utf-8"):
    ln = ln.strip()
    if not ln:
        continue
    if ln.startswith("#"):
        section = "f" if "SECTION f" in ln else ("M" if "SECTION M" in ln else section)
        continue
    t = ln.split()
    if section == "f":
        f_repo[int(t[0])] = int(t[1])
    elif t[0] == "M":
        cur = (int(t[1]), int(t[2]), t[3])
        blocks[cur[0]] = [cur[1], cur[2], []]
    else:
        blocks[cur[0]][2].append(tuple(int(x) for x in t))

# mine
mine_M, mine_cnt = {}, {}
for ln in open(os.path.join(rdir, "M_table.txt")):
    if ln.startswith("#") or not ln.strip():
        continue
    k, m, c = ln.split()
    mine_M[int(k)] = int(m)
    mine_cnt[int(k)] = int(c)
mine_sets = {}
for ln in open(os.path.join(rdir, "optimal_sets.txt")):
    k, m, s = ln.split()
    mine_sets.setdefault(int(k), []).append(tuple(int(x) for x in s.split(",")))
f_mine = {}
for ln in open(os.path.join(rdir, "f_table.txt")):
    if ln.startswith("#") or not ln.strip():
        continue
    t = ln.split()
    assert "NO" not in t[2:4], f"missing evidence: {ln}"
    f_mine[int(t[0])] = int(t[1])
oeis = read_oeis_terms(OEIS)

bad = 0
print("| k | M(k) mine | M(k) repo | OEIS A364132 | sets mine | sets repo | identical set lists | verdict |")
print("|--:|--:|--:|--:|--:|--:|:-:|:-:|")
for k in sorted(set(blocks) | set(mine_M)):
    rm, rc, rs = blocks.get(k, [None, None, []])
    mm, mc = mine_M.get(k), mine_cnt.get(k)
    ms = sorted(mine_sets.get(k, []))
    same_sets = ms == sorted(rs)
    o = oeis[k - 1] if k <= len(oeis) else "-"
    ok = (mm == rm) and (mc == len(rs)) and same_sets and (o == "-" or o == mm)
    bad += not ok
    print(f"| {k} | {mm} | {rm} | {o} | {mc} | {len(rs)} | {'yes' if same_sets else '**NO**'} | {'agree' if ok else '**DISAGREE**'} |")
tot_m = sum(mine_cnt.values())
tot_r = sum(len(b[2]) for b in blocks.values())
print(f"\nTotal optimal sets: mine {tot_m}, repo {tot_r}.")
fd = [n for n in range(1, 78) if f_mine.get(n) != f_repo.get(n)]
print(f"f(n) for n = 1..77: {len(f_mine)} values mine, {len(f_repo)} repo; disagreements at n = {fd if fd else 'none'}")
print(f"f(77): mine {f_mine.get(77)}, repo {f_repo.get(77)}")
bad += len(fd)
bad += tot_m != tot_r
print("RESULT:", "ALL AGREE" if bad == 0 else f"{bad} DISAGREEMENT(S)")
sys.exit(1 if bad else 0)
