#!/usr/bin/env python3
"""Write results/f_table.txt ("n f(n)" plus the evidence for each row), n = 1..77.

usage: make_f_table.py EXACT_DIR        (EXACT_DIR contains results/ and logs/)

For every n it takes f(n) = #{k : M(k) <= n} from results/M_table.txt and then requires LOGGED evidence
for the two halves of "f(n) = k":
  (>=)  a set with k = f(n) terms and maximum M(k) <= n exists (it is in results/optimal_sets.txt and was
        re-checked from the definition by the engine; witness_check.py re-checks it again);
  (<=)  count(f(n)+1, n') = 0 in one of the engine logs for some n' >= n.  Because "a_k <= n" is
        monotone in n (a sequence with a_k <= n also has a_k <= n'), count(k, n') = 0 implies count(k, n) = 0
        for every n <= n'.  Longer sequences are excluded as well: an admissible (k+j)-term sequence
        contains an admissible (k+1)-term prefix with a_{k+1} <= a_{k+j} <= n (heredity, README Lemma 2).
Sources of the zeros: results/f_table_decisions.txt (per-n decisions, n <= 68), logs/table_k28.log
("k=.. n=..: 0 sets" lines) and logs/decisions_n69_77.log ("count k=.. n=..: 0 admissible" lines).
The evidence column says whether the zero was obtained at exactly n ("direct") or at a larger n' ("via n'").
"""
import re
import sys

D = sys.argv[1]
M = {}
for ln in open(f"{D}/results/M_table.txt"):
    if ln.startswith("#") or not ln.strip():
        continue
    k, m, c = ln.split()
    M[int(k)] = (int(m), int(c))
assert sorted(M) == list(range(1, 29)), "M table must cover k = 1..28"
ms = [M[k][0] for k in range(1, 29)]
assert ms == sorted(set(ms))

# optimal sets: each M(k) has its sets, counts agree
sets = {}
for ln in open(f"{D}/results/optimal_sets.txt"):
    k, m, s = ln.split()
    sets.setdefault(int(k), []).append((int(m), s))
for k in M:
    assert len(sets[k]) == M[k][1] and all(m == M[k][0] for m, _ in sets[k]), k

zero = {}   # (k, n) -> source string, only zero counts
pos = {}    # (k, n) -> count, positive counts


def add(k, n, cnt, src):
    if cnt == 0:
        zero.setdefault((k, n), src)
    else:
        pos[(k, n)] = cnt


for ln in open(f"{D}/logs/table_k28.log"):
    m = re.match(r"k=\s*(\d+) n=\s*(\d+): (\d+) sets", ln)
    if m:
        add(int(m[1]), int(m[2]), int(m[3]), "table_k28.log")
for ln in open(f"{D}/results/f_table_decisions.txt"):
    if ln.startswith("#") or not ln.strip():
        continue
    head, cnt, _nodes, _secs = [t.strip() for t in ln.split("|")]
    n, f = (int(t) for t in head.split())
    m = re.match(r"count\((\d+),(\d+)\) = (\d+)", cnt)
    assert int(m[1]) == f + 1 and int(m[2]) == n
    add(int(m[1]), int(m[2]), int(m[3]), "f_table_decisions.txt")
try:
    for ln in open(f"{D}/logs/decisions_n69_77.log"):
        m = re.match(r"count k=(\d+) n=(\d+) .*?: (\d+) admissible", ln)
        if m:
            add(int(m[1]), int(m[2]), int(m[3]), "decisions_n69_77.log")
except FileNotFoundError:
    pass

# the first hit for each k in the table log is M(k) with the recorded set count
for k, (m, c) in M.items():
    assert pos.get((k, m)) == c, f"table log has no matching positive row for k={k} (M={m}, count {c})"

rows, bad = [], 0
for n in range(1, 78):
    f = sum(1 for m in ms if m <= n)
    k = f + 1
    cands = sorted(nn for (kk, nn) in zero if kk == k and nn >= n)
    if not cands:
        rows.append(f"{n} {f}  NO EVIDENCE for count({k},{n}) = 0")
        bad += 1
        continue
    nn = cands[0]
    how = "direct" if nn == n else f"via n={nn}"
    rows.append(f"{n} {f}  count({k},{n})=0 {how} [{zero[(k, nn)]}]")
with open(f"{D}/results/f_table.txt", "w", newline="\n") as fh:
    fh.write("# n f(n)  evidence for f(n)+1 being impossible; f(n) >= k is witnessed by the optimal set(s) of M(k) <= n\n")
    fh.write("\n".join(rows) + "\n")
print(f"wrote {D}/results/f_table.txt: {len(rows)} rows, {bad} without evidence, f(77) = {rows[-1].split()[1]}")
sys.exit(1 if bad else 0)
