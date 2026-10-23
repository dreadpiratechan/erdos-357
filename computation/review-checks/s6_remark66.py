"""Remark 6.6 numerics: for j=2,3 scan offsets u below the left end of U and report
(a) the largest u having a collision that is NOT of divisor type (iv, h=12, (s+12)d = 72u+66+12b),
(b) the smallest u for which the sequence is completely valid, and the set of valid u below the left end."""
import sys, time
import numpy as np
r = [2, 7, 11, 25, 26, 34]
def g(t): return 42 * (t // 6) + r[t % 6]

def collisions(j, u):
    k = 360 * j; b = 288 * j
    a = np.array([42 * u + g(t) + (84 if t >= b else 0) for t in range(k)], dtype=np.int64)
    P = np.concatenate(([0], np.cumsum(a)))
    Y, X = np.tril_indices(k + 1, -1)
    vals = P[Y] - P[X]
    order = np.argsort(vals, kind="stable")
    sv = vals[order]
    eqm = np.nonzero(sv[1:] == sv[:-1])[0]
    if len(eqm) == 0: return []
    groups = {}
    for e in eqm:
        groups.setdefault(int(sv[e]), set()).update([int(order[e]), int(order[e + 1])])
    cols = []
    for v, idxs in groups.items():
        bl = [(int(X[q]), int(Y[q])) for q in sorted(idxs)]
        for p in range(len(bl)):
            for q in range(p + 1, len(bl)):
                (x1, y1), (x2, y2) = bl[p], bl[q]
                if y1 <= x2 or y2 <= x1:
                    if y2 <= x1: (x1, y1), (x2, y2) = (x2, y2), (x1, y1)
                    cols.append((x1, y1 - x1, x2, y2 - x2))
    return cols

for j in [int(a) for a in sys.argv[1:]]:
    t0 = time.time()
    b = 288 * j
    uL = 288 * j * j + 12 * j + 1
    valid_us = []
    last_nondiv = None
    for u in range(0, uL + 1):
        cols = collisions(j, u)
        if not cols:
            valid_us.append(u)
            continue
        for (x, l, y, s) in cols:
            div_type = (l - s == 12 and y < b < y + s and (s + 12) * (y - x) == 72 * u + 66 + 12 * b)
            if not div_type:
                last_nondiv = u
                break
    print(f"j={j}: left end uL={uL}; largest u<=uL with a non-divisor-type collision: {last_nondiv}; "
          f"smallest valid u: {valid_us[0] if valid_us else None} ({valid_us[0]/uL:.4f} of uL); number of valid u in [0,uL]: {len(valid_us)}; "
          f"(uL-last)/uL = {(uL-last_nondiv)/uL:.4f}   [{time.time()-t0:.0f}s]", flush=True)
    print("   valid u below uL (first 15):", valid_us[:15])
