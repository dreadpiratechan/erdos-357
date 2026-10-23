"""Extra independent checks for statements made in the manuscript.

E1  The four modulus-42 patterns reported by the search are R, -R, R+21, -R+21 (mod 42).
E2  For every 1 <= j <= 499 the window U_j contains a u with no divisor pair (so, with the
    reduction, f(N(j)) >= 360 j also for j < 500; computation only, not formalized).
E3  Thresholds: for j = 2, 3, below the left end of U_j, the largest u whose sequence has a
    coincidence NOT of type (iv) with h = 12 (case analysis says none exists for u >= left end).
Run without -I (numba)."""
import os, sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_lower import bad_mask, skip_seq, collisions, has_pair

R = [2, 7, 11, 25, 26, 34]
reported = [[2, 7, 11, 25, 26, 34], [4, 5, 13, 23, 28, 32], [8, 16, 17, 31, 35, 40], [10, 14, 19, 29, 37, 38]]
imgs = {"R": sorted(R), "-R": sorted((-r) % 42 for r in R), "R+21": sorted((r + 21) % 42 for r in R),
        "-R+21": sorted((-r + 21) % 42 for r in R)}
print("E1", {k: v for k, v in imgs.items()}, "all reported:", sorted(map(tuple, imgs.values())) == sorted(map(tuple, reported)))

t0 = time.time()
worst = (1.0, None)
for j in range(1, 500):
    mask, pairs, _, _ = bad_mask(j)
    frac = mask.mean()
    if frac > 1 - 1e-12:
        print("E2 FAIL: no good u for j =", j); sys.exit(1)
    if 1 - frac < worst[0]:
        worst = (1 - frac, j)
print(f"E2 every j in 1..499 has a good u; smallest good fraction {worst[0]:.4f} at j={worst[1]}  ({time.time()-t0:.1f}s)")

for j in (2, 3):
    b, k = 288 * j, 360 * j
    left = 288 * j * j + 12 * j + 1
    last_other = None
    types = {}
    for u in range(0, left):
        a = skip_seq(u, b, k)
        for g in collisions(a):
            for i1 in range(len(g)):
                for i2 in range(i1 + 1, len(g)):
                    (x1, l1), (x2, l2) = sorted([g[i1], g[i2]])
                    if x1 + l1 > x2:
                        continue
                    x, L, y, s = x1, l1, x2, l2
                    h = L - s
                    if y + s <= b: c = "i"
                    elif x >= b: c = "ii"
                    elif x < b <= y: c = "iii"
                    else: c = "iv" if h == 12 else "iv,h>=24"
                    if c != "iv":
                        types[c] = max(types.get(c, -1), u)
                        last_other = u if last_other is None else max(last_other, u)
    print(f"E3 j={j}: left end of U = {left}; largest u < left end with a coincidence of another type = {last_other}; "
          f"largest u per case {types}")
