"""Independent validity check of the 2e7 reverse-greedy set (manuscript Sec 8 'Greedy sequences'): are all consecutive-block sums distinct?
Bucketed by sum mod NB so memory stays small; each bucket is sorted and tested for duplicates."""
import sys, time
import numpy as np
from numba import njit
path = sys.argv[1]
a = np.array([int(t) for t in open(path).read().strip().split(",")], dtype=np.int64)
k = len(a)
assert np.all(a[1:] > a[:-1]) and a[0] >= 1
print("terms", k, "min", a[0], "max", a[-1], "ratio terms/sqrt(max) = %.3f" % (k / a[-1] ** 0.5), flush=True)
P = np.concatenate(([0], np.cumsum(a)))

@njit(cache=True)
def fill(P, NB, r, out):
    n = len(P)
    c = 0
    for x in range(n):
        px = P[x]
        for y in range(x + 1, n):
            s = P[y] - px
            if s % NB == r:
                out[c] = s
                c += 1
    return c

@njit(cache=True)
def count_bucket(P, NB, r):
    n = len(P); c = 0
    for x in range(n):
        px = P[x]
        for y in range(x + 1, n):
            if (P[y] - px) % NB == r:
                c += 1
    return c

NB = int(sys.argv[2]) if len(sys.argv) > 2 else 8
t0 = time.time()
total = 0; dup = 0
for r in range(NB):
    c = count_bucket(P, NB, r)
    out = np.empty(c, dtype=np.int64)
    fill(P, NB, r, out)
    out.sort()
    d = int(np.count_nonzero(out[1:] == out[:-1]))
    total += c; dup += d
    print(f"bucket {r}: {c} sums, duplicate adjacent pairs {d}  [{time.time()-t0:.0f}s]", flush=True)
print("total block sums", total, "expected", k * (k + 1) // 2, "duplicates", dup, "VALID" if dup == 0 and total == k * (k + 1) // 2 else "INVALID")
