"""Independent exhaustive computation of M(k) = least n such that a valid k-term sequence 1<=a_1<...<a_k<=n exists.
Method: DFS over increasing sequences with a boolean table of block sums; the only pruning is the elementary
a_r >= M(r) (the first r terms form a valid r-term sequence, so its largest term is >= M(r)), and a_r <= n-(k-r).
Usage: python exact_small.py KMAX
"""
import sys, time
import numpy as np
from numba import njit

@njit(cache=True)
def search(n, k, Mtab, seq, used, nodes_limit):
    # iterative DFS; seq[0..d-1] chosen; used[s] = 1 if s is a block sum of the current sequence
    d = 0
    cand = np.zeros(k + 1, dtype=np.int64)       # current candidate value at depth d
    nodes = 0
    cand[0] = 1
    # pre = starting candidate for depth 0
    lo0 = Mtab[1] if Mtab[1] > 1 else 1
    cand[0] = lo0
    while d >= 0:
        # try next candidate at depth d
        advanced = False
        while cand[d] <= n - (k - 1 - d):
            a = cand[d]
            cand[d] += 1
            # check lower pruning a >= M(d+1)
            if a < Mtab[d + 1]:
                continue
            # new block sums: a, a+seq[d-1], a+seq[d-1]+seq[d-2], ... (strictly increasing, so no self-collision)
            s = a
            ok = used[s] == 0
            if ok:
                i = d - 1
                while i >= 0:
                    s += seq[i]
                    if used[s] != 0:
                        ok = False
                        break
                    i -= 1
            if ok:
                s = a
                used[s] += 1
                i = d - 1
                while i >= 0:
                    s += seq[i]
                    used[s] += 1
                    i -= 1
            if ok:
                seq[d] = a
                nodes += 1
                if d + 1 == k:
                    return 1, nodes
                d += 1
                cand[d] = a + 1
                advanced = True
                break
        if not advanced:
            # backtrack
            d -= 1
            if d >= 0:
                a = seq[d]
                s = a
                used[s] -= 1
                i = d - 1
                while i >= 0:
                    s += seq[i]
                    used[s] -= 1
                    i -= 1
        if nodes > nodes_limit:
            return -1, nodes
    return 0, nodes

def M_of(kmax, verbose=True):
    Mtab = np.zeros(kmax + 2, dtype=np.int64)
    Mtab[0] = 0
    n = 0
    res = {}
    for k in range(1, kmax + 1):
        n = max(n, Mtab[k - 1] + 1)
        t0 = time.time()
        while True:
            seq = np.zeros(k + 1, dtype=np.int64)
            used = np.zeros(k * n + 10, dtype=np.int8)
            Mtab[k] = 1      # placeholder for pruning of position k itself; set below
            # pruning table for depths: positions 1..k use Mtab[1..k]; Mtab[k] must be a valid lower bound (<= true M(k)), use previous M(k-1)+1
            Mtab[k] = Mtab[k - 1] + 1
            found, nodes = search(n, k, Mtab, seq, used, 10**13)
            if found == 1:
                Mtab[k] = n
                res[k] = (n, [int(v) for v in seq[:k]])
                if verbose:
                    print(f"M({k}) = {n}   [{time.time()-t0:.1f}s, last search {nodes} nodes]  witness {list(seq[:k])}", flush=True)
                break
            n += 1
    return Mtab, res

if __name__ == "__main__":
    kmax = int(sys.argv[1])
    Mtab, res = M_of(kmax)
    print("M(1..%d) =" % kmax, [int(Mtab[k]) for k in range(1, kmax + 1)])
