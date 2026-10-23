"""Exhaustive test of the Section-4 lemmas on ALL valid strictly increasing sequences in [1,N] (small N).
Independent of the search programs: enumerates valid sequences by DFS from the definition (all block sums distinct),
then tests, for every sequence and for several n >= max(a):
  Cor 4.2, Lemma 4.1 (sigma in (t,n], injective), Lemma 4.3, Lemma 4.5, Prop 4.6, Lemma 4.7(b).
"""
import sys, time
from math import isqrt

def valid_sequences(N, min_len=0):
    out = []
    def rec(seq, sums_set, last):
        if len(seq) >= min_len:
            out.append(tuple(seq))
        for a in range(last + 1, N + 1):
            new = []
            s = a
            ok = s not in sums_set
            if ok:
                new.append(s)
                for i in range(len(seq) - 1, -1, -1):
                    s += seq[i]
                    if s in sums_set or s in new:
                        ok = False
                        break
                    new.append(s)
            if ok:
                sums_set.update(new)
                seq.append(a)
                rec(seq, sums_set, a)
                seq.pop()
                sums_set.difference_update(new)
    rec([], set(), 0)
    return out

def test_seq(a, n, stats):
    k = len(a)
    P = [0]
    for v in a: P.append(P[-1] + v)
    T = lambda x, y: P[y] - P[x]
    A = set(a)
    assert k <= (n + 1) // 2 + isqrt(n), ("Cor 4.2", a, n)
    thmax = (2 * n + 4) // 3
    # Lemma 4.3 with theta = thmax
    for y in range(3, k + 1):
        for x in range(1, y - 1):
            if T(x, y) <= thmax:
                assert T(x - 1, y) <= n, ("Lemma 4.3", a, n, x, y)
                stats["L43"] += 1
    for t in range(0, n // 2 + 1):
        # Lemma 4.1
        sig = {}
        for y in range(1, k + 1):
            if P[y] > t:
                c = max(x for x in range(0, y) if T(x, y) > t)
                s = T(c, y)
                assert t < s <= n, ("Lemma 4.1 range", a, n, t, y)
                assert s not in sig, ("Lemma 4.1 injective", a, n, t)
                sig[s] = (c, y)
                stats["L41"] += 1
        for th in range(t, min(n, thmax) + 1):
            H = [z for z in range(t + 1, th + 1) if z not in A]
            assert k + len(H) <= (n - t) + isqrt(2 * th), ("Prop 4.6", a, n, t, th, k, len(H))
            stats["P46"] += 1
            # Lemma 4.5
            for y in range(2, k + 1):
                if P[y] > th:
                    for c in range(0, y - 1):
                        if T(c, y) <= th:
                            ok = any(th < T(x, y) <= n for x in range(0, c))
                            assert ok, ("Lemma 4.5", a, n, t, th, y, c)
                            stats["L45"] += 1
    # Lemma 4.7(b): no pattern with both runs inside A
    for l in range(1, n):
        for w in range(0, n):
            if (l + 1) * w + l > n: break
            Y = range(l * w, l * w + l + 1)
            X = range((l + 1) * w + 1, (l + 1) * w + l + 1)
            if all(v in A for v in Y) and all(v in A for v in X):
                raise AssertionError(("Lemma 4.7(b)", a, l, w))
            stats["L47"] += 1

if __name__ == "__main__":
    N = int(sys.argv[1]); minlen = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    t0 = time.time()
    seqs = valid_sequences(N, minlen)
    print("N =", N, "valid sequences (len>=%d):" % minlen, len(seqs), "enumerated in", round(time.time() - t0, 1), "s", flush=True)
    stats = {k: 0 for k in ("L41", "L43", "L45", "P46", "L47")}
    maxk = 0
    tight46 = 0
    for a in seqs:
        if not a: continue
        amax = a[-1]
        ns = sorted(set([amax, amax + 1, (amax + N) // 2, N]))
        for n in ns:
            if amax <= n <= N:
                test_seq(a, n, stats)
        maxk = max(maxk, len(a))
    print("all assertions passed; max length =", maxk, "; instance counts:", stats, "; time", round(time.time() - t0, 1), "s")
