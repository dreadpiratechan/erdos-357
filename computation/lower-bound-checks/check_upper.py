"""Independent computational checks of the upper bound f(n) <= (797/1620) n + 2 sqrt n + 7
for Erdos Problem #357 (Lean: Erdos357Upper.f_le_real2).

Written from scratch as an independent re-check; no code shared with the search programs. The Lean
proof is the proof; these are consistency checks of every finite/arithmetic ingredient and of the
intermediate inequalities on concrete admissible sets. numba is used: run WITHOUT `python -I`.

    python check_upper.py [NMAX]      (default NMAX = 10**7 for the arithmetic sweeps)

U1  The eight side conditions of the (5, 9) design and its range conditions, all 12 <= n <= NMAX.
U2  Fiber degree: for 12 <= n <= 100000 the pattern supports Y u X of the design lie in (t, theta]
    and every integer is covered by at most 2 patterns (Lemma F), computed from the supports.
U3  Closing arithmetic 1620 (n - floor(n/2)) <= 797 n + 810 P + 8000 for 12 <= n <= NMAX, and the
    exact worst-case additive constant.
U4  Real-form step isqrt(2 theta) <= 2 isqrt(n) + 2 for n <= NMAX; where the explicit integer bound
    drops below ceil(n/2) for good, and comparison with the other known explicit upper bounds.
U5  Lemma 2, Prop 4, Lemma G and Prop 6' on concrete admissible sets (forward greedy, reverse
    greedy, randomised greedy) for n up to 3000, each set re-verified admissible from scratch.
U6  Exhaustive: every admissible set for n <= 21: Lemma 2 and Prop 4 (and Prop 6' for n >= 12),
    plus exact f(n) for n <= 21 compared with the explicit bound.
"""
import math
import random
import sys
import time

import numpy as np
from numba import njit

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("  FAIL:", msg)
    return cond


@njit(cache=True)
def design(n):
    t = n // 2
    th = (2 * n + 4) // 3
    a5 = t // 5
    b5 = (th - 5) // 6 if th >= 5 else 0
    a9 = (5 * b5 + 5) // 9
    b9 = (th - 9) // 10 if th >= 9 else 0
    return t, th, a5, b5, a9, b9


@njit(cache=True)
def sweep_conditions(nmax):
    """Returns (first failing n or -1, worst additive constant, n at worst)."""
    worst = -(1 << 60)
    worst_n = -1
    for n in range(12, nmax + 1):
        t, th, a5, b5, a9, b9 = design(n)
        ok = (t < 5 * (a5 + 1)) and (6 * b5 + 5 <= th) and (t < 9 * (a9 + 1)) and (10 * b9 + 9 <= th) \
            and (5 * b5 + 5 < 9 * (a9 + 1)) and (9 * b9 + 9 < 6 * (a5 + 1) + 1) \
            and (9 * b9 + 9 < 10 * (a9 + 1) + 1) and (5 * b5 + 5 < 6 * (a5 + 1) + 1) \
            and (th <= n) and (2 * t <= n)
        if not ok:
            return n, worst, worst_n
        P = max(b5 - a5, 0) + max(b9 - a9, 0)
        c = 1620 * (n - t) - 797 * n - 810 * P
        if c > worst:
            worst = c
            worst_n = n
    return -1, worst, worst_n


@njit(cache=True)
def fiber_sweep(nmax):
    """For each n: supports inside (t, theta] and pointwise pattern degree <= 2."""
    for n in range(12, nmax + 1):
        t, th, a5, b5, a9, b9 = design(n)
        cnt = np.zeros(n + 2, dtype=np.int32)
        for fam in range(2):
            l = 5 if fam == 0 else 9
            lo = a5 if fam == 0 else a9
            hi = b5 if fam == 0 else b9
            for w in range(lo + 1, hi + 1):
                mark = np.zeros(0, dtype=np.int64)
                # Y = [l w, l w + l], X = [(l+1) w + 1, (l+1) w + l]; count each z once per pattern
                zs = []
                for z in range(l * w, l * w + l + 1):
                    zs.append(z)
                for z in range((l + 1) * w + 1, (l + 1) * w + l + 1):
                    if z > l * w + l:
                        zs.append(z)
                    else:
                        return n, 3  # Y and X overlap (would need set union)
                for z in zs:
                    if z <= t or z > th:
                        return n, 1
                    cnt[z] += 1
                    if cnt[z] > 2:
                        return n, 2
    return -1, 0


def explicit_bound(n):
    th = (2 * n + 4) // 3
    return (797 * n + 1620 * math.isqrt(2 * th) + 8000) // 1620


def U1_U3(nmax):
    print(f"U1+U3 design conditions and closing arithmetic, 12 <= n <= {nmax}")
    t0 = time.time()
    bad, worst, wn = sweep_conditions(nmax)
    check(bad == -1, f"design condition fails at n = {bad}")
    check(worst <= 8000, f"additive constant {worst} > 8000")
    print(f"  all hold; worst 1620(n-t) - 797n - 810P = {worst} at n = {wn} (Lean allows 8000)  ({time.time() - t0:.1f}s)")
    # small-n sanity of truncated subtraction: the Lean conditions are stated with natural subtraction
    for n in range(12, 40):
        t, th, a5, b5, a9, b9 = design(n)
        check(th >= 9, f"theta >= 9 at n={n}")


def U2(nmax):
    print(f"U2 fiber degree <= 2 and supports in (t, theta], 12 <= n <= {nmax}")
    t0 = time.time()
    bad, code = fiber_sweep(nmax)
    check(bad == -1, f"fiber/support failure code {code} at n = {bad}")
    n = 10 ** 6
    t, th, a5, b5, a9, b9 = design(n)
    print(f"  ok  ({time.time() - t0:.1f}s); at n=10^6 zones (fractions of n): "
          f"Y5 [{5 * (a5 + 1) / n:.4f},{(5 * b5 + 5) / n:.4f}] Y9 [{9 * (a9 + 1) / n:.4f},{(9 * b9 + 9) / n:.4f}] "
          f"X5 [{(6 * (a5 + 1) + 1) / n:.4f},{(6 * b5 + 5) / n:.4f}] X9 [{(10 * (a9 + 1) + 1) / n:.4f},{(10 * b9 + 9) / n:.4f}]; "
          f"patterns P = {(b5 - a5) + (b9 - a9)} vs 13n/810 = {13 * n / 810:.1f}")


def U4(nmax):
    print(f"U4 real-form step and comparisons, n <= {nmax}")
    t0 = time.time()
    last_not_below = None
    for n in range(0, nmax + 1):
        th = (2 * n + 4) // 3
        if not check(math.isqrt(2 * th) <= 2 * math.isqrt(n) + 2, f"sqrt step at n={n}"):
            break
        if n >= 2 and explicit_bound(n) >= (n + 1) // 2:
            last_not_below = n
    print(f"  sqrt step ok; explicit integer bound floor((797n+1620 isqrt(2theta)+8000)/1620) < ceil(n/2) "
          f"for every n in ({last_not_below}, {nmax}]  ({time.time() - t0:.1f}s)")
    # real form vs other explicit bounds (leading constants all 1/2 except this one)
    rows = []
    for n in (10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7, 10 ** 9, 10 ** 12):
        new = 797 / 1620 * n + 2 * math.sqrt(n) + 7
        rows.append((n, new / n, ((n + 1) // 2 + math.isqrt(n)) / n,
                     (n / 2 + 1.5 * 2 ** (-2 / 3) * n ** (2 / 3)) / n))
    print("  n, new/n, [(n+1)/2 + isqrt n]/n (Lean f_le_half_add_sqrt), [n/2 + (3/2)2^(-2/3) n^(2/3)]/n (Pickhardt)")
    for r in rows:
        print(f"   {r[0]:>14}  {r[1]:.6f}  {r[2]:.6f}  {r[3]:.6f}")


# ---------------------------------------------------------------- admissible sets

def admissible(A):
    seen = set()
    for x in range(len(A)):
        s = 0
        for y in range(x, len(A)):
            s += A[y]
            if s in seen:
                return False
            seen.add(s)
    return all(A[i] < A[i + 1] for i in range(len(A) - 1))


def forward_greedy(n, start, skip_p=0.0, rng=None):
    A, sums = [], set()
    for a in range(start, n + 1):
        if rng is not None and rng.random() < skip_p:
            continue
        new, s, ok = [], a, True
        if a in sums:
            continue
        new.append(a)
        for prev in reversed(A):
            s += prev
            if s in sums:
                ok = False
                break
            new.append(s)
        if ok and len(set(new)) == len(new):
            A.append(a)
            sums.update(new)
    return A


def reverse_greedy(n, skip_p=0.0, rng=None):
    A, sums = [], set()  # A kept increasing; new elements are added at the front
    for a in range(n, 0, -1):
        if rng is not None and rng.random() < skip_p:
            continue
        new, s, ok = [a], a, True
        if a in sums:
            continue
        for nxt in A:
            s += nxt
            if s in sums:
                ok = False
                break
            new.append(s)
        if ok and len(set(new)) == len(new):
            A.insert(0, a)
            sums.update(new)
    return A


def audit_set(A, n):
    """Lemma 2, Prop 4, Lemma G, Prop 6' and the final inequality on one admissible set."""
    k = len(A)
    t, th = n // 2, (2 * n + 4) // 3
    Aset = set(A)
    # Lemma 2: block [x, y) with >= 2 terms, x >= 1, sum <= theta  =>  sum + A[x-1] <= n
    for x in range(1, k):
        s = A[x]
        for y in range(x + 1, k):
            s += A[y]
            if s > th:
                break
            if not check(s + A[x - 1] <= n, f"Lemma 2 fails n={n} x={x} y={y + 1}"):
                return None
    holes = sum(1 for z in range(t + 1, th + 1) if z not in Aset)
    s4 = (n - t) + math.isqrt(2 * th)
    check(k + holes <= s4, f"Prop 4 fails n={n}: k={k} holes={holes} bound={s4}")
    slack6 = None
    if n >= 12:
        _, _, a5, b5, a9, b9 = design(n)
        P = max(b5 - a5, 0) + max(b9 - a9, 0)
        for l, lo, hi in ((5, a5, b5), (9, a9, b9)):
            for w in range(lo + 1, hi + 1):
                sup = set(range(l * w, l * w + l + 1)) | set(range((l + 1) * w + 1, (l + 1) * w + l + 1))
                check(not sup <= Aset, f"Lemma G pattern inside A n={n} l={l} w={w}")
        check(P <= 2 * holes, f"Prop 6' fails n={n}: P={P} holes={holes}")
        check(1620 * k <= 797 * n + 1620 * math.isqrt(2 * th) + 8000, f"final bound fails n={n}")
        slack6 = 2 * holes - P
    return s4 - (k + holes), slack6


def U5():
    print("U5 intermediate inequalities on concrete admissible sets")
    rng = random.Random(1620)
    t0 = time.time()
    count, min4, min6, maxk = 0, None, None, 0
    ns = list(range(12, 200)) + [250, 300, 400, 600, 800, 1000, 1500, 2000, 3000]
    for n in ns:
        cands = [forward_greedy(n, 1), forward_greedy(n, max(1, n // 3)), reverse_greedy(n)]
        if n <= 1000:
            cands += [forward_greedy(n, rng.randrange(1, n // 2 + 1), 0.3, rng) for _ in range(3)]
            cands += [reverse_greedy(n, 0.2, rng) for _ in range(3)]
        for A in cands:
            if not check(admissible(A) and all(1 <= a <= n for a in A), f"generated set not admissible n={n}"):
                continue
            r = audit_set(A, n)
            if r is None:
                continue
            count += 1
            maxk = max(maxk, len(A) / math.sqrt(n))
            min4 = r[0] if min4 is None else min(min4, r[0])
            if r[1] is not None:
                min6 = r[1] if min6 is None else min(min6, r[1])
    print(f"  {count} admissible sets (n = 12..3000): all inequalities hold; min slack Prop 4 = {min4}, "
          f"Prop 6' = {min6}; largest k/sqrt(n) = {maxk:.3f}  ({time.time() - t0:.1f}s)")


def U6(nmax):
    print(f"U6 exhaustive over all admissible sets, n <= {nmax}")
    t0 = time.time()
    for n in range(2, nmax + 1):
        best, total = 0, 0
        stack = [((), frozenset())]
        while stack:
            A, sums = stack.pop()
            total += 1
            if len(A) > best:
                best = len(A)
            if A:
                audit_set(list(A), n)
            start = A[-1] + 1 if A else 1
            for a in range(start, n + 1):
                new, s, ok = [a], a, a not in sums
                if not ok:
                    continue
                for prev in reversed(A):
                    s += prev
                    if s in sums:
                        ok = False
                        break
                    new.append(s)
                if ok:
                    stack.append((A + (a,), sums | frozenset(new)))
        bound = explicit_bound(n)
        check(best <= bound, f"exact f({n}) = {best} > explicit bound {bound}")
        if n in (5, 10, 15, 18, 21) or n == nmax:
            print(f"  n={n}: {total} admissible sets (incl. empty), exact f(n)={best}, explicit bound={bound}")
    print(f"  ok  ({time.time() - t0:.1f}s)")


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 7
    t0 = time.time()
    print(f"check_upper.py NMAX={nmax}")
    U1_U3(nmax)
    U2(100000)
    U4(min(nmax, 2 * 10 ** 6))
    U5()
    U6(21)
    print(f"\n{'ALL CHECKS PASSED' if not FAIL else str(len(FAIL)) + ' FAILURES'}  ({time.time() - t0:.0f}s)")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
