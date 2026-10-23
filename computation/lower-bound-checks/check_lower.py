"""Independent computational checks of the two lower bounds for Erdos Problem #357 (the modulus-42 family
and the skip construction; Sections 5 and 6 of the manuscript).

Written from scratch as an independent re-check; it shares no code with the search programs.
Integer arithmetic throughout (floats only in printed ratios). numba is used for
the brute-force window-sum loops, so run WITHOUT `python -I`.

    python check_lower.py quick        # L1-L4, L7 (one row), L8  (seconds)
    python check_lower.py full         # everything below          (about 30 minutes)

L1  Pattern facts for R = (2,7,11,25,26,34) mod 42: R(r) = 7r + eps(r); the prefix table mod 42
    has period 12; the residue spectra of window lengths 0..11 partition Z/42.
L2  Modulus-42 family of the Lean proof (base B = 21(m^2+m+2), k = 12m): brute-force distinctness
    of all window sums for m = 1..60, maximal term, and a negative control (small bases collide).
L3  Skip sequence: the exact doubled window-sum formula (W) on random windows.
L4  Skip sequence: the mod-7 / mod-6 phase filter over all 216 phase triples.
L5  Skip sequence, j = 1..4, EVERY u of the window W_j: all equal-sum window pairs by brute force;
    each must be of the one predicted type (length gap 12, the short later window straddles the
    skip index b, and (s+12) d = 72u + 66 + 12b with 14 <= s+12 <= d <= b-1). This tests
    `collision_pair` / `distinct_skip` ("no divisor pair => all sums distinct") on these rows.
L6  Skip sequence, larger rows j = 10, 25, 50: brute-force distinctness for chosen good u, and a
    collision for a chosen bad u (negative control).
L7  Exact number of bad u in W_j (u having a divisor pair in the box) for j = 500, 501, 1000,
    2000, against |W_j| = 2000 j and the union bound 12000 + (8000/3) ln2 j + 96 (j + 8).
L8  Assembly arithmetic: maximal terms, N(j) <= n for j = isqrt(n // 12096) - 4, and the passage
    from the floor forms to the real forms, in exact integer arithmetic.
"""
import math
import random
import sys
import time

import numpy as np
from numba import njit

R6 = (2, 7, 11, 25, 26, 34)
Q = 42
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("  FAIL:", msg)
    return cond


# ---------------------------------------------------------------- brute-force kernels

@njit(cache=True)
def all_window_sums(a):
    k = a.shape[0]
    out = np.empty(k * (k + 1) // 2, dtype=np.int64)
    p = 0
    for x in range(k):
        s = 0
        for y in range(x, k):
            s += a[y]
            out[p] = s
            p += 1
    return out


@njit(cache=True)
def has_duplicate_sorted(s):
    for i in range(1, s.shape[0]):
        if s[i] == s[i - 1]:
            return True
    return False


@njit(cache=True)
def windows_with_sums(a, targets):
    """All windows (x, L) whose sum lies in the sorted array `targets`."""
    k = a.shape[0]
    xs = []
    ls = []
    vs = []
    for x in range(k):
        s = 0
        for y in range(x, k):
            s += a[y]
            lo, hi = 0, targets.shape[0]
            while lo < hi:
                mid = (lo + hi) // 2
                if targets[mid] < s:
                    lo = mid + 1
                else:
                    hi = mid
            if lo < targets.shape[0] and targets[lo] == s:
                xs.append(x)
                ls.append(y - x + 1)
                vs.append(s)
    return xs, ls, vs


def distinct(a):
    s = all_window_sums(a)
    s.sort()
    return not has_duplicate_sorted(s)


def collisions(a):
    """List of groups [(x, L), ...] of windows sharing a sum (only groups of size >= 2)."""
    s = all_window_sums(a)
    s.sort()
    d = np.nonzero(s[1:] == s[:-1])[0]
    if d.size == 0:
        return []
    targets = np.unique(s[d])
    xs, ls, vs = windows_with_sums(a, targets)
    groups = {}
    for x, L, v in zip(xs, ls, vs):
        groups.setdefault(v, []).append((x, L))
    return [g for g in groups.values() if len(g) >= 2]


# ---------------------------------------------------------------- sequences

def mod42_seq(m):
    B = 21 * (m * m + m + 2)
    return np.array([B + Q * (i // 6) + R6[i % 6] for i in range(12 * m)], dtype=np.int64)


def skip_seq(u, b, k):
    return np.array([Q * u + Q * (t // 6) + R6[t % 6] + (84 if t >= b else 0) for t in range(k)],
                    dtype=np.int64)


def eps():
    return [R6[r] - 7 * r for r in range(6)]


def pe(n):
    e = eps()
    return sum(e[i] for i in range(n % 6))


def has_pair(u, j):
    b = 288 * j
    M = 72 * u + 66 + 12 * b
    for L in range(14, math.isqrt(M) + 1):
        if M % L == 0:
            d = M // L
            if L <= d <= b - 1:
                return True
    return False


# ---------------------------------------------------------------- L1

def L1():
    print("L1 pattern facts")
    e = eps()
    check(e == [2, 0, -3, 4, -2, -1] and sum(e) == 0, f"eps = {e}")
    check(all(R6[i] < R6[i + 1] for i in range(5)) and R6[0] + Q > R6[5], "R increasing across periods")
    # prefix residues of the 6-periodic pattern a_t = 42*floor(t/6) + R[t%6] (mod 42)
    pref = [0]
    for t in range(48):
        pref.append((pref[-1] + R6[t % 6]) % Q)
    check(pref[12] == 0 and pref[6] == sum(R6) % Q == 21, f"period: pref6={pref[6]}, pref12={pref[12]}")
    check(all(pref[t + 12] == pref[t] for t in range(36)), "prefix table has period 12")
    spectra = [frozenset((pref[i + l] - pref[i]) % Q for i in range(12)) for l in range(12)]
    union = set().union(*spectra)
    sizes = [len(s) for s in spectra]
    check(sum(sizes) == Q and union == set(range(Q)), f"spectra partition Z/42 (sizes {sizes})")
    expected = {0: {0}, 1: set(R6), 2: {9, 18, 36}, 3: {1, 20}, 6: {21}}
    for l, s in expected.items():
        check(spectra[l] == s, f"spectrum of length {l} = {sorted(spectra[l])}")
    # lengths >= 12: spectrum depends only on length mod 12
    for l in range(12, 36):
        sp = frozenset((pref[i + l] - pref[i]) % Q for i in range(12))
        check(sp == spectra[l % 12], f"spectrum of length {l} equals that of {l % 12}")
    print("  sizes", sizes, "-> partition of Z/42: equal window sums force equal lengths mod 12")


# ---------------------------------------------------------------- L2

def L2(mmax):
    print(f"L2 modulus-42 family, m = 1..{mmax}")
    t0 = time.time()
    for m in range(1, mmax + 1):
        a = mod42_seq(m)
        check(np.all(np.diff(a) > 0) and a[0] >= 1, f"mod42 m={m} increasing/positive")
        check(int(a[-1]) <= 21 * m * m + 105 * m + 46, f"mod42 m={m} max term")
        check(int(a[-1]) == 21 * m * m + 105 * m + 34, f"mod42 m={m} max term exact")
        check(distinct(a), f"mod42 m={m} distinct sums")
    print(f"  all window sums distinct for m = 1..{mmax}  ({time.time() - t0:.1f}s)")
    # negative control: bases 42*t with t small collide; minimal good t vs the Lean base
    for m in (10, 20):
        k = 12 * m
        lean_t = m * (m + 1) // 2 + 1
        first_good = None
        bad = 0
        for t in range(0, lean_t + 1):
            a = np.array([42 * t + Q * (i // 6) + R6[i % 6] for i in range(k)], dtype=np.int64)
            if distinct(a):
                if first_good is None:
                    first_good = t
            else:
                bad += 1
        check(first_good is not None and first_good <= lean_t, f"mod42 m={m} control")
        print(f"  control m={m} (k={k}): bases 42t, t<=Lean t={lean_t}: {bad} collide, first distinct t={first_good}")


# ---------------------------------------------------------------- L3

def L3(trials):
    print(f"L3 window formula (W), {trials} random windows")
    rng = random.Random(357)
    for _ in range(trials):
        u = rng.randrange(0, 10 ** 6)
        b = rng.randrange(0, 3000)
        x = rng.randrange(0, 3000)
        L = rng.randrange(0, 400)
        lhs = 2 * sum(Q * u + Q * (t // 6) + R6[t % 6] + (84 if t >= b else 0) for t in range(x, x + L))
        nm = lambda z: max(z - b, 0)
        rhs = 84 * u * L + 7 * L * (2 * x + L - 1) + 2 * (pe(x + L) - pe(x)) + 168 * (nm(x + L) - nm(x))
        if not check(lhs == rhs, f"(W) fails at u={u} b={b} x={x} L={L}"):
            break
    print("  ok")


# ---------------------------------------------------------------- L4

def L4():
    print("L4 phase filter")
    pe6 = [pe(r) for r in range(6)]
    check(pe6 == [0, 2, 2, -1, 3, 1], f"pe table {pe6}")
    seen = set()
    survivors = 0
    for xi in range(6):
        for eta in range(6):
            for l in range(6):
                dE = (pe6[(eta + l) % 6] - pe6[eta]) - (pe6[(xi + l) % 6] - pe6[xi])
                seen.add(dE)
                d6 = (eta - xi) % 6
                c7 = dE % 7 == 0
                c6 = (7 * d6 * (l + 12) + dE) % 6 == 0
                if c7 and c6:
                    survivors += 1
                    check(dE == 0, f"phase filter: xi={xi} eta={eta} l={l} dE={dE}")
    check(min(seen) >= -8 and max(seen) <= 8, f"dE range {min(seen)}..{max(seen)}")
    print(f"  dE values {sorted(seen)}; triples passing both congruences: {survivors}, all with dE = 0")


# ---------------------------------------------------------------- L5

def classify(group, u, j):
    """Check every disjoint pair in an equal-sum group against the predicted collision type."""
    b, k = 288 * j, 360 * j
    bad_type = 0
    pairs = 0
    for i1 in range(len(group)):
        for i2 in range(i1 + 1, len(group)):
            (x1, l1), (x2, l2) = group[i1], group[i2]
            if not (x1 + l1 <= x2 or x2 + l2 <= x1):
                continue  # overlapping: its disjoint reduction is another pair of the list
            pairs += 1
            if x1 > x2:
                x1, l1, x2, l2 = x2, l2, x1, l1
            # earlier window must be the longer one (the sequence increases)
            if not l1 > l2:
                bad_type += 1
                continue
            x, L, y, s = x1, l1, x2, l2
            d = y - x
            ok = (L - s == 12 and y < b < y + s and x + L <= y and y + s <= k
                  and (s + 12) * d == 72 * u + 66 + 12 * b and 14 <= s + 12 <= d <= b - 1)
            if not ok:
                bad_type += 1
    return pairs, bad_type


def L5(jmax):
    print(f"L5 skip rows j = 1..{jmax}, every u in W_j")
    for j in range(1, jmax + 1):
        t0 = time.time()
        b, k = 288 * j, 360 * j
        ulo, uhi = 288 * j * j + 12 * j + 1, 288 * j * j + 2012 * j
        n_pair = n_collide = n_pair_no_coll = n_pairs_total = n_badtype = 0
        for u in range(ulo, uhi + 1):
            p = has_pair(u, j)
            a = skip_seq(u, b, k)
            if not p:
                if not check(distinct(a), f"skip j={j} u={u}: no divisor pair but a collision"):
                    groups = collisions(a)
                    print("    groups:", groups[:3])
                continue
            n_pair += 1
            groups = collisions(a)
            if groups:
                n_collide += 1
            else:
                n_pair_no_coll += 1
            for g in groups:
                pr, bt = classify(g, u, j)
                n_pairs_total += pr
                n_badtype += bt
        check(n_badtype == 0, f"skip j={j}: {n_badtype} collisions of an unpredicted type")
        W = uhi - ulo + 1
        print(f"  j={j} k={k} |W|={W}: no-pair u all distinct ({W - n_pair}); with pair {n_pair} "
              f"(collide {n_collide}, distinct anyway {n_pair_no_coll}); disjoint colliding pairs "
              f"{n_pairs_total}, unpredicted type {n_badtype}  ({time.time() - t0:.0f}s)")


# ---------------------------------------------------------------- L6

def L6(js):
    print(f"L6 larger skip rows j in {js}")
    rng = random.Random(42)
    for j in js:
        b, k = 288 * j, 360 * j
        ulo, uhi = 288 * j * j + 12 * j + 1, 288 * j * j + 2012 * j
        good = [u for u in (ulo,) if not has_pair(u, j)]
        while len(good) < 2:
            u = rng.randrange(ulo, uhi + 1)
            if not has_pair(u, j):
                good.append(u)
        for u in good:
            t0 = time.time()
            a = skip_seq(u, b, k)
            ok = distinct(a)
            check(ok, f"skip j={j} u={u} distinct")
            ratio = k / math.sqrt(int(a[-1]))
            print(f"  j={j} k={k} u={u} ({'left end' if u == ulo else 'random good'}): distinct={ok}, "
                  f"max={int(a[-1])}, k/sqrt(max)={ratio:.4f}  ({time.time() - t0:.0f}s)")
        if j <= 25:
            u = next(u for u in range(ulo, uhi + 1) if has_pair(u, j))
            a = skip_seq(u, b, k)
            groups = collisions(a)
            pr = bt = 0
            for g in groups:
                p_, b_ = classify(g, u, j)
                pr += p_
                bt += b_
            check(bt == 0, f"skip j={j} bad u={u}: unpredicted collision type")
            print(f"  control j={j} first u with a divisor pair u={u}: {len(groups)} colliding sums, "
                  f"{pr} disjoint pairs, unpredicted type {bt}")


# ---------------------------------------------------------------- L7

@njit(cache=True)
def bad_mask(j):
    b = 288 * j
    ulo = 288 * j * j + 12 * j + 1
    uhi = 288 * j * j + 2012 * j
    P1 = 72 * ulo + 66 + 12 * b
    P2 = 72 * uhi + 66 + 12 * b
    mask = np.zeros(uhi - ulo + 1, dtype=np.uint8)
    pairs = 0
    Lmin_seen = 1 << 62
    Lmax_seen = 0
    L = 14
    while L * L <= P2:
        dlo = max(L, (P1 + L - 1) // L)
        dhi = min(b - 1, P2 // L)
        for d in range(dlo, dhi + 1):
            M = L * d
            if (M - 66 - 12 * b) % 72 == 0:
                u = (M - 66 - 12 * b) // 72
                if ulo <= u <= uhi:
                    mask[u - ulo] = 1
                    pairs += 1
                    if L < Lmin_seen:
                        Lmin_seen = L
                    if L > Lmax_seen:
                        Lmax_seen = L
        L += 1
    return mask, pairs, Lmin_seen, Lmax_seen


def L7(js):
    print(f"L7 exact bad-u counts for j in {js}")
    ln2 = 0.6931471808
    for j in js:
        t0 = time.time()
        mask, pairs, lmin, lmax = bad_mask(j)
        nbad = int(mask.sum())
        W = 2000 * j
        bound = 12000 + (8000 / 3) * ln2 * j + 96 * (j + 8)
        check(nbad < W, f"j={j}: bad {nbad} >= |W|")
        check(nbad <= pairs <= bound, f"j={j}: pairs {pairs} exceed the union bound {bound:.0f}")
        check(72 * j <= lmin and lmax <= 144 * j + 514, f"j={j}: L range {lmin}..{lmax}")
        first_good = int(np.argmin(mask)) + 288 * j * j + 12 * j + 1
        print(f"  j={j}: |W|={W}, bad u={nbad} ({nbad / W:.4f}), divisor pairs={pairs} ({pairs / W:.4f}), "
              f"Lean union bound={bound:.0f} ({bound / W:.4f}); L in [{lmin},{lmax}] vs [72j,144j+514]=[{72 * j},{144 * j + 514}]; "
              f"left end good={mask[0] == 0}, first good u={first_good}  ({time.time() - t0:.1f}s)")


# ---------------------------------------------------------------- L8

def L8():
    print("L8 assembly arithmetic")
    # skip: maximal term over the whole window, N(j), and the floor -> real step
    for j in (1, 2, 500, 501, 10 ** 4, 10 ** 6):
        uhi = 288 * j * j + 2012 * j
        k, b = 360 * j, 288 * j
        t = k - 1
        top = Q * uhi + Q * (t // 6) + R6[t % 6] + 84
        check(top == 12096 * j * j + 87024 * j + 76, f"skip max term j={j}")
        check(12096 * j * j + 87024 * j + 81 <= 12096 * (j + 4) ** 2, f"N(j) <= 12096 (j+4)^2 at j={j}")
    n0 = 12096 * 504 ** 2
    check(n0 == 3072577536, f"threshold {n0}")
    rng = random.Random(7)
    samples = [n0, n0 + 1, n0 + 12095, 12096 * 505 ** 2 - 1, 10 ** 10, 10 ** 12, 10 ** 15] + \
              [rng.randrange(n0, 10 ** 14) for _ in range(20000)]
    for n in samples:
        q = math.isqrt(n // 12096)
        j = q - 4
        check(j >= 500, f"j >= 500 at n={n}")
        check(12096 * j * j + 87024 * j + 81 <= n, f"N(j) <= n at n={n}")
        # 360 j >= (15/sqrt21) sqrt n - 1800  <=>  360 (q+1) >= 15 sqrt(n/21)  <=>  12096 (q+1)^2 >= n
        check(12096 * (q + 1) ** 2 > n, f"real step at n={n}")
    # all-n form: below the threshold, (15/sqrt21) sqrt n < 181440
    check(225 * (n0 - 1) < 181440 ** 2 * 21, "skip_lower_real below threshold")
    # mod 42: floor -> real step for n = 0..10^6 and random large n
    for n in list(range(0, 10 ** 6)) + [rng.randrange(10 ** 6, 10 ** 15) for _ in range(20000)]:
        q = math.isqrt(n // 21)
        m = max(q - 3, 0)
        if q >= 3:
            if not check(21 * m * m + 105 * m + 46 <= n, f"mod42 N(m) <= n at n={n}"):
                break
        # 12 m >= 12 sqrt(n/21) - 48  <=>  12 (q+1) >= 12 sqrt(n/21) when q >= 3; trivially true for q < 3
        if not check(21 * (q + 1) ** 2 > n, f"mod42 real step at n={n}"):
            break
    print(f"  ok; constants 15/sqrt21 = {15 / math.sqrt(21):.6f} = 360/sqrt12096 = {360 / math.sqrt(12096):.6f}; "
          f"12/sqrt21 = {12 / math.sqrt(21):.6f}")


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "quick"
    t0 = time.time()
    print(f"check_lower.py mode={mode}  numpy {np.__version__}")
    L1()
    L3(20000 if mode == "full" else 2000)
    L4()
    L8()
    if mode == "full":
        L2(60)
        L5(4)
        L6([10, 25, 50])
        L7([500, 501, 1000, 2000])
    else:
        L2(15)
        L5(1)
        L7([500])
    print(f"\n{'ALL CHECKS PASSED' if not FAIL else str(len(FAIL)) + ' FAILURES'}  ({time.time() - t0:.0f}s)")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
