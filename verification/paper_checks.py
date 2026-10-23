"""Exact checks of every numerical claim and finite case analysis used in the written proofs.

Independent of the Lean development: plain Python with integers and Fractions (the one real
number, ln 2, is bracketed by rationals). Each check prints PASS or raises. Run:
    py verification/paper_checks.py
Section numbers refer to the manuscript.
"""
from fractions import Fraction as Fr
from math import isqrt, log, sqrt
import itertools

CHECKS = []


def check(name):
    def deco(fn):
        CHECKS.append((name, fn))
        return fn
    return deco


# ---------------------------------------------------------------- Section 5: the mod-42 pattern
RHO = (2, 7, 11, 25, 26, 34)
EPS = (2, 0, -3, 4, -2, -1)            # rho(r) = 7 r + eps(r)


def pe(n):                              # sum_{i < n mod 6} eps(i)
    return sum(EPS[: n % 6])


@check("rho(r) = 7r + eps(r), sum eps = 0, pe table, increments of the pattern")
def _():
    assert all(RHO[r] == 7 * r + EPS[r] for r in range(6))
    assert sum(EPS) == 0
    assert [pe(n) for n in range(6)] == [0, 2, 2, -1, 3, 1]
    assert min(pe(n) for n in range(6)) == -1 and max(pe(n) for n in range(6)) == 3
    seq = [42 * (t // 6) + RHO[t % 6] for t in range(13)]
    assert [b - a for a, b in zip(seq, seq[1:])][:6] == [5, 4, 14, 1, 8, 10]
    for t in range(1000):              # 42 floor(t/6) + rho(t mod 6) = 7t + eps(t mod 6)
        assert 42 * (t // 6) + RHO[t % 6] == 7 * t + EPS[t % 6]
    for x in range(60):                # sum_{t=x}^{x+L-1} eps(t mod 6) = pe(x+L) - pe(x)
        for L in range(60):
            assert sum(EPS[t % 6] for t in range(x, x + L)) == pe(x + L) - pe(x)


@check("mod-42 spectra D_0..D_11 partition Z/42 (equal window sums force lengths = mod 12)")
def _():
    P = [0]
    for t in range(48):
        P.append((P[-1] + RHO[t % 6]) % 42)
    assert all(P[m + 12] == P[m] for m in range(36))           # 12-periodic prefix residues
    assert P[:12] == [0, 2, 9, 20, 3, 29, 21, 23, 30, 41, 24, 8]
    D = [sorted({(P[x + l] - P[x]) % 42 for x in range(12)}) for l in range(12)]
    expected = [[0], [2, 7, 11, 25, 26, 34], [9, 18, 36], [1, 20], [3, 12, 27],
                [10, 14, 19, 29, 37, 38], [21], [4, 5, 13, 23, 28, 32], [15, 30, 39],
                [22, 41], [6, 24, 33], [8, 16, 17, 31, 35, 40]]
    assert D == expected, D
    allres = sorted(r for d in D for r in d)
    assert allres == list(range(42))                            # disjoint and covering


@check("mod-42 size argument: 12B > 7(12m+1)^2/4 for B = 21(m^2+m+2); max term 21m^2+105m+34")
def _():
    for m in range(0, 2000):
        B = 21 * (m * m + m + 2)
        assert 4 * 12 * B > 7 * (12 * m + 1) ** 2
        k = 12 * m
        if k:
            amax = B + 42 * ((k - 1) // 6) + RHO[(k - 1) % 6]
            assert amax == 21 * m * m + 105 * m + 34 <= 21 * m * m + 105 * m + 46


@check("mod-42 construction is admissible (brute force, m = 1..12)")
def _():
    for m in range(1, 13):
        B = 21 * (m * m + m + 2)
        a = [B + 42 * (i // 6) + RHO[i % 6] for i in range(12 * m)]
        sums = set()
        for u in range(len(a)):
            s = 0
            for v in range(u, len(a)):
                s += a[v]
                assert s not in sums
                sums.add(s)


# ---------------------------------------------------------------- Section 6: the skip construction
def sk(u, b, t):
    return 42 * u + 42 * (t // 6) + RHO[t % 6] + (84 if t >= b else 0)


@check("window-sum formula (W) for the skip sequence")
def _():
    for u in (0, 1, 5):
        for b in (0, 7, 13):
            for x in range(40):
                for L in range(40):
                    lhs = 2 * sum(sk(u, b, t) for t in range(x, x + L))
                    nm = lambda m: max(m - b, 0)
                    rhs = 84 * u * L + 7 * L * (2 * x + L - 1) + 2 * (pe(x + L) - pe(x)) \
                        + 168 * (nm(x + L) - nm(x))
                    assert lhs == rhs


@check("phase filter: 7 | dE and 6 | 7 d (s+12) + dE force dE = 0 (all 216 phase triples)")
def _():
    hits = 0
    for xi, eta, ell in itertools.product(range(6), repeat=3):
        # long window [x, x+s+12), short window [y, y+s): x+L = x+s+12 = xi+ell (mod 6)
        dE = (pe(eta + ell) - pe(eta)) - (pe(xi + ell) - pe(xi))
        d = (eta - xi) % 6
        for dd in range(d, 36, 6):                      # every d with d = eta - xi (mod 6)
            for ss in range(ell, 36, 6):                # every s with s = ell (mod 6)
                if dE % 7 == 0 and (7 * dd * (ss + 12) + dE) % 6 == 0:
                    assert dE == 0, (xi, eta, ell, dE)
        if dE % 7 == 0 and dE != 0:
            hits += 1
    assert hits > 0                                     # the filter is not vacuous: dE = +-7 occurs


@check("sum over rho mod 72 of #{r : rho r = 66 mod 72} is 96 (= 8 * 12)")
def _():
    assert sum(1 for a in range(72) for b in range(72) if a * b % 72 == 66) == 96
    assert sum(1 for a in range(8) for b in range(8) if a * b % 8 == 2) == 8
    assert sum(1 for a in range(9) for b in range(9) if a * b % 9 == 3) == 12


@check("skip case analysis constants (A)-(D) and the window W")
def _():
    for j in (1, 2, 3, 10, 230, 500, 10**4):
        b, k = 288 * j, 360 * j
        lo = 1008 * (288 * j * j + 12 * j + 1)          # 1008 u at the left end of W
        assert lo == 290304 * j * j + 12096 * j + 1008
        assert 14 * (b * b // 4) + 16 < lo              # (A): s + d <= b, h >= 12
        assert 14 * ((k - b) ** 2 // 4) + 16 < lo       # (B)
        assert 14 * (72 * j) * (288 * j + 12) + 16 < lo  # (C): s <= 72j, s + d <= 360j
        assert 2 * lo // 1 > 0
        two016 = 2016 * (288 * j * j + 12 * j + 1)
        assert 14 * (k * k // 4) + 168 * k + 16 < two016  # (D), h >= 24
        P1 = 72 * (288 * j * j + 12 * j + 1) + 66 + 12 * b
        P2 = 72 * (288 * j * j + 2012 * j) + 66 + 12 * b
        assert P1 == 20736 * j * j + 4320 * j + 138 and P2 == 20736 * j * j + 148320 * j + 66
        assert 72 * j * 288 * j < P1                    # L < 72j impossible
        assert (144 * j + 515) ** 2 > P2                 # L > 144j + 514 impossible
        assert (144 * j + 514) // 72 <= 2 * j + 7


@check("union bound: |Bad| <= (8000/3) j (ln2 + 4.5/j) + 96 (j + 8) < 2000 j exactly for j >= 230")
def _():
    ln2_hi = Fr(6931471808, 10**10)
    assert log(2) < float(ln2_hi)
    first = None
    for j in range(1, 2000):
        bound = Fr(8000, 3) * j * (ln2_hi + Fr(9, 2 * j)) + 96 * (j + 8)
        if bound < 2000 * j:
            first = first or j
        elif first:
            raise AssertionError(f"bound fails again at j = {j}")
    assert first == 230, first
    # harmonic estimate sum_{q=j}^{2j+7} 1/q <= ln 2 + 4.5/j, checked exactly for small j
    for j in range(1, 400):
        H = sum(Fr(1, q) for q in range(j, 2 * j + 8))
        assert H <= ln2_hi + Fr(9, 2 * j)


@check("Theorem 1.3 arithmetic: N(j) <= 12096 (j+4)^2, 12096 = 24^2 * 21, 360/sqrt 12096 = 15/sqrt 21")
def _():
    assert 12096 == 24 * 24 * 21
    assert Fr(360, 24) == 15
    for j in range(0, 100000, 37):
        assert 12096 * j * j + 87024 * j + 81 <= 12096 * (j + 4) ** 2
        u = 288 * j * j + 2012 * j
        if j:
            amax = 42 * u + 42 * ((360 * j - 1) // 6) + RHO[(360 * j - 1) % 6] + 84
            assert amax == 12096 * j * j + 87024 * j + 76
    assert 12096 * 504 ** 2 == 3072577536


# ---------------------------------------------------------------- Section 4: the upper bound
M = 360000
BANDS = [(4, 45000, 45687), (5, 36550, 37499), (6, 31250, 31729), (5, 38075, 39999), (9, 22222, 23999)]


@check("band data: 5816 patterns per j; 44273/90000 = 1/2 - 5816/720000")
def _():
    assert sum(b - a for _, a, b in BANDS) == 5816
    assert Fr(44273, 90000) == Fr(1, 2) - Fr(5816, 720000) == Fr(180000 - 2908, 360000)


@check("band zones: Y-zones disjoint, Y below all X, at most two X-zones meet; inside (t, theta] (j >= 2)")
def _():
    for j in list(range(2, 200)) + [10**6]:
        t, theta = 180000 * j, 240000 * j + 1
        assert theta == (2 * M * j + 4) // 3
        Y = sorted((l * (a * j + 1), l * b * j + l) for l, a, b in BANDS)
        X = [((l + 1) * (a * j + 1) + 1, (l + 1) * b * j + l) for l, a, b in BANDS]
        for (lo1, hi1), (lo2, hi2) in zip(Y, Y[1:]):
            assert hi1 < lo2
        assert Y[-1][1] < min(lo for lo, _ in X)
        assert Y[0][0] > t and max(hi for _, hi in X) <= theta
        pts = sorted({lo for lo, _ in X} | {hi + 1 for _, hi in X})
        for p in pts:                                  # X-load is piecewise constant
            assert sum(1 for lo, hi in X if lo <= p <= hi) <= 2


@check("band degree <= 2 by exact integer count of patterns through every z (j = 2..6)")
def _():
    for j in range(2, 7):
        size = 240000 * j + 3
        load = [0] * (size + 2)
        for l, a, b in BANDS:
            for w in range(a * j + 1, b * j + 1):
                for z in range(l * w, l * w + l + 1):          # Y_{l,w}
                    load[z] += 1
                for z in range((l + 1) * w + 1, (l + 1) * w + l + 1):  # X_{l,w}
                    load[z] += 1
        # a single pattern meets z at most once (Y and X disjoint), so load = number of patterns at z
        assert max(load) <= 2, (j, max(load))


@check("Theorem 1.1 arithmetic: k <= 177092 j + isqrt(480000 j + 2) <= (44273/90000) n + 2 sqrt n + 177792")
def _():
    for n in list(range(2 * M, 2 * M + 3000)) + [10**7, 10**8 + 7, 3 * 10**9 + 11, 10**12 + 5]:
        j = -(-n // M)
        lhs = 177092 * j + isqrt(480000 * j + 2)
        assert Fr(lhs) <= Fr(44273, 90000) * n + 177792 + 2 * isqrt(n)  # 2 isqrt(n) <= 2 sqrt(n)
    for n in range(0, 2 * M, 997):                      # crossing bound covers n < 2M
        assert (n + 1) // 2 + isqrt(n) <= Fr(44273, 90000) * n + 177792


@check("thresholds quoted in the paper (exact)")
def _():
    def below_half(c, const, n):        # c n + 2 sqrt n + const < n/2, decided exactly
        v = (Fr(1, 2) - c) * n - const
        return v > 0 and v * v > 4 * n
    # Theorem 1.1, real form: below n/2 exactly from n = 23202647 (quadratic in sqrt n, one positive root)
    c4 = Fr(44273, 90000)
    assert below_half(c4, 177792, 23202647) and not below_half(c4, 177792, 23202646)
    # Theorem 1.1, integer form: floor(bound) < ceil(n/2) for every n > 23202420, and not at 23202420
    b4 = lambda n: (354184 * n + 1440000 * isqrt(n) + 128010240000) // 720000
    assert b4(23202420) >= (23202420 + 1) // 2
    assert all(b4(n) < (n + 1) // 2 for n in range(23202421, 23202647))   # above 23202647 the real form is below n/2
    # Remark 4.9 (f_le_real2): real form below n/2 exactly from n = 63849
    c2 = Fr(797, 1620)
    assert below_half(c2, 7, 63849) and not below_half(c2, 7, 63848)
    # f_le_upper2 integer form: below ceil(n/2) for every n > 21800 (scan to 10^6; beyond, the real form is below n/2)
    b2 = lambda n: (797 * n + 1620 * isqrt(2 * ((2 * n + 4) // 3)) + 8000) // 1620
    assert b2(21800) >= 10900 and all(b2(n) < (n + 1) // 2 for n in range(21801, 10**6))
    assert below_half(c2, 7, 10**6)
    # Theorem 1.1 beats f_le_real2 exactly when 43 n / 810000 > 177785, i.e. n >= 3348973256
    gap = Fr(797, 1620) - Fr(44273, 90000)
    assert gap == Fr(43, 810000)
    assert gap * 3348973256 > 177785 and not gap * 3348973255 > 177785
    # Theorem 1.1 proof: constants of the two cases
    assert 354184 * 359999 + 720000 * 700 == 128009885816 <= 128010240000
    assert 5816 * 4320000 + 360000 < 128010240000
    assert Fr(354184, 720000) == Fr(44273, 90000) and Fr(128010240000, 720000) == 177792
    for s_ in range(0, 5000):                                   # isqrt(480000 j + 2) <= 2 isqrt(n) + 700
        assert (2 * s_ + 701) ** 2 * 3 - 4 * (s_ + 1) ** 2 >= 3 * 480001
    # mod-42 at n = 2e7: largest m with 21m^2+105m+46 <= n
    m = max(m for m in range(2000) if 21 * m * m + 105 * m + 46 <= 2 * 10**7)
    assert (m, 12 * m) == (973, 11676)


def main():
    for name, fn in CHECKS:
        fn()
        print(f"PASS  {name}")
    print(f"ALL {len(CHECKS)} CHECKS PASSED")


if __name__ == "__main__":
    main()
