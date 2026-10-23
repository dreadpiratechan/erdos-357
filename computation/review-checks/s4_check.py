"""Independent recomputation of the numbers in Section 4 (upper bound) of the manuscript (manuscript/main.tex).
Written from the text of the manuscript only; does NOT import or read any other script of this repository.
All arithmetic with Python ints / Fractions.
"""
from fractions import Fraction as Fr
from math import isqrt, ceil, floor
import itertools, sys

ok = True
def check(name, cond, extra=""):
    global ok
    print(("PASS " if cond else "FAIL ") + name + (("  " + extra) if extra else ""))
    ok = ok and cond

# ---------------------------------------------------------------- bands, zones
bands = [(4, 45000, 45687), (5, 36550, 37499), (6, 31250, 31729), (5, 38075, 39999), (9, 22222, 23999)]
check("band sizes 687,949,479,1924,1777 sum to 5816",
      [b - a for _, a, b in bands] == [687, 949, 479, 1924, 1777] and sum(b - a for _, a, b in bands) == 5816)
check("44273/90000 = 1/2 - 2908/360000 = 1/2 - 5816/720000",
      Fr(44273, 90000) == Fr(1, 2) - Fr(2908, 360000) == Fr(1, 2) - Fr(5816, 720000))
check("354184/720000 = 44273/90000 and 128010240000/720000 = 177792",
      Fr(354184, 720000) == Fr(44273, 90000) and 128010240000 == 720000 * 177792)

def zones(j):
    out = []
    for l, a, b in bands:
        Y = (l * (a * j + 1), l * b * j + l)
        X = ((l + 1) * (a * j + 1) + 1, (l + 1) * b * j + l)
        out.append((l, a, b, Y, X))
    return out

# manuscript's table, symbolic in j: (coef, const) for each end
table = {
    (4, 45000): ((180000, 4), (182748, 4), (225000, 6), (228435, 4)),
    (5, 36550): ((182750, 5), (187495, 5), (219300, 7), (224994, 5)),
    (6, 31250): ((187500, 6), (190374, 6), (218750, 8), (222103, 6)),
    (5, 38075): ((190375, 5), (199995, 5), (228450, 7), (239994, 5)),
    (9, 22222): ((199998, 9), (215991, 9), (222220, 11), (239990, 9)),
}
tab_ok = True
for j in (1, 2, 3, 7, 12, 1000, 10**6):
    for l, a, b, Y, X in zones(j):
        c = table[(l, a)]
        exp = (c[0][0] * j + c[0][1], c[1][0] * j + c[1][1], c[2][0] * j + c[2][1], c[3][0] * j + c[3][1])
        if exp != (Y[0], Y[1], X[0], X[1]):
            tab_ok = False
            print("table mismatch", j, l, a, exp, (Y, X))
check("zone table in the manuscript agrees with the definition (j in 1,2,3,7,12,1000,1e6)", tab_ok)

def prop48_zone_checks(j):
    t, th = 180000 * j, 240000 * j + 1
    z = zones(j)
    # (1) every zone in (t, th]
    c1 = all(t < Y[0] and Y[1] <= th and t < X[0] and X[1] <= th for _, _, _, Y, X in z)
    # pattern-level hypotheses at extreme w
    c1b = all(t < l * (a * j + 1) and (l + 1) * (b * j) + l <= th for l, a, b, _, _ in z)
    # (2) Y-zones pairwise disjoint, all below every X zone
    Ys = sorted(Y for _, _, _, Y, _ in z)
    c2a = all(Ys[i][1] < Ys[i + 1][0] for i in range(len(Ys) - 1))
    c2b = max(Y[1] for Y in Ys) < min(X[0] for _, _, _, _, X in z)
    # (3) X zones: max clique of the interval-overlap graph is <= 2
    Xs = [X for _, _, _, _, X in z]
    pts = sorted(set([x[0] for x in Xs] + [x[1] for x in Xs]))
    maxdeg = max(sum(1 for x in Xs if x[0] <= p <= x[1]) for p in pts)
    return c1, c1b, c2a, c2b, maxdeg

res = {j: prop48_zone_checks(j) for j in list(range(1, 60)) + [100, 1000, 10**6, 10**9]}
check("zones inside (t,theta] for all j>=1 tested", all(r[0] and r[1] for r in res.values()))
check("Y-zones disjoint and below X-zones for all j>=2 tested", all(r[2] and r[3] for j, r in res.items() if j >= 2))
print("     (for j=1 Y-zone disjointness holds? ->", res[1][2], "; the manuscript only claims j>=2)")
check("max X-zone overlap <= 2 for all j tested (incl. j=1)", all(r[4] <= 2 for r in res.values()))
# the overlap graph exactly as stated in the manuscript
j = 2
labels = {(6, 31250): "6", (5, 36550): "5", (9, 22222): "9", (4, 45000): "4", (5, 38075): "5'"}
zz = {labels[(l, a)]: X for l, a, b, Y, X in zones(j)}
edges = sorted(tuple(sorted((p, q))) for p, q in itertools.combinations(zz, 2)
               if not (zz[p][1] < zz[q][0] or zz[q][1] < zz[p][0]))
print("     X-zone overlap edges at j=2:", edges)
check("overlap edges are exactly {6,5},{5,9},{9,4},{9,5'}",
      set(edges) == {tuple(sorted(e)) for e in [("6", "5"), ("5", "9"), ("9", "4"), ("9", "5'")]})
# order by left end
order = [labels[(l, a)] for l, a, b, Y, X in sorted(zones(2), key=lambda r: r[4][0])]
check("X zones ordered by left end: 6,5,9,4,5'", order == ["6", "5", "9", "4", "5'"], str(order))
check("the three separating inequalities of the manuscript",
      all(222103 * j + 6 < 222220 * j + 11 and 224994 * j + 5 < 225000 * j + 6 and 228435 * j + 4 < 228450 * j + 7
          for j in range(1, 100)))

# ---- direct incidence count: for each integer z, number of patterns whose support contains z
def degree_count(j):
    cnt = {}
    for l, a, b in bands:
        for w in range(a * j + 1, b * j + 1):
            sup = list(range(l * w, l * w + l + 1)) + list(range((l + 1) * w + 1, (l + 1) * w + l + 1))
            assert len(set(sup)) == len(sup) == 2 * l + 1, (l, w)       # Y and X do not overlap
            for z in sup:
                cnt[z] = cnt.get(z, 0) + 1
    return cnt, sum(b * j - a * j for _, a, b in bands)
for j in (2, 3, 4, 5, 6, 12, 13, 17, 30):
    cnt, npat = degree_count(j)
    t, th = 180000 * j, 240000 * j + 1
    in_range = all(t < z <= th for z in cnt)
    check(f"direct incidence count j={j}: #patterns={npat}=5816j, max degree={max(cnt.values())}<=2, supports inside (t,theta]",
          npat == 5816 * j and max(cnt.values()) <= 2 and in_range)
    # equal sums of the two runs of every pattern (sample)
for l, w in [(4, 45001), (5, 36551), (6, 31251), (9, 22223), (5, 38076), (9, 23999)]:
    check(f"sum identity for pattern ({l},{w})", sum(range(l * w, l * w + l + 1)) == sum(range((l + 1) * w + 1, (l + 1) * w + l + 1)))

# ---------------------------------------------------------------- Theorem 1.1 assembly
# Case n >= 4320000
bad = []
for n in list(range(4320000, 4320000 + 3000)) + [10**7, 3 * 10**7 + 5, 360000 * 13, 360000 * 13 + 1, 360000 * 100, 10**12 + 7]:
    r = isqrt(n)
    j = -(-n // 360000)
    npr = 360000 * j
    assert j >= 12 and n <= npr <= n + 359999
    t, th = 180000 * j, 240000 * j + 1
    assert 2 * t == npr and t <= th <= npr and 3 * th == 2 * npr + 3
    kmax = (npr - t) - 2908 * j + isqrt(2 * th)
    if isqrt(480000 * j + 2) > 2 * r + 700:
        bad.append(("isqrt step", n))
    if 720000 * kmax > 354184 * n + 1440000 * r + 128010240000:
        bad.append(("final", n))
check("Theorem 1.1, case n>=4320000, spot check of every inequality for 3000 consecutive n + extras", not bad, str(bad[:3]))
# the algebra of the step (2r+701)^2 - 4/3 (r+1)^2 >= 491401 - 4/3
check("(2r+701)^2 - 4/3 (r+1)^2 >= 491401 - 4/3 and 480001 <= that", all(Fr((2*r+701)**2) - Fr(4,3)*(r+1)**2 >= 491401 - Fr(4,3) >= 480001 for r in range(0, 5000)))
# worst case n of the step 480000 j + 2 < (2r+701)^2 over a window of n near squares
mxratio = 0
for r in list(range(2078, 3000)):          # 2078^2 = 4318084
    n = r * r  # smallest n with isqrt = r
    if n < 4320000: continue
    j = -(-n // 360000)
    assert 480000 * j + 2 < (2 * r + 701) ** 2
check("480000j+2 < (2r+701)^2 at n=r^2 for r in 2078..3000", True)
check("354184*359999 + 504000000 = 128009885816 <= 128010240000",
      354184 * 359999 + 504000000 == 128009885816 <= 128010240000)
# Case n < 4320000
check("Case n<4320000: 5816*4320000+360000 < 128010240000", 5816 * 4320000 + 360000 < 128010240000, str(5816 * 4320000 + 360000))
# also verify the inequality in the n<4320000 case over a coarse sample, with Cor 4.2 as the only input
check("n<4320000: 360000(n+1) + 720000 r <= RHS for sampled n",
      all(720000 * (((n + 1) // 2) + isqrt(n)) <= 354184 * n + 1440000 * isqrt(n) + 128010240000 for n in range(0, 4320000, 997)))
check("n=0 : f(0)=0 trivial", 0 <= 128010240000)

# ---------------------------------------------------------------- thresholds quoted in the introduction
def first_n_below_half(A, B, C, lo, hi):
    """smallest n such that A*n + B*sqrt(n) + C < n/2  (A Fraction).  Exact check using integers."""
    # condition: (1/2 - A) n - B sqrt n - C > 0  <=> with D=(1/2-A):  D n - C > B sqrt n  <=> (D n - C > 0) and (D n - C)^2 > B^2 n
    D = Fr(1, 2) - A
    def ok_(n):
        v = D * n - C
        return v > 0 and v * v > B * B * n
    # find the threshold by binary search on the monotone region and verify neighbours + that nothing below fails to be false
    a, b = lo, hi
    assert ok_(b)
    while a < b:
        m = (a + b) // 2
        if ok_(m): b = m
        else: a = m + 1
    return a, ok_
t1, ok1 = first_n_below_half(Fr(44273, 90000), 2, 177792, 10**5, 10**9)
check("Thm 1.1 real form < n/2 first at n = 23202647", t1 == 23202647, str(t1))
check("  ... and fails at n-1; holds on a long window above", (not ok1(t1 - 1)) and all(ok1(n) for n in range(t1, t1 + 20000)))
# monotone failure region: test all n below threshold on coarse grid
check("  ... fails for all n < threshold (grid)", not any(ok1(n) for n in range(0, t1, 1013)))
t2, ok2 = first_n_below_half(Fr(797, 1620), 2, 7, 10**3, 10**8)
check("797/1620 form < n/2 first at n = 63849", t2 == 63849, str(t2))
check("  ... fails at n-1 and for grid below", (not ok2(t2 - 1)) and not any(ok2(n) for n in range(0, t2, 7)))
check("797/1620 - 44273/90000 = 43/810000", Fr(797, 1620) - Fr(44273, 90000) == Fr(43, 810000))
nth = (177792 - 7) * 810000 // 43 + 1
check("crossover: Thm1.1 bound smaller than 797 bound exactly for n >= 3348973256",
      nth == 3348973256 and Fr(43, 810000) * nth > 177785 and Fr(43, 810000) * (nth - 1) <= 177785, str(nth))
check("0.4919 2-bar: 44273/90000 = 0.491922...", abs(44273 / 90000 - 0.4919222222) < 1e-9)
check("1/2 - 44273/90000 = 727/90000 = 0.0080778", Fr(1, 2) - Fr(44273, 90000) == Fr(727, 90000))

# ---------------------------------------------------------------- Lemma 4.3 and Remark 4.4
for n in range(0, 300):
    th_max = (2 * n + 4) // 3
    assert 3 * th_max <= 2 * n + 4 < 3 * (th_max + 1)
bad_m = []
for m in range(2, 200):
    n = 3 * m
    seq = [m - 1, m, m + 2]
    sums = [sum(seq[i:j]) for i in range(3) for j in range(i + 1, 4)]
    valid = len(set(sums)) == len(sums) and max(seq) <= n
    if not valid:
        bad_m.append(m)
        continue
    assert (2 * n + 6) // 3 == 2 * m + 2 == seq[1] + seq[2] and sum(seq) == 3 * m + 1 > n
    assert (2 * n + 4) // 3 == 2 * m + 1
print("     Remark 4.4 example (m-1,m,m+2) is NOT valid for m in", bad_m, "(m=3: 2+3=5 collides)")
check("Remark 4.4: example valid and sharp for every 2<=m<200 except m=3", bad_m == [3])

print("\nALL PASS" if ok else "\nSOME FAILED")
sys.exit(0 if ok else 1)
