"""Independent recomputation of Section 5 (modulus-42 pattern) and of Remark 5.2 numerics."""
import sys
import numpy as np
from math import isqrt, sqrt
from fractions import Fraction as Fr

ok = True
def check(name, cond, extra=""):
    global ok
    print(("PASS " if cond else "FAIL ") + name + (("  " + extra) if extra else ""))
    ok = ok and cond

r = [2, 7, 11, 25, 26, 34]
def g(t): return 42 * (t // 6) + r[t % 6]
check("g starts 2,7,11,25,26,34,44,49,53,67,68,76,86", [g(t) for t in range(13)] == [2,7,11,25,26,34,44,49,53,67,68,76,86])
check("increments 5,4,14,1,8,10 periodic", [g(t + 1) - g(t) for t in range(12)] == [5,4,14,1,8,10]*2)
eps = [r[c] - 7 * c for c in range(6)]
check("eps = (2,0,-3,4,-2,-1), sum 0", eps == [2,0,-3,4,-2,-1] and sum(eps) == 0)
pi = [sum(eps[:t]) for t in range(7)]
check("pi(0..5) = (0,2,2,-1,3,1), pi(6)=0, range [-1,3]", pi[:6] == [0,2,2,-1,3,1] and pi[6] == 0 and min(pi) == -1 and max(pi) == 3)
check("g_t = 7t + eps_t", all(g(t) == 7 * t + eps[t % 6] for t in range(200)))
check("-3 <= eps <= 4", min(eps) == -3 and max(eps) == 4)

# Lemma 5.1: spectra
G = [0]
for i in range(24): G.append((G[-1] + r[i % 6]) % 42)
check("G(0..11)", G[:12] == [0,2,9,20,3,29,21,23,30,41,24,8], str(G[:12]))
check("G is 12-periodic", all(G[t + 12] == G[t] for t in range(12)))
D = {lam: sorted(set((G[x + lam] - G[x]) % 42 for x in range(12))) for lam in range(12)}
paper = {0:[0],1:[2,7,11,25,26,34],2:[9,18,36],3:[1,20],4:[3,12,27],5:[10,14,19,29,37,38],
         6:[21],7:[4,5,13,23,28,32],8:[15,30,39],9:[22,41],10:[6,24,33],11:[8,16,17,31,35,40]}
check("spectra tables D_0..D_11 equal the manuscript's", D == paper)
allv = [v for lam in D for v in D[lam]]
check("pairwise disjoint, sizes sum to 42, partition Z/42", len(allv) == len(set(allv)) == 42 and sum(len(D[l]) for l in D) == 42)

# direct test of the lemma: any residues w_t = g_t mod 42 (take g_t + 42*random) ; blocks with equal sums have lengths = mod 12
rng = np.random.default_rng(1)
cnt = 0
bad = 0
for trial in range(300):
    w = [g(t) + 42 * int(rng.integers(-1000, 1000)) for t in range(60)]
    # random pairs of blocks with equal sums mod 42 are not what the lemma says; check contrapositive: equal sums => equal length mod 12
    P = [0]
    for v in w: P.append(P[-1] + v)
    d = {}
    for x in range(61):
        for y in range(x + 1, 61):
            d.setdefault(P[y] - P[x], []).append((x, y))
    # inject deliberate coincidences by searching for equal sums among many random sequences (rare) -- instead check residue map
    for x in range(61):
        for y in range(x + 1, 61):
            res = (P[y] - P[x]) % 42
            lam = (y - x) % 12
            cnt += 1
            if res not in paper[lam]: bad += 1
check("residue of every block sum lies in D_{len mod 12} (random shifts by multiples of 42)", bad == 0, f"{cnt} blocks")

# Theorem 1.2 brute force
def valid_by_sort(a):
    a = np.asarray(a, dtype=np.int64)
    P = np.concatenate(([0], np.cumsum(a)))
    k = len(a)
    iu = np.triu_indices(k + 1, 1)
    s = (P[:, None] - P[None, :])  # P[y]-P[x]
    vals = s[np.tril_indices(k + 1, -1)]   # y>x -> positive
    vals = np.sort(vals)
    return not np.any(vals[1:] == vals[:-1])

mod42_ok = True
for m in range(1, 61):
    k = 12 * m
    B = 21 * (m * m + m + 2)
    assert B % 42 == 0
    a = [B + g(t) for t in range(k)]
    if a[-1] != 21 * m * m + 105 * m + 34 or a[0] != B + 2: mod42_ok = False
    if not valid_by_sort(a): mod42_ok = False; print("INVALID at m =", m)
check("Theorem 1.2 sequence valid for m = 1..60, last term 21m^2+105m+34", mod42_ok)

# size argument
check("12B > 7(12m+1)^2/4 for B=21(m^2+m+2) (exact, m=0..10^4)",
      all(Fr(12 * 21 * (m*m + m + 2)) > Fr(7 * (12*m + 1)**2, 4) for m in range(0, 10001)))
check("12B - 7(12m+1)^2/4 = 210 m + 504 - 7/4", all(Fr(12*21*(m*m+m+2)) - Fr(7*(12*m+1)**2, 4) == 210*m + 504 - Fr(7,4) for m in range(100)))

# n-form of Theorem 1.2
bad = []
for n in list(range(0, 20000)) + [10**6, 10**7, 21 * 10**8 + 5]:
    Q = isqrt(n // 21)
    assert n < 21 * (Q + 1) ** 2
    if Q >= 3:
        m = Q - 3
        if not (21*m*m + 105*m + 46 <= n): bad.append(("m", n))
        fl = 12 * m
        # f(n) >= 12m > 12/sqrt21 sqrt n - 48  <=> 12(Q+1) > 12/sqrt21 sqrt n ; test exactly: (Q+1)^2*21 > n
        if not (21 * (Q + 1) ** 2 > n): bad.append(("Q", n))
    else:
        if not (12 * (Q + 1) - 48 < 0): bad.append(("neg", n))
check("Theorem 1.2 real-form derivation (Q=isqrt(floor(n/21)), m=Q-3)", not bad, str(bad[:3]))
check("12/sqrt21 = 2.618614...", 2.6186 < 12 / sqrt(21) < 2.6187, f"{12/sqrt(21):.7f}")
check("f(21m^2+105m+46) with m=0 : 46 = 21*0+0+46 ; and m=1 -> 172", 21 + 105 + 46 == 172)

# Remark 5.2 numerics: the largest offset B=42t that still yields a coincidence
def invalid_for_B(m, B):
    k = 12 * m
    a = [B + g(t) for t in range(k)]
    return not valid_by_sort(a)
print("\nRemark 5.2: largest invalid offset B = 42 t (scan downward from 21(m^2+m+2))")
for m in (20, 60, 100):
    Bp = 21 * (m * m + m + 2)
    t = Bp // 42
    found = None
    while t >= 0:
        if invalid_for_B(m, 42 * t):
            found = t; break
        t -= 1
    print(f"   m={m}: B_paper={Bp}, largest invalid 42t = {42*found}, ratio = {42*found/Bp:.4f}")
print("\nALL PASS" if ok else "\nSOME FAILED")
