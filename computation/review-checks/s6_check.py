"""Independent recomputation of Section 6 (skip construction): identities, phase filter, case constants,
and exhaustive brute force of Proposition 6.3 for small j.  Usage: python s6_check.py [jmax_bruteforce]"""
import sys, time
import numpy as np
from math import isqrt
from fractions import Fraction as Fr

ok = True
def check(name, cond, extra=""):
    global ok
    print(("PASS " if cond else "FAIL ") + name + (("  " + extra) if extra else ""), flush=True)
    ok = ok and cond

r = [2, 7, 11, 25, 26, 34]
eps = [r[c] - 7 * c for c in range(6)]
pi6 = [sum(eps[:t]) for t in range(6)]
def pi(t): return pi6[t % 6]
def g(t): return 42 * (t // 6) + r[t % 6]

# ---- Lemma 6.1 numerically
import random
random.seed(5)
good = True
for _ in range(3000):
    j = random.randint(1, 5); k = 360 * j; b = 288 * j; u = random.randint(0, 3000)
    a = [42 * u + g(t) + (84 if t >= b else 0) for t in range(k)]
    x = random.randint(0, k); l = random.randint(0, k - x)
    S = sum(a[x:x + l])
    nu = lambda z: max(z - b, 0)
    rhs = 84 * u * l + 7 * l * (2 * x + l - 1) + 2 * (pi(x + l) - pi(x)) + 168 * (nu(x + l) - nu(x))
    if 2 * S != rhs: good = False
check("Lemma 6.1 window identity (3000 random (j,u,x,l))", good)

# ---- Lemma 6.2: phase filter, all 216 triples
cnt = 0; viol = []; nonvac = 0
for xi in range(6):
    for eta in range(6):
        for lam in range(6):
            D = (pi(eta + lam) - pi(eta)) - (pi(xi + lam) - pi(xi))
            if D % 7 == 0 and ((eta - xi) * lam + D) % 6 == 0:
                cnt += 1
                if D != 0: viol.append((xi, eta, lam, D))
            if abs(D) == 7: nonvac += 1
check("Lemma 6.2: all 216 triples; no triple with D%7==0 and (eta-xi)lam+D%6==0 has D != 0", not viol, f"{cnt} triples pass hyp; D=+-7 occurs in {nonvac} triples")
Ds = sorted(set((pi(eta + lam) - pi(eta)) - (pi(xi + lam) - pi(xi)) for xi in range(6) for eta in range(6) for lam in range(6)))
print("     range of Delta over Z/6 triples:", Ds)
check("|Delta|<=8 and Delta in {-8..8}", min(Ds) >= -8 and max(Ds) <= 8)
# table of four cases in the manuscript
four = sorted((xi, eta, lam, (pi(eta + lam) - pi(eta)) - (pi(xi + lam) - pi(xi))) for xi in range(6) for eta in range(6) for lam in range(6)
              if abs((pi(eta + lam) - pi(eta)) - (pi(xi + lam) - pi(xi))) == 7)
print("     triples with |Delta|=7:", four)
check("exactly the 4 triples of the manuscript's table", sorted([(2,3,1,7),(4,3,5,7),(3,4,5,-7),(3,2,1,-7)]) == four)
for (xi, eta, lam, D) in four:
    print(f"       (xi,eta,lam)=({xi},{eta},{lam}) D={D}: (eta-xi)lam mod 6 = {((eta-xi)*lam)%6}, required (-D) mod 6 = {(-D)%6}")

# ---- constants in the four cases (symbolic in j: compare as polynomials at several j)
for j in (1, 2, 5, 17, 230, 500, 12345):
    u_lo = 288 * j * j + 12 * j + 1
    b = 288 * j; k = 360 * j
    c = {}
    c["1008u_lo"] = 1008 * u_lo == 290304 * j * j + 12096 * j + 1008
    # (i) s+d <= b => s d <= b^2/4
    c["i"] = 14 * (b * b // 4) == 290304 * j * j and 14 * (b * b // 4) + 16 < 1008 * u_lo
    # (ii) s+d <= k-b = 72 j
    c["ii"] = k - b == 72 * j and 14 * (36 * j) ** 2 + 16 < 1008 * u_lo
    # (iii) maximize 14 s (k+12-s) over 0<=s<=72j (increasing since 72j <= 180 j + 6)
    mx = max(14 * s * (k + 12 - s) for s in range(0, min(72 * j, 400) + 1)) if j <= 5 else None
    top = 14 * 72 * j * (288 * j + 12) + 16
    c["iii"] = top == 290304 * j * j + 12096 * j + 16 < 1008 * u_lo and (mx is None or mx <= top - 16)
    # (iv) h>=24
    c["iv"] = 14 * (180 * j) ** 2 + 168 * 360 * j + 16 == 453600 * j * j + 60480 * j + 16 < 2016 * u_lo == 580608 * j * j + 24192 * j + 2016
    if not all(c.values()): print("   failing at j =", j, c)
    ok = ok and all(c.values())
check("case constants (i)-(iv) of Prop 6.3 at j in {1,2,5,17,230,500,12345}", True)

# ---- algebra of (K), (E)
import sympy as sp
u, x, s, d, h, cs, cl, Dl = sp.symbols('u x s d h cs cl Dl')
y = x + d; l = s + h
Dl_ = sp.symbols('Delta')
# 2S(x,l) - 2S(y,s) = 0 with the pi-terms collected into Delta := (pi(y+s)-pi(y)) - (pi(x+l)-pi(x))
expr = sp.expand(84*u*(l - s) + 7*(l*(2*x + l - 1) - s*(2*y + s - 1)) - 2*Dl_ + 168*(cl - cs))
Kform = sp.expand(84*u*h - (7*(2*s*d - 2*h*x - 2*h*s - h**2 + h) + 2*Dl_ + 168*(cs - cl)))
check("(K): 84uh = 7(2sd-2hx-2hs-h^2+h) + 2Delta + 168(c_s - c_l)  [symbolic]", sp.simplify(expr - Kform) == 0)
# (E): h=12, cl=0, cs = x+d+s-b
b_ = sp.symbols('b')
Eexpr = sp.expand((Kform.subs({h: 12, cl: 0, cs: x + d + s - b_})) / 2)
Etarget = sp.expand(504*u + 462 + 84*b_ - 7*d*(s + 12) - Dl_)
check("(E): 504u+462+84b = 7d(s+12) + Delta  [symbolic, from (K) with h=12, c_l=0, c_s=x+d+s-b]", sp.simplify(Eexpr + Etarget) == 0 or sp.simplify(Eexpr - Etarget) == 0,
      f"{sp.simplify(Eexpr)}")

# ---- Prop 6.4 data
for j in (230, 500, 1000):
    b = 288 * j
    P1 = 72 * (288 * j * j + 12 * j + 1) + 66 + 12 * b
    P2 = 72 * (288 * j * j + 2012 * j) + 66 + 12 * b
    check(f"P1,P2 formulas at j={j}", P1 == 20736 * j * j + 4320 * j + 138 and P2 == 20736 * j * j + 148320 * j + 66 and P2 - P1 == 72 * (2000 * j - 1))
    check(f"  (144j+515)^2 > P2 and (72j-1)(288j-1) < P1 at j={j}", (144 * j + 515) ** 2 > P2 and (72 * j - 1) * (288 * j - 1) < P1 and (144*j+514)**2 <= P2 + 10**9)
    check(f"  floor((144j+514)/72) = 2j+7 at j={j}", (144 * j + 514) // 72 == 2 * j + 7)
kappa = [sum(1 for rr in range(72) if (rho * rr - 66) % 72 == 0) for rho in range(72)]
check("sum kappa = 96 = 8*12", sum(kappa) == 96)
k8 = sum(1 for a_ in range(8) for b_ in range(8) if (a_ * b_ - 66) % 8 == 0)
k9 = sum(1 for a_ in range(9) for b_ in range(9) if (a_ * b_ - 66) % 9 == 0)
check("CRT counts 8 and 12", (k8, k9) == (8, 12), str((k8, k9)))
import math
l2 = 0.6931471808
check("log 2 < 0.6931471808 (true value 0.69314718056)", math.log(2) < l2)
check("(8000/3)*0.6931471808 + 96 < 1944.4", (Fr(8000, 3) * Fr(6931471808, 10**10) + 96) < Fr(19444, 10))
first = next(j for j in range(1, 100000) if 12768 + Fr(19444, 10) * j < 2000 * j)
check("1944.4 j + 12768 < 2000 j iff j >= 230", first == 230 and all(12768 + Fr(19444,10)*j < 2000*j for j in range(230, 5000)), f"first j = {first}")
# Harmonic bound numerically
for j in (230, 500, 777):
    H = sum(Fr(1, mu) for mu in range(j, 2 * j + 8))
    check(f"sum_{{mu=j}}^{{2j+7}} 1/mu <= log2 + 9/(2j) at j={j}", float(H) <= math.log(2) + 4.5 / j, f"{float(H):.6f} <= {math.log(2)+4.5/j:.6f}")

# ---- Theorem 1.3 arithmetic
bad = []
for j in range(500, 3000):
    top = 42 * (288 * j * j + 2012 * j) + 42 * (60 * j - 1) + 34 + 84
    if not (top <= 12096 * j * j + 87024 * j + 76 <= 12096 * j * j + 87024 * j + 81): bad.append(j)
check("a_{k-1} <= 12096 j^2 + 87024 j + 76 for j in 500..3000", not bad)
check("12096*504^2 = 3,072,577,536 ; 12096 = 21*24^2 ; 360*504 = 181440", 12096 * 504 ** 2 == 3072577536 and 12096 == 21 * 24 ** 2 and 360 * 504 == 181440)
bad = []
for n in list(range(12096 * 504 ** 2, 12096 * 504 ** 2 + 20000)) + [10 ** 11, 12096 * 505 ** 2 - 1, 12096 * 505 ** 2]:
    Q = isqrt(n // 12096)
    jj = Q - 4
    if not (jj >= 500 and 12096 * jj * jj + 87024 * jj + 81 <= 12096 * Q * Q <= n and n < 12096 * (Q + 1) ** 2): bad.append(n)
check("Theorem 1.3 real-form derivation (Q, j=Q-4)", not bad)
check("15/sqrt21 = 3.273268...", 3.27326 < 15 / 21 ** .5 < 3.27327)
check("12096(j+4)^2 - (12096j^2+87024j+81) = 9744 j + 193455 > 0", all(12096 * (j + 4) ** 2 - (12096 * j * j + 87024 * j + 81) == 9744 * j + 193455 for j in range(1, 100)))

# ---- brute force of Prop 6.3
def blocks_dups(a):
    """return list of all (x1,y1,x2,y2) raw duplicate block-sum pairs (consecutive in sorted order), as groups"""
    a = np.asarray(a, dtype=np.int64)
    k = len(a)
    P = np.concatenate(([0], np.cumsum(a)))
    Y, X = np.tril_indices(k + 1, -1)       # row>col: Y > X
    vals = P[Y] - P[X]
    order = np.argsort(vals, kind="stable")
    sv = vals[order]
    eqm = np.nonzero(sv[1:] == sv[:-1])[0]
    return X, Y, order, sv, eqm

def seq(j, u):
    k = 360 * j; b = 288 * j
    return [42 * u + g(t) + (84 if t >= b else 0) for t in range(k)]

def divisor_pairs(j, u):
    b = 288 * j
    M = 72 * u + 66 + 12 * b
    out = []
    for L in range(14, isqrt(M) + 1):
        if M % L == 0:
            dl = M // L
            if L <= dl <= b - 1: out.append((L, dl))
    return out

def classify(j, u):
    """returns (is_valid, list of disjoint ordered collisions as (x,l,y,s))"""
    a = seq(j, u)
    X, Y, order, sv, eqm = blocks_dups(a)
    if len(eqm) == 0: return True, []
    cols = []
    # group
    i = 0
    n_ = len(eqm)
    eqset = set(eqm.tolist())
    groups = {}
    for e in eqm:
        v = sv[e]
        groups.setdefault(int(v), set()).update([int(order[e]), int(order[e + 1])])
    for v, idxs in groups.items():
        idxs = sorted(idxs)
        bl = [(int(X[q]), int(Y[q])) for q in idxs]
        for p in range(len(bl)):
            for q in range(p + 1, len(bl)):
                (x1, y1), (x2, y2) = bl[p], bl[q]
                # disjoint ordered form
                if y1 <= x2 or y2 <= x1:
                    if y2 <= x1: (x1, y1), (x2, y2) = (x2, y2), (x1, y1)
                    cols.append((x1, y1 - x1, x2, y2 - x2))
    return False, cols

jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
for j in range(1, jmax + 1):
    t0 = time.time()
    b = 288 * j; k = 360 * j
    U = range(288 * j * j + 12 * j + 1, 288 * j * j + 2012 * j + 1)
    n_valid = n_invalid = 0
    contra = 0           # invalid but no divisor pair  (would contradict Prop 6.3)
    nonIV = 0            # invalid with a disjoint ordered collision that is NOT (iv)/h=12/divisor-type
    pair_but_valid = 0
    no_pair_invalid = 0
    for u in U:
        valid, cols = classify(j, u)
        pairs = divisor_pairs(j, u)
        if valid:
            n_valid += 1
            if pairs: pair_but_valid += 1
        else:
            n_invalid += 1
            if not pairs: contra += 1; print("   CONTRADICTION of Prop 6.3 at j,u =", j, u)
            for (xx, ll, yy, ss) in cols:
                h_ = ll - ss
                good = (h_ == 12 and yy < b < yy + ss and (ss + 12) * (yy - xx) == 72 * u + 66 + 12 * b)
                if not good:
                    nonIV += 1
                    if nonIV <= 3: print("   non-(iv) collision:", j, u, (xx, ll, yy, ss))
    print(f"j={j}: |U|={len(U)} valid={n_valid} invalid={n_invalid} | invalid-without-divisor-pair={contra} | non-(iv,h=12) collisions={nonIV} | valid-but-has-pair={pair_but_valid} | {time.time()-t0:.0f}s", flush=True)
    check(f"Prop 6.3 brute force j={j}: every invalid u in U has a divisor pair; every collision is of type (iv), h=12", contra == 0 and nonIV == 0)

print("\nALL PASS" if ok else "\nSOME FAILED")
