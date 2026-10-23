"""Exact count of bad offsets u in U for each j (Prop 6.4 / Remark 6.5 / Section 8 items 4-5), numba-accelerated.
u is bad iff there are integers 14 <= L <= delta <= 288j-1 with L*delta = 72u + 66 + 3456 j."""
import numpy as np, time, sys
from numba import njit
from math import gcd

@njit(cache=True)
def bad_count(j):
    b = 288 * j
    uL = 288 * j * j + 12 * j + 1
    uH = 288 * j * j + 2012 * j
    nU = uH - uL + 1
    bad = np.zeros(nU, dtype=np.bool_)
    P1 = 72 * uL + 66 + 12 * b
    P2 = 72 * uH + 66 + 12 * b
    L = 14
    while L * L <= P2:
        # delta range
        dlo = (P1 + L - 1) // L
        if dlo < L: dlo = L
        dhi = P2 // L
        if dhi > b - 1: dhi = b - 1
        if dlo <= dhi:
            # solve L*delta = 66 mod 72
            g = 1
            a_, b_ = L, 72
            while b_:
                a_, b_ = b_, a_ % b_
            g = a_
            if 66 % g == 0:
                m72 = 72 // g
                # find delta0 with L*delta0 = 66 (mod 72): brute over m72 residues
                d0 = -1
                for t in range(m72):
                    if (L * t) % 72 == 66 % 72:
                        d0 = t
                        break
                if d0 >= 0:
                    # first delta >= dlo with delta = d0 mod m72
                    start = dlo + ((d0 - dlo) % m72)
                    d = start
                    while d <= dhi:
                        M = L * d
                        # M = 72u + 66 + 12 b  ->  u = (M - 66 - 12 b)/72
                        num = M - 66 - 12 * b
                        if num % 72 == 0:
                            u = num // 72
                            if u >= uL and u <= uH:
                                bad[u - uL] = True
                        d += m72
        L += 1
    return nU, bad.sum(), bad

if __name__ == "__main__":
    jmax = int(sys.argv[1]) if len(sys.argv) > 1 else 499
    t0 = time.time()
    worst = (1.0, None)
    nogood = []
    for j in range(1, jmax + 1):
        nU, nb, _ = bad_count(j)
        prop_good = 1 - nb / nU
        if nb == nU: nogood.append(j)
        if prop_good < worst[0]: worst = (prop_good, j)
    print(f"j = 1..{jmax}: every j has a good u: {not nogood} (j without: {nogood}); smallest proportion of good u = {worst[0]:.4f} at j = {worst[1]}  [{time.time()-t0:.1f}s]")
    for j in (500, 230, 229, 1000):
        nU, nb, _ = bad_count(j)
        bound = 1944.4 * j + 12768
        print(f"j={j}: |U|={nU}, bad={nb}, paper bound 1944.4j+12768 = {bound:.1f}, ratio bound/bad = {bound/nb:.2f}")
