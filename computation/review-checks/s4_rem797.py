"""Remark 4.9 (797/1620 design): direct check of the ranges of w, degree <= 2, supports inside (t, theta], and the closing arithmetic."""
from math import isqrt
bad = []
maxdeg_seen = 0
for n in range(12, 6001):
    t = n // 2
    th = (2 * n + 4) // 3
    a5, b5 = t // 5, (th - 5) // 6
    a9, b9 = (5 * b5 + 5) // 9, (th - 9) // 10
    cnt = {}
    for l, lo, hi in ((5, a5, b5), (9, a9, b9)):
        for w in range(lo + 1, hi + 1):
            sup = list(range(l * w, l * w + l + 1)) + list(range((l + 1) * w + 1, (l + 1) * w + l + 1))
            if not (t < l * w and (l + 1) * w + l <= th):
                bad.append(("range", n, l, w))
            for z in sup:
                cnt[z] = cnt.get(z, 0) + 1
    P = max(0, b5 - a5) + max(0, b9 - a9)
    md = max(cnt.values()) if cnt else 0
    maxdeg_seen = max(maxdeg_seen, md)
    if md > 2: bad.append(("degree", n, md))
    # closing arithmetic: k + holes <= n - t + s  and  holes >= P/2  =>  1620 k <= 1620 (n-t) - 810 P + 1620 s
    if not (1620 * (n - t) - 810 * P <= 797 * n + 8000):
        bad.append(("arith", n, 1620 * (n - t) - 810 * P - 797 * n))
print("n in 12..6000: violations:", bad[:5], "; max degree seen:", maxdeg_seen)
# slack of the additive constant 8000 over all n up to 2e6 (vectorised formula only)
mx = -10**9
for n in range(12, 2_000_000):
    t = n // 2; th = (2 * n + 4) // 3
    a5, b5 = t // 5, (th - 5) // 6
    a9, b9 = (5 * b5 + 5) // 9, (th - 9) // 10
    P = (b5 - a5) + (b9 - a9)
    v = 1620 * (n - t) - 810 * P - 797 * n
    if v > mx: mx = v; arg = n
print("max over 12<=n<2e6 of 1620(n-t) - 810 P - 797 n =", mx, "at n =", arg, "(must be <= 8000)")
