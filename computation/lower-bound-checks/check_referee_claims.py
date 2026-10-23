"""Independent re-check of two numerical statements added to the manuscript during revision.

R1  Pure modulus-42 pattern, offsets B = 42 t: the largest colliding t below the proof's t(m) = m(m+1)/2 + 1, as a fraction of
    the proof's offset 21(m^2+m+2), for m = 20, 60, 100.
R2  Pickhardt's construction: offset B plus the first k nonnegative integers outside the class -B (mod 3); with B the least
    integer > 3k^2/16 + k/8 + 1, the sequence is valid, for k = 40, 100, 200, 400.
Run without -I (numba via check_lower)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from check_lower import distinct, R6

for m in (20, 60, 100):
    k, t_lean = 12 * m, m * (m + 1) // 2 + 1
    base = lambda t: np.array([42 * t + 42 * (i // 6) + R6[i % 6] for i in range(k)], dtype=np.int64)
    last_bad = None
    for t in range(t_lean, -1, -1):
        if not distinct(base(t)):
            last_bad = t
            break
    print(f"R1 m={m}: proof offset 42*{t_lean} = {42 * t_lean}; largest colliding t = {last_bad} "
          f"({last_bad / t_lean:.3f} of the proof's offset)")

for k in (40, 100, 200, 400):
    B = (3 * k * k) // 16 + k // 8 + 1
    while not B * 16 > 3 * k * k + 2 * k + 16:  # least integer B > 3k^2/16 + k/8 + 1
        B += 1
    seq, y = [], 0
    while len(seq) < k:
        if (B + y) % 3 != 0:  # y avoids the class -B mod 3, i.e. B + y is not divisible by 3
            seq.append(B + y)
        y += 1
    a = np.array(seq, dtype=np.int64)
    print(f"R2 k={k}: B={B}, valid={distinct(a)}, max={int(a[-1])}, k/sqrt(max)={k / np.sqrt(a[-1]):.4f}")
