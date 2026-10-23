"""Small facts quoted in the manuscript: smallest valid offset u for j = 2, 3 (any u >= 0), and the
reverse-greedy length at n = 1000, 2000, 3000. Independent code (imports check_lower/check_upper)."""
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_lower import skip_seq, distinct
from check_upper import reverse_greedy, admissible
for j in (2, 3):
    b, k, left = 288 * j, 360 * j, 288 * j * j + 12 * j + 1
    first = next(u for u in range(0, left + 1) if distinct(skip_seq(u, b, k)))
    print(f"j={j}: smallest u with a valid sequence = {first}, left end of U = {left}, ratio {first / left:.4f}")
for n in (1000, 2000, 3000):
    A = reverse_greedy(n)
    print(f"reverse greedy n={n}: k={len(A)}, admissible={admissible(A)}, k/sqrt(n)={len(A) / math.sqrt(n):.3f}")
