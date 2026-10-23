"""Print the residue spectra D_0..D_11 of the modulus-42 pattern (for the manuscript table)
and compare with the table listed in this script (the residue-spectra table of the manuscript). Independent, pure Python."""
R6 = (2, 7, 11, 25, 26, 34)
G = [0]
for t in range(24):
    G.append((G[-1] + R6[t % 6]) % 42)
print("G(0..11) =", G[:12], " G(12) =", G[12])
D = [sorted({(G[x + L] - G[x]) % 42 for x in range(12)}) for L in range(12)]
listed = [[0], [2, 7, 11, 25, 26, 34], [9, 18, 36], [1, 20], [3, 12, 27], [10, 14, 19, 29, 37, 38], [21],
          [4, 5, 13, 23, 28, 32], [15, 30,39], [22, 41], [6, 24, 33], [8, 16, 17, 31, 35, 40]]
for L in range(12):
    print(f"D_{L:<2} size {len(D[L])}: {D[L]}  {'= listed table' if D[L] == listed[L] else 'DIFFERS from listed table'}")
allv = sorted(v for d in D for v in d)
print("partition of Z/42:", allv == list(range(42)))
