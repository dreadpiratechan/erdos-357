import sys, time
def count(N):
    cnt = 0
    sys.setrecursionlimit(10000)
    def rec(seq, sums_set, pref, last):
        nonlocal cnt
        cnt += 1
        for a in range(last + 1, N + 1):
            # new sums: sums of blocks ending at the new element
            new = []
            s = a
            ok = s not in sums_set
            if ok:
                new.append(s)
                for i in range(len(seq) - 1, -1, -1):
                    s += seq[i]
                    if s in sums_set or s in new:
                        ok = False
                        break
                    new.append(s)
            if ok:
                for s in new: sums_set.add(s)
                seq.append(a)
                rec(seq, sums_set, pref, a)
                seq.pop()
                for s in new: sums_set.discard(s)
    rec([], set(), [], 0)
    return cnt
for N in (12, 16, 18, 20, 22):
    t = time.time(); c = count(N); print(N, c, round(time.time() - t, 1), flush=True)
