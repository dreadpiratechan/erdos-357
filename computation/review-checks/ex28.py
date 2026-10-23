seq=[2,3,4,6,11,25,38,40,41,47,52,54,56,57,58,60,61,62,64,66,67,68,69,70,71,72,73,75]
assert len(seq)==28 and all(seq[i]<seq[i+1] for i in range(27)) and seq[-1]==75
P=[0]
for a in seq: P.append(P[-1]+a)
d={}
for x in range(29):
    for y in range(x+1,29):
        d.setdefault(P[y]-P[x],[]).append((x,y))
print("28-term example: terms",len(seq),"blocks",sum(len(v) for v in d.values()),"distinct sums",len(d),"valid",all(len(v)==1 for v in d.values()))
