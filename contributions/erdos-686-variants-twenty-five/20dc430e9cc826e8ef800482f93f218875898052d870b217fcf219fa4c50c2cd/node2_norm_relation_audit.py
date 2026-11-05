"""Exact regrouping to one copy of each auxiliary class group.

Also restricts the relation to all unramified Frobenius prime-orbit lattices.
No field arithmetic, class groups, or elliptic-curve computations.
"""
from itertools import permutations
from pathlib import Path
import json
import time

started = time.monotonic()
ROOT = Path(__file__).resolve().parent
d = json.loads((ROOT / 'odd_norm_relation_certificate.json').read_text())
def tup(x): return tuple(tup(y) for y in x) if isinstance(x, list) else x
X = tup(d['X']); Y = {k:tup(v) for k,v in d['Y'].items()}
A0,A1,A2,_ = d['maps']['pairs15']
B0 = d['maps']['matchings15'][0]
C0 = d['maps']['cyclic5_36'][0]
def tr(A): return [list(x) for x in zip(*A)]
def mul(A,B):
    Bt=tr(B)
    return [[sum(x*y for x,y in zip(r,c)) for c in Bt] for r in A]
def lin(*terms):
    return [[sum(c*A[i][j] for c,A in terms) for j in range(len(terms[0][1][0]))] for i in range(len(terms[0][1]))]
P=Y['pairs15'];M=Y['matchings15']
J=[[int(len(set(p)&set(q))==1) for q in P] for p in P]
D=[[int(p in m) for p in P] for m in M]
assert J == tr(J)
assert A1 == mul(A0,J)
assert A2 == lin((1,mul(B0,D)),(-1,A0))
FP=lin((-4,A0),(-3,A1),(-1,A2))
FM=lin((1,mul(A2,tr(D))),(-1,B0))
FC=C0
total=lin((1,mul(FP,tr(A0))),(1,mul(FM,tr(B0))),(1,mul(FC,tr(C0))))
assert total == [[5*int(i==j) for j in range(45)] for i in range(45)]

def pair(g,p):return tuple(sorted(g[i] for i in p))
def match(g,m):return tuple(sorted(pair(g,p) for p in m))
def conjugate(g,h):
    gi=[g.index(i) for i in range(6)]
    return tuple(g[h[gi[i]]] for i in range(6))
def act(g,v,name):
    if name=='X':return (pair(g,v[0]),match(g,v[1]))
    if name=='pairs15':return pair(g,v)
    if name=='matchings15':return match(g,v)
    return tuple(sorted(conjugate(g,h) for h in v))
def cycles(a):
    unused=set(range(len(a)));out=[]
    while unused:
        k=min(unused);cyc=[]
        while k in unused:
            unused.remove(k);cyc.append(k);k=a[k]
        out.append(cyc)
    return out
def orbits(g,items,name):
    ix={v:i for i,v in enumerate(items)}
    return cycles([ix[act(g,v,name)] for v in items])
def induced(A,target,source):
    out=[]
    for tx in target:
        row=[sum(A[tx[0]][j] for j in sy) for sy in source]
        assert all(row==[sum(A[i][j] for j in sy) for sy in source] for i in tx)
        out.append(row)
    return out
representatives={}
for g in permutations(range(6)):
    representatives.setdefault(tuple(sorted(map(len,cycles(g)))),g)
checks=[]
for typ,g in sorted(representatives.items()):
    xo=orbits(g,X,'X');total=[[0]*len(xo) for _ in xo]
    for name,F,A in [('pairs15',FP,A0),('matchings15',FM,B0),('cyclic5_36',FC,C0)]:
        yo=orbits(g,Y[name],name)
        total=lin((1,total),(1,mul(induced(F,xo,yo),induced(tr(A),yo,xo))))
    assert total==[[5*int(i==j) for j in range(len(xo))] for i in range(len(xo))]
    checks.append(dict(cycle_type=typ,prime_orbits_L=len(xo),entries=len(xo)**2))
assert len(checks)==11
out=dict(status='passed',source='odd_norm_relation_certificate.json',
         auxiliary_multiplicities=dict(Epair=1,Ematching=1,F36=1),
         factorization='5 I = (-4 A0 -3 A1 - A2) A0^t + (A2 D^t - B0) B0^t + C0 C0^t',
         checked_identities=['J symmetric','A1=A0 J','A2=B0 D-A0','three-channel coefficient-five relation'],
         full_identity_entries=2025,unramified_Frobenius_checks=checks,
         source_maps=dict(pair_norm=tr(A0),matching_norm=tr(B0),F36_correspondence=tr(C0)),
         return_maps=dict(pairs15=FP,matchings15=FM,cyclic5_36=FC),
         runtime_seconds=time.monotonic()-started,
         scope='Exact permutation and Frobenius prime-orbit certificates; no numerical class-group or rank bound.')
(ROOT/'node2_norm_relation_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ('source_maps','return_maps')},indent=2))
