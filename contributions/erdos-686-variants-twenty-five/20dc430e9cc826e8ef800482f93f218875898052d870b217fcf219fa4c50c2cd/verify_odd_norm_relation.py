"""Independent full matrix and generator-equivariance certificate check.

No orbit generation, orbit compression, linear solving, or algebra package.
The two permutation generators generate S6. Incidence-map equivariance
therefore holds for all of S6. Checks the displayed 45x45 identity entrywise.
"""
from pathlib import Path
from fractions import Fraction
from itertools import permutations
import json,time
start=time.monotonic()
d=json.loads(Path(__file__).with_name('odd_norm_relation_certificate.json').read_text())
def tup(v):return tuple(tup(x) for x in v) if isinstance(v,list) else v
X=tup(d['X']);Y={name:tup(items) for name,items in d['Y'].items()}
assert len(set(X))==45
assert {name:len(set(items)) for name,items in Y.items()}==dict(pairs15=15,matchings15=15,cyclic5_36=36)
def pair(g,p):return tuple(sorted(g[i] for i in p))
def match(g,m):return tuple(sorted(pair(g,p) for p in m))
def conjugate(g,h):
    gi=[g.index(i) for i in range(6)]
    return tuple(g[h[gi[i]]] for i in range(6))
def act_y(g,v,name):
    if name=='pairs15':return pair(g,v)
    if name=='matchings15':return match(g,v)
    return tuple(sorted(conjugate(g,h) for h in v))
idxX={v:i for i,v in enumerate(X)}
checked=0
for g in [(1,0,2,3,4,5),(1,2,3,4,5,0)]:
    ax=[idxX[(pair(g,p),match(g,m))] for p,m in X]
    for name,items in Y.items():
        iy={v:i for i,v in enumerate(items)}
        ay=[iy[act_y(g,v,name)] for v in items]
        for A in d['maps'][name]:
            assert len(A)==45 and all(len(row)==len(items) for row in A)
            assert all(v in [0,1] for row in A for v in row)
            for i in range(45):
                for j in range(len(items)):
                    assert A[i][j]==A[ax[i]][ay[j]]
                    checked+=1
# Directly check all entries of the claimed integral relation.
out=[[0]*45 for _ in X]
for term in d['relation']['terms']:
    name,a,b=term['map'];c=term['coefficient']
    A=d['maps'][name][a];B=d['maps'][name][b]
    for i in range(45):
        for j in range(45):out[i][j]+=c*sum(x*y for x,y in zip(A[i],B[j]))
denom=d['relation']['coefficient']
assert denom==5 and denom%2==1
assert all(out[i][j]==denom*int(i==j) for i in range(45) for j in range(45))
# Direct stabilizer orders identify the auxiliary fixed fields.
allg=list(permutations(range(6)))
stabs={name:sum(act_y(g,items[0],name)==items[0] for g in allg) for name,items in Y.items()}
assert stabs==dict(pairs15=48,matchings15=48,cyclic5_36=20)
sig={}
cc=(1,0,3,2,4,5)
for name,items in Y.items():
    r1=sum(act_y(cc,v,name)==v for v in items)
    sig[name]=[r1,(len(items)-r1)//2]
res=dict(status='passed',matrix_identities=2025,equivariance_entries=checked,
         odd_coefficient=denom,stabilizer_orders=stabs,signatures=sig,
         runtime_seconds=time.monotonic()-start,
         scope='Exact permutation relation only; no arithmetic class-group certificate or curve resolution.')
Path(__file__).with_suffix('.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res,indent=2))
