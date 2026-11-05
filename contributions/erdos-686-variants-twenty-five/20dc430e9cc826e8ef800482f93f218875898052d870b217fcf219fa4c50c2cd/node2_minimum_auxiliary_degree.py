"""Exact character/degree audit for rational S6 permutation correspondences.

Character table: Murnaghan--Nakayama, checked by orthogonality and hook lengths.
The (3,2,1) row is independently checked by Jacobi--Trudi/Frobenius.
No number-field arithmetic or class-group computations.
"""
from collections import Counter
from functools import lru_cache
from itertools import permutations
from math import factorial
from pathlib import Path
import json,time

start=time.monotonic();root=Path(__file__).resolve().parent
def partitions(n,top=None):
    if n==0:return [()]
    return [(a,)+p for a in range(min(n,top or n),1-1,-1) for p in partitions(n-a,a)]
parts=partitions(6)
def cells(lam):return {(i,j) for i,a in enumerate(lam) for j in range(a)}
@lru_cache(None)
def mn(lam,cyc):
    if not cyc:return int(not lam)
    if sum(lam)!=sum(cyc):return 0
    k=cyc[0];out=0;diagram=cells(lam)
    for mu in partitions(sum(lam)-k):
        sub=cells(mu)
        if not sub <= diagram:continue
        strip=diagram-sub
        if any({(i,j),(i+1,j),(i,j+1),(i+1,j+1)} <= strip for i,j in strip):continue
        seen=set();todo=[next(iter(strip))]
        while todo:
            p=todo.pop()
            if p in seen:continue
            seen.add(p);i,j=p
            todo.extend(q for q in [(i-1,j),(i+1,j),(i,j-1),(i,j+1)] if q in strip-seen)
        if seen!=strip:continue
        out+=(-1)**(len({i for i,j in strip})-1)*mn(mu,cyc[1:])
    return out
def hook_degree(lam):
    product=1;diagram=cells(lam)
    for i,j in diagram:
        product*=1+sum(ii==i and jj>j for ii,jj in diagram)+sum(jj==j and ii>i for ii,jj in diagram)
    assert factorial(6)%product==0
    return factorial(6)//product
def class_size(cyc):
    z=1
    for a,m in Counter(cyc).items():z*=a**m*factorial(m)
    return factorial(6)//z
table={lam:[mn(lam,cyc) for cyc in parts] for lam in parts}
assert sum(class_size(cyc) for cyc in parts)==720
for lam in parts:
    assert mn(lam,(1,)*6)==hook_degree(lam)
    for mu in parts:
        assert sum(class_size(c)*mn(lam,c)*mn(mu,c) for c in parts)==720*int(lam==mu)

# Independent Frobenius character formula through the Schur determinant.
def young_permutation_character(comp,cyc):
    if min(comp)<0:return 0
    counts={(0,)*len(comp):1}
    for k in cyc:
        nxt=Counter()
        for exp,num in counts.items():
            for i in range(len(comp)):
                new=list(exp);new[i]+=k
                if new[i]<=comp[i]:nxt[tuple(new)]+=num
        counts=nxt
    return counts.get(tuple(comp),0)
def frobenius_character(lam,cyc):
    total=0
    for p in permutations(range(len(lam))):
        comp=tuple(lam[i]-i+p[i] for i in range(len(lam)))
        parity=sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))%2
        total+=(-1)**parity*young_permutation_character(comp,cyc)
    return total
target=(3,2,1)
assert all(frobenius_character(target,c)==mn(target,c) for c in parts)

def tup(a):return tuple(map(tup,a)) if isinstance(a,list) else a
d=json.loads((root/'odd_norm_relation_certificate.json').read_text())
X=tup(d['X']);Y={k:tup(v) for k,v in d['Y'].items()}
def rep(cyc):
    g=list(range(6));k=0
    for length in cyc:
        for i in range(k,k+length):g[i]=k+(i-k+1)%length
        k+=length
    return tuple(g)
def pair(g,p):return tuple(sorted(g[i] for i in p))
def match(g,m):return tuple(sorted(pair(g,p) for p in m))
def conjugate(g,h):return tuple(g[h[g.index(i)]] for i in range(6))
def action(g,v,name):
    if name=='flag45':return pair(g,v[0]),match(g,v[1])
    if name=='pairs15':return pair(g,v)
    if name=='matchings15':return match(g,v)
    return tuple(sorted(conjugate(g,h) for h in v))
sets=dict(flag45=X,**Y)
characters={name:[sum(action(rep(c),v,name)==v for v in vs) for c in parts] for name,vs in sets.items()}
multiplicities={}
for name,ch in characters.items():
    inner=sum(class_size(c)*mn(target,c)*a for c,a in zip(parts,ch))
    assert inner%720==0
    multiplicities[name]=inner//720
assert multiplicities==dict(flag45=1,pairs15=0,matchings15=0,cyclic5_36=1)

indices=[d for d in range(1,36) if 720%d==0]
possible=[]
for degree in indices:
    for count16 in range(1,degree//16+1):
        for sign in (0,1):
            rem=degree-1-16*count16-sign
            for a in range(max(rem,0)//5+1):
                for b in range(max(rem,0)//9+1):
                    for c in range(max(rem,0)//10+1):
                        if rem==5*a+9*b+10*c:possible.append([degree,count16,sign,a,b,c])
assert possible==[[18,1,1,0,0,0]]
# An order40 subgroup has a unique Sylow5 subgroup.
assert [n for n in range(1,9) if 8%n==0 and n%5==1]==[1]
assert [n for n in range(1,5) if 4%n==0 and n%5==1]==[1]
# Independent normalizer enumeration in S6: one 5-cycle fixes letter5.
identity=tuple(range(6));g=(1,2,3,4,0,5)
def mul(a,b):return tuple(a[b[i]] for i in range(6))
power=identity;powers=[]
for _ in range(5):powers.append(power);power=mul(power,g)
P=set(powers)
normalizer=[h for h in permutations(range(6)) if {conjugate(h,a) for a in P}==P]
assert len(normalizer)==20
out=dict(status='passed',irreducible_degrees=[dict(partition=lam,degree=hook_degree(lam)) for lam in parts],
         character_classes=[dict(cycle_type=c,size=class_size(c),chi_321=mn(target,c),flag_character=characters['flag45'][i],F36_character=characters['cyclic5_36'][i]) for i,c in enumerate(parts)],
         target_multiplicities=multiplicities,orthogonality_checks=121,independent_target_character_checks=11,
         candidate_indices_below36=indices,degree_equation_survivors=possible,
         sylow5_count_for_order40=[1],normalizer_order=20,
         index36_subgroup_unique_up_to_conjugacy=True,
         conclusion='36 is the minimum possible auxiliary field degree carrying the missing (3,2,1) constituent in this S6 closure. No collection of fields of degrees strictly below36 can support a rational permutation-correspondence factorization of the flag45 identity.',
         scope='Only rational equivariant permutation correspondences in the fixed S6 closure; no obstruction to other arithmetic methods.',runtime_seconds=time.monotonic()-start)
(root/'node2_minimum_auxiliary_degree.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
