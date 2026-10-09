"""Derive and check the universal Frobenius resolvent by exact polynomials.

Run with work/session6/run-sage-python.sh. The five roots have sum zero;
the invariant is translation invariant so this loses no characteristic-zero
case. No formula is accepted on the basis of numerical interpolation.
"""
from sage.all__sagemath_schemes import PolynomialRing, QQ, matrix, vector
from itertools import permutations, combinations
from functools import reduce
from operator import mul
from pathlib import Path
import json,time
here=Path(__file__).resolve().parent;started=time.monotonic()
R=PolynomialRing(QQ,4,'a',order='lex')
xs=list(R.gens());xs.append(-sum(xs))
prod=lambda terms:reduce(mul,terms,R(1))
theta=[]
for p in permutations(range(5)):
    edge=sum(xs[p[i]]*xs[p[(i+1)%5]] for i in range(5))
    diag=sum(xs[p[i]]*xs[p[(i+2)%5]] for i in range(5))
    t=(edge-diag)**2
    if t not in theta:theta.append(t)
assert len(theta)==6
coeffs=[R(1)]
for t in theta:
    new=[R(0)]*(len(coeffs)+1)
    for i,c in enumerate(coeffs):new[i]-=t*c;new[i+1]+=c
    coeffs=new
e=[sum(prod(xs[i] for i in ids) for ids in combinations(range(5),k)) for k in range(2,6)]
pqrs=[e[0],-e[1],e[2],-e[3]]
records=[];gp=[]
for j in range(7):
    weight=4*(6-j)
    exps=[(a,b,c,d) for a in range(weight//2+1) for b in range(weight//3+1)
          for c in range(weight//4+1) for d in range(weight//5+1) if 2*a+3*b+4*c+5*d==weight]
    polys=[prod(v**n for v,n in zip(pqrs,ex)) for ex in exps]
    mons=sorted(set(coeffs[j].monomials()).union(*(set(v.monomials()) for v in polys)))
    mat=matrix(QQ,[[v.monomial_coefficient(m) for v in polys] for m in mons])
    rhs=vector(QQ,[coeffs[j].monomial_coefficient(m) for m in mons])
    sol=mat.solve_right(rhs)
    assert sum(c*v for c,v in zip(sol,polys))==coeffs[j]
    data=[dict(exponents=list(ex),coefficient=str(c)) for ex,c in zip(exps,sol) if c]
    records.append(data)
    terms=['('+str(c)+')' + ''.join('*'+var+('^'+str(n) if n!=1 else '') for var,n in zip(['p','q','r','s'],ex) if n)
           for ex,c in zip(exps,sol) if c]
    gp.append('('+'+'.join(terms)+')*t^'+str(j))
    print(json.dumps(dict(coefficient=j,weight=weight,basis_size=len(exps),nonzero_terms=len(data),seconds=time.monotonic()-started)),flush=True)
assert all(len(c)==0 or all('/' not in a['coefficient'] for a in c) for c in records)
(here/'cayley_resolvent_formula.gp').write_text('cayley(p,q,r,s,t)={\n  '+ '+\n  '.join(gp)+'\n};\n')
result=dict(status='passed',universal_coefficients_checked=7,distinct_invariants=6,
            formula_coefficients_ascending=records,runtime_seconds=time.monotonic()-started,
            scope='Exact polynomial identities, not an arithmetic class-group certificate.')
(here/'cayley_resolvent_identity.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='passed',runtime_seconds=time.monotonic()-started)))
