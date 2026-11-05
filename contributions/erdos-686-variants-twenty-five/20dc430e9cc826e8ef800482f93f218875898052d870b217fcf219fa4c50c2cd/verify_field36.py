"""Independent exact algebra check in Sage, using the exported GP data.

Rebuilds the relative resolvent from the universally verified identity,
computes its norm as a six-by-six polynomial determinant, and checks the
raw-generator map in the reduced field. It does not certify a class group.
"""
from sage.all__sagemath_schemes import PolynomialRing, QQ, matrix
from pathlib import Path
import time,json
start=time.monotonic();here=Path(__file__).resolve().parent
d=json.loads((here/'field36_exact_data.json').read_text())
formula=json.loads((here/'cayley_resolvent_identity.json').read_text())['formula_coefficients_ascending']
RB=PolynomialRing(QQ,'b');b=RB.gen();base=RB(d['base'])
K=RB.quotient(base,'a');a=K.gen()
RT=PolynomialRing(K,'t');t=RT.gen()
quintic,rem=RT(d['base']).quo_rem(t-a);assert rem==0
dep=quintic(t-quintic[4]/5);assert dep[4]==0
pqrs=[dep[3],dep[2],dep[1],dep[0]]
relative=[]
for j,terms in enumerate(formula):
    c=K(0)
    for term in terms:
        v=K(QQ(term['coefficient']))
        for u,n in zip(pqrs,term['exponents']):v*=u**n
        c+=v
    expected=K(RB([QQ(v) for v in d['relative'][j]]))
    assert c==expected;relative.append(c)
print('relative_formula_verified',flush=True)
R=PolynomialRing(QQ,'u');u=R.gen();QZ=PolynomialRing(R,'z');z=QZ.gen()
baseZ=QZ([R(v) for v in d['base']])
relZ=sum(QZ([QQ(v) for v in row])*u**j for j,row in enumerate(d['relative']))
cols=[]
for j in range(6):
    v=(relZ*z**j)%baseZ
    cols.append([v[i] for i in range(6)])
mat=matrix(R,6,6,lambda i,j:cols[j][i])
norm=mat.determinant();assert norm==R(d['raw'])
print('relative_norm_determinant_verified',flush=True)
red=R(d['reduced']);assert red.degree()==36 and red.is_irreducible()
amap=R([QQ(v) for v in d['raw_map']]);v=R(0)
for c in reversed(d['raw']):v=(v*amap+c)%red
assert v==0
result=dict(status='passed',relative_coefficients_recomputed=7,
            norm_determinant_size=6,absolute_degree=36,
            reduced_polynomial_irreducible=True,raw_generator_map_verified=True,
            runtime_seconds=time.monotonic()-start,
            scope='Independent algebra checks; maximal-order certification remains PARI nfcertify. No class-group or rank certificate.')
(here/'verify_field36.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
