"""Independent exact matching invariant/embedding check; no class-group claims."""
from sage.all__sagemath_schemes import PolynomialRing, QQ
from pathlib import Path
import json,time
start=time.monotonic();here=Path(__file__).resolve().parent
d=json.loads((here/'matching_exact_data.json').read_text())
R=PolynomialRing(QQ,'t');t=R.gen();p=R(d['L'])
def elt(v):return R([QQ(x) for x in v])%p
def mul(a,b):return a*b%p
def ev(coeff,a):
    v=R.zero()
    for c in reversed(coeff):v=(v*a+QQ(c))%p
    return v
e,bottom,c,b,one=map(elt,d['quartic']);assert one==1
theta=elt(d['theta']);rho=(3*c-theta)/9
assert (mul(mul(rho,rho),rho)-mul(c,mul(rho,rho))+mul(mul(b,bottom)-4*e,rho)+4*mul(c,e)-mul(bottom,bottom)-mul(mul(b,b),e))%p==0
rawmap=elt(d['raw_map']);reducedmap=elt(d['map'])
assert rawmap==(81*(elt(d['q0'])+rho))%p
assert len(d['raw'])==16 and len(d['reduced'])==16
assert R(d['raw']).is_irreducible() and R(d['reduced']).is_irreducible()
assert ev(d['raw'],rawmap)==0 and ev(d['reduced'],reducedmap)==0
result=dict(status='passed',quartic_pair_product_resolvent_verified=True,
            matching_invariant_verified=True,degree=15,
            irreducible_polynomials_checked=2,embeddings_into_degree45_checked=2,
            runtime_seconds=time.monotonic()-start,
            scope='Independent exact algebra; maximal-order certificate is separate. No class-group or curve rank result.')
(here/'verify_matching.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
