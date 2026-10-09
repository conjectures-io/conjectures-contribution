"""Independently recount finite reductions in the small-isogeny obstruction.
Uses only adjacent public JSON data and the Python standard library.
"""
from fractions import Fraction
from pathlib import Path
from math import isqrt
from time import monotonic
import json
start=monotonic(); here=Path(__file__).resolve().parent
fd=json.loads((here/'quartic_cover_exact_data.json').read_text())
models=json.loads((here/'node2_small_models.json').read_text())
cert=json.loads((here/'isogeny-screen.json').read_text())
def prime(p):return p>1 and all(p%d for d in range(2,isqrt(p)+1))
def ev(cs,t,p):
 out=0
 for c in reversed(cs):
  q=Fraction(c);out=(out*t+q.numerator*pow(q.denominator,-1,p))%p
 return out
seen={}; checks=0
for c in cert['certificates']:
 ell,p,t=c['ell'],c['residue_prime'],c['field_root']
 assert prime(ell) and prime(p) and p!=ell
 assert ev(fd['field'],t,p)==0
 deriv=[str(i*Fraction(x)) for i,x in enumerate(fd['field'])][1:]
 assert ev(deriv,t,p)!=0
 key=p,t
 if key not in seen:
  aa,bb,cc,dd,ee=[ev(x,t,p) for x in fd['quartic'][::-1]]
  I=(12*aa*ee-3*bb*dd+cc*cc)%p
  J=(72*aa*cc*ee+9*bb*cc*dd-27*aa*dd*dd-27*bb*bb*ee-2*cc**3)%p
  squares=[0]*p
  for y in range(p):squares[y*y%p]+=1
  traces=[]
  for model in models:
   g=ev(model['gamma'],t,p);A=-27*g*g*I%p;B=-27*g*g*g*J%p
   assert (4*A**3+27*B**2)%p!=0
   order=1+sum(squares[(x**3+A*x+B)%p] for x in range(p))
   traces.append(p+1-order);checks+=1
  seen[key]=traces
 assert seen[key]==c['traces']
 assert all(all((z*z-tr*z+p)%ell for z in range(ell)) for tr in seen[key])
assert [c['ell'] for c in cert['certificates']]==[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]
assert len(models)==16
print(json.dumps(dict(status='passed',finite_curve_recounts=checks,good_places=len(seen),prime_degrees=15,curves=16,seconds=monotonic()-start)))
