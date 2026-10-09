"""Independent rational arithmetic verification of the degree-15 factor model."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,time

SOURCE=Path(__file__).with_name('quartic_cover_exact_data.json')

def main():
    begin=time.monotonic(); data=json.loads(SOURCE.read_text())
    field=list(map(F,data['field'])); degree=len(field)-1
    assert degree==15 and field[-1]==1
    def zero(): return [F(0)]*degree
    def constant(c):
        a=zero();a[0]=F(c);return a
    def add(a,b): return [x+y for x,y in zip(a,b)]
    def neg(a): return [-x for x in a]
    def times(a,b):
        out=[F(0)]*(2*degree-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): out[i+j]+=x*y
        for i in range(len(out)-1,degree-1,-1):
            for j in range(degree): out[i-degree+j]-=out[i]*field[j]
        return out[:degree]
    def ev(cs,x):
        out=zero()
        for c in cs[::-1]:out=add(times(out,x),c)
        return out
    q=[list(map(F,row)) for row in data['quadratic']]
    h=[list(map(F,row)) for row in data['quartic']]
    s=list(map(F,data['pair_sum']));delta=list(map(F,data['delta']))
    product=[zero() for _ in range(7)]
    for i,a in enumerate(q):
        for j,b in enumerate(h): product[i+j]=add(product[i+j],times(a,b))
    original=[5625,400,0,-1250,0,400,9]
    assert product==[constant(F(c,9)) for c in original]
    assert q[2]==h[4]==constant(1)
    assert q[1]==neg(s)
    assert h[0]==delta and delta!=zero()
    # q(s-X)=q(X) checks the pair-sum interpretation in the actual field.
    assert add(times(s,s),times(q[1],s))==zero()
    assert ev(q,s)==q[0]
    quartic=[times(delta,c) for c in h]
    assert quartic[0]==times(delta,delta)
    report=dict(status='passed',field_degree=degree,exact_factorization=True,
                monic_factors=True,pair_sum_identity=True,known_quartic_point=True,
                source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                seconds=time.monotonic()-begin,scope='Factor and point identities; not ranks, Selmer completeness, or target solution',
                lean_checked=False,full_target_solved=False)
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
