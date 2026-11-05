# Complete-factor stencil API for Erdős686, multiplier25

Erdős686 remains unresolved. These theorems give a conditional exclusion and an
arithmetic reduction; they do not settle the full length-five case or all lengths.
All new names below are in `Contribution.Erdos686TwentyFive.FactorStencil`.

## Complete factorizations and actual positions

For positive integer coefficients `a,b,c,d,e,f` and positive integer factors
`z,t,u,v,w,r,x,y`, suppose

    n+1 = a*z*t*u,   n+2 = b*v*w,     n+3 = c*r*x,
    m+2 = d*v*u,     m+3 = e*z*r*w,   m+4 = f*x*y,
    n < m.

These are complete products. Extra factors must remain in the coefficients;
finding the same edges inside a larger allocation does not permit deleting them.
The four exact consecutive differences are

    b*v*w = a*z*t*u + 1,     e*z*r*w = d*v*u + 1,
    c*r*x = b*v*w + 1,       f*x*y = e*z*r*w + 1.

The order condition implies `b*w < d*u`. The lemma does not require the product
multiplier25 or the stronger disjointness condition; it may be applied to a
hypothetical bounty witness once these complete factorizations are established.
No permutation of the actual term positions is assumed.

## What the dense reduction proves

`dense_stencil_reduction` derives positive integers `q,h,j` with

    2*q = j*x,        q*h < d*e*z,       IsCoprime x z,
    b*d*c^2*q*x^2 = a^2*b*e*z^3*h*t^2 + (d*e*z-q*h)^2,
    (d*e*z-q*h)*r = a*b*z*t + 2*b*q*w,
    d*c*x = (d*e*z-q*h)*w - a*h*z*t,
    d*u = b*w + r*h.

A later solver can use this to replace the local factor equations by a checked
norm identity and divisibility conditions, with every coefficient retained.

`dense_stencil_complementary_divisor` then constructs a positive integer `K`.
Writing

    L = 2*(d*e*z-q*h),     T = 2*d^2*e*c,     S = a*j*h^2*t,

its key identity is `K*L = 2*(T+S)`. The positive cubic identity gives `0<S<T`,
so `L<4*T`. `dense_stencil_linear_bound` assembles this deduction from the four
consecutive differences. `labeled_dense_pattern_bound` is the direct use site
from the six complete products at the actual `n,m` positions above.

**T remains unbounded.** Its coefficients `d,e,c` contain omitted factors in a
dense allocation. There is no theorem here bounding those factors or converting
this inequality into a finite search for arbitrary witnesses. In particular,
`L<4*T` is not an absolute height bound for `n`.

## Complete unscaled special case

`consecutive_stencil_impossible` excludes positive integers satisfying

    v*w = z*t*u+1,    z*r*w = v*u+1,
    r*x = v*w+1,      x*y = z*r*w+1,     w<u.

It is an unbounded theorem: there is no upper limit on the factors. Its proof
specializes the dense reduction at `a=b=c=d=e=f=1`, then uses the session20
integer contradiction. `labeled_pattern_impossible` excludes the exact products

    n+1=ztu, n+2=vw, n+3=rx,
    m+2=vu,  m+3=zrw, m+4=xy,    n<m.

This is a complete exclusion of the specified factorization. There is no proof
that every multiplier25 witness has this pattern. It does not by itself exclude
a larger support with additional factors.

## Scope relative to earlier work and external certificates

The PR already contains the length-six exclusion, unbounded rational-square
cross-pair exclusion at length five, and supporting transport/quotient interfaces.
Those declarations are retained unchanged and are not presented as new work in
this update. The generic matrix-product rearrangement, toy countermodels and
unrelated session15–19 results are intentionally not added to this delta.

The separate research package externally excludes every proper normalized prime-
owner support at k5. Its proof and finite certificates are not Lean premises in
this file. Therefore neither the unscaled stencil nor the incoming restricted
scaled-stencil exclusion is claimed to clear a new remaining length-five region.
Full normalized25-pair support remains open.

The incoming scaled-stencil research also reports a conditional finite reduction
for `a*b|25` and an external exact search. That assembled exclusion and its search
are not Lean theorems here; the bound and search logs are not included in this
patch. The published Lean proof does not depend on them. Older arithmetic-geometry
artifacts retained from the pending PR remain explicitly external computations,
not unconditional rank bounds or imported proof assumptions.

## Verification and reuse

`script.lean` is the sole standalone Lean artifact, as required by the repository.
It imports only the permitted Mathlib modules and defines names under
`Contribution.Erdos686TwentyFive`. The private cubic/positivity and reduced-system
lemmas are included only because the public results depend on them.

The complete file is compiled under the repository's pinned Lean4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. A separate local harness audits every
elaborated declaration transitively, including generated private helpers. The
harness is not part of the contribution; its result is in `verification.json` and
`declaration_axioms.json`. Only standard foundational axioms are permitted.
