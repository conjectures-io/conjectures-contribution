# Primitive length-five reduction for Erdős 686

This contribution turns the actual rational five-factor ratio in the pinned target into an integral primitive-pair reduction and a rational point on an explicit sextic curve. It supplies the multiplier-4 target interface and also a multiplier-25 specialization of the same proof. It does not exclude length five, classify rational points, or solve either all-length bounty.

## Reusable result

All declarations are in `Contribution.Erdos686Five`. The entry points are `ratio_four_reduction` and `ratio_twenty_five_reduction`, with common theorem `length_five_reduction`. They take natural offsets m,n, the disjointness hypothesis n+5<=m, and the exact rational finite-product equality at k=5. Their conclusion provides natural g,u,v and integer W satisfying `ReductionData`:

- g=gcd(m+3,n+3)>0; u,v>0; gcd(u,v)=1;
- m+3=g*v, n+3=g*u, g*u>=3 and g*v>=g*u+5;
- A=v^5-R*u^5 is nonzero;
- W=2*A*g^2-5*B and W^2=Q_R(u,v), where B=v^3-R*u^3;
- g^2=(5*B+W)/(2*A) in the rationals, and g^2 divides 4*(v-R*u) in the integers;
- the rational point (v/u,W/u^3) satisfies z^2=9*t^6+16*R*t^5-50*R*t^3+16*R*t+9*R^2.

Here Q_R(u,v)=9*v^6+16*R*v^5*u-50*R*v^3*u^3+16*R*v*u^5+9*R^2*u^6. The chosen definition of W gives the plus sign in recovery; changing its sign gives the other quadratic root. Positivity and the perfect-square requirement are retained by using the square of a positive natural g.

`integral_reconstruction` proves the reverse algebraic step: an integer sextic point satisfying 2*A*g^2=5*B+W, with A nonzero, gives F(g*v)=R*F(g*u), where F(t)=t^5-5*t^3+4*t. A caller must still supply positivity and separation to obtain an admissible block representation. A rational point alone is not a representation.

A future solver can apply the target entry point, classify only primitive curve points that meet these recovery and divisibility constraints, and use the returned equations to transfer that classification to the original ratio. This removes the normalization, denominator, nonvanishing and reconstruction proof obligations. No point enumeration is imported as a premise.

## Provenance and novelty boundary

The informal common-gcd reduction and the displayed sextic were supplied by the user on 2026-11-03, attributed to Claude. OpenAI Codex independently checked the polynomial identities and wrote the attached Lean formalization, including both target interfaces and the integral converse. These tool-assisted calculations are not independent human discoveries.

An existing **open** [PR #141](https://github.com/conjectures-io/conjectures-contribution/pull/141), inspected at commit `8ab9a0460eea0cf90d844499e005fd9e35744bd9`, already contains the multiplier-25 rational sextic equation in `Contribution.Erdos686TwentyFive.quotient_discriminant` and `centeredFive_to_quotient`. Its source is [script.lean](https://github.com/Dom1W1ns/conjectures-contribution/blob/8ab9a0460eea0cf90d844499e005fd9e35744bd9/contributions/erdos-686-variants-twenty-five/20dc430e9cc826e8ef800482f93f218875898052d870b217fcf219fa4c50c2cd/script.lean). **That ratio-25 curve equation is not claimed as new here.**

The incremental content is the primitive natural-pair normalization, integer W, nonzero leading coefficient, square recovery, gcd-square divisibility, converse, and direct target-shaped multiplier-4 interface. The common multiplier-25 specialization is included for reuse, not as a second novelty or reward claim. The new proofs were developed from the supplied reduction; the existing PR is acknowledged as overlapping prior work, not imported. It remains unmerged and therefore is not a published parent record. No published contribution is substantially reused as a mathematical premise; `parents=[]`.

Canonical main was checked at `aac7d4c614e399e8f6f8090ddfb685327081877a`, including both 686 indexes, the pinned 686 source and the current open-PR listing. The above primitive reduction was not found there or in the inspected PR. This is a scoped repository novelty review, not a worldwide priority claim. The entire common proof is filed once under the multiplier-4 target to avoid duplicate submissions.

The exact target is in the [pinned task bundle](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-four-counterexample). General problem context is [Erdős 686](https://www.erdosproblems.com/686).

## Verification and limits

The standalone source compiles with warnings treated as errors under Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It has no local sibling imports, extra axioms or computational proof assumptions. All public theorem dependencies were audited against the standard foundational axioms.

The user supplied bounded PARI point lists. Those lists, any claimed search coverage, Jacobian rank or simplicity heuristics, and a completeness assertion are deliberately absent from the Lean theorem and its assumptions. The formal artifact proves the explicit curve equation and recovery statements; it does not formalize the algebro-geometric genus classification. Completion would still require a rigorous point classification with recovery checks, or another argument, even to settle k=5. Other lengths remain beyond this contribution.

Recognition and payment are separate operator decisions; this partial reduction makes no bounty or payment claim.
