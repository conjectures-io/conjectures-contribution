# Provenance and intended use

This contribution excludes multiplier 4 at length ten for **every** pair of natural offsets m,n, even without the target's disjointness condition. `length_ten` states the natural-product exclusion. `no_ratio_ten` states the rational finite-product interface used by the [pinned target](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-four-counterexample). A future solver may use it to discharge the k=10 branch of a putative representation. No claim is made for all lengths.

## Mathematical argument

Write F(n)=(n+1)...(n+10), q=2n+11,
P(q)=8q^5-660q^3+7887q and r(q)=25960q^4-218295q^2+2286144.
The polynomial P(q) is divisible by 5 for every integer q. With A(n)=P(2n+11)/5, the exact identity is

    25 A(n)^2 - 65536 F(n) = 25 r(2n+11).

For n>=16300, the proof establishes sqrt(4)*r(2n+11)<A(n). If F(m)=4F(n), monotonicity gives m>n. The integer-square gap lemma then forces A(m)=sqrt(4)A(n), and the remainder equality follows. But P(u)/r(u) is strictly increasing for u>v>=11: `cross_pos` proves this by expanding P(u)r(v)-P(v)r(u) in d=u-v and z=v-11, with strictly positive coefficients. The forced equalities give the opposite sign. Thus `bound` proves n<16300.

`checked` verifies exact brackets for every 0<=n<16384, using two finite indices. The arithmetic expression in `bracket` is only a hint: no real-root approximation is assumed by the proof. Each actual bracket is checked by `decide +kernel`. Strict monotonicity of F excludes every m, without a separate bound on m. The finite computation finds no equality, including overlapping blocks.

## Lineage and external sources

The square-gap and polynomial cross-multiplication approach extends the following published contributions, all declared as parents:

- [1e9266022bf5586a144c4e5c2901d43cfb58994fe3184e45a38113e4db7a98e1](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-four/1e9266022bf5586a144c4e5c2901d43cfb58994fe3184e45a38113e4db7a98e1)
- [951dcfa511fe294dab5fc36209f3a17f798c7b72726b2a10e49c4ce3e31b662f](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-four/951dcfa511fe294dab5fc36209f3a17f798c7b72726b2a10e49c4ce3e31b662f)

The earlier cases are not resubmitted or claimed as new credit. The new content is the complete length-ten exclusion, its explicit bound, divisibility normalization and exact finite certificate.

The general even-length polynomial-expansion approach appears in Vjeko Kovač's length-six comment and [IRAMBONA's post 9291](https://www.erdosproblems.com/forum/thread/686#post-9291), which handles lengths eight and twelve and discusses fixed even lengths more generally. We used that approach and independently derived the displayed length-ten polynomial identities and bound with SymPy assistance. This is not a claim to have invented the general method.

[Open PR #141](https://github.com/conjectures-io/conjectures-contribution/pull/141), inspected at `8ab9a0460eea0cf90d844499e005fd9e35744bd9`, demonstrates compact arithmetic bracket hints for a length-five certificate. This informed our choice of compact hints. The present finite certificate instead quantifies directly over two `Fin` indices; it does not copy or depend on that PR's recursive checker or soundness theorem. No mathematical exclusion from that PR is used as a premise.

Code and proof development used OpenAI Codex assistance, exact Python arithmetic and SymPy. These programs are not proof premises. All declarations use [Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and Lean 4.33.1. There is no native-computation axiom, unproved premise or local sibling import.

## Novelty boundary

Canonical main was checked at `ebdc44c5f08be18c5d65ce0bf7f09635c03213b4` on 2026-11-03, including both 686 contribution indexes, and open PR #141 at the head above. Neither these records nor the pinned 686 source supplies a length-ten exclusion. The full forum text read on this date supplies k=8 and k=12 exclusions but no k=10 exclusion. Targeted web searches did not locate a prior k=10 exclusion. This is a bounded novelty review, not a proof of worldwide priority. Earlier bounded searches reported no examples at k=10; the contribution proves the exclusion for all offsets.

Recognition and payment remain separate from admissibility under the contribution contract; this contribution does not settle the full bounty.
