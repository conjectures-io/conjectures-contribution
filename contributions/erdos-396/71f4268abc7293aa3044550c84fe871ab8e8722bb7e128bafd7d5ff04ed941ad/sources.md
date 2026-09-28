# Adjacent quadratic rows for Erdős 396

## Target and intended use

This is a partial contribution to [Erdős 396](https://conjectures.io/problems/erdos396-erdos-396).
Write D_K(N) = N(N-1)…(N-K+1). The conjecture requires D_K(N) to divide
the central binomial coefficient for every positive width K, at some N.
Here K is the number of factors; it is k+1 in the original statement.

The main declaration is
`Contribution.Erdos396AdjacentRows.cofinal_adjacent_rows`.
For every K ≥ 2 and every lower bound T, it constructs positive t,s and
one N ≥ max(T,K) such that

    N = t(2t-1) = 1 + 2s(3s-1).

For every prime p ≥ K with p > 2 dividing N or N-1, if

    p² > 4t and p² > 12s,

then

    v_p(D_K(N)) = 1 ≤ v_p(binomial(2N,N)).

All these eligible primes concern the same N. The equality concerns the
whole descending product, not just one factor in a row. The hypotheses do
not assume that either quadratic factor is prime.

A later solver can use this declaration to supply a common endpoint and
discharge the valuation obligations for the eligible primes of the first
two rows. `scaled_owner_all_width` is a more general reusable interface for
a row of the form A t(a t-h), with an explicit divisor-residue hypothesis.
`example_five_term_prime_payment` demonstrates that interface at N=4005,
K=5 and p=89.

## Exact limitations

This does not prove full divisibility, even for two rows. It leaves primes
below K, the prime 2, primes failing the size conditions, and prime factors
of the other rows untreated. It supplies no density estimate and no claim
that those remaining conditions have a common solution on this family.
The common-endpoint construction is not a solution of Erdős 396.

## Proof explanation

Start with (u,s)=(0,0), and repeatedly replace it by

    (97u + 168s + 44, 56u + 97s + 26).

The recurrence preserves 2u²+3u+2s=6s² and makes u grow without bound.
Putting t=u+1 gives the two neighboring row identities above.

For a prime dividing t(2t-1), distinguish the factor it divides. After
removing p, the resulting cofactor lies above halfway modulo p when p²>4t.
For the other row, the same argument uses that 2c² is 2 modulo 3 for every
divisor c of 3s-1; p²>12s bounds the correction. The generic lemma retains
these residue and size conditions explicitly.

An upper-half cofactor supplies a carry at p² when N is doubled in base p.
Kummer's formula then gives at least one copy of p in the central binomial
coefficient. Since p≥K, two different rows cannot both be divisible by p.
The nonzero cofactor residue also excludes p² from its row, so the complete
block's demand is exactly one.

## Attribution

This contribution combines original AI-assisted mathematical research by the
contributor, developed using OpenAI ChatGPT and Codex. The contributor is
responsible for the statements, proofs, and attribution. It is not presented
as independent rediscovery by a separate human collaborator.

Earlier work in this same research developed the adjacent-row recurrence,
the common-endpoint construction, residue conditions, single-row ownership,
and cofactor carry arguments. This contribution packages those arguments
into a self-contained arbitrary-width interface and adds a concrete use
example. All needed proofs are included; no private files or services are
required to use the result.

No mathematical priority claim is made for the classical recurrence or the
underlying carry principle. External mathematical and software sources are
attributed below.

The only imported library is [Mathlib](https://github.com/leanprover-community/mathlib4).
The carry argument uses its existing `padicValNat_choose'` theorem, from
[the factorial valuation module](https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/NumberTheory/Padics/PadicVal/Basic.lean).
The original target is in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/7d1a8c9912747679d0093f6d1216420c33ee5ffa/FormalConjectures/ErdosProblems/396.lean).
We do not import or use the unproved target declaration.

The public [Erdős 396 contribution index](https://github.com/conjectures-io/conjectures-contribution/blob/main/contributions/erdos-396/index.md)
listed zero contributions when read on 28 September 2026. This is evidence
about that index, not an exhaustive literature or semantic novelty claim.
Recognition remains subject to the repository's review.

## Verification status

The exact standalone file passed both Lean 4.27.0 / Mathlib v4.27.0 and the
contribution site's pinned Lean 4.33.1 / Mathlib v4.33.1 import environment
locally on 28 September 2026. The site-source commit was reconstructed as
`6a786f997e18e8f095762a2830d191b7e25e505e`, with Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. All 17 declaration axiom audits
in each version contain only standard axioms, with no unproved placeholders.
The source now imports seven specific Mathlib modules instead of the whole
library; the statements are unchanged. The source-policy scan found no
prohibited code or imports.

This establishes the stated partial theorem and source compatibility in
those two environments. It is not an official Linux CI run, signed-record
admissibility decision, or recognition decision. Those remain separate.
