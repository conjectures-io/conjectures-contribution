# Sources and provenance — Erdős 242 modulo-24 follow-up

## Intended submission metadata

- Target: `erdos-242`
- Kind: `lemma`
- Mode: `either`
- Proposed title: `Erdős 242: reduce the prime residual from 1 mod 12 to 1 mod 24`
- Parent contribution:
  [`6862728fa0017d77cc6e4e19fe2d84df35c94abb79d5188fccc7ae7674c0f859`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-242/6862728fa0017d77cc6e4e19fe2d84df35c94abb79d5188fccc7ae7674c0f859)

The parent must be listed in the promoted payload's `parents` field. It is a
semantic dependency and lineage declaration, not a Lean import: contribution
files elaborate independently.

## Exact delta over the parent

The parent proves a reduction from the full Erdős 242 target to prime
denominators `p % 12 = 1`. This follow-up does not reproduce that reduction or
any of its helper API. It adds only the next checked step:

1. `mod_eight_five_family` constructs an ordered three-unit-fraction
   decomposition whenever `n % 8 = 5`. Writing `n = 8k + 5`, its witnesses are
   `x = 2(k+1)`, `y = n(k+1)`, and `z = 2n(k+1)`.
2. `mod_eight_five_of_mod_twelve_one_of_mod_twenty_four_ne_one` proves the
   residue bridge: within `1 mod 12`, failure to be `1 mod 24` forces `5 mod 8`
   (the `13 mod 24` class).
3. `primes_mod_twelve_of_primes_mod_twenty_four` discharges that missing half,
   and `primes_mod_twelve_iff_primes_mod_twenty_four` packages the exact
   equivalence of the two residual prime obligations.
4. `decomp_thirteen` is a concrete non-vacuous example with witnesses
   `(4, 26, 52)`.
5. `use_with_mod_twelve_prime_reduction` shows the exact composition point a
   later solver uses with the parent's reduction theorem.

Thus the marginal result is a reduction of the unsolved prime residue from
`1 mod 12` to `1 mod 24`; it is not a full solution of Erdős 242.

## Mathematical and formal sources

- The exact pinned target is
  [`FormalConjectures/ErdosProblems/242.lean`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/242.lean).
- Historical context and references are collected at
  [Erdős Problems 242](https://www.erdosproblems.com/242).
- The classical congruence reductions for the Erdős–Straus equation are
  discussed in Section 1 of Christian Elsholtz and Terence Tao,
  [Counting the number of solutions to the Erdős–Straus equation on unit fractions](https://arxiv.org/abs/1107.1010).
- The local source from which this focused draft was extracted is
  `sn66-conjecture/harry/erdos242/Main.lean`. That larger unpublished workspace
  also contains baseline families already covered by the parent; they were
  deliberately excluded here.

## Originality and assistance disclosure

The number-theoretic identity is classical; no claim of new mathematics is
made. The contribution's claimed delta is the standalone Lean formalization
and explicit integration of the `5 mod 8` family with the already-published
`1 mod 12` reduction. No Lean code was copied from the parent contribution.

The Lean proof and documentation were composed locally with OpenAI Codex
assistance, then checked by the Lean kernel against both recorded target
environments. The eventual signer remains responsible for reviewing the
mathematics, provenance, title, lineage, and reward metadata before promotion.
