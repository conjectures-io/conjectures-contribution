# Erdős 375, `k = 3`: sources and scope

## Intended submission metadata

- Target: `erdos-375`
- Kind: `lemma`
- Mode: `formalized`
- Proposed title: `Erdős 375: the complete k = 3 case of Grimm's problem`
- Parents: none

## Exact formal target

- Google DeepMind Formal Conjectures, pinned source at commit
  [`379fc0298dc146df549e7061c3ede0353a5bb51f`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/375.lean).
- The open target is `Erdos375.erdos_375`, whose proposition asks for distinct
  prime divisors across every finite block of consecutive composite integers.
- The same pinned file already contains a complete theorem
  `Erdos375.erdos_375.variants.le_two` for every `k ≤ 2`.

## Marginal contribution

This draft does **not** claim a full solution of Erdős 375 or Grimm's
conjecture. Its new step is the exact `k = 3` case. It also proves the stronger
elementary lemma that every three consecutive natural numbers beginning at
least at `3` have a system of three distinct prime divisors. Combining the new
case with the source's existing `k ≤ 2` theorem gives an unconditional theorem
for every `k ≤ 3`.

The construction separates three parity cases for the first integer `a`:

- if `a` is odd, arbitrary prime divisors of `a`, `a+1`, and `a+2` are
  pairwise distinct;
- if `4 ∣ a`, use `2` for `a`, a prime divisor of `a+1`, and an odd prime
  divisor obtained from `(a+2)/2`;
- if `2 ∣ a` but `4 ∤ a`, use an odd prime divisor obtained from `a/2`, a
  prime divisor of `a+1`, and `2` for `a+2`.

## Mathematical context

- [Erdős Problems, problem 375](https://www.erdosproblems.com/375).
- P. Erdős and R. Graham, *Old and New Problems and Results in Combinatorial
  Number Theory*, Monographies de L'Enseignement Mathématique (1980).
- K. Ramachandra, T. N. Shorey, and R. Tijdeman, “On Grimm's problem relating
  to factorisation of a block of consecutive integers,” *Journal für die reine
  und angewandte Mathematik* (1975), pp. 109–124. This is the `[RST75]`
  reference recorded by the pinned formal source for a substantially broader
  asymptotic result.

These references provide target and historical context. The Lean proof in
`script.lean` is self-contained apart from the pinned repository and Mathlib;
it does not import or assume a paper proof.

## Originality and assistance disclosure

The parity case split and the Lean implementation in this draft were developed
locally for this contribution. No Lean code was copied from the historical
references, another contribution, or a third-party formalization. The proof
was developed with OpenAI Codex assistance. The eventual signer remains
responsible for reviewing correctness, provenance, novelty, and metadata before
promotion.
