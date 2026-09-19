# Sources and use

## Contribution

This is a formalization of known partial results for Erdős 835, together with an
exact local counting interface for the official coloring predicate. It does not
settle whether a qualifying coloring exists for any parameter greater than two.

Write `Property k` for `Erdos835.Property k`: the k-subsets of a 2k-element set
are colored with k+1 colors, and every (k+1)-subset contains all colors.
For positive k, the contribution proves:

- `Contribution.Erdos835Divisibility.local_color_count`: if a coloring is rainbow
  on every (k+1)-subset of a finite ground set E, then for every color a,
  `(|E|-k) * #{S ⊆ E : |S|=k, c(S)=a} = choose |E| (k+1)`.
  The theorem also handles smaller ground sets, where both sides vanish.
- `property_divisibility`: under the exact official predicate, every
  `1 ≤ r ≤ k` satisfies `r ∣ choose (k+r) (r-1)`.
- `prime_succ_of_property`: `0 < k → Property k → Nat.Prime (k+1)`.
  Thus `not_property_of_not_prime` eliminates every composite successor.
- `divisibility_iff_prime`: for positive k the entire scalar divisibility family
  holds if and only if k+1 is prime. This identifies precisely the remaining
  limitation of this arithmetic obstruction.
- `exists_property_iff_prime_parameter`: the original existential question is
  equivalent to `∃ p, p.Prime ∧ 3 < p ∧ Property (p-1)`.

All declarations are in `Contribution.Erdos835Divisibility`.

## Why a future solver can use this

A solver working directly with the task predicate can use
`prime_succ_of_property` to eliminate every parameter with composite successor,
then attack only prime parameters in `exists_property_iff_prime_parameter`.
`local_color_count` retains more information than the scalar necessary condition:
when `|E| > k`, it gives the exact size of every color class inside E.
The arithmetic converse prevents mistaking additional instances of the same
scalar condition for progress on the remaining prime cases.

## Official target and pinned environment

- [Conjectures.io problem page](https://conjectures.io/problems/erdos835-erdos-835).
- [Exact task metadata](https://github.com/conjectures-io/conjectures-tasks/blob/275ef4824c41d41f97ac4e9fff95ca471de9341d/pool/tier-1/erdos-835-formalized/source-metadata.json).
- [Pinned challenge](https://github.com/conjectures-io/conjectures-tasks/blob/275ef4824c41d41f97ac4e9fff95ca471de9341d/pool/tier-1/erdos-835-formalized/Challenge.lean).
- [Upstream problem source before the official audit patch](https://github.com/google-deepmind/formal-conjectures/blob/7d1a8c9912747679d0093f6d1216420c33ee5ffa/FormalConjectures/ErdosProblems/835.lean).

Environment: Lean 4.33.1, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, audited FormalConjectures commit
`8432eac998110a563e03df65a28c117e97c8c142`. The audited commit is reconstructed
using the contribution repository's official source pin and patch.

The problem source records the composite-successor theorem as an unproved
statement. The proof uses only the official definition from that module;
none of the problem's unfinished theorem proofs is used.

## Mathematical provenance

Jie Ma and Quanyu Tang, *A note on Erdős Problem #835*, Proposition 2.1,
Theorem 2.2, and Lemma 2.3:
[author-hosted note, revision 7f131832](https://github.com/QuanyuTang/erdos-problem-835/blob/7f131832bab5abfc903014ddb61efff21d56ae01/On_Problem_835.pdf).
These establish the divisibility condition, composite exclusion, and its
satisfaction at prime successors. No claim of historical mathematical priority
is made. The formal proof here uses direct local incidence counting, in place
of the note's maximum-independent-set and packing argument.

## Prior contribution and marginal value

Parent:
[`91dc274f5ffca92a31dd3dc17fdb02968d947def2abe9a53f2621a7a9970960b`](https://github.com/conjectures-io/conjectures-contribution/tree/22019a3051609bca40902de7ac3c9764ac0326d7/contributions/erdos-835/91dc274f5ffca92a31dd3dc17fdb02968d947def2abe9a53f2621a7a9970960b).
Its title is “Johnson-graph chromatic identities: Property iff chromatic number,
and chi(J(18,9)) > 10”. It proves the coloring/chromatic-number equivalence and
a parity obstruction for k=9 by counting inside an 11-element set.

That source was read during development. Its incidence-counting idea is
generalized here to arbitrary parameters and all colors. The parent is declared
for this intellectual lineage. The new Lean implementation is independently
written, using the pinned Mathlib subset-counting theorem; no parent code is
copied and no sibling contribution is imported. The prior equivalence and
numerical case are not republished. The added value is the uniform local count,
the infinite composite exclusion, the arithmetic converse, and the exact
restriction of the official existential statement.

## Central Mathlib dependencies

- `Finset.card_powersetCard`, `Finset.card_filter_powersetCard_subset`:
  [finite subset counting](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Powerset.lean).
- `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`:
  [finite incidence double counting](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/Enumerative/DoubleCounting.lean).
- `Choose.choose_modEq_choose_mod_mul_choose_div_nat`:
  [Lucas congruence](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Choose/Lucas.lean).
- `Nat.Prime.dvd_choose_add`, `Nat.choose_succ_right_eq`:
  [binomial divisibility](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Choose/Dvd.lean)
  and [binomial identities](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Choose/Basic.lean).

## Development, trust, and license

Developed with AI assistance. A separate mathematical and static Lean review
was performed; compilation and transitive axiom inspection provide the formal
verification. Exact finite arithmetic tests were used only for falsification;
no computation certificate, numerical assumption, or external solver is a proof
dependency. The ten declarations use only the standard Lean foundations
`propext`, `Classical.choice`, and `Quot.sound`.

The new source is offered under Apache-2.0. The cited mathematics and previous
contribution are credited above; this license statement covers only the new
source and accompanying original prose.
