# Sources and provenance — Erdős 479 Fermat–CRT family

## Intended submission metadata

- Eligible target: `erdos-479`
- Kind: `partial-proof`
- Mode: `formalized`
- Proposed title: `Erdős 479: Fermat-CRT family for infinitely many power-tower parameters`
- Parents: none

At contribution-repository commit
`68aa91546faf9627ea0bdce9d148d12a7e0e1209`, the `erdos-479` index contained
zero published contributions. A read-only GitHub check at
`2026-09-02 22:25 UTC` also found no open pull request whose title or branch
mentioned `479`.

## Exact result and relevance

The pinned target asks whether every natural `k > 1` has infinitely many
natural denominators `n` satisfying `2^n ≡ k [MOD n]`. This contribution does
not prove the universal statement. It proves a substantial infinite family:

- for every `t : ℕ`, set `q = 2^t` and `k = 2^q`;
- for every prime `p > 2`, the denominator `n = q*p` satisfies the exact
  pinned congruence;
- therefore that fixed `k` has infinitely many valid `n`;
- the map `t ↦ 2^(2^t)` is injective, so infinitely many distinct `k > 1`
  satisfy the target body.

`pinned_target_body_at_power_tower` is the minimal use site against the exact
target body, while `infinitely_many_good_nat_parameters` packages the global
partial progress.

## Fermat and CRT provenance

For `q = 2^t`, both `2^(q*p)` and `2^q` are divisible by `q`. For the odd prime
modulus `p`, the exponent difference is `q*(p-1)`, so Fermat's little theorem
gives congruence modulo `p`. Since `q` and `p` are coprime, the Chinese
remainder theorem combines the two congruences modulo `q*p`.

The Lean proof uses these pinned Mathlib results directly:

- Fermat exponent reduction:
  [`Int.ModEq.pow_eq_pow`](https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/FieldTheory/Finite/Basic.lean#L652)
- coprime-moduli combination:
  [`Nat.modEq_and_modEq_iff_modEq_mul`](https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/ModEq.lean#L490)
- natural-to-integer transport:
  [`Int.natCast_modEq_iff`](https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Int/ModEq.lean#L96)

Problem history is available at [Erdős Problems
479](https://www.erdosproblems.com/479).

## Pinned versus upstream statement drift

The eligible pool target at Formal Conjectures commit
[`379fc0298dc146df549e7061c3ede0353a5bb51f`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/479.lean)
quantifies natural `k > 1` and uses `Nat.ModEq`.

Upstream commit `9e64bb9b` ([pull request
#5242](https://github.com/google-deepmind/formal-conjectures/pull/5242)) corrects
the informal/formal domain to every integer `k ≠ 1`, using `Int.ModEq`. That
change is present in the audited derived environment `8432eac9` but does not
retroactively change the currently eligible pinned target.

The primary claims and metadata remain bound to the pinned natural statement.
The supplementary declarations `int_modEq_of_nat_modEq`,
`power_tower_parameter_int`, and `infinitely_many_good_int_parameters`
transport the same positive power-tower family into the corrected integer
body. They do not claim the missing zero or negative integer cases and do not
weaken the pinned theorem.

## Originality and assistance disclosure

The Fermat/CRT argument is elementary number theory; no claim of new
mathematics is made. The claimed deliverable is the checked Lean construction,
the infinite-denominator proof for each parameter, the proof of infinitely
many distinct good parameters, and the explicit statement-drift bridge.

The verified starting point was
`/tmp/formal-new28-b/Scratch479.lean`. The contribution-shaped proof and
documentation were refined locally with OpenAI Codex assistance. The eventual
signer remains responsible for reviewing correctness, provenance, novelty,
and submission metadata.
