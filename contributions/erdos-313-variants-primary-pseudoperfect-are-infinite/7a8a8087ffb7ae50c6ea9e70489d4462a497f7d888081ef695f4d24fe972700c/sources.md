# Erdős 313: canonical equivalence and direct prime-successor closure

## Exact target

- Pinned source: [`FormalConjectures/ErdosProblems/313.lean`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/313.lean)
- Open declaration:
  `Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite`
- Target: `Set.Infinite {n | Erdos313.IsPrimaryPseudoperfect n}`
- Contribution slug:
  `erdos-313-variants-primary-pseudoperfect-are-infinite`

The file never invokes either admitted open declaration in the upstream Erdős
313 module.

## Formalized structural argument

For a formal witness `(m, P)`, put

```text
D = ∏ p in P, p
A = ∑ p in P, ∏ q in P.erase p, q.
```

Multiplying the defining reciprocal identity by `D` and then by `m` gives the
natural-number identity

```text
m * A = (m - 1) * D.                         (1)
```

Fix `p ∈ P`. Every term of `A` except the cofactor indexed by `p` is
divisible by `p`. The remaining cofactor is not divisible by `p`, because all
members of `P` are distinct primes. Hence `p ∤ A`. But `p ∣ D`, so (1)
and Euclid's lemma imply `p ∣ m`.

Since the primes in the finset are pairwise coprime, their product satisfies
`D ∣ m`. Conversely, adding `D` to (1) yields

```text
m * A + D = m * D,
```

so `m ∣ D`. Positivity and antisymmetry of divisibility give `D = m`.

The package formalizes further consequences and interfaces:

- `m` is squarefree;
- every `p ∈ P` satisfies `p ∣ m` and `p ≤ m`;
- `P = m.primeFactors`, so a witness finset is unique;
- `IsPrimaryPseudoperfect m` is equivalent to using the canonical witness
  `m.primeFactors`;
- the subtype of solution pairs is equivalent to the subtype of primary
  pseudoperfect denominators;
- infinitude of the pair-valued solution set is equivalent to infinitude of
  primary pseudoperfect denominators.

## Direct recurrence

If `m + 1` is prime, the divisibility result makes `m + 1 ∉ P` automatic.
Adjoining this prime changes the reciprocal sum by `1 / (m + 1)`, and the
elementary identity

```text
(1 - 1 / m) + 1 / (m + 1) = 1 - 1 / (m * (m + 1))
```

produces a witness for `m * (m + 1)`. Unlike the preserved draft, the final
interface starts from the bare upstream proposition
`IsPrimaryPseudoperfect m`.

## Prior art, scope, and provenance

The mathematics is not claimed as new. In particular, Proposition 2.1 of Han
Wang's 2026 paper
[Port Fillings for Primary Pseudoperfect Numbers](https://arxiv.org/abs/2605.21518)
proves that the denominator in Erdős's reciprocal equation equals the product
of the witness primes, and Corollary 5.2 states the one-prime inheritance step
`K ↦ K(K + 1)` when `K + 1` is prime. The same recurrence and its initial chain
`2 → 6 → 42 → 1806` are also recorded in
[OEIS A054377](https://oeis.org/A054377).

The contribution is the checked Lean formalization against the pinned
`Erdos313.erdos313Solutions` definition: the cleared-denominator argument,
canonical-witness and subtype equivalences, exact equivalence of the two
infinitude formulations, and a direct recurrence interface on the upstream
`IsPrimaryPseudoperfect` predicate.

This is a partial lemma package, not an infinitude proof. It supplies no theorem
ensuring that the required successor primes occur indefinitely.

OpenAI Codex assisted with the proof design, Mathlib API search, Lean
formalization, compilation, and axiom audit. A human submitter should review
the mathematics, attribution, and claim boundary before publication.
