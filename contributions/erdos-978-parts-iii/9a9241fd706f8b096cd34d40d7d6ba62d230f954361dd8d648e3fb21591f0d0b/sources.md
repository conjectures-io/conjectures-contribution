# Sources and provenance

## Declared target

- Contribution target: `erdos-978-parts-iii`; site slug:
  `erdos978-erdos-978-parts-iii`.
- Proposed kind/mode: `lemma` / `formalized`.
- Proposed title: `Erdős 978(iii): Hensel correspondence and four-class local bound`.
- Reward target: `fc-target:Erdos978.erdos_978.parts.iii`.
- Formalized task: `fc-379fc029-parts-iii-bc83630eb3-formalized-v1`.
- Exact source: [`FormalConjectures/ErdosProblems/978.lean`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/978.lean)
  at commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.
- Problem reference: [erdosproblems.com/978](https://www.erdosproblems.com/978).

The generated formalized target is exactly

```lean
True ↔ {n : ℕ | Squarefree (n ^ 4 + 2)}.Infinite.
```

The source declaration uses the corresponding `answer(sorry)` wrapper. This
package does not prove the infinitude statement and is therefore a partial
formalized-side contribution, not a solution of Erdős 978(iii).

## Published background

The pinned formal source records:

- P. Erdős, *Arithmetical properties of polynomials*, Journal of the London
  Mathematical Society 28 (1953), 416--425;
- C. Hooley, [*On the power free values of polynomials*](https://doi.org/10.1112/S002557930000797X),
  Mathematika 14 (1967), 21--26;
- T. D. Browning, *Power-free values of polynomials*, Archiv der Mathematik
  96 (2011), 139--150.

The formalized local argument is classical. If an odd prime-square divides
`n⁴ + 2`, then `-2` is a square modulo `p`; the supplementary law for the
Legendre symbol forces `p ≡ 1` or `3 (mod 8)`. Mathlib supplies this last step
as `ZMod.exists_sq_eq_neg_two_iff`.

For odd `p`, every root of `X⁴ + 2` modulo `p` is simple because it is nonzero
and the derivative is `4X³`. The file proves directly, without invoking an
external Hensel theorem, that every such root has exactly one lift modulo
`p²`. It then injects the lifted roots into the roots of a degree-four
polynomial over `ZMod p`, obtaining

```text
ρ(p²) = #{a mod p² : p² | a⁴+2} ≤ 4.
```

No new informal number-theoretic theorem is claimed. The contribution is the
Lean formalization and reusable finite-set/sieve interface.

## Public prior local analysis

The July 2026 [Erdős Problem a Day working report for problem 978](https://erdosproblemaday.com/report/978)
publicly records a stronger informal formula: `ρ(p²)` is always `0`, `2`, or
`4`, with an exact congruence/quartic-residue case split. It also isolates the
remaining uniform large-prime-square tail. This package formalizes the Hensel
correspondence and uniform bound `ρ(p²) ≤ 4`, but not that full `0/2/4`
classification, its CRT product formula, or the tail estimate.

## Current preprint warning

S. R. Zapata Ceballos and F. Jalalvand,
[*On the Squarefree Values of Degree-2q Polynomials*](https://arxiv.org/abs/2608.10335),
arXiv:2608.10335v1 (11 August 2026), claims a positive-density theorem whose
quartic corollary would include `X⁴ + 2`: the polynomial is Eisenstein at `2`,
its quartic field contains `ℚ(√-2)`, and its fixed-value gcd is squarefree.

This portfolio does not import that claim as an established solution. In the
posted v1, our audit did not find a uniform estimate justifying the passage
from every finite collection of prime-square restrictions to avoidance of all
prime squares, and it could not justify treating diagonal rational residue
classes at conjugate prime ideals as a full Cartesian product. Until those
points are independently resolved, the conservative formal boundary is the
local result actually proved in `script.lean`.

## Exact theorem content

The final file contains 18 declarations and proves:

1. `4 ∤ n⁴+2`, and every obstructing prime lies in class `1` or `3` modulo `8`;
2. every obstructing prime is coprime to `n`;
3. obstruction is periodic modulo `p²` and is decided by the finite set
   `primeSquareObstructionResidues p`;
4. Hensel uniqueness and an explicit existence construction for odd primes;
5. a bijection, via reduction, between roots modulo `p²` and modulo `p`;
6. the uniform bound `(primeSquareObstructionResidues p).card ≤ 4`;
7. a good/bad partition with at least `p² - 4` good residue classes; and
8. an exact rewrite of squarefreeness using only primes congruent to `1` or
   `3` modulo `8`.

The local bad proportion is therefore at most `4 / p²`. The file does not sum
these local estimates across primes and, crucially, does not control primes
whose size grows with the input range.

## Lean/library ingredients

The proof uses `ZMod.natCast_eq_zero_iff`,
`ZMod.exists_sq_eq_neg_two_iff`, natural and integer modular congruence,
`Polynomial.card_roots'`, finite-set injection/bijection cardinality, and
`Nat.squarefree_iff_prime_squarefree`. The `p = 2` case is handled separately
in `ZMod 4`.

## Authorship disclosure

The Lean proof and these notes were developed with OpenAI Codex assistance. A
future signer must independently inspect the mathematics, target relevance,
prior-art boundary, metadata, and recognition risk.
