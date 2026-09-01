# Sources

## Target

* Erdős problem 236 — https://www.erdosproblems.com/236
* The statement and counting function are formalized as `Erdos236.erdos_236` and
  `Erdos236.f` in the pinned source:
  https://github.com/conjectures-io/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/236.lean
* This contribution uses `Erdos236.f` directly and proves target-shaped little-o
  statements on two infinite subfamilies of inputs.

## Prior contributions

At the development base on 2026-09-01, the target index
https://github.com/conjectures-io/conjectures-contribution/blob/main/contributions/erdos-236/index.md
listed zero prior contributions. This submission has no parents.

## Covering-system seed

* OEIS A206430 — https://oeis.org/A206430
* OEIS A345685 — https://oeis.org/A345685

These references record the classical constant `509203` and the covering primes
`{3, 5, 7, 13, 17, 241}` associated with the Riesel sequence
`509203 * 2^m - 1`. Only those constants and the finite-cover idea were taken from
the references.

The present contribution makes a different target-specific use of the data. It
rotates the residue classes to prove `509203 ≡ 2^r (mod p)`, lifts those
congruences to every `n ≡ 509203 (mod 2^24 - 1)`, and separately excludes the
exceptional possibility `n - 2^k = p`. All 24 congruence certificates and all 24
exceptional-prime exclusions are re-proved inside Lean by kernel-checked `decide`.

## Original work and reusable handoff

The following material was developed for this contribution:

* the `candidate` / `validExponents` API for the filtered count in `Erdos236.f`;
* injectivity of the candidate-value map on valid exponents;
* `f_le_card_of_candidate_mem`, reducing the exponent count to a finite candidate set;
* `f_le_card_add_card_of_partial_divisor_cover`, a reusable quantitative finite-cover
  theorem allowing a finite untreated set of exponents;
* the complete special case `f n ≤ 2` for every even `n` and its exact little-o wrapper;
* the theorem `f (509203 + (2^24 - 1) * t) = 0` for every `t`;
* arbitrarily large odd zero inputs and the exact little-o wrapper on the resulting
  odd arithmetic progression.

No external Lean code was copied.

## Mathlib interface

The proof uses `Nat.ModEq`, `Nat.Prime` divisor lemmas, finite-set/list cardinality,
powers of two, and standard `Asymptotics` composition and transitivity declarations
from the pinned Mathlib environment.

## Tool assistance and verification

The mathematical argument and Lean implementation were developed with assistance from
OpenAI GPT-5.6 Pro — https://openai.com/ — and compiled against Lean 4.27.0 and the
pinned Formal Conjectures commit above. Key exported theorems were audited with
`#print axioms`; they depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Tool-assisted/generated work is disclosed under G6 of the contribution recognition
contract; the signer remains responsible for correctness, provenance, and value.
