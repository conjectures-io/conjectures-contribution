# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/1074.lean` declares the following under research-solved/textbook/test
categories with `sorry` proofs — settled mathematics whose formalization was missing:

  `erdos_1074.variants.EHSNumbers_init`
  `erdos_1074.variants.PillaiPrimes_init`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace). Statement provenance and
references are in the pool file's docstrings.

## Method

Explicit prime witnesses and factorizations for every m up to 17 (largest certificate 39916801), counts by decidable kernel evaluation, nth values via Nat.nth_count.

## Verification

Self-contained on Mathlib plus the pool module import. Axiom closure of every theorem
is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`); no `sorry`, `native_decide`, or `set_option`.
