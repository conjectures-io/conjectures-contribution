# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/409.lean` declares the following under research-solved/textbook/test
categories with `sorry` proofs — settled mathematics whose formalization was missing:

  `erdos_409.variants.termination`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace). Statement provenance and
references are in the pool file's docstrings.

## Method

Strong induction: composite n > 1 has phi(n) < n and phi(n) != n-1 (Nat.totient_lt, Nat.totient_eq_iff_prime), so the iterate strictly descends until a prime; n = 1 reaches 2 in one step.

## Verification

Self-contained on Mathlib plus the pool module import. Axiom closure of every theorem
is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`); no `sorry`, `native_decide`, or `set_option`.
