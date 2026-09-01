# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/291.lean` declares the following under research-solved/textbook/test
categories with `sorry` proofs — settled mathematics whose formalization was missing:

  `erdos_291.parts.ii`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace). Statement provenance and
references are in the pool file's docstrings.

## Method

Witnesses n = 2*3^(k+1): all but two terms of the sum are divisible by 3 and the exceptional pair collapses to a multiple of 3, so 3 divides both a(n) and L(n).

## Verification

Self-contained on Mathlib plus the pool module import. Axiom closure of every theorem
is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`); no `sorry`, `native_decide`, or `set_option`.
