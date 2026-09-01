# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/835.lean` declares the following under research-solved/textbook/test
categories with `sorry` proofs — settled mathematics whose formalization was missing:

  `property_iff_chromaticNumber`
  `johnsonGraph_18_9_chromaticNumber`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace). Statement provenance and
references are in the pool file's docstrings.

## Method

Property iff chi = k+1 via rainbow (k+1)-cliques and image-of-coloring counting; the 18/9 case by a parity double count over an 11-set (11 = 2m impossible).

## Verification

Self-contained on Mathlib plus the pool module import. Axiom closure of every theorem
is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`); no `sorry`, `native_decide`, or `set_option`.
