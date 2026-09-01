# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/282.lean` declares the following under research-solved/textbook/test
categories with `sorry` proofs — settled mathematics whose formalization was missing:

  `erdos_282.variants.fibonacci`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace). Statement provenance and
references are in the pool file's docstrings.

## Method

Numerator descent: r = x - 1/N has strictly smaller reduced numerator (minimality of N = sInf cross-multiplied through Rat.divInt bookkeeping); induction on x.num.toNat with a shift lemma and zero-absorption.

## Verification

Self-contained on Mathlib plus the pool module import. Axiom closure of every theorem
is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`); no `sorry`, `native_decide`, or `set_option`.
