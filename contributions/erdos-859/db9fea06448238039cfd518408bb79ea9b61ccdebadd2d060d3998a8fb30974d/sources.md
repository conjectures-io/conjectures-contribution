# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/859.lean` declares the following under research-solved/textbook/test
categories with `sorry` proofs — settled mathematics whose formalization was missing:

  `erdos_859.variants.positive_density`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace). Statement provenance and
references are in the pool file's docstrings.

## Method

Membership of n >= 1 depends only on n mod t! (every part divides t!), so the set is a union of residue classes minus {0}; density = |good residues|/t! > 0 since residue 0 is good via the witness {t}.

## Verification

Self-contained on Mathlib plus the pool module import. Axiom closure of every theorem
is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`); no `sorry`, `native_decide`, or `set_option`.
