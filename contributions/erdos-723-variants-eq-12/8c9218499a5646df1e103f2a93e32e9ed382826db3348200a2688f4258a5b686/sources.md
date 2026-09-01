# Sources

## Target and statements

The pool file `FormalConjectures/ErdosProblems/723.lean` declares the following under `@[category research solved]`
with a `sorry` proof — the mathematics is settled but the formalization was missing:

  `erdos_723.variants.prime_power_is_projplane_order`

This contribution supplies checked proofs of exactly those statements (same
propositions, restated under the `Contribution` namespace since contribution files
cannot patch the pinned pool file). Statement provenance and the original
references are in the pool file's docstrings; background: https://www.erdosproblems.com/723.

## What the proofs use

Self-contained on Mathlib plus the pool module import; helper lemmas are local to
each section's namespace. No new axioms: the closure of every theorem is exactly
`propext`, `Classical.choice`, `Quot.sound` (verified with `#print axioms` against
the pinned toolchain, Lean 4.27.0 / Mathlib `a3a10db0`).
