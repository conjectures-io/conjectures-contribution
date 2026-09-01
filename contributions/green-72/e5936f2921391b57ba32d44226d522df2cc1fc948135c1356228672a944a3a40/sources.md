# Sources

## Target and statement

`FormalConjectures/GreensOpenProblems/72.lean` declares `allowedSetSize_le`
(`AllowedSetSize k N ≤ (k − 1) * N` for `k ≤ N`) under `@[category textbook]` with a
`sorry` proof. This contribution proves exactly that statement (restated under the
`Contribution` namespace) — the pigeonhole upper bound that the no-k-in-line problem
asks to be attained. Background: Ben Green's open problem list, problem 72;
https://en.wikipedia.org/wiki/No-three-in-line_problem.

## Method

Fiberwise counting over first coordinates (`Finset.card_eq_sum_card_fiberwise`): a
fiber with `k` or more points contains a `k`-subset lying on a vertical line, which is
collinear (explicit parametrization `r • (0,1) +ᵥ (c,0)` via
`collinear_iff_exists_forall_eq_smul_vadd`), contradicting `not_collinear`. Hence each
of the `N` fibers has at most `k − 1` points. The `k = 0` case is vacuous: the empty
subset is collinear (`collinear_empty`), so no allowed set exists. The supremum is
bounded via `csSup_le'`.

## Mathlib declarations used

`Finset.card_eq_sum_card_fiberwise`, `Finset.exists_subset_card_eq`,
`collinear_iff_exists_forall_eq_smul_vadd`, `collinear_empty`, `csSup_le'`,
`Finset.sum_le_sum`. Axiom closure exactly `propext`, `Classical.choice`, `Quot.sound`
on the pinned toolchain (Lean 4.27.0 / Mathlib `a3a10db0`).
