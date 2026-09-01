# Sources

## Target and statement

`FormalConjectures/ErdosProblems/359.lean` declares `erdos_359.variants.isGoodFor_1_low_values`
(`A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15}` for any `IsGoodFor A 1`) under
`@[category test]` with a `sorry` proof. This contribution proves exactly that statement
(restated under the `Contribution` namespace). It pins down the greedy sequence's first
eight terms, the concrete ground truth that both open parts of the target quantify over.
Background: https://www.erdosproblems.com/359 (sequence 1, 2, 4, 5, 8, 10, 14, 15, …).

## Method

Stepwise determination from the `IsLeast` characterization: at stage `j` every
consecutive-sum `∑_{i∈Icc a b} A i` with `Icc a b ⊆ Iic j` is evaluated from the
already-determined prefix; each candidate below the true next term is eliminated by its
explicit representation, and the true term is checked against all sums. A small interface
lemma `icc_subset_iic` (`Icc a b ⊆ Iic j ↔ b < a ∨ b ≤ j`) drives the case analysis.

## Mathlib declarations used

`Finset.sum_Icc_succ_top`, `Finset.Icc_self`, `Finset.sum_singleton`,
`Finset.Icc_eq_empty`, `IsLeast`; tactics `interval_cases`, `omega`, `simp only`.
Axiom closure exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned
toolchain (Lean 4.27.0 / Mathlib `a3a10db0`).
