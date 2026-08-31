# Sources

## Target

* Erdős problem 100 — [erdosproblems.com/100](https://www.erdosproblems.com/100)
* Statement formalised as `Erdos100.erdos_100` in
  `FormalConjectures/ErdosProblems/100.lean`, pinned by this pool at
  formal-conjectures commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.
* `Erdos100.DistancesSeparated`, defined in the same file, is the only definition this
  contribution builds on.

## Mathlib declarations used

* `Metric.dist_le_diam_of_mem` — a distance between two points of a bounded set is at most the
  diameter of that set.
* `Set.Finite.isBounded` and `Finset.finite_toSet` — a finite set in a metric space is bounded.
* `Finset.card_le_one` — a finset has at most one element exactly when all of its elements are
  equal.
* `dist_eq_zero` — in a metric space, `dist p q = 0` is equivalent to `p = q`.
* `Finset.mem_coe`, `not_le`.

## Prior contributions

None. This is the first contribution recorded for `erdos-100`; nothing in
`contributions/erdos-100/index.json` is extended or superseded.

## Literature

Not used. The four lemmas are direct consequences of the definition and of Mathlib, so no
result from the problem's bibliography (Kanold; Guth–Katz, *On the Erdős distinct distances
problem in the plane*, Ann. of Math. (2) 181 (2015), 155–190; Piepmeyer) is relied on.

## Note

This is a test submission created to exercise the contribution pipeline. It is labelled as
such in its title and module docstring; the Lean it contains is nonetheless complete and
proved, with no `sorry` and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
