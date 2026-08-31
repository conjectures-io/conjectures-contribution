# Sources

## Target

* Erdős problem 100 — [erdosproblems.com/100](https://www.erdosproblems.com/100)
* Statement formalised as `Erdos100.erdos_100` in
  `FormalConjectures/ErdosProblems/100.lean`, pinned by this pool at
  formal-conjectures commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.

## Formal Conjectures declarations used

* `EuclideanGeometry.distinctDistances`, defined in
  `FormalConjecturesForMathlib/Geometry/2d.lean` as the cardinality of the image of
  `Finset.offDiag` under `fun pair => dist pair.1 pair.2`. This is the only definition the
  contribution builds on.

## Mathlib declarations used

* `Finset.card_image_le` — the image of a finset is no larger than the finset.
* `Finset.offDiag_card` — `#s.offDiag = #s * #s - #s`.
* `Finset.offDiag_mono`, `Finset.image_subset_image`, `Finset.card_le_card`.
* `Nat.mul_sub_one`, `Nat.le_zero`, `Nat.le_one_iff_eq_zero_or_eq_one`.

## Prior contributions

Extends the same target as `0e264f3df724851823072072d2be03bb29ce676acb7bf3bf2a824ea6b383dbc1`,
which covers `Erdos100.DistancesSeparated`. This file is disjoint from it: it touches the
counting side rather than the separation predicate, and shares no declaration name.

## Literature

Not used. The four lemmas are direct consequences of the definition and of Mathlib, so no
result from the problem's bibliography (Kanold; Guth–Katz, *On the Erdős distinct distances
problem in the plane*, Ann. of Math. (2) 181 (2015), 155–190; Piepmeyer) is relied on.

## Note

This is a test submission created to verify that a merge performed by the GitHub App triggers
`contribution-index`. The Lean it contains is nonetheless complete and proved, with no `sorry`
and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
