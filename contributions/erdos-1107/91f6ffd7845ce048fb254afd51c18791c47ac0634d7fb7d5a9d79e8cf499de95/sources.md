# Sources

## Target

* Erdős problem 1107 — [erdosproblems.com/1107](https://www.erdosproblems.com/1107)
* Statement formalised as `Erdos1107.erdos_1107` in
  `FormalConjectures/ErdosProblems/1107.lean`, pinned by this pool at
  formal-conjectures commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.
* `Erdos1107.SumOfRPowerful`, defined in the same file.

## Formal Conjectures declarations used

* `Nat.Full`, from `FormalConjecturesForMathlib/Data/Nat/Full.lean`.
* `Nat.Full.zero_left` — every natural number is `0`-full.
* `Nat.Full.one_left` — every natural number is `1`-full.

## Mathlib declarations used

* `List.length`, `List.mem_singleton` and `List.sum_singleton`, all reached through `simp`.

## Prior contributions

Extends `c1d1a9c2810f979240e35690dc0e7d5b160516b386496b41e7074479f223f026`, which gives the
empty, singleton and two-summand introduction rules for the same predicate. This file
generalises those to an arbitrary list and adds the degenerate `r < 2` cases; it lives in its
own namespace and shares no declaration name with it.

## Literature

Not used. All three lemmas follow from the definition of `SumOfRPowerful` and from the two
`Nat.Full` lemmas cited above, so Heath-Brown's result ([He88]) is not relied on.

## Note

This is a test submission created to re-verify the index rebuild after a bypass was added to
the `main` ruleset. The Lean it contains is nonetheless complete and proved, with no `sorry`
and no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
