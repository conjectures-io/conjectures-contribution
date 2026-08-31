# Sources

## Target

* Erdős problem 1107 — [erdosproblems.com/1107](https://www.erdosproblems.com/1107)
* Statement formalised as `Erdos1107.erdos_1107` in
  `FormalConjectures/ErdosProblems/1107.lean`, pinned by this pool at
  formal-conjectures commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.
* `Erdos1107.SumOfRPowerful`, defined in the same file, is the predicate this contribution
  builds introduction rules for.

## Formal Conjectures declarations used

* `Nat.Full`, from `FormalConjecturesForMathlib/Data/Nat/Full.lean` — `n` is `k`-full when
  `p ^ k` divides `n` for every prime factor `p` of `n`.
* `Nat.Full.one_right` — `1` is `k`-full for every `k`.

## Mathlib declarations used

* `List.sum_nil`, `List.sum_singleton`, `List.sum_cons`, `List.length` and `List.mem_cons`,
  all reached through `simp`.

## Prior contributions

None for this target. The two existing contributions under `erdos-100` are unrelated: they
concern planar distance sets, share no declaration name, and this file imports neither.

## Literature

Not used. The four lemmas are direct consequences of the definition, so Heath-Brown's result
([He88], *Ternary quadratic forms and sums of three square-full numbers*, 1988) — cited by the
problem as the settled `r = 2` case — is referenced only to say what `sumOfRPowerful_add` is a
base case for, and is not relied on.

## Note

This is a test submission created to verify that the dispatched index rebuild runs after an
automatic merge, and that a new target appears in `contributions/index.md`. The Lean it
contains is nonetheless complete and proved, with no `sorry` and no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.
