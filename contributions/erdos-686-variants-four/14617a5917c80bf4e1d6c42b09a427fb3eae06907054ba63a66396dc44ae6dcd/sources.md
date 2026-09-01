# Sources

## Problem

- [Erdős Problem 686](https://www.erdosproblems.com/686) — can `4` be written as
  `∏_{1≤i≤k}(m+i) / ∏_{1≤i≤k}(n+i)` for some `k ≥ 2` and `m ≥ n + k`?
- Pinned statement: `FormalConjectures/ErdosProblems/686.lean` at commit
  `379fc0298dc146df549e7061c3ede0353a5bb51f` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

## This contribution

Original elementary argument, derived and formalised for this contribution
(2026-09-01). The length-`2` case `(m+1)(m+2) = 4(n+1)(n+2)` is shown impossible
for **all** `m, n : ℕ` — with no `m ≥ n + 2` hypothesis needed — by completing the
square: any solution would force `(4n+6)² − (2m+3)² = 3`, i.e. a factorisation
`a · b = 3` with `b = 4n + 2m + 9 ≥ 9`, impossible for integers whether `a ≤ 0`
or `a ≥ 1`.

The technique (difference-of-squares descent on `x(x+1) = c·y(y+1)` products) is
classical Pell-equation folklore, e.g. treated broadly in
[Mordell, *Diophantine Equations*](https://www.sciencedirect.com/bookseries/pure-and-applied-mathematics/vol/30);
the specific statement and Lean proof are new here. It removes the `k = 2` case
from the search space of the counterexample task: any proof that no `(k, n, m)`
witness exists may now start at `k ≥ 3`, where the first open case is the
integral-point problem on the genus-one curve `u³ − u = 4(v³ − v)`
(`u = m + 2`, `v = n + 2`).

Numerical context (not part of the Lean artifact): exhaustive search for
witnesses with `k < 30` over `n ≤ 3·10⁵` (`k ≤ 4`) and `n ≤ 2·10⁴` (`k ≥ 5`)
finds none, and a density heuristic for products of `k` consecutive integers
suggests the total expected number of witnesses over all `k, n` is below `1`.
