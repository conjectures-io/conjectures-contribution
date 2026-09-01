# Sources

## Target and relation to prior work

Target `Erdos364.erdos_364` (`¬ ∃ n, Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2)`).
This supplements our earlier recognized contribution on this target (the congruence
reduction, PR #25) with the *Diophantine* side: constructive API and the reformulation
that connects the problem to consecutive powerful pairs and the abc conjecture.
Background: https://www.erdosproblems.com/364.

## Content

- `Powerful.mul` — a product of nonzero powerful numbers is powerful (no coprimality
  hypothesis, unlike Mathlib-adjacent variants).
- `sq_sub_one_powerful` — the reformulation: a powerful triple at `n` makes
  `(n+1)² − 1` powerful, i.e. yields consecutive powerful numbers `(m² − 1, m²)` —
  the shape governed by the abc conjecture (which predicts finitely many).
- `powerful_prime_pow`, `near_miss_25`, `near_miss_70225` — witness API and the two
  classical near-misses (`25 = 5²` with `24 = 2³·3` failing at 3; `70225 = 265²` with
  `70224` failing similarly), showing where naive constructions break.

## Verification

Axiom closure of every theorem exactly `propext`, `Classical.choice`, `Quot.sound` on
the pinned toolchain (Lean 4.27.0 / Mathlib `a3a10db0`); no sorry/native_decide/set_option.
