# Provenance and intended use

Original, standalone Lean 4 formalization advancing the [Gauss circle problem](https://en.wikipedia.org/wiki/Gauss_circle_problem) across `wikipedia-gausscircleproblem-error-isbigo-formalized` and `wikipedia-gausscircleproblem-error-isbigo-counterexample`.

This self-contained file unconditionally proves both `[research solved]` theorems `GaussCircleProblem.error_le` and `GaussCircleProblem.exact_form_floor` from `FormalConjectures/Wikipedia/GaussCircleProblem.lean`, using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.GaussCircleProblem`)

- `N` and `E`: match `GaussCircleProblem.N` and `GaussCircleProblem.E` definitionally.
- `error_le`: proves `|E r| ≤ 2 * √2 * π * r` for all `r ≥ 1` by tiling `(m, n) ∈ ℤ × ℤ` with disjoint axis-aligned unit squares `unitSquare m n` of Lebesgue measure `1` sandwiched between `closedBall 0 (r - √2 / 2)` and `closedBall 0 (r + √2 / 2)`.
- `exact_form_floor`: proves `(N r : ℤ) = 1 + 4 * ∑' i, (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)` for `0 ≤ r` by establishing `r₂(k) = 4 * a₂(k)` (`k ≥ 1`), proving coprime multiplicativity `a₂(m * n) = a₂(m) * a₂(n)` directly in `GaussianInt` via Euclidean GCD and Bézout, evaluating `a₂(p ^ e)` for `p = 2`, `p ≡ 3 (mod 4)`, and `p ≡ 1 (mod 4)`, summing over `1 ≤ k ≤ ⌊r ^ 2⌋₊`, and exchanging the divisor sum into the finite floor series.

## Minimal Lean usage

Importing `FormalConjectures.Wikipedia.GaussCircleProblem` alongside `Contribution.GaussCircleProblem` discharges both theorems definitionally (`rfl`):

```lean
example : type_of% GaussCircleProblem.error_le :=
  Contribution.GaussCircleProblem.error_le

example : type_of% GaussCircleProblem.exact_form_floor :=
  Contribution.GaussCircleProblem.exact_form_floor
```

## Lineage and external references

- Problem statement and references: [Wikipedia — Gauss circle problem](https://en.wikipedia.org/wiki/Gauss_circle_problem); G. H. Hardy (1959), *Ramanujan: Twelve Lectures on Subjects Suggested by His Life and Work*, Chelsea Publishing, p. 67.
- Checked `main`: `0` published contributions for `wikipedia-gausscircleproblem-error-isbigo` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
