# Provenance and intended use

Original, standalone Lean 4 formalization of the Erdős–Selfridge (1967) variant for [Erdős Problem 889](https://www.erdosproblems.com/889) targeting `erdos-889-variants-general`.

This self-contained module unconditionally proves `Erdos889.erdos_889.variants.v0_gt_1`: for every natural number `n ∉ {0, 1, 2, 3, 4, 7, 8, 16}`, `1 < v₀ n`, using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.Erdos889`)

- `v` and `v₀`: match `Erdos889.v` and `Erdos889.v₀` definitionally (`rfl`) without invoking `open Classical`.
- `two_pow_add_one_ne_three_pow`: proves `2 ^ a + 1 ≠ 3 ^ b` for `a ≥ 4` via congruences modulo `16` and `5`.
- `odd_two_pow_add_one_two_odd_primes`: proves `2 ^ a + 1` has at least two distinct odd prime factors whenever `a ≥ 5` is odd.
- `erdos_889_v0_gt_1`: handles small exceptions in `n < 17` directly and resolves `n ≥ 17` across the cases where `n` or `n + 1` is not a prime power (`k = 0` or `k = 1`) or one of `{n, n + 1}` equals `2 ^ a` (`k = 0, 1, 2`).

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«889»` alongside `Contribution.Erdos889` discharges the solved variant definitionally (`rfl`):

```lean
example : type_of% Erdos889.erdos_889.variants.v0_gt_1 :=
  Contribution.Erdos889.erdos_889_v0_gt_1
```

## Lineage and external references

- Problem statement and literature: [Erdős Problem 889](https://www.erdosproblems.com/889); P. Erdős and J. L. Selfridge (1967), [*Some problems on the prime factors of consecutive integers*](https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-11/issue-3/Some-problems-on-the-prime-factors-of-consecutive-integers/10.1215/ijm/1256054564.full), Illinois J. Math. 11, 428–430.
- Checked `main`: `0` published contributions for `erdos-889-variants-general` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
