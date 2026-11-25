# Provenance and intended use

Original, standalone Lean 4 formalization of `erdos_942.variants.limsup` for [Erdős Problem 942](https://www.erdosproblems.com/942) targeting `erdos-942`.

This self-contained module unconditionally proves `Erdos942.erdos_942.variants.limsup` — `limsup_{n → ∞} h(n) = ⊤` where `h(n)` counts powerful numbers in `[n^2, (n + 1)^2)` — using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.Erdos942`)

- `Full`, `Powerful`, `Powerful.decide`, and `erdos_942_h`: match `FormalConjecturesForMathlib.Data.Nat.Full` and `Erdos942.erdos_942.h` definitionally (`rfl`) without invoking `open Classical`.
- `powerful_cube_mul_sq` and `cube_mul_sq_ne`: show `p ^ 3 * x ^ 2` is powerful for every prime `p` and distinct for distinct primes by comparing the parity of `padicValNat`.
- `exists_large_h` and `erdos_942_limsup`: apply Dirichlet's pigeonhole principle to the fractional parts of `(N / √(p_j^3))` across `2K` distinct primes to place `2K` distinct powerful integers inside `[(d - 1)^2, (d + 1)^2)`, yielding infinitely many `m` with `h(m) ≥ K` and hence `limsup h = ⊤`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«942»` alongside `Contribution.Erdos942` discharges the solved variant definitionally (`rfl`):

```lean
example : type_of% Erdos942.erdos_942.variants.limsup :=
  Contribution.Erdos942.erdos_942_limsup
```

## Lineage and external references

- Problem statement and background: [Erdős Problem 942](https://www.erdosproblems.com/942); [Powerful number](https://en.wikipedia.org/wiki/Powerful_number).
- Checked `main`: `0` published contributions for `erdos-942` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
