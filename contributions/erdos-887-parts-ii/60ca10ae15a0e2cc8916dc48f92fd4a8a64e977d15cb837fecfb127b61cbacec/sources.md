# Provenance and intended use

Original, standalone Lean 4 formalization advancing [Erdős Problem 887](https://www.erdosproblems.com/887) across `erdos-887-parts-ii-formalized` and `erdos-887-parts-ii-counterexample`.

This self-contained file unconditionally proves the `[research solved]` variant `Erdos887.erdos_887.variants.rosenfeld_infinite` from Erdős and Rosenfeld (1997) using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.Erdos887`)

- `polyN (k + 25)`: degree-8 polynomial `t * (t + 1) * ... * (t + 7)` at `t = k + 25`, proved strictly monotone (`polyN_strictMono`).
- `polyD1 < polyD2 < polyD3 < polyD4`: four explicit degree-4 balanced divisors of `polyN t`, with `polyN t < polyD1 t ^ 2` ensuring `⌊√n⌋₊ < polyD1 t`, and `(t^4 + 14 t^3 + 63 t^2)^2 < polyN t`, `t^8 < polyN t`, and `polyD4 t < t^4 + 14 t^3 + 79 t^2` ensuring `polyD4 t < ⌈√n + 16 * n^(1/4)⌉₊` for every `k ≥ 0`.
- `erdos_887_rosenfeld_infinite`: witnesses `C = 16` via `Set.infinite_of_injective_forall_mem`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«887»` alongside `Contribution.Erdos887` discharges `Erdos887.erdos_887.variants.rosenfeld_infinite` definitionally (`rfl`):

```lean
example : type_of% Erdos887.erdos_887.variants.rosenfeld_infinite :=
  Contribution.Erdos887.erdos_887_rosenfeld_infinite
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 887](https://www.erdosproblems.com/887); P. Erdős and M. Rosenfeld (1997), *The factor-difference set of integers*, Acta Arith. 79, 353–359.
- Checked `main`: `0` published contributions for `erdos-887-parts-ii` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
