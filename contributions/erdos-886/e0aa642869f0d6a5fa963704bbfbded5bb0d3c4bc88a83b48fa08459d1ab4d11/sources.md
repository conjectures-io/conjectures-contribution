# Provenance and intended use

Original, standalone Lean 4 formalization advancing [Erdős Problem 886](https://www.erdosproblems.com/886) across `erdos-886-formalized` and `erdos-886-counterexample`.

This self-contained file unconditionally proves both unproved `[research solved]` variants in `FormalConjectures/ErdosProblems/886.lean` from Erdős and Rosenfeld (1997) using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.Erdos886`)

- `Erdos886Divisors`: matches `Erdos886.Erdos886Divisors` definitionally (including the exact `Finset.filter` decidability instance via `Real.decidableLT`).
- `erdos_886_rosenfeld_bound`: proves that for every `C > 0` and all `n ≥ 1`, at most `1 + C ^ 2` divisors `d ∣ n` lie in `[n ^ (1 / 2), n ^ (1 / 2) + C * n ^ (1 / 4)]`:
  - Uses the map `d ↦ d + n / d`, proved injective on the divisor subset `S` via `((d₁ - d₂) * (d₁ * d₂ - n) = 0)` and `n ^ (1 / 2) ≤ d₁, d₂`.
  - Uses `((d + n / d) - 2 n ^ (1 / 2)) * d = (d - n ^ (1 / 2)) ^ 2` to place every image integer in `[2 n ^ (1 / 2), 2 n ^ (1 / 2) + C ^ 2]`, bounding `S.card` by `T.max' - T.min' + 1 ≤ 1 + C ^ 2`.
- `erdos_886_rosenfeld_infinite`: proves `Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card}` via the injective degree-8 polynomial family `polyN (k + 25) = ∏ i ∈ [0, 7], (k + 25 + i)` and its four explicit balanced divisors `polyD1 < polyD2 < polyD3 < polyD4` strictly contained in `(n ^ (1 / 2), n ^ (1 / 2) + 16 * n ^ (1 / 4))`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«886»` alongside `Contribution.Erdos886` discharges both solved variants definitionally (`rfl`):

```lean
example : type_of% Erdos886.erdos_886.variants.rosenfeld_bound :=
  Contribution.Erdos886.erdos_886_rosenfeld_bound

example : type_of% Erdos886.erdos_886.variants.rosenfeld_infinite :=
  Contribution.Erdos886.erdos_886_rosenfeld_infinite
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 886](https://www.erdosproblems.com/886); P. Erdős and M. Rosenfeld (1997), *The factor-difference set of integers*, Acta Arith. 79, 353–359.
- Checked `main`: `0` published contributions for `erdos-886` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
