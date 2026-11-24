# Provenance and intended use

Original, standalone Lean 4 formalization advancing [Erdős Problem 287](https://www.erdosproblems.com/287) across [`erdos-287-formalized`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-287-formalized) and [`erdos-287-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-287-counterexample).

This self-contained file unconditionally proves Erdős's 1932 theorem `2 ≤ max_gap k s` (`Erdos287.erdos_287.variants.gap_at_least_two`), using targeted Mathlib imports only and the standard Lean axioms `[propext, Classical.choice, Quot.sound]`. For `erdos-287-formalized`, this discharges the `sorry` variant `erdos_287.variants.gap_at_least_two` directly and reduces `3 ≤ max_gap k s` to excluding `max_gap k s = 2`; for `erdos-287-counterexample`, any counterexample must achieve `max_gap k s = 2`.

## Mathematical contents (`Contribution.Erdos287GapAtLeastTwo`)

- `two_adic_between`: between any two distinct nonzero natural numbers `m < n` having the same `2`-adic valuation `v`, there exists an intermediate integer `m < t < n` with strictly larger `2`-adic valuation `v < padicValNat 2 t`.
- `no_consecutive_recip_sum`: for any `a ≥ 2` and `k ≥ 2`, `∑ i ∈ Finset.range k, (1 : ℚ) / (a + i) ≠ 1`, proved via existence of a unique index `j < k` maximizing `padicValNat 2 (a + j)` combined with `padicValRat.lt_sum_of_lt` and `padicValRat.add_eq_of_lt`.
- `gap_at_least_two`: proves `2 ≤ max_gap k s` for every strictly increasing `s : Fin k → ℕ` (`k ≥ 2`, `1 < s ⟨0, _⟩`) with `∑ i, 1 / (s i : ℝ) = 1`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«287»` together with this declaration discharges `Erdos287.erdos_287.variants.gap_at_least_two` directly:

```lean
example : type_of% Erdos287.erdos_287.variants.gap_at_least_two :=
  Contribution.Erdos287GapAtLeastTwo.gap_at_least_two
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 287](https://www.erdosproblems.com/287); P. Erdős (1932), *Egy Kürschák-féle elemi számelméleti tétel általánosítása*, Mat. Fiz. Lapok 39, 17–24 (proving `1` cannot be a sum of reciprocals of consecutive integers).
- Checked `main`: `0` published contributions for `erdos-287` (`parents: []`).
- Built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard axioms `[propext, Classical.choice, Quot.sound]`.
