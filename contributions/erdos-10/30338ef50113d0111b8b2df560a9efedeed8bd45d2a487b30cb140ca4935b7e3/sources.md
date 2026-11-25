# Provenance and intended use

Original, standalone Lean 4 formalization advancing [Erdős Problem 10](https://www.erdosproblems.com/10) across `erdos-10-formalized` and `erdos-10-counterexample`.

This self-contained file unconditionally proves both unproved `[research solved]` variants in `FormalConjectures/ErdosProblems/10.lean` using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`, and deduces a lower-threshold refutation for `k ≤ 3`.

## Mathematical contents (`Contribution.Erdos10`)

- `sumPrimeAndTwoPows`: matches `Erdos10.sumPrimeAndTwoPows` definitionally.
- `erdos_10_two_pows`: proves `Set.Infinite <| {n : ℕ | Even n} \ sumPrimeAndTwoPows 2` using Erdős's 1950 covering-system arithmetic progression `erdosN t = 399097567 + 984263280 * t + 1`:
  - `p = 2` is excluded modulo `16` (`(erdosN t - 2) % 16 = 14`, unreachable by a sum of at most two powers of `2`).
  - `card = 0` fails by parity; `card = 1` reduces to `p = erdosM t` which is divisible by `11` (`11 < erdosM t`).
  - `card = 2` reduces to `p + 2 ^ c = erdosM t`, where all residues modulo `24` are covered by the prime moduli `{3, 5, 7, 13, 17, 241}` with quotient check `q % 16 ≠ 15`.
- `erdos_10_grechuk_example`: proves `1117175146 ∉ sumPrimeAndTwoPows 3`:
  - `p = 2` is excluded modulo `512` (`1117175144 % 512 = 360`, unreachable by at most three powers of `2` via `no_triple_mod_512`).
  - For odd primes `p`, parity forces `p = 1117175145 = 3 * 372391715` (`card = 1`), `p = 1117175143 = 7 * 159596449` (all-ones `card = 3`), or explicit factor witnesses verified in-kernel via `decide` (`wit2` for `1 ≤ b ≤ 30` and `wit3` for `1 ≤ b ≤ c ≤ 30`) together with `Nat.not_prime_mul`.
- `sumPrimeAndTwoPows_mono` and `erdos_10_false_for_k_le_three`: proves `sumPrimeAndTwoPows k ≠ Set.univ \ {0, 1}` for every `k ≤ 3`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«10»` alongside `Contribution.Erdos10` discharges both solved variants definitionally (`rfl`):

```lean
example : type_of% Erdos10.erdos_10.variants.two_pows :=
  Contribution.Erdos10.erdos_10_two_pows

example : type_of% Erdos10.erdos_10.variants.grechuk_example :=
  Contribution.Erdos10.erdos_10_grechuk_example
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 10](https://www.erdosproblems.com/10); P. Erdős (1950), *On integers of the form 2^k + p and some related problems*, Summa Brasil. Math. 2, 113–123 (covering system for `k = 2`); Bogdan Grechuk's example `1117175146` (`k = 3`).
- Checked `main`: `0` published contributions for `erdos-10` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
