# Provenance and intended use

Original, standalone Lean 4 formalization of `claim2_inequality` for [Erdős Problem 317](https://www.erdosproblems.com/317) targeting `erdos-317-variants-claim2`.

This self-contained module unconditionally proves `Erdos317.claim2_inequality`: for all sufficiently large `n` (in fact all `n ≥ 1`), any nonzero signed harmonic sum `∑ k : Fin n, δ k / (k + 1)` with `δ k ∈ {-1, 0, 1}` is at least `1 / lcm(1, ..., n)`, using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.Erdos317`)

- `claim2_inequality`: matches `Erdos317.claim2_inequality` definitionally (`rfl`).
- Clearing all denominators by multiplying by `L = (Finset.Icc 1 n).lcm id` produces a nonzero integer `M`, giving `1 ≤ |M| = L * lhs` and hence `lhs ≥ 1 / L`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«317»` alongside `Contribution.Erdos317` discharges the lemma definitionally (`rfl`):

```lean
example : type_of% Erdos317.claim2_inequality :=
  Contribution.Erdos317.claim2_inequality
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 317](https://www.erdosproblems.com/317); P. Erdős and R. L. Graham (1980), [*Old and New Problems and Results in Combinatorial Number Theory*](https://mathweb.ucsd.edu/~ronspubs/80_11_old_and_new.pdf), Monographies de L'Enseignement Mathématique 28.
- Checked `main`: `0` published contributions for `erdos-317-variants-claim2` (`parents: []`).
- Original work built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
