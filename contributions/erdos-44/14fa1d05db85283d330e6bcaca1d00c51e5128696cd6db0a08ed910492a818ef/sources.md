# Sources

## Target and statement

`FormalConjectures/ErdosProblems/44.lean` declares `maxSidonSubsetCard_icc_bound`
(`maxSidonSubsetCard (Icc 1 N) ≤ 2·√N`) under `@[category textbook]` with a `sorry`
proof (reference in the file: arXiv:2103.15850). This contribution proves exactly that
statement (restated under the `Contribution` namespace), the standard counting bound the
open target refines. Background: https://www.erdosproblems.com/44.

## Method

For a Sidon `B ⊆ {1,…,N}` of size `k`, pairwise differences of the `k(k−1)/2`
two-element subsets are injective (the Sidon condition applied to `b + c = d + a`) and
land in `{1,…,N−1}`, giving `k(k−1) ≤ 2(N−1)+1`; with `k ≤ N` this yields
`k² ≤ 4N`, i.e. `k ≤ 2√N`. The difference of a pair `{a,b}` is extracted by the total
map `s ↦ 2·s.sup id − s.sum id` (`= max − min`), avoiding partial `min'`/`max'`.

## Mathlib declarations used

`Finset.card_le_card_of_injOn`, `Finset.card_powersetCard`, `Nat.choose_two_right`,
`Finset.card_eq_two`, `Finset.sum_pair`, `Finset.exists_mem_eq_sup`, `Real.le_sqrt`,
`Real.sqrt_mul`; tactics `omega`, `nlinarith`, `push_cast`. Axiom closure exactly
`propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain (Lean 4.27.0 /
Mathlib `a3a10db0`).
