# Sources

## Target and statement

Target `erdos-23`
(`FormalConjectures/ErdosProblems/23.lean`, theorem `Erdos23.erdos_23`):
every triangle-free graph on `5 * n` vertices can be made bipartite by
deleting at most `n ^ 2` edges. Background:
https://www.erdosproblems.com/23.

This contribution proves, in the `Contribution.Erdos23` namespace, a
self-contained lemma toward that target:

`bipartization_bound`: if `G` is triangle-free on `5 * n` vertices, there is a
bipartite spanning subgraph `H ≤ G` with `8 * |E(G) \ E(H)| ≤ 25 * n ^ 2`
— i.e. at most `25n²/8` deletions, a weaker constant than the conjectured
`n²`, proved via the random-bipartition technique the eventual solution must
use. It complements the two existing contributions on this target (tightness
of the `n = 1` and `n = 5` cases), which exhibit extremal examples; this one
is a proof-technique lemma for the upper bound.

## Mathematical content

1. **Random cut** (`exists_cut_half`): for every finite graph `G` some
   bipartition `f : V → Bool` keeps at least half the edges. Proved by double
   counting: sum `|cutFinset G f|` over all `2^|V|` colorings; a flip
   involution pairs colorings so each edge is cut by exactly half of them
   (`card_filter_ne`). Hence the average cut is `|E|/2`, so some cut attains
   it. The spanning subgraph of cut edges is bipartite by construction
   (witness: `Coloring.mk f`).
2. **Mantel's theorem** (`mantel`): a triangle-free graph satisfies
   `4 * |E| ≤ |V|²`, proved from `degree_add_le_of_adj` (adjacent vertices
   have disjoint neighbor sets) and `sum_degree_sq_eq`.
3. **Combination**: deletions `= |E| − |cut| ≤ |E|/2 ≤ (5n)²/8 = 25n²/8`.

## Mathlib declarations used

`SimpleGraph.edgeFinset`, `SimpleGraph.CliqueFree`, `SimpleGraph.IsBipartite`,
`SimpleGraph.Coloring`, `Sym2`, `Finset.card_sdiff`, `Finset.filter_subset`,
`Finset.sum_comm`, `Finset.mul_sum`.

## Axioms and toolchain

No `sorry`/`admit`/`axiom`/`native_decide`. The closure of every declaration
is exactly `propext`, `Classical.choice`, `Quot.sound` (the permitted axioms
of the target). Elaborated cleanly with `lake env lean` against
`leanprover/lean4:v4.35.0-rc2` + mathlib `v4.35.0-rc2` (zero output, no
warnings) on 2026-10-31.

## References

- https://www.erdosproblems.com/23
- https://conjectures.io/problems/erdos23-erdos-23
- Balogh–Clemen–Lidický, "Max Cuts in Triangle-free Graphs":
  https://arxiv.org/abs/2103.14179
- The standard random-bipartition / maximal-cut argument, e.g. Diestel,
  *Graph Theory*, Proposition 1.2.2 (every graph has a bipartite spanning
  subgraph with at least half the edges).
- Mantel's theorem (1907); the two existing `erdos-23` contributions
  (tightness of `n = 1` and `n = 5` by contributor `5FqLp5…FfZZiK`).
