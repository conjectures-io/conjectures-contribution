# Sources

## Target and statement

`FormalConjectures/ErdosProblems/23.lean` declares `erdos_23.variants.n1_tight`
(`∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ ∀ H ≤ G, H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card`)
under `@[category test]` with a `sorry` proof. This contribution proves exactly that
statement (restated under the `Contribution` namespace). It complements our earlier
recognized contribution on this target (`n5_tight`, the 25-vertex C₅ blow-up).

## Mathematical content

Witness `G = cycleGraph 5`: triangle-free (its 3-clique finset is empty, by `decide`
over the decidable adjacency), and any bipartite subgraph `H ≤ G` dropping no edge
would equal `G` — impossible since `chromaticNumber (cycleGraph 5) = 3`
(`SimpleGraph.chromaticNumber_cycleGraph_of_odd`) while bipartite means 2-colorable.

## Mathlib declarations used

`SimpleGraph.cycleGraph`, `SimpleGraph.cliqueFinset_eq_empty_iff`,
`SimpleGraph.chromaticNumber_cycleGraph_of_odd`, `SimpleGraph.chromaticNumber_le_iff_colorable`,
`SimpleGraph.edgeSet_ssubset_edgeSet`, `Set.exists_of_ssubset`. Axiom closure exactly
`propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain (Lean 4.27.0 /
Mathlib `a3a10db0`).
