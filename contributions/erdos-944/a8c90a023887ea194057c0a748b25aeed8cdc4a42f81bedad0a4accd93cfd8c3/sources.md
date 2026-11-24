# Provenance and intended use

Original, standalone Lean 4 formalization advancing [Erdős Problem 944](https://www.erdosproblems.com/944) across [`erdos-944-formalized`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-944-formalized) and [`erdos-944-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-944-counterexample).

This self-contained file constructs an explicit 17-vertex witness proving the `k = 5, r = 1` case of Dirac's conjecture (`Erdos944.erdos_944.variants.dirac_conjecture.k_eq_5`), using targeted Mathlib imports only and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`. For `erdos-944-formalized`, downstream proofs obtain a verified `5`-vertex-critical graph with no critical edge in any universe `Type u`; for `erdos-944-counterexample`, `(k, r) = (5, 1)` is unconditionally ruled out.

## Mathematical contents (`Contribution.Erdos944DiracK5R1`)

- `C17`: the 17-vertex circulant graph `C_17(1, 3, 4, 5)` on `Fin 17` (`68` edges, cyclic difference set `{±1, ±3, ±4, ±5}`).
- `C17_colorable_five` & `C17_deleteVert_colorable_four`: explicit 4-coloring of `C17 \ {0}` extended to a 5-coloring of `C17` and translated across all vertices `v : Fin 17` by cyclic shift `sub17 x v`.
- `no_indep_five_C17` & `no_indep_five_C17_deleteEdge`: proves `α(C17) ≤ 4` and `α(C17 \ {e}) ≤ 4` for every edge `e` by reducing to the non-neighbors of `0` (`70` sorted 4-tuples) and common non-neighbors across the four edge orbits `d ∈ {1, 3, 4, 5}` (`22` sorted 3-tuples), verified in the Lean kernel by `decide`.
- `C17_not_colorable_four` & `C17_deleteEdge_not_colorable_four`: pigeonhole on color classes over `Fin 17`.
- `dirac_k5_r1_bridge`: universe-polymorphic lift to `ULift.{u} (Fin 17)` proving `G.IsCritical 5` and `∀ edges, G.IsCriticalEdges edges → 1 < edges.ncard`.

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«944»` together with this declaration discharges `Erdos944.erdos_944.variants.dirac_conjecture.k_eq_5` directly:

```lean
universe u
example : ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 5 1 :=
  Contribution.Erdos944DiracK5R1.dirac_k5_r1_bridge.{u}
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 944](https://www.erdosproblems.com/944); G. A. Dirac (1970) conjecture; J. I. Brown (1992), *A vertex critical graph without critical edges*, Discrete Math. 102, 99–101; J. J. Lattanzio (2002), Discrete Math. 258, 323–330.
- The 17-vertex circulant `C_17(1, 3, 4, 5)` was identified via local Python search as a compact 5-critical, edge-non-critical witness; the Python script is not a proof dependency.
- Checked `main`: `0` published contributions for `erdos-944` (`parents: []`).
- Built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard axioms `[propext, Classical.choice, Quot.sound]`.
