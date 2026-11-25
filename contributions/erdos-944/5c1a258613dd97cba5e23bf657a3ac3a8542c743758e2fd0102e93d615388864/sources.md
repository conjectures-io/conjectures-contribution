# Provenance and intended use

Original, standalone Lean 4 formalization resolving **Dirac's 1970 Conjecture at `k = 4, r = 1`** for [Erdős Problem 944](https://www.erdosproblems.com/944) targeting `erdos-944` (`erdos-944-formalized` / `erdos-944-counterexample`).

This self-contained module unconditionally proves the affirmative existential claim of `Erdos944.erdos_944.variants.dirac_conjecture.k_eq_four`: there exists a graph `G` with chromatic number `4` such that every vertex is critical (`χ(G \ {v}) < 4`), yet no single edge is critical (`χ(G \ {e}) = 4` for all `e`), using targeted [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) imports only, kernel-checked `decide +kernel` certificates (zero `native_decide`), and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.

## Mathematical contents (`Contribution.Erdos944DiracK4R1`)

- `grpMul`, `grpInv`, and `G68`: construct the 68-vertex, 204-edge triangle-free Cayley graph on the semidirect product `Z_17 ⋊ Z_4` (multiplication `(a1, b1) * (a2, b2) = (a1 + 4^b1 * a2 mod 17, b1 + b2 mod 4)`, encoded as `b * 17 + a : Fin 68`) with symmetric 6-element generating set `S = {4, 13, 27, 37, 43, 57}`.
- `G68_colorable_four` and `G68_deleteVert_colorable_three`: verify one explicit proper 3-coloring of `G68 \ {0}`, lift it via left-translation automorphisms `x ↦ g * x` to 3-colorability of `G68 \ {v}` for every `v : Fin 68`, and assign color `3` to `0` for 4-colorability of `G68`.
- `checkRefut_sound`, `G68_not_colorable_three`, and `G68_deleteEdge_not_colorable_three`: verify four pruned kernel-checked refutation trees (`cert4`, `cert27`, `cert37`, `cert43`) for the four edge-orbit representatives `(0, 4)`, `(0, 27)`, `(0, 37)`, and `(0, 43)` via `decide +kernel`, and lift non-3-colorability to all 204 edges of `G68` by left translation (which also implies `¬ G68.Colorable 3`).
- `dirac_k4_r1_bridge`: lifts `G68` to `ULift.{u} (Fin 68)` to discharge `∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 4 1` definitionally (`rfl`).

## Minimal Lean usage

Importing `FormalConjectures.ErdosProblems.«944»` alongside `Contribution.Erdos944DiracK4R1` discharges `Erdos944.erdos_944.variants.dirac_conjecture.k_eq_four` (with `answer(True)`) definitionally (`rfl`):

```lean
example : ∃ (V : Type u) (G : SimpleGraph V), Erdos944.SimpleGraph.IsErdos944 G 4 1 :=
  Contribution.Erdos944DiracK4R1.dirac_k4_r1_bridge
```

## Lineage and external references

- Independent discovery: the 68-vertex, 204-edge `Z_17 ⋊ Z_4` Cayley witness was independently discovered by our offline C++20 OpenMP Cayley/critical-graph solver (`hunt_944_k4`) and verified independently before Lean 4 formalization.
- Scholarly provenance: [Erdős Problem 944](https://www.erdosproblems.com/944); G. A. Dirac (1970) conjecture on `k`-vertex-critical graphs without critical edges; and the September 2026 NBER/HBS resolution of Dirac's `k = 4` conjecture ([NBER Working Papers](https://www.nber.org/papers)).
- Checked `main`: `0` published contributions for `erdos-944` (`parents: []`).
- Original Lean 4 formalization built solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the standard axioms `[propext, Classical.choice, Quot.sound]`.
