# Sources

## Target

- `Green18.green_18` in `FormalConjectures/GreensOpenProblems/18.lean`, pinned via the
  `conjectures` submodule: for every finite group `G` and every `α`-dense `A ⊆ G × G`, are there
  `≫_α |G|³` *naive corners* `(x, y), (gx, y), (x, gy)`, `g ≠ 1`? Background: Ben Green,
  "100 open problems", Problem 18
  (<https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.18>); Tim Austin,
  "Ajtai–Szemerédi theorems over quasirandom groups", Question 2 (2016); József Solymosi,
  "Roth-type theorems in finite groups", European J. Combin. 34 (2013) 1454–1458, Theorem 2.1.
- Checked before writing: `contributions/green-18/` had no prior contributions.

## What is proved here (all kernel-checked; axioms: propext, Classical.choice, Quot.sound only)

The pinned file states Solymosi's theorem for *BMZ corners* `(x, y), (xg, y), (x, gy)` as
`green_18.bmz_corners` (category "research solved") but leaves it unproved. This contribution
proves it, and derives the target statement for abelian groups.

- `triangleIndices A = {(x, y, x·y) : (x, y) ∈ A}` — the trivial (`g = 1`) BMZ corners, used as
  triangle indices for Mathlib's `SimpleGraph.TripartiteFromTriangles.graph` on `G ⊕ G ⊕ G`. The
  edges are `x ~ y ⟺ (x, y) ∈ A`, `y ~ w ⟺ (w y⁻¹, y) ∈ A`, `x ~ w ⟺ (x, x⁻¹ w) ∈ A`.
- `instExplicitDisjoint` — the `|A|` explicit triangles are edge-disjoint (cancellation in `G`).
- `farFromTriangleFree_graph` — if `|A| ≥ ε|G|²` the graph is `ε/9`-far from triangle-free
  (`TripartiteFromTriangles.farFromTriangleFree`, since `(3|G|)² = 9|G|²`).
- **`cliqueFinset_subset_image`** — the new ingredient for the *counting* version: every triangle
  of the graph is the explicit triangle `{in₀ x, in₁ y, in₂ (x g y)}` of an extended BMZ corner
  `(x, y, g)` with `g = x⁻¹ w y⁻¹` (via `graph_triple` and the adjacency characterisations).
  Hence `#triangles ≤ #extCorners A` (`card_cliqueFinset_le`).
- `card_extCorners_le` — dropping the `g = 1` corners costs at most `|G|²`:
  `#extCorners A ≤ numBmzCorners A + |G|²`.
- **`bmz_corners_theorem`** — Solymosi's theorem, in exactly the pinned form:
  `∀ α > 0, ∃ c > 0, ∃ m₀, ∀ G [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)),
  |G| ≥ m₀ → |A| ≥ α|G|² → numBmzCorners A ≥ c|G|³`, with the explicit constants
  `c = 27δ/2`, `m₀ = ⌈2/(27δ)⌉`, `δ = triangleRemovalBound (α/9)`. Proof: the removal lemma
  (`FarFromTriangleFree.le_card_cliqueFinset`) gives `≥ δ(3|G|)³ = 27δ|G|³` triangles, of which
  at most `|G|²` are trivial.
- `numNaiveCorners_eq_numBmzCorners` — in a commutative group the two corner counts coincide.
- **`naive_corners_of_comm`** — the right-hand side of `green_18` with `Group` weakened to
  `CommGroup`: the target holds for every finite abelian group (Ajtai–Szemerédi, counting form).

## Why this helps someone attacking the target

Green 18 is open precisely because naive corners are *not* a triangle-removal pattern in a
nonabelian group: the third point `(x, gy)` involves `g = (gx)x⁻¹`, so no auxiliary vertex makes
all three conditions depend on two vertices each (for BMZ corners `w = xgy` works, which is the
whole content of Solymosi's trick). This file makes that boundary precise in Lean: everything up
to and including the abelian case is now kernel-checked, the removal-lemma constants are explicit,
and any future attack on the nonabelian case (Austin's quasirandom argument, or a reduction along
a normal series) can build on `cliqueFinset_subset_image` / `bmz_corners_theorem` directly.

**Caveats, stated explicitly:** nothing here touches the nonabelian naive case, which remains open.
The constants are tower-type (from `SzemerediRegularity.bound`), as in Mathlib's own corners
theorem. The Lean file claims exactly the declarations listed above (2 definitions, 1 instance,
7 lemmas/theorems).

## Mathlib declarations used

`SimpleGraph.TripartiteFromTriangles.graph`, `.ExplicitDisjoint`, `.farFromTriangleFree`,
`.graph_triple`, `.Graph.in₀₁_iff`, `.Graph.in₀₂_iff`, `.Graph.in₁₂_iff`,
`SimpleGraph.FarFromTriangleFree.le_card_cliqueFinset`, `SimpleGraph.triangleRemovalBound`,
`SimpleGraph.triangleRemovalBound_pos`, `SimpleGraph.mem_cliqueFinset_iff`,
`SimpleGraph.is3Clique_iff`, `Sum3.in₀/in₁/in₂`, `Fintype.card_sum`, `Finset.card_map`,
`Finset.card_le_card`, `Finset.card_image_le`, `Finset.card_filter_add_card_filter_not`,
`Finset.card_le_card_of_injOn`, `Fintype.card_prod`, `Nat.le_ceil`, `mul_right_cancel`,
`mul_left_cancel`, the `group` tactic.

## Toolchain

Validated against the pool pin `8432eac9` (upstream Formal Conjectures `7d1a8c99`): Lean `v4.33.1`, Mathlib `0df444a`. Compiles with no warnings; axioms `propext`, `Classical.choice`, `Quot.sound` only.
