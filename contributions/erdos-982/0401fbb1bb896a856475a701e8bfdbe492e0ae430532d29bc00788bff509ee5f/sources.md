# Sources and provenance — partial contribution to `erdos-982`

## Target

`Erdos982.erdos_982`, from
[`FormalConjectures/ErdosProblems/982.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/982.lean):
if `p : Fin n → ℝ²` with `3 ≤ n` is injective and `EuclideanGeometry.IsConvexPolygon p`, then
some vertex `i` satisfies `{ d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2`.
This is Erdős' 1946 conjecture that every `n`-point set in convex position has a point
determining at least `⌊n/2⌋` distinct distances to the others; it is open.

## The obstacle this contribution attacks

Two shape problems block any attempt before the geometry starts.

1. **The goal is a `Set.ncard` of a set-builder set of reals.** `Set.ncard` is `0` on infinite
   sets, so nothing can be said about
   `{ d : ℝ | ∃ j, j ≠ i ∧ d = dist (p i) (p j) }.ncard` until that set has been identified
   with a `Finset`, and no counting tool in Mathlib — pigeonhole, fibrewise cardinality,
   double counting — accepts a set in this shape. Every known argument for this problem is a
   counting argument, so the conversion is on the critical path and has to be repeated at
   every vertex. The associated ℕ-arithmetic (`R < n / 2` implies `2 * R < n - 1`, with
   truncated subtraction and floor division) is easy to get wrong.
2. **`EuclideanGeometry.IsConvexPolygon` is a disjunction.** It unfolds to
   `IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i ↦ p (-i)`, while every usable convexity
   fact in the pinned environment (`IsCcwConvexPolygon.sign_oangle` and its companions in
   `FormalConjecturesForMathlib/Geometry/2d.lean`) is stated for the counter-clockwise branch
   only. A solver who `rcases`es on it must run the whole geometric argument twice, the second
   time through the index reversal `i ↦ -i`.

## The delta (what the file adds)

A small, coherent API around the target's own objects, in namespace
`Contribution.Erdos982DistinctDistances` (21 declarations, all proved):

* `distFinset p i` — the `Finset` of distances from `p i` to the other vertices (the `R(x_i)`
  of the problem), with `mem_distFinset`, `coe_distFinset` and the load-bearing bridge
  `ncard_eq_card_distFinset`, which states that the target's `Set.ncard` *is* a `Finset.card`.
  `card_distFinset_le` and `one_le_card_distFinset` are the trivial bounds; the latter is what
  discharges the degenerate cases `n ≤ 3`.
* `equidistFinset p i d` — the fibre of `j ↦ dist (p i) (p j)`, i.e. the vertices `j ≠ i` on
  the circle of radius `d` centred at `p i`, with `mem_equidistFinset`.
* Counting: `sub_one_le_mul_card_distFinset` (if no circle centred at `p i` carries more than
  `k` other vertices then `n - 1 ≤ k * #(distFinset p i)`), the pigeonhole form
  `exists_lt_card_equidistFinset`, and `half_le_card_distFinset`, which *proves the target's
  bound at any vertex whose distance fibres have size at most 2*.
  `erdos_982_of_forall_card_equidistFinset_le_two` states that consequence in the reward
  theorem's own shape, for an arbitrary family of points, with no convexity used.
* The contrapositive, which is the real handoff: `exists_three_equidistant_of_ncard_lt` and its
  unpacked form `exists_triple_equidistant_of_ncard_lt` — a vertex failing the bound of Erdős
  982 has three *named, pairwise distinct* further vertices at a common distance from it. All
  of the floor-division arithmetic lives here and is done once.
* Geometry: `ne_of_lt_of_isCcwConvexPolygon` / `injective_of_isCcwConvexPolygon` /
  `injective_of_isConvexPolygon` show that for `3 ≤ n` **the reward theorem's hypothesis
  `Function.Injective p` is redundant** — a repeated vertex makes one of the oriented angles
  `∡` degenerate, so its sign is `0`, not `1`. This is not in the pinned environment; the
  three degenerate-angle cases are `oangle_self_left`, `oangle_self_right` and
  `oangle_self_left_right`, selected by the position of the third index.
* `distFinset_comp_equiv` (the distance set at a vertex is invariant under relabelling) plus
  the injectivity result power `erdos_982_of_isCcwConvexPolygon`: **it suffices to prove
  Erdős 982 for counter-clockwise polygons.**
* Worked use sites with the reward theorem's binders: `erdos_982_three` proves the case
  `n = 3` outright, and `erdos_982_of_ccw_reduced` combines both reductions, leaving a goal in
  which neither `Set.ncard` nor the convexity disjunction nor the injectivity hypothesis
  appears, and in which the equidistant triple at every vertex is already given for free.

Why this is the useful API and not an arbitrary one: the published partial results on this
conjecture (Dumitrescu's `13n/36 - O(1)` and its improvement to `(13/36 + ε)n - O(1)` by
Nivasch–Pach–Pinchasi–Zerbib) proceed by bounding the number of *isosceles triangles* spanned
by the point set, and an isosceles triangle with apex `p i` is exactly an unordered pair inside
one `equidistFinset p i d`. The fibres introduced here are the objects those arguments count.

## Novelty relative to Mathlib and to the pinned environment

Checked by grepping the pinned Mathlib source and by trying the goals directly:

* `IsCcwConvexPolygon` / `IsConvexPolygon` exist only in
  `FormalConjecturesForMathlib/Geometry/2d.lean`; that file contains the `sign_oangle`
  variants, the three-point characterisations and `isConvexPolygon_triangle`, but **no**
  injectivity lemma and **no** reindexing lemma, so the geometric results here are new.
* The generic counting statement behind `sub_one_le_mul_card_distFinset` is Mathlib's
  `Finset.card_le_mul_card_image`
  (<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean>);
  the specialisation is proved *through* it and says so in its docstring. The delta is the
  `n - 1` on the left and a hypothesis quantified over all radii `d : ℝ` rather than over the
  members of an image — which is the form in which "no `k + 1` vertices are equidistant from
  `p i`" is actually available.
* An earlier draft defined its own index-reversal equivalence; that was dropped in favour of
  Mathlib's `Equiv.neg` once it was found, precisely to avoid restating an existing
  declaration.
* Nothing here duplicates `EuclideanGeometry.distinctDistancesFrom` or
  `minimalDistinctDistances` from `2d.lean`: those are defined on a `Finset ℝ²` of points,
  whereas the reward statement is indexed by `Fin n` and excludes the vertex itself.

## Verification

* Compiles with **zero errors and zero warnings** against the pinned workspace
  (`leanprover/lean4:v4.27.0`, Mathlib `v4.27.0`) via
  `lake env lean CW_erdos_982.lean`, including with the repository's own options
  (`autoImplicit=false`, `relaxedAutoImplicit=false`, `linter.style.namespace=true`,
  `linter.style.moduleDocstring=true`).
* `#print axioms` was run on all 21 declarations while drafting: each depends only on
  `[propext, Classical.choice, Quot.sound]` (`negEquiv`, before removal, on a subset). The
  `#print` lines were then deleted and the file recompiled clean. No `sorry`, `admit`,
  `axiom`, `native_decide`, `#eval`, `unsafe`, `partial`, or `set_option` anywhere.
* Statement-drift and semantics checks were run in a throwaway probe file (not part of the
  submission): the restated reward goal is literally inhabited by `Erdos982.erdos_982` itself;
  `erdos_982_three` is accepted as the reward theorem at `n = 3`; `distFinset` and
  `equidistFinset` were computed on an explicit constant family to confirm they mean what the
  docstrings claim; and the hypotheses of the conditional theorems were shown to be
  satisfiable, so none of them is vacuous.

## References

* Erdős Problem 982 — <https://www.erdosproblems.com/982>
* The formal statement — <https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/982.lean>
* E. Altman, *On a problem of P. Erdős*, Amer. Math. Monthly **70** (1963), 148–157 (a convex
  `n`-gon determines at least `⌊n/2⌋` distinct distances overall — the weaker, solved,
  companion of this problem).
* G. Nivasch, J. Pach, R. Pinchasi and S. Zerbib, *The number of distinct distances from a
  vertex of a convex polygon*, J. Comput. Geom. **4** (2013), 1–12 —
  <https://arxiv.org/abs/1207.1266> (best known bound `(13/36 + ε)n - O(1)`; the main
  ingredient is a bound on the number of isosceles triangles, i.e. on the fibres formalised
  here as `equidistFinset`).
* A. Dumitrescu's earlier `13n/36 - O(1)` bound, as cited in the above.
* Mathlib source consulted for novelty and for the lemmas specialised here:
  `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` (`card_le_mul_card_image`),
  `Mathlib/Data/Set/Card.lean` (`Set.ncard_coe_finset`),
  `Mathlib/Geometry/Euclidean/Angle/Oriented/Affine.lean` (`oangle_self_left`,
  `oangle_self_right`, `oangle_self_left_right`), `Mathlib/Data/Finset/Card.lean`
  (`exists_subset_card_eq`, `card_eq_three`) — <https://github.com/leanprover-community/mathlib4>.

## AI assistance disclosure

This contribution was produced with AI assistance: the Lean source, its docstrings and this
provenance note were drafted by Anthropic's Claude (Claude Code) working interactively against
the pinned `formal-conjectures` workspace, with every declaration compiled and its axiom
dependencies checked before submission. The mathematical content (the distance-set/fibre API,
the redundancy of the injectivity hypothesis, and the reduction to counter-clockwise polygons)
is original to this submission and was not copied from another contribution, from the
`formal-conjectures` repository, or from any other Lean source; the two lemmas that specialise
existing Mathlib results are identified as such above and in the file itself. The literature
context (Altman; Nivasch–Pach–Pinchasi–Zerbib; Dumitrescu) was obtained from the arXiv abstract
linked above; the erdosproblems.com page itself returned HTTP 403 to automated fetching and was
not read directly, so the attribution of the problem follows the arXiv abstract and the pool
file's own reference.
