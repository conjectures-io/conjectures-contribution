# Sources and provenance — Erdős 108, the case `k = 2`

## Target

* Problem: [erdosproblems.com/108](https://www.erdosproblems.com/108) (Erdős–Hajnal): for every
  `r ≥ 4` and `k ≥ 2`, is there a finite `f(k, r)` such that every graph of chromatic number
  `≥ f(k, r)` contains a subgraph of girth `≥ r` and chromatic number `≥ k`?
* Reward theorem: `Erdos108.erdos_108`, in the pool file
  [`FormalConjectures/ErdosProblems/108.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/108.lean),
  tagged `@[category research open, AMS 5]`. The file contains no companion declarations, only the
  comment `-- TODO: Proof for the case r=4 and statement for the infinite case`.

## The obstacle

The problem is open for `k ≥ 3` (the case `r = 4`, arbitrary `k`, is Rödl's 1977 theorem; the
cases `r ≥ 5` are the open Erdős–Hajnal question). Nothing here touches that.

What blocks a formal treatment even of the settled part is four missing pieces:

1. `SimpleGraph.girth : ℕ` is `egirth.toNat`, so it takes the junk value `0` on an acyclic graph.
   The target's obligation `SimpleGraph.girth H.coe ≥ r` with `r ≥ 1` therefore asserts two things
   at once — a lower bound on cycle lengths *and* the existence of a cycle.
2. Building a witness `H : G.Subgraph` whose *girth* is the length of a prescribed cycle requires
   knowing that no shorter cycle hides inside the graph spanned by that cycle.
3. The target quantifies over an arbitrary `V : Type u`. The pinned Mathlib supplies the raw
   compactness statement `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` but no colouring
   corollary, and no way to view a subgraph of a subgraph of `G` as a subgraph of `G` with the
   same girth and chromatic number.
4. The pinned Mathlib has no degeneracy or greedy-colouring API at all: no Brooks-type or
   Szekeres–Wilf-type bound relating `chromaticNumber` to degrees, and no Dirac-type consequence
   ("minimum degree `d` forces a cycle of length `> d`").

## The delta

All four are removed, and the case `k = 2` of the target is then settled outright with the exact
threshold:

* `bound_two_self` : `Bound r 2 r` for every `r ≥ 3`, where `Bound r k f` is the inner statement
  of `Erdos108.erdos_108` transcribed binder for binder;
* `le_of_bound` : every `f` with `Bound r k f` and `k ≥ 2` satisfies `max r k ≤ f`;
* `bound_two_iff_le` : hence `Bound r 2 f ↔ r ≤ f` for `r ≥ 3`, i.e. `f(2, r) = r` exactly;
* `erdos_108_two` : the right-hand side of the target, written out verbatim, at `k = 2`;
* `erdos_108_rhs_of_three_le` : the whole right-hand side of the target follows from its `k ≥ 3`
  instances alone — the contribution removes the `k = 2` instances from the proof obligation.

Reusable, target-independent lemmas proved along the way (all general graph theory, all novel in
the pinned environment): `le_girth_iff`, `egirth_le_of_embedding`, `egirth_eq_of_iso`,
`girth_eq_of_iso`, `le_length_of_isCycle_spanningCoe`, `egirth_spanningCoe_toSubgraph`,
`cycleSubgraph` with its interface, `exists_coloring_on`,
`colorable_of_forall_exists_low_degree`, `exists_isCycle_of_forall_le_degree`,
`exists_isCycle_length_ge_of_le_chromaticNumber`, `colorable_of_forall_finite_subgraph_colorable`,
`exists_finite_subgraph_le_chromaticNumber`, `coeSubgraphIso`, `bound_of_boundFin`. The last is
the piece that also serves the open cases: for every `r` and `k` it removes the arbitrary vertex
type from the target.

`not_exists_isCycle_of_degree_one` is a checked boundary case: the hypothesis `2 ≤ d` of
`exists_isCycle_of_forall_le_degree` cannot be weakened to `1 ≤ d` (the complete graph on two
vertices has minimum degree 1 and no cycle).

## Mathematical background

The `k = 2` case is classical mathematics, assembled here from standard arguments and formalised
from scratch; no proof was taken from any other repository, and the pool file carries no
`formal_proof` link.

* V. Rödl, *On the chromatic number of subgraphs of a given graph*, Proc. Amer. Math. Soc. **64**
  (1977), 370–371 — the case `r = 4`. Cited as background only; it is not used or formalised here.
* G. Szekeres and H. S. Wilf, *An inequality for the chromatic number of a graph*, J. Combin.
  Theory **4** (1968), 1–3 — the degeneracy bound behind `colorable_of_forall_exists_low_degree`.
* G. A. Dirac, *Some theorems on abstract graphs*, Proc. London Math. Soc. (3) **2** (1952),
  69–81 — the longest-path argument behind `exists_isCycle_of_forall_le_degree`.
* N. G. de Bruijn and P. Erdős, *A colour problem for infinite graphs and a problem in the theory
  of relations*, Indag. Math. **13** (1951), 369–373 — the compactness behind
  `colorable_of_forall_finite_subgraph_colorable`.
* Background page on this problem:
  [mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/SubgraphsOfLargeGirth.html](https://mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/SubgraphsOfLargeGirth.html)
* A 2026 preprint listed under the same conjecture, [arXiv:2606.17901](https://arxiv.org/abs/2606.17901);
  it was not consulted and nothing here depends on it.

I could not open [erdosproblems.com/108](https://www.erdosproblems.com/108) from this environment
(the host returned HTTP 403 behind a Cloudflare interstitial), so the attribution of the `r = 4`
case to Rödl and the statement that `r ≥ 5` is open come from the standard literature and a web
search, not from the page itself. No Lean statement in the contribution depends on that
attribution; the pool file's own `research open` tag is what the docstring cites.

Mathlib references for the definitions used:
[`SimpleGraph.Girth`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Girth.html),
[`SimpleGraph.Coloring`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Coloring.html),
[`SimpleGraph.Finsubgraph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Finsubgraph.html),
[`SimpleGraph.Subgraph`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Subgraph.html).

## Novelty checks actually run

Before keeping each lemma I grepped the pinned Mathlib source tree and ran `exact?` on the
statement in the pinned environment. `exact?` failed to close every one of: `le_girth_iff`,
`egirth_le_of_embedding`, `egirth_eq_of_iso`, `length_le_card_of_isCycle`, `exists_coloring_on`,
`colorable_of_forall_exists_low_degree`, `exists_isCycle_of_forall_le_degree`,
`exists_isCycle_length_ge_of_le_chromaticNumber`, `colorable_of_forall_finite_subgraph_colorable`,
`exists_finite_subgraph_le_chromaticNumber`. Greps confirmed that `egirth` occurs only in
`Mathlib/Combinatorics/SimpleGraph/Girth.lean`, that no graph-degeneracy or Brooks-type notion
exists anywhere in Mathlib, and that `nonempty_hom_of_forall_finite_subgraph_hom` is the last
declaration of `Finsubgraph.lean` with no colouring corollary after it.

## Verification

The file compiles against the pinned toolchain (`leanprover/lean4:v4.27.0`) with **0 errors and 0
warnings** (`lake env lean CW_erdos_108.lean`, ~10 s). `#print axioms` on all 29 declarations
returns exactly `[propext, Classical.choice, Quot.sound]` in every case; the `#print axioms` lines
were then removed and the file recompiled clean. A separate fidelity probe checks that `Bound` is
*definitionally* the target's inner statement: with `Rhs` the right-hand side of
`Erdos108.erdos_108` copied verbatim from the pool file,
`Rhs ↔ ∀ r ≥ 4, ∀ k ≥ 2, ∃ f, Bound r k f` closes by `Iff.rfl`, and `erdos_108_rhs_of_three_le`
type-checks with conclusion literally `Rhs`. No `sorry`, no `set_option`, no `native_decide`, no
extra axioms; the only decision procedure used is `decide` on a two-vertex graph.

## AI assistance

This contribution was produced with AI assistance: Claude (Anthropic) wrote the Lean 4 source,
chose the proof strategy, and ran the compilation, novelty and axiom checks, working under human
direction. Every statement and proof was machine-checked by the Lean kernel in the pinned
environment before submission; no result is asserted that was not compiled.

## Originality

The Lean source is original to this contribution. No proof, statement or file was copied from
another repository, from the `formal-conjectures` upstream, or from any `formal_proof` link; the
target's pool file carries no such link. The classical mathematics (de Bruijn–Erdős,
Szekeres–Wilf, Dirac) is standard textbook material, formalised here from the informal arguments
rather than transcribed from any existing formalisation — none of these results exists in the
pinned Mathlib in any form.
