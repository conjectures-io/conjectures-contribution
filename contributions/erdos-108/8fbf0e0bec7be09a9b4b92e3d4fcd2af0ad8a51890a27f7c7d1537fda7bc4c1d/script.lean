import FormalConjectures.ErdosProblems.«108»

/-!
# Erdős Problem 108: a spanning-subgraph interface, and the case `k = 2` solved

The target `Erdos108.erdos_108` (tagged `research open` in the pool file) asks whether for all
`r ≥ 4` and `k ≥ 2` there is a finite `f = f(k, r)` such that every graph of chromatic number at
least `f` contains a subgraph of girth at least `r` and chromatic number at least `k`.  Its
right-hand side is

`∀ r ≥ 4, ∀ k ≥ 2, ∃ f : ℕ, ∀ (V : Type u) (G : SimpleGraph V), Nonempty V →
  f ≤ G.chromaticNumber → ∃ H : G.Subgraph, H.coe.girth ≥ r ∧ H.coe.chromaticNumber ≥ k`,

and `Bound r k f` below is that inner statement, transcribed binder for binder.

## What is proved

Two independent things.

**(1) An interface for the target's witness obligation, valid for every `r` and every `k`.**  The
obligation `∃ H : G.Subgraph, H.coe.girth ≥ r ∧ H.coe.chromaticNumber ≥ k` is stated with a
`SimpleGraph.Subgraph`, whose coercion `H.coe` lives on the *subtype* `H.verts`; every construction
one would like to perform (take the graph spanned by a cycle, delete edges, take a union) naturally
produces a `SimpleGraph V` on the original vertex type instead.

* `exists_subgraph_iff` : for every `G`, `r`, `k`,
  `(∃ H : G.Subgraph, H.coe.girth ≥ r ∧ H.coe.chromaticNumber ≥ k) ↔
   (∃ H : SimpleGraph V, H ≤ G ∧ H.girth ≥ r ∧ H.chromaticNumber ≥ k)`.
  It is an equivalence, so replacing the target's obligation by the right-hand side loses nothing.
* `bound_iff_boundSpanning` : the same replacement performed on `Bound r k f` itself.
* `bound_iff_boundFin` : `Bound r k f ↔ BoundFin r k f` for `f ≥ 1`, where `BoundFin` restricts
  the target's `∀ V : Type u` to finite vertex types.  Again an equivalence, so a later solver may
  assume the graph finite *and* work with spanning subgraphs on the original vertex type.

**(2) The case `k = 2`, settled outright, with the exact value of the threshold.**

* `bound_two_self` : `Bound r 2 r` holds for every `r ≥ 3`;
* `le_of_bound` : every `f` with `Bound r k f` and `k ≥ 2` satisfies `max r k ≤ f`;
* `bound_two_iff_le` : hence `Bound r 2 f ↔ r ≤ f` for `r ≥ 3`, that is, `f(2, r) = r` exactly;
* `erdos_108_two` : the right-hand side of the target, written out verbatim, at `k = 2`;
* `erdos_108_rhs_iff_three_le` : the right-hand side of the target is *equivalent* to its own
  `k ≥ 3` fragment.

At `k = 2` the problem is a statement about long cycles: a cycle of length `ℓ` spans a subgraph of
girth `ℓ` and chromatic number at least `2`, and conversely a subgraph of girth at least `r`
contains a cycle of length at least `r`.  The proof assembled here is the classical route to
"large chromatic number forces a long cycle": de Bruijn–Erdős compactness reduces the arbitrary
vertex type of the target to a finite one; a finite graph that is not `(r-1)`-colourable has a
nonempty set of vertices inside which every vertex has at least `r - 1` neighbours (the
Szekeres–Wilf degeneracy bound); and a longest path inside such a set closes up into a cycle of
length at least `r` (Dirac's argument).

## The obstacles that are removed

* `SimpleGraph.girth : ℕ` is `egirth.toNat`, so it takes the junk value `0` on an acyclic graph
  (`SimpleGraph.girth_eq_zero`).  Hence `H.coe.girth ≥ r` with `r ≥ 1` is not merely a lower bound
  on cycle lengths: it also asserts that `H.coe` has a cycle at all.  `le_girth_iff` splits it into
  the two honest halves `(r : ℕ∞) ≤ H.coe.egirth` and `¬ H.coe.IsAcyclic`.
* `Mathlib/Combinatorics/SimpleGraph/Girth.lean` relates the girths of two graphs only through
  `girth_anti`/`egirth_anti`, i.e. only for two graphs on the *same* vertex type.  Comparing
  `H.coe` (on `H.verts`) with a graph on `V` therefore has no Mathlib route.
  `egirth_le_of_embedding`, `egirth_eq_of_iso` and `girth_eq_of_iso` transport girth along graph
  embeddings and isomorphisms, and `egirth_spanningCoe` is the sharper statement that a subgraph
  and its spanning coercion have *equal* extended girth -- the inequality coming from the inclusion
  `H.coe ↪g H.spanningCoe` points the wrong way, and the missing half is supplied by
  `mem_verts_of_mem_support_spanningCoe`, which says that a walk of positive length in
  `H.spanningCoe` never leaves `H.verts`.  Together with `toSubgraphIso` these give
  `exists_subgraph_iff`.
* Turning a cycle into a witness whose *girth* is the length of that cycle needs the fact that no
  shorter cycle hides inside the graph spanned by it.  `le_length_of_isCycle_spanningCoe` proves
  this, and `egirth_spanningCoe_toSubgraph` / `girth_spanningCoe_toSubgraph` package it as
  "the graph spanned by a cycle of length `ℓ` has girth exactly `ℓ`".
* The target quantifies over an arbitrary `V : Type u`.  The pinned Mathlib has the compactness
  input `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`, but not the colouring corollary
  `colorable_of_forall_finite_subgraph_colorable`, nor the consequence
  `exists_finite_subgraph_le_chromaticNumber` used here, nor the transport `bound_of_boundFin` of
  the problem itself to finite graphs -- which in turn needs `coeSubgraphIso`, the isomorphism
  between a subgraph of a subgraph of `G` and its image in `G`.
* The pinned Mathlib has no lemma bounding `chromaticNumber` in terms of vertex degrees:
  `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` mentions `degree` nowhere, and there is no
  Brooks- or Szekeres–Wilf-type statement anywhere in `Mathlib/Combinatorics/`.
  `exists_coloring_on` and `colorable_of_forall_exists_low_degree` supply the colouring half;
  `exists_isCycle_of_forall_le_degree` (minimum degree `d ≥ 2` inside a finite vertex set forces a
  cycle of length at least `d + 1`) and `exists_isCycle_length_ge_of_le_chromaticNumber` (a finite
  graph of chromatic number at least `r ≥ 3` has a cycle of length at least `r`) are the cycle
  half.  `exact?` closes none of these four statements in the pinned environment.
  `not_exists_isCycle_of_degree_one` checks that the hypothesis `2 ≤ d` of
  `exists_isCycle_of_forall_le_degree` cannot be weakened to `1 ≤ d`.

A later solver can use declaration `Contribution.Erdos108Two.exists_subgraph_iff` to discharge or
simplify obligation `∃ (H : G.Subgraph), SimpleGraph.girth H.coe ≥ r ∧
SimpleGraph.chromaticNumber H.coe ≥ k` in target `Erdos108.erdos_108`.  A later solver can use
declaration `Contribution.Erdos108Two.erdos_108_two` to discharge or simplify obligation
`∃ (f : ℕ), ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
(_ : f ≤ SimpleGraph.chromaticNumber G), ∃ (H : G.Subgraph), SimpleGraph.girth H.coe ≥ r ∧
SimpleGraph.chromaticNumber H.coe ≥ k`, at `k = 2`, in target `Erdos108.erdos_108`.
`erdos_108_rhs_iff_three_le` is the worked use site: it deletes the `k = 2` instances from the
target's right-hand side, and it is an `↔`, so the fragment it leaves is exactly as strong as the
target and cannot be refuted by any instance of the target's own binders.

## What is not done

Everything with `k ≥ 3`.  The case `r = 4` with arbitrary `k` -- every graph of large chromatic
number has a triangle-free subgraph of large chromatic number -- is Rödl's theorem of 1977, and
the cases `r ≥ 5` carry the open part of the Erdős–Hajnal question; nothing here bears on either.
The three equivalences `exists_subgraph_iff`, `bound_iff_boundSpanning` and `bound_iff_boundFin`
are the parts of this development that apply to those cases as well.
-/

open SimpleGraph

namespace Contribution.Erdos108Two

universe u

variable {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}

/- ### Girth: the junk value, and transport along embeddings and isomorphisms -/

/-- `r ≤ G.girth` for a positive `r` says two things at once: the extended girth is at least `r`,
**and** `G` has a cycle.  The second half is invisible in the notation because `girth` returns the
junk value `0` on an acyclic graph. -/
theorem le_girth_iff {r : ℕ} (hr : 1 ≤ r) :
    r ≤ G.girth ↔ (r : ℕ∞) ≤ G.egirth ∧ ¬ G.IsAcyclic := by
  constructor
  · intro h
    have hac : ¬ G.IsAcyclic := by
      rw [← girth_eq_zero]
      omega
    refine ⟨?_, hac⟩
    have hne : G.egirth ≠ ⊤ := egirth_eq_top.not.mpr hac
    calc (r : ℕ∞) ≤ (G.girth : ℕ∞) := by exact_mod_cast h
      _ = G.egirth := by simp only [SimpleGraph.girth, ENat.coe_toNat hne]
  · rintro ⟨h, hac⟩
    have hne : G.egirth ≠ ⊤ := egirth_eq_top.not.mpr hac
    have h' := ENat.toNat_le_toNat h hne
    simpa [SimpleGraph.girth] using h'

/-- Cycles are transported along graph embeddings, so the extended girth can only decrease. -/
theorem egirth_le_of_embedding (f : G ↪g G') : G'.egirth ≤ G.egirth := by
  rw [le_egirth]
  intro a w hw
  have h : G'.egirth ≤ ((w.map f.toHom).length : ℕ∞) :=
    egirth_le_length ((Walk.map_isCycle_iff_of_injective (f := f.toHom) f.injective).mpr hw)
  rwa [Walk.length_map] at h

/-- The extended girth is an isomorphism invariant. -/
theorem egirth_eq_of_iso (f : G ≃g G') : G.egirth = G'.egirth :=
  le_antisymm (egirth_le_of_embedding f.symm.toEmbedding) (egirth_le_of_embedding f.toEmbedding)

/-- The girth is an isomorphism invariant. -/
theorem girth_eq_of_iso (f : G ≃g G') : G.girth = G'.girth := by
  simp only [SimpleGraph.girth, egirth_eq_of_iso f]

/- ### Subgraphs versus spanning subgraphs -/

/-- The inclusion of the coercion `H.coe` of a subgraph (a graph on the subtype `H.verts`) into its
spanning coercion `H.spanningCoe` (a graph on the ambient vertex type). -/
def spanningCoeEmbedding (H : G.Subgraph) : H.coe ↪g H.spanningCoe where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

/-- A walk of positive length inside `H.spanningCoe` never leaves `H.verts`: every vertex it visits
is an endpoint of one of its edges, and the edges of `H.spanningCoe` are the edges of `H`. -/
theorem mem_verts_of_mem_support_spanningCoe {H : G.Subgraph} {x y : α}
    (c : H.spanningCoe.Walk x y) (hlen : c.length ≠ 0) {z : α} (hz : z ∈ c.support) :
    z ∈ H.verts := by
  obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hz
  rcases Nat.lt_or_ge i c.length with hlt | hge
  · have hadj := c.adj_getVert_succ hlt
    rw [Subgraph.spanningCoe_adj] at hadj
    exact hi ▸ H.edge_vert hadj
  · have hieq : i = c.length := le_antisymm hile hge
    have hlt' : c.length - 1 < c.length := by omega
    have hadj := c.adj_getVert_succ hlt'
    rw [Subgraph.spanningCoe_adj, Nat.sub_add_cancel (by omega)] at hadj
    exact hi ▸ hieq ▸ H.edge_vert hadj.symm

/-- **A subgraph and its spanning coercion have the same extended girth.**  The inclusion
`H.coe ↪g H.spanningCoe` only gives `≤` in one direction; the other direction restricts a cycle of
`H.spanningCoe` to `H.verts`, which is legitimate by `mem_verts_of_mem_support_spanningCoe`. -/
theorem egirth_spanningCoe (H : G.Subgraph) : H.spanningCoe.egirth = H.coe.egirth := by
  refine le_antisymm (egirth_le_of_embedding (spanningCoeEmbedding H)) (le_egirth.mpr ?_)
  intro x c hc
  have hlen : c.length ≠ 0 := by
    have := hc.three_le_length
    omega
  have hsupp : ∀ z ∈ c.support, z ∈ H.verts := fun z hz =>
    mem_verts_of_mem_support_spanningCoe c hlen hz
  have hcyc : (Walk.induce H.verts c hsupp).IsCycle := by
    rw [← Walk.map_isCycle_iff_of_injective (f := (Embedding.induce (G := H.spanningCoe)
      H.verts).toHom) (Embedding.induce (G := H.spanningCoe) H.verts).injective, Walk.map_induce]
    exact hc
  have hlen2 : (Walk.induce H.verts c hsupp).length = c.length := by
    have h2 := congrArg Walk.length (Walk.map_induce (s := H.verts) c hsupp)
    rwa [Walk.length_map] at h2
  have h := egirth_le_length (G := H.coe) (w := Walk.induce H.verts c hsupp) hcyc
  exact le_of_le_of_eq h (by exact_mod_cast hlen2)

/-- A subgraph and its spanning coercion have the same girth (junk value included). -/
theorem girth_spanningCoe (H : G.Subgraph) : H.spanningCoe.girth = H.coe.girth := by
  simp only [SimpleGraph.girth, egirth_spanningCoe]

/-- A subgraph presented as a `SimpleGraph α` below `G` is isomorphic to the coercion of the
corresponding spanning `G.Subgraph`. -/
noncomputable def toSubgraphIso {H : SimpleGraph α} (h : H ≤ G) : H ≃g (G.toSubgraph H h).coe :=
  Subgraph.spanningCoeEquivCoeOfSpanning _ (SimpleGraph.toSubgraph.isSpanning _ _)

/-- **The witness interface of Erdős 108.**  The target's obligation "there is a `G.Subgraph` of
girth at least `r` and chromatic number at least `k`" is *equivalent* to "there is a graph `H ≤ G`
on the same vertex type of girth at least `r` and chromatic number at least `k`".

The second form is the one every construction produces: the graph spanned by a set of edges, a
union of such graphs, or the result of deleting edges from `G` all live on `V`, whereas `H.coe`
lives on the subtype `H.verts`.  Because this is an `↔`, nothing is lost by replacing the target's
obligation with it. -/
theorem exists_subgraph_iff (G : SimpleGraph α) (r k : ℕ) :
    (∃ H : G.Subgraph, (SimpleGraph.girth H.coe ≥ r) ∧
        (SimpleGraph.chromaticNumber H.coe ≥ k)) ↔
      ∃ H : SimpleGraph α, H ≤ G ∧ (SimpleGraph.girth H ≥ r) ∧
        (SimpleGraph.chromaticNumber H ≥ k) := by
  constructor
  · rintro ⟨H, hg, hc⟩
    refine ⟨H.spanningCoe, H.spanningCoe_le, ?_, ?_⟩
    · rwa [ge_iff_le, girth_spanningCoe]
    · exact hc.trans (chromaticNumber_mono_of_hom (spanningCoeEmbedding H).toHom)
  · rintro ⟨H, hle, hg, hc⟩
    refine ⟨G.toSubgraph H hle, ?_, ?_⟩
    · rwa [ge_iff_le, ← girth_eq_of_iso (toSubgraphIso hle)]
    · exact hc.trans (chromaticNumber_mono_of_hom (toSubgraphIso hle).toHom)

/- ### The graph spanned by a cycle has girth equal to the length of that cycle -/

/-- **Key lemma.**  Let `p` be a cycle of `G` and let `c` be any cycle of the graph
`p.toSubgraph.spanningCoe` spanned by the edges of `p`.  Then `c` is at least as long as `p`.

The proof shows that the support of `c` is closed under `p.toSubgraph`-adjacency: every vertex of
`c` has exactly two neighbours in `c` and exactly two neighbours in `p`, and the former are among
the latter, so the two neighbourhoods agree.  Walking along `p` from a vertex of `c` therefore
never leaves `c`, so every vertex of `p` occurs in `c`. -/
theorem le_length_of_isCycle_spanningCoe {a : α} {p : G.Walk a a} (hp : p.IsCycle)
    {x : α} {c : p.toSubgraph.spanningCoe.Walk x x} (hc : c.IsCycle) :
    p.length ≤ c.length := by
  have hns : ∀ v : α, p.toSubgraph.spanningCoe.neighborSet v = p.toSubgraph.neighborSet v := by
    intro v
    ext w
    simp
  -- the support of `c` is closed under adjacency in the graph spanned by `p`
  have hclosed : ∀ v ∈ c.support, ∀ w, p.toSubgraph.spanningCoe.Adj v w → w ∈ c.support := by
    intro v hv w hvw
    have h1 : (c.toSubgraph.neighborSet v).ncard = 2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
    have h2 : (p.toSubgraph.spanningCoe.neighborSet v).ncard = 2 :=
      hp.isCycles_spanningCoe_toSubgraph ⟨w, hvw⟩
    have hsub : c.toSubgraph.neighborSet v ⊆ p.toSubgraph.spanningCoe.neighborSet v :=
      c.toSubgraph.neighborSet_subset v
    have hfin : (p.toSubgraph.spanningCoe.neighborSet v).Finite := by
      rw [hns]
      exact p.finite_neighborSet_toSubgraph
    have heq : c.toSubgraph.neighborSet v = p.toSubgraph.spanningCoe.neighborSet v :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [h1, h2]) hfin
    have hw : w ∈ c.toSubgraph.neighborSet v := by rw [heq]; exact hvw
    exact Walk.mem_support_of_adj_toSubgraph (Subgraph.adj_symm _ hw)
  -- one step along `p` stays inside the support of `c`
  have hstep : ∀ i : ℕ, p.getVert i ∈ c.support → p.getVert (i + 1) ∈ c.support := by
    intro i hi
    by_cases hlt : i < p.length
    · exact hclosed _ hi _ (p.toSubgraph_adj_getVert hlt)
    · have e : p.getVert i = p.getVert (i + 1) := by
        rw [p.getVert_of_length_le (by omega : p.length ≤ i),
          p.getVert_of_length_le (by omega : p.length ≤ i + 1)]
      exact e ▸ hi
  have hsteps : ∀ (d i : ℕ), p.getVert i ∈ c.support → p.getVert (i + d) ∈ c.support := by
    intro d
    induction d with
    | zero => intro i hi; simpa using hi
    | succ n ih => intro i hi; exact hstep (i + n) (ih i hi)
  -- the start of `c` is a vertex of `p`
  have hx : x ∈ p.support := by
    have hadj : p.toSubgraph.spanningCoe.Adj x c.snd := (c.toSubgraph_adj_snd hc.not_nil).adj_sub
    rw [Subgraph.spanningCoe_adj] at hadj
    exact Walk.mem_support_of_adj_toSubgraph hadj
  obtain ⟨i₀, hi₀, -⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have ha : a ∈ c.support := by
    have h := hsteps p.length i₀ (by rw [hi₀]; exact c.start_mem_support)
    rwa [p.getVert_of_length_le (by omega)] at h
  have hall : ∀ j : ℕ, p.getVert j ∈ c.support := by
    intro j
    have h := hsteps j 0 (by simpa using ha)
    simpa using h
  have hsupp : p.support ⊆ c.support := by
    intro y hy
    obtain ⟨j, hj, -⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    rw [← hj]
    exact hall j
  -- compare the two supports as lists of pairwise distinct vertices
  have hcons : c.support = x :: c.support.tail := by
    rw [← Walk.support_tail_of_not_nil c hc.not_nil, Walk.cons_support_tail hc.not_nil]
  have htail : p.support.tail ⊆ c.support.tail := by
    intro y hy
    have hy' : y ∈ c.support := hsupp (List.mem_of_mem_tail hy)
    rw [hcons, List.mem_cons] at hy'
    rcases hy' with rfl | h
    · exact Walk.end_mem_tail_support hc.not_nil
    · exact h
  have hlen := (hp.support_nodup.subperm htail).length_le
  rw [List.length_tail, List.length_tail, Walk.length_support, Walk.length_support] at hlen
  omega

/-- The graph spanned by the edges of a cycle `p` has extended girth exactly `p.length`: it
contains `p`, and by `le_length_of_isCycle_spanningCoe` it contains nothing shorter. -/
theorem egirth_spanningCoe_toSubgraph {a : α} {p : G.Walk a a} (hp : p.IsCycle) :
    p.toSubgraph.spanningCoe.egirth = p.length := by
  refine le_antisymm ?_ (le_egirth.mpr ?_)
  · have hedges : ∀ e ∈ p.edges, e ∈ p.toSubgraph.spanningCoe.edgeSet := by
      intro e
      induction e using Sym2.ind with
      | _ u v => intro he; simpa [Walk.adj_toSubgraph_iff_mem_edges] using he
    have h := egirth_le_length (hp.transfer hedges)
    rwa [Walk.length_transfer] at h
  · intro y c hc
    exact_mod_cast le_length_of_isCycle_spanningCoe hp hc

/-- **The graph spanned by a cycle of length `ℓ` has girth exactly `ℓ`** -- no junk value, and no
shorter cycle hidden inside.  This is the witness a solver feeds to `exists_subgraph_iff`. -/
theorem girth_spanningCoe_toSubgraph {a : α} {p : G.Walk a a} (hp : p.IsCycle) :
    p.toSubgraph.spanningCoe.girth = p.length := by
  simp [SimpleGraph.girth, egirth_spanningCoe_toSubgraph hp]

/- ### Degeneracy and greedy colouring -/

/-- **Greedy colouring.**  If every nonempty subset `t` of a finite set `s` of vertices contains a
vertex with at most `n` neighbours inside `t`, then `s` can be properly coloured with `n + 1`
colours.  Peel off a vertex of small degree, colour the rest by induction, and give the peeled
vertex a colour missed by its at most `n` neighbours. -/
theorem exists_coloring_on [DecidableEq α] [DecidableRel G.Adj] (n : ℕ) :
    ∀ (m : ℕ) (s : Finset α), s.card ≤ m →
      (∀ t ⊆ s, t.Nonempty → ∃ v ∈ t, (t.filter (G.Adj v)).card ≤ n) →
      ∃ C : α → Fin (n + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → C u ≠ C w := by
  intro m
  induction m with
  | zero =>
    intro s hs _
    refine ⟨fun _ => 0, ?_⟩
    intro u hu
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs)] at hu
    simp at hu
  | succ m ih =>
    intro s hs h
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hcard⟩ := h s (le_refl s) hne
    have hcard' : (s.erase v).card ≤ m := by
      rw [Finset.card_erase_of_mem hv]
      have : 1 ≤ s.card := Finset.card_pos.mpr hne
      omega
    obtain ⟨C₀, hC₀⟩ := ih (s.erase v) hcard'
      (fun t ht htne => h t (ht.trans (Finset.erase_subset _ _)) htne)
    obtain ⟨c, hc⟩ : ∃ c : Fin (n + 1), c ∉ ((s.erase v).filter (G.Adj v)).image C₀ := by
      by_contra hcon
      push_neg at hcon
      have huniv : (((s.erase v).filter (G.Adj v)).image C₀) = Finset.univ :=
        Finset.eq_univ_of_forall hcon
      have h1 : (Finset.univ : Finset (Fin (n + 1))).card ≤
          ((s.erase v).filter (G.Adj v)).card := by
        rw [← huniv]; exact Finset.card_image_le
      have h2 : ((s.erase v).filter (G.Adj v)).card ≤ (s.filter (G.Adj v)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      omega
    refine ⟨Function.update C₀ v c, ?_⟩
    intro u hu w hw hadj
    have hne_uw : u ≠ w := hadj.ne
    by_cases hu' : u = v
    · subst hu'
      have hwv : w ≠ u := fun h => hne_uw h.symm
      rw [Function.update_self, Function.update_of_ne hwv]
      intro hcc
      exact hc (Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hwv, hw⟩, hadj⟩, hcc.symm⟩)
    · by_cases hw' : w = v
      · subst hw'
        rw [Function.update_self, Function.update_of_ne hu']
        intro hcc
        exact hc (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr
          ⟨Finset.mem_erase.mpr ⟨hu', hu⟩, hadj.symm⟩, hcc⟩)
      · rw [Function.update_of_ne hu', Function.update_of_ne hw']
        exact hC₀ u (Finset.mem_erase.mpr ⟨hu', hu⟩) w (Finset.mem_erase.mpr ⟨hw', hw⟩) hadj

/-- A finite graph in which every nonempty set of vertices contains a vertex of degree at most `n`
inside that set is `(n + 1)`-colourable. -/
theorem colorable_of_forall_exists_low_degree [Finite α] [DecidableEq α] [DecidableRel G.Adj]
    (n : ℕ) (h : ∀ t : Finset α, t.Nonempty → ∃ v ∈ t, (t.filter (G.Adj v)).card ≤ n) :
    G.Colorable (n + 1) := by
  haveI := Fintype.ofFinite α
  obtain ⟨C, hC⟩ := exists_coloring_on n (Finset.univ.card) Finset.univ le_rfl
    fun t _ htne => h t htne
  exact ⟨SimpleGraph.Coloring.mk C fun {u w} hadj =>
    hC u (Finset.mem_univ u) w (Finset.mem_univ w) hadj⟩

/- ### Minimum degree forces a long cycle -/

/-- A cycle visits pairwise distinct vertices, so it is no longer than the number of vertices. -/
theorem length_le_card_of_isCycle [Fintype α] {a : α} {w : G.Walk a a} (hw : w.IsCycle) :
    w.length ≤ Fintype.card α := by
  have h := hw.support_nodup.length_le_card
  rwa [List.length_tail, Walk.length_support, Nat.add_sub_cancel] at h

/-- **Minimum degree forces a long cycle.**  If every vertex of a nonempty finite set `t` has at
least `d ≥ 2` neighbours inside `t`, then `G` has a cycle of length at least `d + 1`.

Take a path `p` of maximal length among those staying inside `t`.  No neighbour of its first
vertex `a` can lie off `p`, or the path could be extended, so all `d` of them occur among
`p.getVert 1, …, p.getVert p.length`; `d` distinct indices in that range force the largest of them,
`i`, to be at least `d`.  The first `i` steps of `p`, closed by the edge from `p.getVert i` back to
`a`, form a cycle of length `i + 1`. -/
theorem exists_isCycle_of_forall_le_degree [DecidableEq α] [DecidableRel G.Adj]
    {d : ℕ} (hd : 2 ≤ d) {t : Finset α} (ht : t.Nonempty)
    (hdeg : ∀ v ∈ t, d ≤ (t.filter (G.Adj v)).card) :
    ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ d + 1 ≤ w.length := by
  classical
  set L : Set ℕ := {m | ∃ (a b : α) (p : G.Walk a b), p.IsPath ∧
    (∀ x ∈ p.support, x ∈ t) ∧ p.length = m} with hLdef
  have hLne : L.Nonempty := by
    obtain ⟨v, hv⟩ := ht
    exact ⟨0, v, v, Walk.nil, Walk.IsPath.nil, by simp [hv], by simp⟩
  have hLbd : ∀ m ∈ L, m ≤ t.card := by
    rintro m ⟨a, b, p, hp, hsub, rfl⟩
    have h1 : p.support.toFinset.card = p.support.length :=
      List.toFinset_card_of_nodup hp.support_nodup
    have h2 : p.support.toFinset ⊆ t := fun x hx => hsub x (List.mem_toFinset.mp hx)
    have h3 := Finset.card_le_card h2
    rw [h1, Walk.length_support] at h3
    omega
  have hbdd : BddAbove L := ⟨t.card, fun m hm => hLbd m hm⟩
  obtain ⟨a, b, p, hp, hsub, hlen⟩ := Nat.sSup_mem hLne hbdd
  set m := sSup L with hmdef
  -- every neighbour of `a` inside `t` lies on `p`
  have hnb : ∀ w ∈ t, G.Adj a w → w ∈ p.support := by
    intro w hw hadj
    by_contra hcon
    have hpath : (Walk.cons hadj.symm p).IsPath := by
      rw [Walk.cons_isPath_iff]
      exact ⟨hp, hcon⟩
    have hmem : m + 1 ∈ L := by
      refine ⟨w, b, Walk.cons hadj.symm p, hpath, ?_, by simp [hlen]⟩
      intro x hx
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hw
      · exact hsub x hx
    have := le_csSup hbdd hmem
    omega
  have ha_t : a ∈ t := hsub a p.start_mem_support
  set N := t.filter (G.Adj a) with hNdef
  set S := (Finset.range (m + 1)).filter (fun i => G.Adj a (p.getVert i)) with hSdef
  have hNcard : d ≤ N.card := hdeg a ha_t
  have hNS : N = S.image p.getVert := by
    ext w
    simp only [hNdef, hSdef, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hwt, hadj⟩
      obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp (hnb w hwt hadj)
      exact ⟨i, ⟨by omega, by rw [hi]; exact hadj⟩, hi⟩
    · rintro ⟨i, ⟨hi, hadj⟩, rfl⟩
      exact ⟨hsub _ (Walk.mem_support_iff_exists_getVert.mpr ⟨i, rfl, by omega⟩), hadj⟩
  have hmemS : ∀ j ∈ S, j ≤ p.length := by
    intro j hj
    simp only [hSdef, Finset.mem_filter, Finset.mem_range] at hj
    omega
  have hinj : Set.InjOn p.getVert ↑S := fun x hx y hy hxy =>
    hp.getVert_injOn (by simpa using hmemS x hx) (by simpa using hmemS y hy) hxy
  have hcardS : S.card = N.card := by rw [hNS, Finset.card_image_of_injOn hinj]
  have h0 : (0 : ℕ) ∉ S := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_range, Walk.getVert_zero, not_and]
    exact fun _ => G.irrefl
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  set i := S.max' hSne with hidef
  have hiS : i ∈ S := S.max'_mem hSne
  have hSIcc : S ⊆ Finset.Icc 1 i := by
    intro j hj
    refine Finset.mem_Icc.mpr ⟨?_, S.le_max' j hj⟩
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact absurd hj h0
    · exact hpos
  have hcardIcc : S.card ≤ i := by
    have h := Finset.card_le_card hSIcc
    simpa [Nat.card_Icc] using h
  have hdi : d ≤ i := by omega
  have him : i < m + 1 ∧ G.Adj a (p.getVert i) := by
    simpa only [hSdef, Finset.mem_filter, Finset.mem_range] using hiS
  obtain ⟨him', hadji⟩ := him
  have hqlen : (p.take i).length = i := by
    rw [Walk.take_length]
    omega
  have hqpath : (p.take i).IsPath := by
    have h : ((p.take i).append (p.drop i)).IsPath := by
      rw [Walk.append_take_drop_eq]; exact hp
    exact h.of_append_left
  refine ⟨a, Walk.cons hadji (p.take i).reverse, ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    refine ⟨hqpath.reverse, ?_⟩
    intro hmem
    rw [Walk.edges_reverse, List.mem_reverse] at hmem
    have hsnd := hqpath.eq_snd_of_mem_edges hmem
    rw [Walk.snd, Walk.take_getVert, min_eq_right (by omega : 1 ≤ i)] at hsnd
    have h1 : i = 1 := hp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hsnd
    omega
  · rw [Walk.length_cons, Walk.length_reverse, hqlen]
    omega

/-- The hypothesis `2 ≤ d` of `exists_isCycle_of_forall_le_degree` is sharp: in the complete graph
on two vertices every vertex has exactly one neighbour, and the graph has no cycle at all. -/
theorem not_exists_isCycle_of_degree_one :
    (∀ v : Bool, 1 ≤ ((Finset.univ : Finset Bool).filter ((⊤ : SimpleGraph Bool).Adj v)).card) ∧
      ¬ ∃ (a : Bool) (w : (⊤ : SimpleGraph Bool).Walk a a), w.IsCycle := by
  refine ⟨by decide, ?_⟩
  rintro ⟨a, w, hw⟩
  have h1 := length_le_card_of_isCycle hw
  have h2 := hw.three_le_length
  simp only [Fintype.card_bool] at h1
  omega

/-- **Chromatic number forces a long cycle.**  A finite graph with chromatic number at least `r`
contains a cycle of length at least `r`, for every `r ≥ 3`.  A graph that is not
`(r-1)`-colourable has, by `colorable_of_forall_exists_low_degree`, a nonempty set of vertices in
which every vertex has at least `r - 1` neighbours, and then
`exists_isCycle_of_forall_le_degree` produces the cycle. -/
theorem exists_isCycle_length_ge_of_le_chromaticNumber [Finite α] {r : ℕ} (hr : 3 ≤ r)
    (hχ : (r : ℕ∞) ≤ G.chromaticNumber) :
    ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ r ≤ w.length := by
  classical
  have hnc : ¬ G.Colorable (r - 1) := by
    intro hcol
    have h1 : (r : ℕ∞) ≤ ((r - 1 : ℕ) : ℕ∞) := hχ.trans hcol.chromaticNumber_le
    have h2 : r ≤ r - 1 := by exact_mod_cast h1
    omega
  have hdense : ∃ t : Finset α, t.Nonempty ∧ ∀ v ∈ t, r - 1 ≤ (t.filter (G.Adj v)).card := by
    by_contra hcon
    push_neg at hcon
    refine hnc ?_
    have hr1 : r - 1 = (r - 2) + 1 := by omega
    rw [hr1]
    refine colorable_of_forall_exists_low_degree (r - 2) fun t htne => ?_
    obtain ⟨v, hv, hlt⟩ := hcon t htne
    exact ⟨v, hv, by omega⟩
  obtain ⟨t, htne, hdeg⟩ := hdense
  obtain ⟨a, w, hw, hwlen⟩ :=
    exists_isCycle_of_forall_le_degree (d := r - 1) (by omega) htne hdeg
  exact ⟨a, w, hw, by omega⟩

/- ### Compactness: removing the arbitrary vertex type -/

/-- **de Bruijn–Erdős for chromatic number.**  If every finite subgraph of `G` is `n`-colourable
then so is `G`.  The pinned Mathlib has the underlying compactness statement for graph
homomorphisms (`SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom`) but not this corollary
for colourings. -/
theorem colorable_of_forall_finite_subgraph_colorable {n : ℕ}
    (h : ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable n) : G.Colorable n :=
  nonempty_hom_of_forall_finite_subgraph_hom (F := (⊤ : SimpleGraph (Fin n)))
    fun H hH => (h H hH).some

/-- A graph of chromatic number at least `f ≥ 1` has a finite subgraph of chromatic number at
least `f`. -/
theorem exists_finite_subgraph_le_chromaticNumber {f : ℕ} (hf : 1 ≤ f)
    (hχ : (f : ℕ∞) ≤ G.chromaticNumber) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ Nonempty H.verts ∧
      (f : ℕ∞) ≤ H.coe.chromaticNumber := by
  by_contra hcon
  push_neg at hcon
  have hcol : ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable (f - 1) := by
    intro H hfin
    haveI : Finite H.verts := hfin.to_subtype
    rcases isEmpty_or_nonempty (H.verts : Type _) with _ | hNE
    · exact colorable_of_isEmpty _ _
    · have hlt : H.coe.chromaticNumber < (f : ℕ∞) := hcon H hfin hNE
      have hne : H.coe.chromaticNumber ≠ ⊤ := ne_top_of_lt hlt
      have h1 : ((H.coe.chromaticNumber.toNat : ℕ) : ℕ∞) < (f : ℕ∞) := by
        rwa [ENat.coe_toNat hne]
      have h2 : H.coe.chromaticNumber.toNat < f := by exact_mod_cast h1
      exact (colorable_of_chromaticNumber_ne_top hne).mono (by omega)
  have hGc : (f : ℕ∞) ≤ ((f - 1 : ℕ) : ℕ∞) :=
    hχ.trans (colorable_of_forall_finite_subgraph_colorable hcol).chromaticNumber_le
  have : f ≤ f - 1 := by exact_mod_cast hGc
  omega

/-- A subgraph `K` of a subgraph `H` of `G`, viewed inside `G`, is isomorphic to `K` itself.  This
is what lets an obligation about `G.Subgraph` be discharged by working inside `H.coe`. -/
noncomputable def coeSubgraphIso {H : G.Subgraph} (K : H.coe.Subgraph) :
    K.coe ≃g (Subgraph.coeSubgraph K).coe where
  toEquiv := Equiv.Set.image (Subtype.val : H.verts → α) K.verts Subtype.val_injective
  map_rel_iff' := by
    intro a b
    simp only [Equiv.Set.image, Equiv.Set.imageOfInjOn, Equiv.coe_fn_mk,
      SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.coeSubgraph_adj]
    constructor
    · rintro ⟨-, -, h⟩
      exact h
    · intro h
      exact ⟨(a : H.verts).2, (b : H.verts).2, h⟩

/- ### The statement of Erdős 108, and three equivalent forms of it -/

/-- The inner statement of `Erdos108.erdos_108` for a girth bound `r`, a chromatic bound `k` and a
candidate threshold `f`, transcribed binder for binder.  The right-hand side of the target is
`∀ r ≥ 4, ∀ k ≥ 2, ∃ f, Bound r k f`. -/
def Bound (r k f : ℕ) : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
    (_ : f ≤ SimpleGraph.chromaticNumber G),
    ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
      (SimpleGraph.chromaticNumber H.coe ≥ k)

/-- `Bound` restricted to graphs on a finite vertex type. -/
def BoundFin (r k f : ℕ) : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (_ : Finite V) (_ : Nonempty V)
    (_ : f ≤ SimpleGraph.chromaticNumber G),
    ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
      (SimpleGraph.chromaticNumber H.coe ≥ k)

/-- `Bound` with the witness presented as a spanning subgraph of `G` on the same vertex type
instead of as a `G.Subgraph`. -/
def BoundSpanning (r k f : ℕ) : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
    (_ : f ≤ SimpleGraph.chromaticNumber G),
    ∃ (H : SimpleGraph V), H ≤ G ∧ (SimpleGraph.girth H ≥ r) ∧
      (SimpleGraph.chromaticNumber H ≥ k)

/-- `Bound` is antitone in the girth bound and in the chromatic bound, and monotone in the
threshold. -/
theorem Bound.mono {r k f r' k' f' : ℕ} (h : Bound.{u} r k f) (hr : r' ≤ r) (hk : k' ≤ k)
    (hf : f ≤ f') : Bound.{u} r' k' f' := by
  intro V G hV hχ
  obtain ⟨H, hg, hc⟩ := h V G hV ((Nat.cast_le.mpr hf).trans hχ)
  exact ⟨H, hr.trans hg, (Nat.cast_le.mpr hk).trans hc⟩

/-- **Spanning form of the target, valid for every `r` and `k`.**  Immediate from
`exists_subgraph_iff`, applied under the four binders of `Bound`. -/
theorem bound_iff_boundSpanning {r k f : ℕ} : Bound.{u} r k f ↔ BoundSpanning.{u} r k f := by
  constructor
  · intro h V G hV hχ
    exact (exists_subgraph_iff G r k).mp (h V G hV hχ)
  · intro h V G hV hχ
    exact (exists_subgraph_iff G r k).mpr (h V G hV hχ)

/-- **Compactness reduction, valid for every `r` and `k`.**  To prove the inner statement of
`Erdos108.erdos_108` for an arbitrary vertex type it suffices to prove it for finite graphs: a
graph of chromatic number at least `f` has a finite subgraph of chromatic number at least `f`, and
a subgraph of that subgraph is a subgraph of the original graph with the same girth and the same
chromatic number. -/
theorem bound_of_boundFin {r k f : ℕ} (hf : 1 ≤ f) (h : BoundFin.{u} r k f) : Bound.{u} r k f := by
  intro V G _ hχ
  obtain ⟨H, hfin, hne, hχH⟩ := exists_finite_subgraph_le_chromaticNumber hf hχ
  haveI : Finite H.verts := hfin.to_subtype
  obtain ⟨K, hg, hc⟩ := h H.verts H.coe inferInstance hne hχH
  refine ⟨Subgraph.coeSubgraph K, ?_, ?_⟩
  · rw [← girth_eq_of_iso (coeSubgraphIso K)]
    exact hg
  · exact hc.trans (chromaticNumber_mono_of_hom (coeSubgraphIso K).toHom)

/-- **The finite case of the target is equivalent to the target**, for every `r`, `k` and every
threshold `f ≥ 1`.  A later solver may therefore assume the vertex type finite without weakening
what is proved. -/
theorem bound_iff_boundFin {r k f : ℕ} (hf : 1 ≤ f) : Bound.{u} r k f ↔ BoundFin.{u} r k f :=
  ⟨fun h V G _ hV hχ => h V G hV hχ, bound_of_boundFin hf⟩

/- ### The case `k = 2` -/

/-- The case `k = 2` for finite graphs: a cycle of length at least `r` in a finite graph of
chromatic number at least `r`, packaged through `exists_subgraph_iff` as a subgraph of girth at
least `r` and chromatic number at least `2`. -/
theorem boundFin_two_self {r : ℕ} (hr : 3 ≤ r) : BoundFin.{u} r 2 r := by
  intro V G hfin _ hχ
  haveI := hfin
  obtain ⟨a, w, hw, hwlen⟩ := exists_isCycle_length_ge_of_le_chromaticNumber hr hχ
  refine (exists_subgraph_iff G r 2).mpr
    ⟨w.toSubgraph.spanningCoe, w.toSubgraph.spanningCoe_le, ?_, ?_⟩
  · rw [ge_iff_le, girth_spanningCoe_toSubgraph hw]
    exact hwlen
  · exact two_le_chromaticNumber_of_adj (u := a) (v := w.snd)
      (w.toSubgraph_adj_snd hw.not_nil)

/-- **The case `k = 2` of Erdős 108, with threshold `f = r`.** -/
theorem bound_two_self {r : ℕ} (hr : 3 ≤ r) : Bound.{u} r 2 r :=
  bound_of_boundFin (by omega) (boundFin_two_self hr)

/- ### The threshold is exactly `r`, and the resulting form of the target -/

/-- Any threshold witnessing `Bound r k f` with `k ≥ 2` satisfies `max r k ≤ f`.  Complete graphs
witness this: `K_n` has chromatic number `n`, every subgraph of it has chromatic number at most
`n`, and every cycle in it has length at most `n`. -/
theorem le_of_bound {r k f : ℕ} (hk : 2 ≤ k) (h : Bound.{u} r k f) : max r k ≤ f := by
  haveI : Nonempty (ULift.{u} (Fin (max f 1))) := ⟨⟨⟨0, by omega⟩⟩⟩
  have hcard : (⊤ : SimpleGraph (ULift.{u} (Fin (max f 1)))).chromaticNumber = (max f 1 : ℕ) := by
    rw [chromaticNumber_top, Fintype.card_ulift, Fintype.card_fin]
  obtain ⟨H, hg, hc⟩ := h (ULift.{u} (Fin (max f 1))) ⊤ inferInstance
    (by rw [hcard]; exact_mod_cast le_max_left f 1)
  have hkn : k ≤ max f 1 := by
    have hle := hc.trans (chromaticNumber_mono_of_hom H.hom)
    rw [hcard] at hle
    exact_mod_cast hle
  have hrn : r ≤ max f 1 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · omega
    · obtain ⟨-, hac⟩ := (le_girth_iff hr).mp hg
      obtain ⟨b, w, hw, hwl⟩ := exists_girth_eq_length.mpr hac
      haveI : Fintype H.verts := Fintype.ofFinite _
      have h1 := length_le_card_of_isCycle hw
      have h2 : Fintype.card H.verts ≤ Fintype.card (ULift.{u} (Fin (max f 1))) :=
        Fintype.card_le_of_injective _ Subtype.val_injective
      rw [Fintype.card_ulift, Fintype.card_fin] at h2
      omega
  omega

/-- **The `k = 2` row of Erdős 108, exactly.**  For `r ≥ 3` a threshold `f` works for `k = 2` if
and only if `r ≤ f`; in the notation of the problem, `f(2, r) = r`. -/
theorem bound_two_iff_le {r f : ℕ} (hr : 3 ≤ r) : Bound.{u} r 2 f ↔ r ≤ f := by
  refine ⟨fun h => le_trans (le_max_left r 2) (le_of_bound (by norm_num) h), fun h => ?_⟩
  exact (bound_two_self hr).mono le_rfl le_rfl h

/-- **Use site.**  The right-hand side of `Erdos108.erdos_108`, written out verbatim, at `k = 2`:
it holds, with `f = r`. -/
theorem erdos_108_two :
    ∀ r ≥ 4, ∃ (f : ℕ), ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
      (_ : f ≤ SimpleGraph.chromaticNumber G),
      ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
        (SimpleGraph.chromaticNumber H.coe ≥ 2) :=
  fun r hr => ⟨r, bound_two_self (by omega)⟩

/-- **Use site.**  The whole right-hand side of `Erdos108.erdos_108` is *equivalent* to its own
`k ≥ 3` fragment: the `k = 2` instances are supplied by `bound_two_self`, and conversely the
`k ≥ 3` fragment is a special case of the right-hand side.  A later solver may therefore assume
`3 ≤ k` throughout, with no loss. -/
theorem erdos_108_rhs_iff_three_le :
    (∀ r ≥ 4, ∀ k ≥ (2 : ℕ), ∃ (f : ℕ), ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
      (_ : f ≤ SimpleGraph.chromaticNumber G),
      ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
        (SimpleGraph.chromaticNumber H.coe ≥ k)) ↔
    (∀ r ≥ 4, ∀ k ≥ (3 : ℕ), ∃ (f : ℕ), ∀ (V : Type u) (G : SimpleGraph V) (_ : Nonempty V)
      (_ : f ≤ SimpleGraph.chromaticNumber G),
      ∃ (H : G.Subgraph), (SimpleGraph.girth H.coe ≥ r) ∧
        (SimpleGraph.chromaticNumber H.coe ≥ k)) := by
  constructor
  · intro h r hr k hk
    exact h r hr k (by omega)
  · intro h r hr k hk
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2 : k = 2 := by omega
      subst hk2
      exact ⟨r, bound_two_self (by omega)⟩
    · exact h r hr k hk3

end Contribution.Erdos108Two
