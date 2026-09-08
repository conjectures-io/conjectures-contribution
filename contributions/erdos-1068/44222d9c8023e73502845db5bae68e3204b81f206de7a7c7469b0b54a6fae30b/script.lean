import Mathlib
import FormalConjectures.ErdosProblems.«1068»

/-!
# Erdős 1068: a finite-cut criterion for `InfinitelyConnected`, and countable-decomposition
stability of uncountable chromatic number

The reward statement `Erdos1068.erdos_1068` is an equivalence whose right-hand side is

`∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
    ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s)`.

## The obstacle

Both bespoke notions occurring there come with no lemmas at all in the pinned environment.

* `SimpleGraph.InfinitelyConnected` and `SimpleGraph.InternallyDisjoint` are the only two
  declarations of `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Connectivity.lean`, and
  the pinned `Mathlib` contains no occurrence of either name, so no ambient theory applies.
  Unfolded, `InfinitelyConnected G` demands, for every pair `u ≠ v`, an **infinite** set
  `P : Set (G.Walk u v)` of pairwise internally disjoint paths.  That is an awkward object on
  both sides of a proof: to establish it one must produce infinitely many walks at once, and the
  type `G.Walk u v` depends on the endpoints, so even transporting the property along a graph
  isomorphism needs an endpoint-substitution dance.  In the target the walks additionally live in
  the subtype `↥s`.
* `SimpleGraph.chromaticCardinal` is an `sInf` over a set of cardinals; the pinned `Mathlib`
  contains no occurrence of the name, and inside this repository it occurs only in its own
  definition and in the statements and documentation of Erdős problems 75, 593, 740, 918, 1067,
  1068, 1175 and 1176 (the namesake `ThreeUniformHypergraph.chromaticCardinal` is a different
  function on a different type, and the lemmas proved about that one do not apply here).  Nothing
  records that the defining infimum is attained, so the target's hypothesis
  `G.chromaticCardinal = ℵ_ 1` cannot be turned into a statement about colourings without
  unfolding the `sInf` by hand.

Both halves of the problem are therefore inaccessible before some API is built, and the two
halves are the two sides of the intended construction: one has to grow a countable set `s`
greedily while keeping the colouring hypothesis alive on what is left over.

## What is proved here

**1. A finite-cut criterion.**  `infinitelyConnected_iff` : `InfinitelyConnected G` holds *iff*
`V` is nontrivial and `FinitelyUnseparated G` holds, where the latter says that for all `u ≠ v`
and every *finite* `S : Set V` there is a `u`-`v` path of length at least two whose interior
misses `S`.  This replaces one infinite object by a family of finite obligations.  The reverse
direction is the substantial one: the infinite family of pairwise internally disjoint paths is
built greedily (`blockedSet`, `pathAt`), each new path avoiding the finite set of interior
vertices used so far, and the length condition is what forces the paths to be pairwise distinct.
`finitelyUnseparated_length_condition_necessary` checks that the length condition cannot be
dropped.

**2. Countable-decomposition stability of `chromaticCardinal = ℵ_ 1`.**
`exists_chromaticCardinal_eq_aleph_one_of_cover` : if `G.chromaticCardinal = ℵ_ 1` and
`V = ⋃ₙ A n` is covered by countably many sets, then some `G.induce (A n)` again has chromatic
cardinal `ℵ_ 1`.  Two consequences drive a greedy construction:
`chromaticCardinal_induce_compl_eq_aleph_one` (deleting a *countable* set of vertices leaves the
hypothesis intact) and `exists_connectedComponent_chromaticCardinal_eq_aleph_one` (some connected
component keeps it).  The engine is `nonempty_coloring_nat_of_cover`, which glues countably many
`ℕ`-colourings by pairing each vertex's colour with the least index of a covering set.

**3. A checked delimiter for the hypothesis.**
`not_forall_chromaticCardinal_eq_aleph0_exists_countable_infinitelyConnected` : the statement
obtained from the target's right-hand side by replacing `ℵ_ 1` with `ℵ₀` is **false**.  The
witness is `cliqueLadder`, which is *defined* to be the Mathlib graph
`(SimpleGraph.completeMultipartiteGraph fun n : ℕ => Fin n)ᶜ`, i.e. the disjoint union of the
finite complete graphs; its chromatic cardinal is exactly `ℵ₀` (`cliqueLadder_chromaticCardinal`)
and all of its degrees are finite (`cliqueLadder_neighborSet_finite`), while
`infinite_neighborSet_of_infinitelyConnected_induce` shows every vertex of a witness set `s` must
have infinite degree in `G`.  So any proof of 1068 must use uncountability of the chromatic
cardinal, not merely its infiniteness.

**4. Use sites against the target itself.**  `erdos_1068_rhs_iff_connected` shows the target's
right-hand side is *equivalent* to its restriction to connected graphs, and
`answer_iff_normal_form` rewrites the target itself into a normal form: for every connected `G`
of chromatic cardinal `ℵ_ 1`, find a graph `H` on `ℕ` such that no finite set of vertices
separates two vertices of `H` along paths with nonempty interior, together with an induced
embedding `H ↪g G`.  Every step is an equivalence, so nothing is lost in either direction.
`answer_iff_normal_form` takes the equivalence defining the answer as a hypothesis, so
`answer_iff_normal_form Erdos1068.erdos_1068` is exactly the equivalence between problem 1068 and
that normal form, while this file itself stays free of any dependence on the unproved reward
statement.

**5. Supporting API**, used above and reusable on its own.  `mem_innerSupport_iff` and
`internallyDisjoint_iff_of_isPath` describe the interior of a **path**: it is exactly the set of
vertices of the path other than its two endpoints, and consequently two *paths with the same
endpoints* are internally disjoint exactly when every vertex they share is one of those two
endpoints.  This is what the docstring of `SimpleGraph.InternallyDisjoint` claims, and it is not
what its definition — disjointness of the lists `support.tail.dropLast` — says outright.  The
`IsPath` hypothesis of both lemmas is load-bearing and cannot be dropped: for the *walk*
`0 → 1 → 0 → 1` in `⊤ : SimpleGraph (Fin 2)` the inner support is `[1, 0]`, so the endpoint `1`
lies in the interior.  Note also that `SimpleGraph.InternallyDisjoint` is stated for walks with
arbitrary endpoint pairs, whereas `internallyDisjoint_iff_of_isPath` covers only the case of
common endpoints, which is the case the target needs.  Further supporting API:
`connected_of_infinitelyConnected` and `exists_isPath_avoiding` (bridges to the ambient
connectivity API); `finitelyUnseparated_of_iso`, `infinitelyConnected_of_iso`, `isoInduceRange`
and `induceInduceIso` (transport along isomorphisms and embeddings); `chromaticCardinal_attained`,
`chromaticCardinal_le_iff`, `chromaticCardinal_le_of_hom`, `chromaticCardinal_le_aleph0_iff`,
`chromaticCardinal_le_aleph0_of_countable`, `chromaticCardinal_top` and
`exists_adj_eq_of_chromaticCardinal_eq_aleph_one` (the missing `chromaticCardinal` API); and the
two non-vacuity checks `exists_chromaticCardinal_eq_aleph_one` (the target's hypothesis is
satisfiable inside `Type`) and `exists_countable_infinitelyConnected_of_infinite_clique` (its
conclusion is satisfiable).

A later solver can use declaration
`Contribution.Erdos1068CountableCore.infinitelyConnected_iff` to discharge or simplify obligation
`InfinitelyConnected (G.induce s)` in target `Erdos1068.erdos_1068`.  A later solver can use
declaration `Contribution.Erdos1068CountableCore.erdos_1068_rhs_iff_connected` to discharge or
simplify obligation `∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s)` in target
`Erdos1068.erdos_1068`, since it reduces that obligation to the case of a connected `G`.  While
building `s`, `chromaticCardinal_induce_compl_eq_aleph_one` re-establishes the target's
hypothesis on the complement of the countably many vertices already used.

What is **not** done here: nothing decides the answer, and no reduction below assumes anything
about it.  The construction of `s` itself stays open — the localization lemmas keep the
colouring hypothesis alive on the unused part of the graph, but they say nothing about paths
between vertices *already chosen*, which is exactly what the finite-cut criterion asks for.

*References:* [erdosproblems.com/1068](https://www.erdosproblems.com/1068),
[erdosproblems.com/1067](https://www.erdosproblems.com/1067).
-/

open Cardinal SimpleGraph

namespace Contribution.Erdos1068CountableCore

universe u

section InnerSupport

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- The *inner support* of a walk: the list of vertices that `SimpleGraph.InternallyDisjoint`
compares, i.e. `p.support` with its first and last entries removed.  By definition
`SimpleGraph.InternallyDisjoint p q` is `List.Disjoint (innerSupport p) (innerSupport q)`. -/
def innerSupport {u v : V} (p : G.Walk u v) : List V := p.support.tail.dropLast

/-- A vertex of a walk which is not its final vertex already occurs in `support.dropLast`. -/
theorem mem_support_dropLast {v : V} : ∀ {w : V} (q : G.Walk w v) {x : V},
    x ∈ q.support → x ≠ v → x ∈ q.support.dropLast := by
  intro w q
  induction q with
  | nil =>
    intro x hx hxv
    rw [Walk.support_nil] at hx
    exact absurd (List.mem_singleton.mp hx) hxv
  | cons _ r ih =>
    intro x hx hxv
    rw [Walk.support_cons] at hx ⊢
    rw [List.dropLast_cons_of_ne_nil r.support_ne_nil]
    rcases List.mem_cons.mp hx with h1 | h1
    · exact List.mem_cons.mpr (Or.inl h1)
    · exact List.mem_cons.mpr (Or.inr (ih h1 hxv))

/-- Every vertex of a walk other than the two endpoints lies in its inner support. -/
theorem mem_innerSupport_of_mem_support {u v x : V} (p : G.Walk u v) (hx : x ∈ p.support)
    (hxu : x ≠ u) (hxv : x ≠ v) : x ∈ innerSupport p := by
  rw [Walk.support_eq_cons p] at hx
  rcases List.mem_cons.mp hx with h1 | h1
  · exact absurd h1 hxu
  · cases p with
    | nil => simp at h1
    | cons _ q =>
      rw [Walk.support_cons] at h1
      show x ∈ (Walk.support _).tail.dropLast
      rw [Walk.support_cons]
      simpa using mem_support_dropLast q (by simpa using h1) hxv

/-- The last vertex of a walk with no repeated vertex does not occur before the last position. -/
theorem not_mem_support_dropLast {v : V} : ∀ {w : V} (q : G.Walk w v), q.support.Nodup →
    v ∉ q.support.dropLast := by
  intro w q
  induction q with
  | nil => simp
  | cons _ r ih =>
    intro hnd hmem
    rw [Walk.support_cons, List.nodup_cons] at hnd
    rw [Walk.support_cons, List.dropLast_cons_of_ne_nil r.support_ne_nil] at hmem
    rcases List.mem_cons.mp hmem with h1 | h1
    · exact hnd.1 (h1 ▸ r.end_mem_support)
    · exact ih hnd.2 h1

/-- **Full characterisation of the inner support of a path**: it consists exactly of the
vertices of the path other than its two endpoints.

The `IsPath` hypothesis is load-bearing.  For the *walk* `0 → 1 → 0 → 1` in
`⊤ : SimpleGraph (Fin 2)` the inner support is `[1, 0]`, so the endpoint `1` lies in it. -/
theorem mem_innerSupport_iff {u v x : V} {p : G.Walk u v} (hp : p.IsPath) :
    x ∈ innerSupport p ↔ x ∈ p.support ∧ x ≠ u ∧ x ≠ v := by
  refine ⟨fun hx => ⟨(List.tail_sublist _).subset ((List.dropLast_sublist _).subset hx), ?_, ?_⟩,
    fun hx => mem_innerSupport_of_mem_support p hx.1 hx.2.1 hx.2.2⟩
  · have hnd := hp.support_nodup
    rw [Walk.support_eq_cons p, List.nodup_cons] at hnd
    rintro rfl
    exact hnd.1 ((List.dropLast_sublist _).subset hx)
  · rintro rfl
    cases p with
    | nil => simp [innerSupport] at hx
    | cons _ q =>
      have hq : innerSupport (Walk.cons ‹_› q) = q.support.dropLast := by simp [innerSupport]
      rw [hq] at hx
      exact not_mem_support_dropLast q hp.of_cons.support_nodup hx

/-- **The bespoke predicate `SimpleGraph.InternallyDisjoint` means, for two paths with common
endpoints, what its docstring says.**  They are internally disjoint exactly when every vertex
they have in common is one of the two endpoints.  The definition itself only says that the lists
`support.tail.dropLast` are disjoint, which is not obviously the same thing.

Both `IsPath` hypotheses are load-bearing (see `mem_innerSupport_iff`), and
`SimpleGraph.InternallyDisjoint` is defined for walks with arbitrary endpoint pairs, of which
only the common-endpoint case is characterised here. -/
theorem internallyDisjoint_iff_of_isPath {u v : V} {p q : G.Walk u v} (hp : p.IsPath)
    (hq : q.IsPath) :
    InternallyDisjoint p q ↔ ∀ x ∈ p.support, x ∈ q.support → x = u ∨ x = v := by
  constructor
  · intro hd x hxp hxq
    by_contra hcon
    push_neg at hcon
    have hd' : List.Disjoint (innerSupport p) (innerSupport q) := hd
    exact hd' ((mem_innerSupport_iff hp).mpr ⟨hxp, hcon.1, hcon.2⟩)
      ((mem_innerSupport_iff hq).mpr ⟨hxq, hcon.1, hcon.2⟩)
  · intro hcond
    show List.Disjoint (innerSupport p) (innerSupport q)
    intro x hxp hxq
    obtain ⟨hxps, hxu, hxv⟩ := (mem_innerSupport_iff hp).mp hxp
    obtain ⟨hxqs, -, -⟩ := (mem_innerSupport_iff hq).mp hxq
    rcases hcond x hxps hxqs with h1 | h1
    · exact hxu h1
    · exact hxv h1

/-- The inner support is empty exactly for the walks of length at most one. -/
theorem innerSupport_eq_nil_iff {u v : V} (p : G.Walk u v) :
    innerSupport p = [] ↔ p.length ≤ 1 := by
  show p.support.tail.dropLast = [] ↔ _
  rw [← List.length_eq_zero_iff, List.length_dropLast, List.length_tail, Walk.length_support]
  omega

/-- Between two *distinct* vertices there is at most one walk of length at most one, so the
walks of length `≤ 1` cannot contribute more than one member to a family of internally disjoint
paths. -/
theorem eq_of_length_le_one {u v : V} (huv : u ≠ v) {p q : G.Walk u v}
    (hp : p.length ≤ 1) (hq : q.length ≤ 1) : p = q := by
  have key : ∀ r : G.Walk u v, r.length ≤ 1 → ∃ h : G.Adj u v, r = Walk.cons h Walk.nil := by
    intro r hr
    cases r with
    | nil => exact absurd rfl huv
    | cons h r' =>
      cases r' with
      | nil => exact ⟨h, rfl⟩
      | cons _ _ => simp [Walk.length_cons] at hr
  obtain ⟨h1, rfl⟩ := key p hp
  obtain ⟨h2, rfl⟩ := key q hq
  rfl

/-- A path of length at least two starts with an edge into its inner support. -/
theorem exists_adj_mem_innerSupport {u v : V} {p : G.Walk u v} (hp : p.IsPath)
    (hlen : 2 ≤ p.length) : ∃ w, G.Adj u w ∧ w ∈ innerSupport p := by
  cases p with
  | nil => simp at hlen
  | cons h q =>
    refine ⟨_, h, mem_innerSupport_of_mem_support _ (by simp) h.ne' ?_⟩
    rintro rfl
    rw [Walk.isPath_iff_eq_nil.mp hp.of_cons] at hlen
    simp at hlen

/-- The inner support commutes with pushing a walk forward along a graph homomorphism. -/
theorem innerSupport_map (f : G →g G') {u v : V} (p : G.Walk u v) :
    innerSupport (p.map f) = (innerSupport p).map f := by
  simp only [innerSupport, Walk.support_map, List.map_tail, List.map_dropLast]

end InnerSupport

section Criterion

variable {V : Type*} {G : SimpleGraph V}

/-- `FinitelyUnseparated G` says that no finite set of vertices separates two distinct vertices
of `G` *along paths of positive interior*: for all `u ≠ v` and every finite `S` there is a `u`-`v`
path of length at least two whose inner support misses `S`.

The length condition cannot be dropped: in `⊤ : SimpleGraph (Fin 2)` the only path between the
two vertices is the edge itself, whose inner support is empty and therefore misses every `S`,
yet that graph is not `InfinitelyConnected`; see
`finitelyUnseparated_length_condition_necessary`. -/
def FinitelyUnseparated (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∀ S : Set V, S.Finite →
    ∃ p : G.Walk u v, p.IsPath ∧ 2 ≤ p.length ∧ ∀ x ∈ innerSupport p, x ∉ S

/-- The finite set of vertices already used as interior vertices after `n` rounds of the greedy
construction of internally disjoint paths, packaged with its finiteness proof.  Round `n` uses
the path that `FinitelyUnseparated` supplies for the obstruction accumulated so far. -/
noncomputable def blockedSet (h : FinitelyUnseparated G) {u v : V} (huv : u ≠ v) :
    ℕ → {S : Set V // S.Finite}
  | 0 => ⟨∅, Set.finite_empty⟩
  | n + 1 =>
      ⟨(blockedSet h huv n).1 ∪
          {x | x ∈ innerSupport
            (h u v huv (blockedSet h huv n).1 (blockedSet h huv n).2).choose},
        (blockedSet h huv n).2.union (List.finite_toSet _)⟩

/-- The `n`-th path of the greedy construction. -/
noncomputable def pathAt (h : FinitelyUnseparated G) {u v : V} (huv : u ≠ v) (n : ℕ) :
    G.Walk u v :=
  (h u v huv (blockedSet h huv n).1 (blockedSet h huv n).2).choose

/-- Defining property of `pathAt`: the `n`-th greedy path is a path of length at least two whose
interior avoids every interior vertex used at an earlier stage. -/
theorem pathAt_spec (h : FinitelyUnseparated G) {u v : V} (huv : u ≠ v) (n : ℕ) :
    (pathAt h huv n).IsPath ∧ 2 ≤ (pathAt h huv n).length ∧
      ∀ x ∈ innerSupport (pathAt h huv n), x ∉ (blockedSet h huv n).1 :=
  (h u v huv (blockedSet h huv n).1 (blockedSet h huv n).2).choose_spec

/-- The blocked sets increase along the greedy construction. -/
theorem blockedSet_mono (h : FinitelyUnseparated G) {u v : V} (huv : u ≠ v) {m n : ℕ}
    (hmn : m ≤ n) : (blockedSet h huv m).1 ⊆ (blockedSet h huv n).1 := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans fun _ hx => Or.inl hx
      · rw [heq]

/-- **Finite-cut criterion for infinite connectivity.**  The bespoke predicate
`SimpleGraph.InfinitelyConnected`, which asks for an *infinite family of pairwise internally
disjoint paths* between every two vertices, is equivalent to the purely local statement that no
finite set of vertices blocks all paths with nonempty interior.

The reverse implication is the substantial one: the family of paths is built greedily, each new
path being asked to avoid the (finite) set of interior vertices used so far. -/
theorem infinitelyConnected_iff (G : SimpleGraph V) :
    InfinitelyConnected G ↔ Nontrivial V ∧ FinitelyUnseparated G := by
  constructor
  · rintro ⟨hnt, hP⟩
    refine ⟨hnt, ?_⟩
    intro u v huv S hS
    obtain ⟨P, hinf, hpath, hdisj⟩ := hP huv
    by_contra hcon
    push_neg at hcon
    have hshort : {p : G.Walk u v | p.length ≤ 1}.Subsingleton :=
      fun _ hp _ hq => eq_of_length_le_one huv hp hq
    haveI : Infinite ↥(P \ {p : G.Walk u v | p.length ≤ 1}) :=
      (hinf.diff hshort.finite).to_subtype
    haveI : Finite ↥S := hS.to_subtype
    have key : ∀ p : ↥(P \ {p : G.Walk u v | p.length ≤ 1}),
        ∃ x : ↥S, (x : V) ∈ innerSupport (p : G.Walk u v) := by
      intro p
      have hlen : 2 ≤ (p : G.Walk u v).length := by
        have := p.2.2
        simp only [Set.mem_setOf_eq, not_le] at this
        omega
      obtain ⟨x, hx, hxS⟩ := hcon (p : G.Walk u v) (hpath _ p.2.1) hlen
      exact ⟨⟨x, hxS⟩, hx⟩
    choose f hf using key
    obtain ⟨p, q, hpq, hfeq⟩ := Finite.exists_ne_map_eq_of_infinite f
    have hd : List.Disjoint (innerSupport (p : G.Walk u v)) (innerSupport (q : G.Walk u v)) :=
      hdisj p.2.1 q.2.1 fun hc => hpq (Subtype.ext hc)
    exact hd (hf p) (by rw [hfeq]; exact hf q)
  · rintro ⟨hnt, h⟩
    refine ⟨hnt, ?_⟩
    intro u v huv
    have hblock : ∀ {m n : ℕ}, m < n →
        ∀ x ∈ innerSupport (pathAt h huv m), x ∈ (blockedSet h huv n).1 := by
      intro m n hmn x hx
      exact blockedSet_mono h huv hmn (Or.inr hx)
    have hdisj : ∀ {m n : ℕ}, m < n →
        List.Disjoint (innerSupport (pathAt h huv m)) (innerSupport (pathAt h huv n)) := by
      intro m n hmn x hxm hxn
      exact (pathAt_spec h huv n).2.2 x hxn (hblock hmn x hxm)
    have hinj : Function.Injective (pathAt h huv) := by
      have haux : ∀ {m n : ℕ}, m < n → pathAt h huv m ≠ pathAt h huv n := by
        intro m n hmn hcon
        have hne : innerSupport (pathAt h huv n) ≠ [] := by
          intro hnil
          rw [innerSupport_eq_nil_iff] at hnil
          have h2 := (pathAt_spec h huv n).2.1
          omega
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
        exact hdisj hmn (hcon ▸ hx) hx
      intro m n hmn
      rcases lt_trichotomy m n with hlt | heq | hgt
      · exact absurd hmn (haux hlt)
      · exact heq
      · exact absurd hmn.symm (haux hgt)
    refine ⟨Set.range (pathAt h huv), Set.infinite_range_of_injective hinj, ?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact (pathAt_spec h huv n).1
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hne
      have hmn : m ≠ n := fun hc => hne (by rw [hc])
      show List.Disjoint _ _
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · exact hdisj hlt
      · exact (hdisj hgt).symm

/-- **The length condition in `FinitelyUnseparated` is necessary.**  Dropping `2 ≤ p.length`
gives a criterion satisfied by `⊤ : SimpleGraph (Fin 2)` — whose unique path between the two
vertices is the edge itself, with empty interior — even though that graph is not infinitely
connected.  So `infinitelyConnected_iff` is sharp: the weakened criterion is strictly weaker. -/
theorem finitelyUnseparated_length_condition_necessary :
    (∀ u v : Fin 2, u ≠ v → ∀ S : Set (Fin 2), S.Finite →
        ∃ p : (⊤ : SimpleGraph (Fin 2)).Walk u v, p.IsPath ∧ ∀ x ∈ innerSupport p, x ∉ S) ∧
      ¬ InfinitelyConnected (⊤ : SimpleGraph (Fin 2)) := by
  constructor
  · intro u v huv S _
    refine ⟨Walk.cons (by simpa using huv) Walk.nil, by simp [Walk.isPath_def, huv], ?_⟩
    intro x hx
    simp [innerSupport] at hx
  · intro hIC
    obtain ⟨p, hp, hlen, -⟩ :=
      ((infinitelyConnected_iff _).mp hIC).2 0 1 (by decide) ∅ Set.finite_empty
    have hlt := hp.length_lt
    simp only [Fintype.card_fin] at hlt
    omega

/-- Bridge to Mathlib: an infinitely connected graph is `SimpleGraph.Connected`.  This is what
makes the countable subgraph produced by `Erdos1068.erdos_1068` usable with the ambient
connectivity API. -/
theorem connected_of_infinitelyConnected (hG : InfinitelyConnected G) : G.Connected := by
  haveI := hG.1
  rw [connected_iff]
  refine ⟨fun u v => ?_, inferInstance⟩
  rcases eq_or_ne u v with rfl | huv
  · exact Reachable.refl u
  · obtain ⟨p, -, -, -⟩ := ((infinitelyConnected_iff G).mp hG).2 u v huv ∅ Set.finite_empty
    exact ⟨p⟩

/-- The form in which infinite connectivity is used: any finite set of vertices avoiding two
given distinct vertices can be avoided by a path between them. -/
theorem exists_isPath_avoiding (hG : InfinitelyConnected G) {u v : V}
    (huv : u ≠ v) {S : Set V} (hS : S.Finite) (hu : u ∉ S) (hv : v ∉ S) :
    ∃ p : G.Walk u v, p.IsPath ∧ ∀ x ∈ S, x ∉ p.support := by
  obtain ⟨p, hp, -, havoid⟩ := ((infinitelyConnected_iff G).mp hG).2 u v huv S hS
  refine ⟨p, hp, fun x hxS hxsup => havoid x ?_ hxS⟩
  exact mem_innerSupport_of_mem_support p hxsup (by rintro rfl; exact hu hxS)
    (by rintro rfl; exact hv hxS)

/-- **Infinitely connected graphs have infinite minimum degree.**  Every vertex of an infinitely
connected graph has infinitely many neighbours; this is a necessary condition that any witness
for the conclusion of `Erdos1068.erdos_1068` has to satisfy. -/
theorem infinite_neighborSet_of_infinitelyConnected (hG : InfinitelyConnected G) (u : V) :
    (G.neighborSet u).Infinite := by
  obtain ⟨hnt, hfu⟩ := (infinitelyConnected_iff G).mp hG
  haveI := hnt
  obtain ⟨v, hv⟩ := exists_ne u
  intro hfin
  obtain ⟨p, hp, hlen, havoid⟩ := hfu u v (Ne.symm hv) (G.neighborSet u) hfin
  obtain ⟨w, hw, hwmem⟩ := exists_adj_mem_innerSupport hp hlen
  exact havoid w hwmem hw

/-- An infinitely connected graph has infinitely many vertices. -/
theorem infinite_of_infinitelyConnected (hG : InfinitelyConnected G) : Infinite V := by
  haveI := hG.1
  obtain ⟨u, -⟩ := exists_pair_ne V
  exact Set.infinite_univ_iff.mp
    ((infinite_neighborSet_of_infinitelyConnected hG u).mono (Set.subset_univ _))

end Criterion

section Transport

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

/-- `FinitelyUnseparated` transports along graph isomorphisms. -/
theorem finitelyUnseparated_of_iso (e : G ≃g G') (h : FinitelyUnseparated G) :
    FinitelyUnseparated G' := by
  intro x y hxy S hS
  obtain ⟨u, rfl⟩ : ∃ u, e u = x := ⟨e.symm x, e.apply_symm_apply x⟩
  obtain ⟨v, rfl⟩ : ∃ v, e v = y := ⟨e.symm y, e.apply_symm_apply y⟩
  have huv : u ≠ v := fun hc => hxy (by rw [hc])
  obtain ⟨p, hp, hlen, havoid⟩ :=
    h u v huv (e ⁻¹' S) (hS.preimage e.toEquiv.injective.injOn)
  refine ⟨p.map e.toHom, Walk.map_isPath_of_injective e.toEmbedding.injective hp, ?_, ?_⟩
  · rwa [Walk.length_map]
  · intro z hz
    rw [innerSupport_map] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact havoid w hw

/-- `SimpleGraph.InfinitelyConnected` transports along graph isomorphisms.  Proving this through
the finite-cut criterion avoids transporting an infinite family of walks whose type depends on
its endpoints. -/
theorem infinitelyConnected_of_iso (e : G ≃g G') (h : InfinitelyConnected G) :
    InfinitelyConnected G' := by
  rw [infinitelyConnected_iff] at h ⊢
  haveI := h.1
  exact ⟨e.toEquiv.injective.nontrivial, finitelyUnseparated_of_iso e h.2⟩

/-- A graph embedding is an isomorphism onto the subgraph induced by its range. -/
noncomputable def isoInduceRange (f : G' ↪g G) : G' ≃g G.induce (Set.range f) where
  toEquiv := Equiv.ofInjective f f.injective
  map_rel_iff' := f.map_adj_iff

/-- Inducing twice is inducing once, on the image.  This is what moves a witness found inside a
connected component back into the ambient graph. -/
noncomputable def induceInduceIso (G : SimpleGraph V) (t : Set V) (s : Set t) :
    (G.induce t).induce s ≃g G.induce (Subtype.val '' s) where
  toEquiv := Equiv.Set.image Subtype.val s Subtype.val_injective
  map_rel_iff' := Iff.rfl

end Transport

section ChromaticCardinal

/-- The infimum defining `SimpleGraph.chromaticCardinal` is **attained**: there is a colour type
whose cardinality is exactly the chromatic cardinal.  Nothing in the pinned environment records
this, yet any use of a hypothesis `G.chromaticCardinal = κ` needs it. -/
theorem chromaticCardinal_attained {V : Type u} (G : SimpleGraph V) :
    ∃ C : Type u, #C = G.chromaticCardinal ∧ Nonempty (G.Coloring C) := by
  have hne : {κ : Cardinal.{u} | ∃ (C : Type u) (_ : #C = κ), Nonempty (G.Coloring C)}.Nonempty :=
    ⟨#V, V, rfl, ⟨G.selfColoring⟩⟩
  obtain ⟨C, hC, hcol⟩ := csInf_mem hne
  exact ⟨C, hC, hcol⟩

/-- `chromaticCardinal` is characterised from above by the existence of a small colouring. -/
theorem chromaticCardinal_le_iff {V : Type u} (G : SimpleGraph V) {κ : Cardinal.{u}} :
    G.chromaticCardinal ≤ κ ↔ ∃ C : Type u, #C ≤ κ ∧ Nonempty (G.Coloring C) := by
  constructor
  · intro h
    obtain ⟨C, hC, hcol⟩ := chromaticCardinal_attained G
    exact ⟨C, hC ▸ h, hcol⟩
  · rintro ⟨C, hC, hcol⟩
    have hle : G.chromaticCardinal ≤ #C := csInf_le (OrderBot.bddBelow _) ⟨C, rfl, hcol⟩
    exact hle.trans hC

/-- **The chromatic cardinal is monotone under graph homomorphisms**, in particular under passing
to an induced subgraph (`(SimpleGraph.Embedding.induce s).toHom`).  This is the direction that
lets a hypothesis about the whole graph be inherited by the pieces one localizes to. -/
theorem chromaticCardinal_le_of_hom {V W : Type u} {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G →g G') : G.chromaticCardinal ≤ G'.chromaticCardinal := by
  have hne : Set.Nonempty {κ : Cardinal.{u} | ∃ (C : Type u) (_ : #C = κ),
      Nonempty (G'.Coloring C)} := ⟨#W, W, rfl, ⟨G'.selfColoring⟩⟩
  refine csInf_le_csInf (OrderBot.bddBelow _) hne ?_
  rintro κ ⟨C, rfl, ⟨c⟩⟩
  exact ⟨C, rfl, ⟨Coloring.mk (fun v => c (f v)) fun hadj => c.valid (f.map_adj hadj)⟩⟩

/-- Countable chromatic cardinal is the same thing as being properly colourable by `ℕ`.  This is
the shape in which the hypothesis of `Erdos1068.erdos_1068` becomes usable. -/
theorem chromaticCardinal_le_aleph0_iff {V : Type} (G : SimpleGraph V) :
    G.chromaticCardinal ≤ ℵ₀ ↔ Nonempty (G.Coloring ℕ) := by
  rw [chromaticCardinal_le_iff]
  constructor
  · rintro ⟨C, hC, ⟨c⟩⟩
    haveI : Countable C := Cardinal.mk_le_aleph0_iff.mp hC
    obtain ⟨g, hg⟩ := Countable.exists_injective_nat C
    exact ⟨G.recolorOfEmbedding ⟨g, hg⟩ c⟩
  · rintro ⟨c⟩
    exact ⟨ℕ, by simp, ⟨c⟩⟩

/-- A graph on a countable vertex type has countable chromatic cardinal. -/
theorem chromaticCardinal_le_aleph0_of_countable {V : Type} [Countable V] (G : SimpleGraph V) :
    G.chromaticCardinal ≤ ℵ₀ := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat V
  exact (chromaticCardinal_le_aleph0_iff G).mpr ⟨G.recolorOfEmbedding ⟨g, hg⟩ G.selfColoring⟩

/-- The target's hypothesis, unpacked: if `G.chromaticCardinal = ℵ_ 1` then **no** function
`V → ℕ` is a proper colouring, i.e. every such function identifies the ends of some edge. -/
theorem exists_adj_eq_of_chromaticCardinal_eq_aleph_one {V : Type} (G : SimpleGraph V)
    (h : G.chromaticCardinal = ℵ_ 1) (f : V → ℕ) : ∃ a b, G.Adj a b ∧ f a = f b := by
  by_contra hcon
  push_neg at hcon
  have hle := (chromaticCardinal_le_aleph0_iff G).mpr
    ⟨Coloring.mk f fun {a b} hab => hcon a b hab⟩
  rw [h] at hle
  exact absurd hle (not_le.mpr aleph0_lt_aleph_one)

/-- The chromatic cardinal of a complete graph is its number of vertices. -/
theorem chromaticCardinal_top {V : Type u} : (⊤ : SimpleGraph V).chromaticCardinal = #V := by
  refine le_antisymm ((chromaticCardinal_le_iff _).mpr
    ⟨V, le_rfl, ⟨(⊤ : SimpleGraph V).selfColoring⟩⟩) ?_
  refine le_csInf ⟨#V, V, rfl, ⟨(⊤ : SimpleGraph V).selfColoring⟩⟩ ?_
  rintro κ ⟨C, rfl, ⟨c⟩⟩
  refine Cardinal.mk_le_of_injective (f := c) fun a b hab => ?_
  by_contra hne
  exact c.valid (by simpa using hne) hab

/-- The hypothesis of `Erdos1068.erdos_1068` is satisfiable inside `Type`, so the target is not
vacuously true. -/
theorem exists_chromaticCardinal_eq_aleph_one :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 :=
  ⟨(ℵ_ 1 : Cardinal.{0}).out, ⊤, by rw [chromaticCardinal_top, Cardinal.mk_out]⟩

end ChromaticCardinal

section Localization

variable {V : Type} {G : SimpleGraph V}

/-- **Countably many `ℕ`-colourings glue.**  If the vertex set is covered by countably many sets
each of which induces a graph properly colourable by `ℕ`, then so is the whole graph: colour a
vertex by the pair consisting of the least index of a covering set containing it and its colour
there.  (No disjointness is required of the cover.) -/
theorem nonempty_coloring_nat_of_cover {A : ℕ → Set V} (hcov : ∀ v : V, ∃ n, v ∈ A n)
    (h : ∀ n, Nonempty ((G.induce (A n)).Coloring ℕ)) : Nonempty (G.Coloring ℕ) := by
  classical
  have c : ∀ n, (G.induce (A n)).Coloring ℕ := fun n => (h n).some
  set part : ℕ → V → ℕ := fun n v => if hv : v ∈ A n then c n ⟨v, hv⟩ else 0 with hpart
  set idx : V → ℕ := fun v => Nat.find (hcov v) with hidx
  have hmem : ∀ v : V, v ∈ A (idx v) := fun v => Nat.find_spec (hcov v)
  refine ⟨Coloring.mk (fun v => Nat.pair (idx v) (part (idx v) v)) ?_⟩
  intro u v huv
  show Nat.pair (idx u) (part (idx u) u) ≠ Nat.pair (idx v) (part (idx v) v)
  by_cases hiu : idx u = idx v
  · rw [hiu, ne_eq, Nat.pair_eq_pair]
    simp only [not_and, true_implies]
    have hu : u ∈ A (idx v) := hiu ▸ hmem u
    have hv : v ∈ A (idx v) := hmem v
    have hne : c (idx v) ⟨u, hu⟩ ≠ c (idx v) ⟨v, hv⟩ := (c (idx v)).valid (by simpa using huv)
    simpa [hpart, hu, hv] using hne
  · rw [ne_eq, Nat.pair_eq_pair]
    exact fun hc => hiu hc.1

/-- **Localization of the target's hypothesis.**  Chromatic cardinal `ℵ_ 1` cannot be destroyed
by splitting the vertex set into countably many (not necessarily disjoint) pieces: one of the
pieces induces a subgraph of chromatic cardinal `ℵ_ 1` again.

This is the tool that keeps the hypothesis of `Erdos1068.erdos_1068` alive along a construction
that consumes countably many vertices. -/
theorem exists_chromaticCardinal_eq_aleph_one_of_cover (G : SimpleGraph V)
    (hG : G.chromaticCardinal = ℵ_ 1) {A : ℕ → Set V} (hcov : ∀ v : V, ∃ n, v ∈ A n) :
    ∃ n, (G.induce (A n)).chromaticCardinal = ℵ_ 1 := by
  by_contra hcon
  push_neg at hcon
  refine absurd hG (ne_of_lt ?_)
  refine lt_of_le_of_lt ((chromaticCardinal_le_aleph0_iff G).mpr
    (nonempty_coloring_nat_of_cover hcov fun n => (chromaticCardinal_le_aleph0_iff _).mp ?_))
    aleph0_lt_aleph_one
  have hle : (G.induce (A n)).chromaticCardinal ≤ ℵ_ 1 :=
    hG ▸ chromaticCardinal_le_of_hom (Embedding.induce (A n)).toHom
  have hlt := lt_of_le_of_ne hle (hcon n)
  rwa [← succ_aleph0, Order.lt_succ_iff] at hlt

/-- **Deleting countably many vertices preserves the target's hypothesis.**  If
`G.chromaticCardinal = ℵ_ 1` and `s` is countable, then the graph induced on the complement of
`s` still has chromatic cardinal `ℵ_ 1`. -/
theorem chromaticCardinal_induce_compl_eq_aleph_one (G : SimpleGraph V)
    (hG : G.chromaticCardinal = ℵ_ 1) {s : Set V} (hs : s.Countable) :
    (G.induce sᶜ).chromaticCardinal = ℵ_ 1 := by
  classical
  obtain ⟨n, hn⟩ := exists_chromaticCardinal_eq_aleph_one_of_cover G hG
    (A := fun n => if n = 0 then sᶜ else s) (fun v => by
      by_cases h : v ∈ s
      · exact ⟨1, by simpa using h⟩
      · exact ⟨0, by simpa using h⟩)
  by_cases hn0 : n = 0
  · rw [hn0] at hn
    simpa using hn
  · rw [if_neg hn0] at hn
    haveI : Countable ↥s := hs.to_subtype
    have hle := chromaticCardinal_le_aleph0_of_countable (G.induce s)
    rw [hn] at hle
    exact absurd hle (not_le.mpr aleph0_lt_aleph_one)

/-- **Some connected component carries the whole chromatic cardinal.**  A graph of chromatic
cardinal `ℵ_ 1` has a connected component whose induced subgraph again has chromatic cardinal
`ℵ_ 1`; the gluing uses `SimpleGraph.homOfConnectedComponents`.

Together with `chromaticCardinal_induce_compl_eq_aleph_one` this is the engine of a greedy
construction: after countably many vertices have been used up, what is left still contains a
*connected* induced subgraph of chromatic cardinal `ℵ_ 1`. -/
theorem exists_connectedComponent_chromaticCardinal_eq_aleph_one (G : SimpleGraph V)
    (hG : G.chromaticCardinal = ℵ_ 1) :
    ∃ C : G.ConnectedComponent, (G.induce C.supp).chromaticCardinal = ℵ_ 1 := by
  by_contra hcon
  push_neg at hcon
  have hcol : ∀ C : G.ConnectedComponent, Nonempty ((G.induce C.supp).Coloring ℕ) := by
    intro C
    refine (chromaticCardinal_le_aleph0_iff _).mp ?_
    have hle : (G.induce C.supp).chromaticCardinal ≤ ℵ_ 1 :=
      hG ▸ chromaticCardinal_le_of_hom (Embedding.induce _).toHom
    have hlt := lt_of_le_of_ne hle (hcon C)
    rwa [← succ_aleph0, Order.lt_succ_iff] at hlt
  have hglue : Nonempty (G.Coloring ℕ) := ⟨G.homOfConnectedComponents fun C => (hcol C).some⟩
  rw [← chromaticCardinal_le_aleph0_iff, hG] at hglue
  exact absurd hglue (not_le.mpr aleph0_lt_aleph_one)

end Localization

section Witnesses

variable {V : Type*} {G : SimpleGraph V}

/-- The complete graph on an infinite vertex type is infinitely connected.  With the finite-cut
criterion in hand this is a two-line argument: pick any vertex outside the finite obstruction. -/
theorem infinitelyConnected_top {α : Type*} [Infinite α] :
    InfinitelyConnected (⊤ : SimpleGraph α) := by
  rw [infinitelyConnected_iff]
  refine ⟨inferInstance, fun u v huv S hS => ?_⟩
  obtain ⟨w, hw⟩ := ((hS.union ((Set.finite_singleton v).insert u)).infinite_compl).nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at hw
  obtain ⟨hwS, hwu, hwv⟩ := hw
  refine ⟨Walk.cons (show (⊤ : SimpleGraph α).Adj u w by simpa using Ne.symm hwu)
    (Walk.cons (show (⊤ : SimpleGraph α).Adj w v by simpa using hwv) Walk.nil), ?_, by simp, ?_⟩
  · simp [Walk.isPath_def, hwv, huv, Ne.symm hwu]
  · intro x hx
    have hxw : x = w := by simpa [innerSupport] using hx
    rw [hxw]
    exact hwS

/-- **A checked sufficient condition for the conclusion of `Erdos1068.erdos_1068`:** a graph
containing an infinite clique contains a countable infinitely connected induced subgraph.
This is a *sufficient* condition only and does not solve the target: a graph of chromatic
cardinal `ℵ_ 1` need not contain an infinite clique.  Indeed this repository carries, as
`Erdos593.erdos_593.variants.graph_case_no_odd_cycle` (Erdős–Galvin–Hajnal), the statement that
for every odd `k ≥ 3` there is a graph of chromatic cardinal `ℵ_ 1` with no cycle of length `k`,
and its instance `k = 3` is a triangle-free such graph, which has no clique of size three, let
alone an infinite one.  What the lemma does show is that the target's conclusion is
satisfiable. -/
theorem exists_countable_infinitelyConnected_of_infinite_clique {K : Set V} (hK : K.Infinite)
    (hclique : G.IsClique K) :
    ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s) := by
  set g : ℕ → V := fun n => ((Set.Infinite.natEmbedding K hK n : K) : V)
  have hginj : Function.Injective g := fun a b hab =>
    (Set.Infinite.natEmbedding K hK).injective (Subtype.ext hab)
  refine ⟨Set.range g, Set.countable_range g, ?_⟩
  have hsub : Set.range g ⊆ K := by
    rintro _ ⟨n, rfl⟩
    exact (Set.Infinite.natEmbedding K hK n).2
  rw [(isClique_iff_induce_eq G).mp (hclique.subset hsub)]
  haveI : Infinite ↥(Set.range g) :=
    Set.infinite_coe_iff.mpr (Set.infinite_range_of_injective hginj)
  exact infinitelyConnected_top

/-- Any witness `s` for the conclusion of `Erdos1068.erdos_1068` consists of vertices of infinite
degree in `G`; in particular a graph all of whose degrees are finite cannot satisfy the
conclusion. -/
theorem infinite_neighborSet_of_infinitelyConnected_induce {s : Set V}
    (h : InfinitelyConnected (G.induce s)) {x : V} (hx : x ∈ s) :
    (G.neighborSet x).Infinite := by
  have himg : (fun y : ↥s => (y : V)) '' ((G.induce s).neighborSet ⟨x, hx⟩) ⊆ G.neighborSet x := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  refine Set.Infinite.mono himg ?_
  exact (infinite_neighborSet_of_infinitelyConnected h ⟨x, hx⟩).image
    Subtype.val_injective.injOn

end Witnesses

section Delimiter

/-- The disjoint union of the finite complete graphs `Kₙ`, `n : ℕ`, as a name for the Mathlib
graph `(SimpleGraph.completeMultipartiteGraph fun n : ℕ => Fin n)ᶜ`: vertices are pairs `⟨n, i⟩`
with `i : Fin n`, and two distinct ones are adjacent exactly when they have the same first
coordinate. -/
def cliqueLadder : SimpleGraph (Σ n : ℕ, Fin n) :=
  (completeMultipartiteGraph fun n : ℕ => Fin n)ᶜ

/-- Adjacency in `cliqueLadder`, unfolded away from the complement. -/
theorem cliqueLadder_adj {x y : Σ n : ℕ, Fin n} :
    cliqueLadder.Adj x y ↔ x.1 = y.1 ∧ x ≠ y := by
  simp [cliqueLadder, and_comm]

/-- `cliqueLadder` is locally finite: every vertex has finitely many neighbours, since they all
live in the (finite) level of that vertex. -/
theorem cliqueLadder_neighborSet_finite (x : Σ n : ℕ, Fin n) :
    (cliqueLadder.neighborSet x).Finite := by
  refine Set.Finite.subset (Set.finite_range fun i : Fin x.1 => (⟨x.1, i⟩ : Σ m : ℕ, Fin m)) ?_
  rintro ⟨m, i⟩ hy
  have hm : m = x.1 := (cliqueLadder_adj.mp hy).1.symm
  subst hm
  exact ⟨i, rfl⟩

/-- The chromatic cardinal of `cliqueLadder` is exactly `ℵ₀`: it is countable, and it contains
arbitrarily large cliques, so no finite colour type works. -/
theorem cliqueLadder_chromaticCardinal : cliqueLadder.chromaticCardinal = ℵ₀ := by
  refine le_antisymm (chromaticCardinal_le_aleph0_of_countable _) ?_
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨C, hCeq, ⟨c⟩⟩ := chromaticCardinal_attained cliqueLadder
  rw [← hCeq] at hcon
  haveI : Finite C := Cardinal.lt_aleph0_iff_finite.mp hcon
  have hpair : Pairwise fun i j : Fin (Nat.card C + 1) =>
      cliqueLadder.Adj ⟨Nat.card C + 1, i⟩ ⟨Nat.card C + 1, j⟩ := by
    intro i j hij
    exact cliqueLadder_adj.mpr ⟨rfl, by simpa using hij⟩
  have hinj := c.injective_comp_of_pairwise_adj
    (fun i : Fin (Nat.card C + 1) => (⟨Nat.card C + 1, i⟩ : Σ m : ℕ, Fin m)) hpair
  have hcard := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  omega

/-- **The hypothesis of `Erdos1068.erdos_1068` cannot be weakened from `ℵ_ 1` to `ℵ₀`.**  The
statement obtained from the right-hand side of the target by replacing `ℵ_ 1` with `ℵ₀` is false:
`cliqueLadder` has chromatic cardinal exactly `ℵ₀`, but all of its degrees are finite, and by
`infinite_neighborSet_of_infinitelyConnected_induce` a countable infinitely connected induced
subgraph would need a vertex of infinite degree.  So any proof of 1068 has to use uncountability
of the chromatic cardinal, not merely that it is infinite. -/
theorem not_forall_chromaticCardinal_eq_aleph0_exists_countable_infinitelyConnected :
    ¬ ∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ₀ →
        ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s) := by
  intro h
  obtain ⟨s, -, hIC⟩ := h _ cliqueLadder cliqueLadder_chromaticCardinal
  obtain ⟨x, -⟩ := hIC.1.exists_pair_ne
  exact (infinite_neighborSet_of_infinitelyConnected_induce hIC x.2)
    (cliqueLadder_neighborSet_finite _)

end Delimiter

section UseSite

/-- Having a countable induced subgraph which is infinitely connected is **equivalent** to
having an induced embedding of an infinitely connected graph on `ℕ`. -/
theorem exists_countable_induce_infinitelyConnected_iff {V : Type} (G : SimpleGraph V) :
    (∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s)) ↔
      ∃ H : SimpleGraph ℕ, InfinitelyConnected H ∧ Nonempty (H ↪g G) := by
  constructor
  · rintro ⟨s, hcnt, hIC⟩
    haveI : Countable s := hcnt.to_subtype
    haveI : Infinite s := infinite_of_infinitelyConnected hIC
    obtain ⟨ε⟩ : Nonempty (s ≃ ℕ) := nonempty_equiv_of_countable
    exact ⟨(G.induce s).map ε.toEmbedding, infinitelyConnected_of_iso (Iso.map ε _) hIC,
      ⟨((Iso.map ε (G.induce s)).symm.toEmbedding).trans (Embedding.induce s)⟩⟩
  · rintro ⟨H, hIC, ⟨f⟩⟩
    exact ⟨Set.range f, Set.countable_range _, infinitelyConnected_of_iso (isoInduceRange f) hIC⟩

/-- **Worked use site I: the connected reduction.**  The right-hand side of
`Erdos1068.erdos_1068` is *equivalent* to its restriction to connected graphs.  The nontrivial
direction uses `exists_connectedComponent_chromaticCardinal_eq_aleph_one` to move to a component
carrying the whole chromatic cardinal, and `induceInduceIso` to move the witness found there back
into the ambient graph. -/
theorem erdos_1068_rhs_iff_connected :
    (∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
        ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s)) ↔
      ∀ (V : Type) (G : SimpleGraph V), G.Connected → G.chromaticCardinal = ℵ_ 1 →
        ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s) := by
  constructor
  · intro h V G _ hchi
    exact h V G hchi
  · intro h V G hchi
    obtain ⟨C, hC⟩ := exists_connectedComponent_chromaticCardinal_eq_aleph_one G hchi
    obtain ⟨s, hcnt, hIC⟩ := h C.supp (G.induce C.supp) C.connected_toSimpleGraph hC
    exact ⟨Subtype.val '' s, hcnt.image _,
      infinitelyConnected_of_iso (induceInduceIso G C.supp s) hIC⟩

/-- **Worked use site II: the normal form, applied to the reward statement.**  For any
proposition `A` equivalent to the right-hand side of the target — in particular for the answer of
the reward statement, by applying this lemma to `Erdos1068.erdos_1068` itself — problem 1068 is
equivalent to: for every *connected* graph `G` of chromatic cardinal `ℵ_ 1` there is a graph `H`
on `ℕ` such that no finite set of vertices separates two vertices of `H` along paths with
nonempty interior, together with an induced embedding `H ↪g G`.  Only finite obligations remain
on the connectivity side, and the graph to be produced now lives on a fixed countable vertex type.

Every step of the proof is an equivalence (`erdos_1068_rhs_iff_connected`,
`exists_countable_induce_infinitelyConnected_iff`, `infinitelyConnected_iff`), so nothing is lost
in either direction.  Taking the defining equivalence as the hypothesis `hA` keeps this file free
of any dependence on the unproved reward statement while remaining directly applicable to it. -/
theorem answer_iff_normal_form {A : Prop}
    (hA : A ↔ (∀ (V : Type) (G : SimpleGraph V), G.chromaticCardinal = ℵ_ 1 →
      ∃ s : Set V, s.Countable ∧ InfinitelyConnected (G.induce s))) :
    A ↔ ∀ (V : Type) (G : SimpleGraph V), G.Connected → G.chromaticCardinal = ℵ_ 1 →
      ∃ H : SimpleGraph ℕ, FinitelyUnseparated H ∧ Nonempty (H ↪g G) := by
  rw [hA, erdos_1068_rhs_iff_connected]
  refine forall_congr' fun V => forall_congr' fun G => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  rw [exists_countable_induce_infinitelyConnected_iff G]
  refine exists_congr fun H => and_congr_left fun _ => ?_
  rw [infinitelyConnected_iff, and_iff_right (inferInstanceAs (Nontrivial ℕ))]

end UseSite

end Contribution.Erdos1068CountableCore
