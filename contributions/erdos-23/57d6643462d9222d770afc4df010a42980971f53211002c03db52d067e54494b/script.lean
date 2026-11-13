/-
Random-bipartition piece for Erdős Problem 23 (conjectures.io).

Every graph has a bipartite subgraph with at least half its edges (random-cut /
double-counting argument). Combined with Mantel's bound, a triangle-free graph
on 5n vertices can be made bipartite by deleting at most 25n²/8 edges — a weaker
constant than the conjectured n², but via the technique the eventual solution
must use.

No sorry. Axioms: propext, Classical.choice, Quot.sound (via Classical).
-/

import Mathlib

open scoped Classical
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Contribution.Erdos23

/-! ## The random cut: some bipartition keeps half the edges -/

/-- The edges of `G` cut by the bipartition `f`: the endpoints receive
different values. -/
def cutFinset (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∃ u v, e = s(u, v) ∧ f u ≠ f v

lemma mem_cutFinset (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool)
    (e : Sym2 V) :
    e ∈ cutFinset G f ↔ e ∈ G.edgeFinset ∧ ∃ u v, e = s(u, v) ∧ f u ≠ f v := by
  simp only [cutFinset, Finset.mem_filter]

/-- Flipping the value at `u` is an involution. -/
private lemma flip_invol (u : V) (f : V → Bool) :
    Function.update (Function.update f u (!(f u))) u
      (!(Function.update f u (!(f u)) u)) = f := by
  funext w
  by_cases hw : w = u
  · subst hw
    simp [Function.update_self]
  · rw [Function.update_of_ne hw, Function.update_of_ne hw]

/-- For distinct `u v`, exactly half of all bipartitions separate them.
Proved by the flip-at-`u` involution, with no fiber counting. -/
lemma card_filter_ne (u v : V) (huv : u ≠ v) :
    (Finset.univ.filter (fun f : V → Bool => f u ≠ f v)).card
      = 2 ^ (Fintype.card V - 1) := by
  classical
  have hcard_eq : (Finset.univ.filter (fun f : V → Bool => f u ≠ f v)).card
      = (Finset.univ.filter (fun f : V → Bool => f u = f v)).card := by
    apply Finset.card_bij (fun f _ => Function.update f u (!(f u)))
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      rw [Function.update_self, Function.update_of_ne huv.symm]
      cases hu : f u <;> cases hv : f v <;> simp_all
    · intro f _ g _ hfg
      have hinj : Function.Injective
          (fun f : V → Bool => Function.update f u (!(f u))) :=
        Function.Involutive.injective (fun f => flip_invol u f)
      exact hinj hfg
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      refine ⟨Function.update g u (!(g u)), ?_, flip_invol u g⟩
      rw [Function.update_self, Function.update_of_ne huv.symm, hg]
      cases hv : g v <;> simp [hv]
  have hsum : (Finset.univ.filter (fun f : V → Bool => f u ≠ f v)).card
      + (Finset.univ.filter (fun f : V → Bool => f u = f v)).card
      = 2 ^ Fintype.card V := by
    have hunion : Finset.univ.filter (fun f : V → Bool => f u ≠ f v)
        ∪ Finset.univ.filter (fun f : V → Bool => f u = f v) = Finset.univ := by
      ext f
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => (eq_or_ne (f u) (f v)).symm⟩
    have hdisj : Disjoint (Finset.univ.filter (fun f : V → Bool => f u ≠ f v))
        (Finset.univ.filter (fun f : V → Bool => f u = f v)) := by
      rw [Finset.disjoint_filter]
      intro f _ h1 h2
      exact h1 h2
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool]
  have hN : 1 ≤ Fintype.card V := by
    haveI : Nonempty V := ⟨u⟩
    exact Fintype.card_pos
  have hpow : (2 : ℕ) ^ Fintype.card V = 2 * 2 ^ (Fintype.card V - 1) := by
    nth_rewrite 1 [← Nat.sub_add_cancel hN]
    rw [pow_succ']
  omega

/-- Card as a sum of indicators over the edge set. -/
lemma card_cutFinset_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) : (cutFinset G f).card
    = ∑ e ∈ G.edgeFinset, (if e ∈ cutFinset G f then (1 : ℕ) else 0) := by
  classical
  have hsub : cutFinset G f ⊆ G.edgeFinset := Finset.filter_subset _ _
  have heq : G.edgeFinset.filter (· ∈ cutFinset G f) = cutFinset G f := by
    ext e
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨hsub h, h⟩
  calc (cutFinset G f).card
      = (G.edgeFinset.filter (· ∈ cutFinset G f)).card := by rw [heq]
    _ = ∑ e ∈ G.edgeFinset, (if e ∈ cutFinset G f then (1 : ℕ) else 0) := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
/-- For a single edge, the number of separating bipartitions. -/
lemma sum_single_edge_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (huv : u ≠ v) (he : s(u, v) ∈ G.edgeFinset) :
    ∑ f : V → Bool, (if s(u, v) ∈ cutFinset G f then (1 : ℕ) else 0)
      = 2 ^ (Fintype.card V - 1) := by
  classical
  have hmem : ∀ f : V → Bool, (s(u, v) ∈ cutFinset G f) ↔ (f u ≠ f v) := by
    intro f
    rw [mem_cutFinset]
    constructor
    · rintro ⟨-, u', v', heq, hne⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact Ne.symm hne
    · intro hne
      exact ⟨he, u, v, rfl, hne⟩
  calc ∑ f : V → Bool, (if s(u, v) ∈ cutFinset G f then (1 : ℕ) else 0)
      = ∑ f : V → Bool, (if f u ≠ f v then (1 : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro f _
        simp only [hmem f]
    _ = (Finset.univ.filter (fun f : V → Bool => f u ≠ f v)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = 2 ^ (Fintype.card V - 1) := card_filter_ne u v huv
/-- Double count: the total number of cut edges over all bipartitions. -/
lemma sum_cutFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ f : V → Bool, (cutFinset G f).card
      = G.edgeFinset.card * 2 ^ (Fintype.card V - 1) := by
  classical
  calc ∑ f : V → Bool, (cutFinset G f).card
      = ∑ f : V → Bool, ∑ e ∈ G.edgeFinset,
          (if e ∈ cutFinset G f then (1 : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro f _
        exact card_cutFinset_eq_sum G f
    _ = ∑ e ∈ G.edgeFinset, ∑ f : V → Bool,
        (if e ∈ cutFinset G f then (1 : ℕ) else 0) := Finset.sum_comm
    _ = ∑ e ∈ G.edgeFinset, 2 ^ (Fintype.card V - 1) := by
        apply Finset.sum_congr rfl
        intro e he
        obtain ⟨u, v⟩ := e
        have huv : u ≠ v := by
          have hadj : G.Adj u v := by simpa using he
          exact SimpleGraph.Adj.ne hadj
        exact sum_single_edge_mk G u v huv he
    _ = G.edgeFinset.card * 2 ^ (Fintype.card V - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
/-- The random-cut lemma: some bipartition keeps at least half the edges. -/
lemma exists_cut_half (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ f : V → Bool, G.edgeFinset.card ≤ 2 * (cutFinset G f).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ f : V → Bool, 2 * (cutFinset G f).card < G.edgeFinset.card := by
    intro f
    have := hcon f
    omega
  have hlt_sum : ∑ f : V → Bool, 2 * (cutFinset G f).card
      < 2 ^ Fintype.card V * G.edgeFinset.card := by
    have hne : (Finset.univ : Finset (V → Bool)).Nonempty :=
      ⟨fun _ => false, Finset.mem_univ _⟩
    calc ∑ f : V → Bool, 2 * (cutFinset G f).card
        < ∑ _f : V → Bool, G.edgeFinset.card :=
          Finset.sum_lt_sum_of_nonempty hne (fun f _ => hlt f)
      _ = 2 ^ Fintype.card V * G.edgeFinset.card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
            Fintype.card_bool, nsmul_eq_mul]
          norm_cast
  have hT : ∑ f : V → Bool, 2 * (cutFinset G f).card
      = G.edgeFinset.card * 2 ^ Fintype.card V := by
    have h2 : ∑ f : V → Bool, 2 * (cutFinset G f).card
        = 2 * (∑ f : V → Bool, (cutFinset G f).card) := by
      rw [Finset.mul_sum]
    rw [h2, sum_cutFinset_eq]
    rcases Nat.eq_zero_or_pos (Fintype.card V) with hN0 | hNpos
    · have hE : G.edgeFinset = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨u, v⟩ := e
        have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
        omega
      simp [hE]
    · have hpow : (2 : ℕ) ^ Fintype.card V = 2 * 2 ^ (Fintype.card V - 1) := by
        nth_rewrite 1 [← Nat.sub_add_cancel hNpos]
        rw [pow_succ']
      rw [hpow]
      ring
  have hcon2 : G.edgeFinset.card * 2 ^ Fintype.card V
      < G.edgeFinset.card * 2 ^ Fintype.card V := by
    calc G.edgeFinset.card * 2 ^ Fintype.card V
        = ∑ f : V → Bool, 2 * (cutFinset G f).card := hT.symm
      _ < 2 ^ Fintype.card V * G.edgeFinset.card := hlt_sum
      _ = G.edgeFinset.card * 2 ^ Fintype.card V := mul_comm _ _
  exact lt_irrefl _ hcon2
/-! ## Mantel's bound: triangle-free graphs are sparse -/

/-- A triangle in `G` contradicts `CliqueFree 3`. -/
private lemma not_cliqueFree_of_triangle (G : SimpleGraph V)
    (hfree : G.CliqueFree 3) {u v w : V} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hadj : G.Adj u v) (huadj : G.Adj u w) (hvadj : G.Adj v w) :
    False := by
  have htri : G.IsNClique 3 ({u, v, w} : Finset V) := by
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro a ha b hb hab
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact absurd rfl hab
      · exact hadj
      · exact huadj
      · exact G.symm hadj
      · exact absurd rfl hab
      · exact hvadj
      · exact G.symm huadj
      · exact G.symm hvadj
      · exact absurd rfl hab
    · have h1 : u ∉ ({v, w} : Finset V) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨huv, huw⟩
      have h2 : v ∉ ({w} : Finset V) := by
        simp only [Finset.mem_singleton]
        exact hvw
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_singleton]
  exact (hfree _ htri).elim
/-- For an edge `u v` in a triangle-free graph, `degree u + degree v ≤ |V|`. -/
lemma degree_add_le_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 3) {u v : V} (hadj : G.Adj u v) :
    G.degree u + G.degree v ≤ Fintype.card V := by
  classical
  have huv : u ≠ v := SimpleGraph.Adj.ne hadj
  have hdisj : Disjoint (G.neighborFinset u \ {v}) (G.neighborFinset v \ {u}) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hw1 hw2
    obtain ⟨huw, -⟩ := hw1
    obtain ⟨hvw, -⟩ := hw2
    exact not_cliqueFree_of_triangle G hfree huv (SimpleGraph.Adj.ne huw)
      (SimpleGraph.Adj.ne hvw) hadj huw hvw
  have hsub : (G.neighborFinset u \ {v}) ∪ (G.neighborFinset v \ {u})
      ⊆ Finset.univ \ {u, v} := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with ⟨hw, hwv⟩ | ⟨hw, hwu⟩
    · rw [SimpleGraph.mem_neighborFinset] at hw
      push_neg
      exact ⟨(SimpleGraph.Adj.ne hw).symm, hwv⟩
    · rw [SimpleGraph.mem_neighborFinset] at hw
      push_neg
      exact ⟨hwu, (SimpleGraph.Adj.ne hw).symm⟩
  have hcard : (G.neighborFinset u \ {v}).card + (G.neighborFinset v \ {u}).card
      ≤ Fintype.card V - 2 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    have h2 : (Finset.univ \ ({u, v} : Finset V)).card = Fintype.card V - 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      have h3 : u ∉ ({v} : Finset V) := by simp [huv]
      rw [Finset.card_insert_of_notMem h3, Finset.card_singleton]
    omega
  have hn2 : 2 ≤ Fintype.card V := by
    have hle : ({u, v} : Finset V).card ≤ Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    have h3 : u ∉ ({v} : Finset V) := by simp [huv]
    rwa [Finset.card_insert_of_notMem h3, Finset.card_singleton] at hle
  have hdu : G.degree u = (G.neighborFinset u \ {v}).card + 1 := by
    have hmem : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr hadj
    have hsplit : G.neighborFinset u = insert v (G.neighborFinset u \ {v}) := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · intro hw
        by_cases h : w = v
        · exact Or.inl h
        · exact Or.inr ⟨hw, h⟩
      · rintro (rfl | ⟨hw, -⟩)
        · exact hmem
        · exact hw
    have h1 : G.degree u = (G.neighborFinset u).card :=
      (SimpleGraph.card_neighborFinset_eq_degree G u).symm
    have hnot : v ∉ SDiff.sdiff (G.neighborFinset u) {v} := by simp [Finset.mem_sdiff]
    rw [h1]
    conv_lhs => rw [hsplit]
    exact Finset.card_insert_of_notMem hnot
  have hdv : G.degree v = (G.neighborFinset v \ {u}).card + 1 := by
    have hmem : u ∈ G.neighborFinset v :=
      (SimpleGraph.mem_neighborFinset G v u).mpr (G.symm hadj)
    have hsplit : G.neighborFinset v = insert u (G.neighborFinset v \ {u}) := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · intro hw
        by_cases h : w = u
        · exact Or.inl h
        · exact Or.inr ⟨hw, h⟩
      · rintro (rfl | ⟨hw, -⟩)
        · exact hmem
        · exact hw
    have h1 : G.degree v = (G.neighborFinset v).card :=
      (SimpleGraph.card_neighborFinset_eq_degree G v).symm
    have hnot : u ∉ SDiff.sdiff (G.neighborFinset v) {u} := by simp [Finset.mem_sdiff]
    rw [h1]
    conv_lhs => rw [hsplit]
    exact Finset.card_insert_of_notMem hnot
  omega
/-- Edges incident to `v` are in bijection with its neighbors. -/
lemma card_filter_mem_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (G.edgeFinset.filter (fun e => v ∈ e)).card = G.degree v := by
  classical
  rw [eq_comm, ← SimpleGraph.card_neighborFinset_eq_degree G v]
  apply Finset.card_bij (fun w _ => s(v, w))
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_filter]
    refine ⟨?_, (Sym2.mem_iff).mpr (Or.inl rfl)⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hw
  · intro w₁ hw₁ w₂ hw₂ h
    rw [SimpleGraph.mem_neighborFinset] at hw₁ hw₂
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exact absurd h1.symm (SimpleGraph.Adj.ne hw₂).symm
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heE, hmem⟩ := he
    obtain ⟨u, w⟩ := e
    rw [Sym2.mem_iff] at hmem
    rcases hmem with h1 | h1
    · subst h1
      refine ⟨w, ?_, rfl⟩
      rw [SimpleGraph.mem_neighborFinset]
      have hadj : G.Adj v w := by simpa using heE
      exact hadj
    · subst h1
      refine ⟨u, ?_, ?_⟩
      · rw [SimpleGraph.mem_neighborFinset]
        have hadj : G.Adj u v := by simpa using heE
        exact G.symm hadj
      · rw [Sym2.eq_iff]
        exact Or.inr ⟨rfl, rfl⟩
/-- The vertices in an edge are exactly its two endpoints. -/
lemma filter_mem_mk_eq (u v : V) (huv : u ≠ v) :
    Finset.univ.filter (fun w => w ∈ s(u, v)) = {u, v} := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Sym2.mem_iff]

/-- For a single edge, the incident degree sum. -/
lemma sum_filter_mem_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 3) (u v : V) (huv : u ≠ v)
    (he : s(u, v) ∈ G.edgeFinset) :
    ∑ w ∈ Finset.univ.filter (fun w => w ∈ s(u, v)), G.degree w
      ≤ Fintype.card V := by
  classical
  have hadj : G.Adj u v := by simpa using he
  rw [filter_mem_mk_eq u v huv, Finset.sum_insert (by simp [huv]),
    Finset.sum_singleton]
  exact degree_add_le_of_adj G hfree hadj
/-- Double count: `∑ v, degree v ^ 2` via edge incidences. -/
lemma sum_degree_sq_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ v : V, (G.degree v) ^ 2
      = ∑ e ∈ G.edgeFinset,
        ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), G.degree v := by
  classical
  have per_v : ∀ v : V, (G.degree v) ^ 2
      = ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), G.degree v := by
    intro v
    rw [Finset.sum_const, nsmul_eq_mul, ← card_filter_mem_edgeFinset G v,
      pow_two]
    norm_cast
  calc ∑ v : V, (G.degree v) ^ 2
      = ∑ v : V, ∑ e ∈ G.edgeFinset.filter (fun e => v ∈ e), G.degree v := by
        apply Finset.sum_congr rfl
        intro v _
        exact per_v v
    _ = ∑ v : V, ∑ e ∈ G.edgeFinset, (if v ∈ e then G.degree v else 0) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_filter]
    _ = ∑ e ∈ G.edgeFinset, ∑ v : V, (if v ∈ e then G.degree v else 0) :=
        Finset.sum_comm
    _ = ∑ e ∈ G.edgeFinset,
        ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), G.degree v := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.sum_filter]
/-- Mantel's theorem: a triangle-free graph has at most `n²/4` edges. -/
lemma mantel (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  classical
  have hdeg : ∀ e ∈ G.edgeFinset,
      ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), G.degree v
        ≤ Fintype.card V := by
    intro e he
    obtain ⟨u, v⟩ := e
    have huv : u ≠ v := by
      have hadj : G.Adj u v := by simpa using he
      exact SimpleGraph.Adj.ne hadj
    exact sum_filter_mem_le G hfree u v huv he
  have hsum1 : ∑ e ∈ G.edgeFinset,
      ∑ v ∈ Finset.univ.filter (fun v => v ∈ e), G.degree v
      ≤ Fintype.card V * G.edgeFinset.card := by
    calc _ ≤ ∑ e ∈ G.edgeFinset, Fintype.card V := Finset.sum_le_sum hdeg
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        norm_cast
        exact mul_comm _ _
  have hsq_nat : ∑ v : V, (G.degree v) ^ 2
      ≤ Fintype.card V * G.edgeFinset.card := by
    rw [sum_degree_sq_eq]
    exact hsum1
  -- Cauchy–Schwarz in ℚ
  have hCS : ((∑ v : V, (G.degree v : ℚ)) ^ 2
      ≤ (Fintype.card V : ℚ) * ∑ v : V, ((G.degree v : ℚ) ^ 2)) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun v : V => (G.degree v : ℚ))
    rwa [Finset.card_univ] at h
  have h1 : (∑ v : V, (G.degree v : ℚ)) = 2 * (G.edgeFinset.card : ℚ) := by
    rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges, Nat.cast_mul,
      Nat.cast_ofNat]
  have h2 : (∑ v : V, ((G.degree v : ℚ) ^ 2))
      ≤ (Fintype.card V : ℚ) * (G.edgeFinset.card : ℚ) := by
    rw [show (∑ v : V, ((G.degree v : ℚ) ^ 2))
        = (((∑ v : V, (G.degree v) ^ 2 : ℕ)) : ℚ)
      from by simp only [← Nat.cast_pow, ← Nat.cast_sum]]
    rw [← Nat.cast_mul]
    exact Nat.cast_le.mpr hsq_nat
  have h3 : ((2 * (G.edgeFinset.card : ℚ)) ^ 2)
      ≤ ((Fintype.card V : ℚ)) ^ 2 * (G.edgeFinset.card : ℚ) := by
    calc (2 * (G.edgeFinset.card : ℚ)) ^ 2
        = (∑ v : V, (G.degree v : ℚ)) ^ 2 := by rw [h1]
      _ ≤ (Fintype.card V : ℚ) * ∑ v : V, ((G.degree v : ℚ) ^ 2) := hCS
      _ ≤ (Fintype.card V : ℚ) * (((Fintype.card V : ℚ))
          * (G.edgeFinset.card : ℚ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((Fintype.card V : ℚ)) ^ 2 * (G.edgeFinset.card : ℚ) := by ring
  rcases eq_or_ne (G.edgeFinset.card : ℚ) 0 with h0 | h0
  · have hC0 : G.edgeFinset.card = 0 := by exact_mod_cast h0
    rw [hC0]
    simp
  · have hpos : (0 : ℚ) < (G.edgeFinset.card : ℚ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm h0)
    have h4 : (4 * (G.edgeFinset.card : ℚ)) ≤ ((Fintype.card V : ℚ)) ^ 2 := by
      have hrw : (2 * (G.edgeFinset.card : ℚ)) ^ 2
          = (4 * (G.edgeFinset.card : ℚ)) * (G.edgeFinset.card : ℚ) := by ring
      rw [hrw] at h3
      exact le_of_mul_le_mul_right h3 hpos
    exact_mod_cast h4
/-! ## The cut subgraph and the bipartization bound -/

/-- The spanning subgraph keeping exactly the cut edges. -/
def cutGraph (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u ≠ f v
  symm u v h := ⟨G.symm h.1, Ne.symm h.2⟩
  loopless u h := G.loopless u h.1

lemma cutGraph_le (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Bool) :
    cutGraph G f ≤ G := by
  intro u v h
  exact h.1

lemma cutGraph_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) : (cutGraph G f).IsBipartite := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (fun v => if f v then (1 : Fin 2) else 0) ?_⟩
  intro u v hadj
  have hne : f u ≠ f v := hadj.2
  by_cases hu : f u <;> by_cases hv : f v <;> simp_all

lemma cutGraph_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Bool) : (cutGraph G f).edgeFinset = cutFinset G f := by
  classical
  ext e
  simp only [cutFinset, Finset.mem_filter]
  constructor
  · intro he
    obtain ⟨u, v⟩ := e
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    obtain ⟨hadj, hne⟩ := he
    refine ⟨?_, u, v, rfl, hne⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hadj
  · rintro ⟨heG, u, v, rfl, hne⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    have hadj : G.Adj u v := by
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heG
    exact ⟨hadj, hne⟩
/-- Bipartization with `25n²/8` deletions: the piece's main statement.
Weaker than the conjectured `n²`, via the random-cut technique. -/
theorem bipartization_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : G.CliqueFree 3) (n : ℕ) (hn : Fintype.card V = 5 * n) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
      8 * (G.edgeFinset \ H.edgeFinset).card ≤ 25 * n ^ 2 := by
  classical
  obtain ⟨f, hf⟩ := exists_cut_half G
  refine ⟨cutGraph G f, cutGraph_le G f, cutGraph_bipartite G f, ?_⟩
  rw [cutGraph_edgeFinset]
  have hsub : cutFinset G f ⊆ G.edgeFinset := Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hsub]
  have hmantel : 4 * G.edgeFinset.card ≤ (5 * n) ^ 2 := by
    have h := mantel G hfree
    rwa [hn] at h
  have h2 : 2 * (G.edgeFinset.card - (cutFinset G f).card)
      ≤ G.edgeFinset.card := by omega
  have hsq : (5 * n) ^ 2 = 25 * n ^ 2 := by ring
  omega

end Contribution.Erdos23
