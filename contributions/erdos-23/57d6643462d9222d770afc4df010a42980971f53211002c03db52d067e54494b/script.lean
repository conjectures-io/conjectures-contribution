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
