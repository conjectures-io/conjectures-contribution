import Mathlib
import FormalConjectures.ErdosProblems.«23»

/-!
# Erdős Problem 23: the `n5_tight` variant

There exists a triangle-free graph on 25 vertices such that at least 25 edges must be
removed to make it bipartite.  The witness is the balanced blow-up of `C₅` with five
parts of size 5, realized on `Fin 25` (vertex `v` lies in block `v / 5 ∈ ZMod 5`, and
two vertices are adjacent iff their blocks are consecutive mod 5).

The lower bound is proved by exhibiting 25 pairwise edge-disjoint 5-cycles that
together use all 125 edges: for `(s, t) : ZMod 5 × ZMod 5` the transversal cycle
visits block `i` at offset `s + i * t`.  A bipartite subgraph (i.e. one that is
properly 2-colorable) must omit at least one edge of every odd cycle, and since the
25 cycles are edge-disjoint this forces at least 25 omitted edges.
-/

open SimpleGraph BigOperators

namespace Contribution.ErdosTwentyThreeN5Tight

/-- A kernel-reducible decidability instance for implications, so that `decide` can
handle statements of the form `hypothesis → conclusion`. -/
instance (priority := 500) instDecidableArrow {p q : Prop} [Decidable p] [Decidable q] :
    Decidable (p → q) :=
  if hp : p then
    if hq : q then .isTrue fun _ => hq else .isFalse fun h => hq (h hp)
  else .isTrue fun h => absurd h hp

/-- The block of a vertex of `Fin 25`: which of the five groups of five consecutive
vertices it belongs to, as an element of `ZMod 5`. -/
def blk (v : Fin 25) : ZMod 5 := ((v : ℕ) / 5 : ℕ)

/-- The balanced blow-up of the 5-cycle `C₅` with five parts of size 5, on `Fin 25`:
two vertices are adjacent iff their blocks are consecutive in `ZMod 5`. -/
def G25 : SimpleGraph (Fin 25) :=
  SimpleGraph.fromRel fun u v => blk u + 1 = blk v ∨ blk v + 1 = blk u

instance : DecidableRel G25.Adj := fun a b =>
  decidable_of_iff
    (a ≠ b ∧ ((blk a + 1 = blk b ∨ blk b + 1 = blk a) ∨
      (blk b + 1 = blk a ∨ blk a + 1 = blk b))) Iff.rfl

/-- Encode a pair (block, offset) as a vertex of `Fin 25`. -/
def enc (i x : ZMod 5) : Fin 25 :=
  ⟨5 * i.val + x.val, by
    have hi : i.val < 5 := i.val_lt
    have hx : x.val < 5 := x.val_lt
    omega⟩

/-- The `i`-th vertex of the transversal 5-cycle indexed by `(s, t)`:
it lies in block `i` at offset `s + i * t`. -/
def cyc (s t i : ZMod 5) : Fin 25 := enc i (s + i * t)

/-- Consecutive vertices of each transversal cycle are adjacent in `G25`. -/
lemma cyc_adj : ∀ s t i : ZMod 5, G25.Adj (cyc s t i) (cyc s t (i + 1)) := by decide

/-- The transversal cycles are pairwise edge-disjoint: an (unordered) edge shared by the
cycles indexed by `(s, t)` and `(s', t')` forces `s = s'` and `t = t'`. -/
lemma cyc_disj : ∀ s t i s' t' i' : ZMod 5,
    (cyc s t i = cyc s' t' i' ∧ cyc s t (i + 1) = cyc s' t' (i' + 1)) ∨
      (cyc s t i = cyc s' t' (i' + 1) ∧ cyc s t (i + 1) = cyc s' t' i') →
    s = s' ∧ t = t' := by decide

/-- The 5-cycle on `ZMod 5` (block level) has no triangles. -/
lemma blk_no_triangle : ∀ a b c : ZMod 5,
    (a + 1 = b ∨ b + 1 = a) → (a + 1 = c ∨ c + 1 = a) → (b + 1 = c ∨ c + 1 = b) →
    False := by decide

/-- The blow-up `G25` is triangle-free. -/
lemma G25_cliqueFree : G25.CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
  simp only [G25, SimpleGraph.fromRel_adj] at hab hac hbc
  exact blk_no_triangle (blk a) (blk b) (blk c)
    (by tauto) (by tauto) (by tauto)

/-- A 5-cycle admits no proper 2-coloring. -/
lemma fin2_cycle : ∀ x0 x1 x2 x3 x4 : Fin 2,
    ¬(x0 ≠ x1 ∧ x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x4 ∧ x4 ≠ x0) := by decide

/-- If `H` is properly 2-colored, then every transversal cycle has an edge missing
from `H`. -/
lemma exists_missing (H : SimpleGraph (Fin 25)) (col : H.Coloring (Fin 2))
    (s t : ZMod 5) :
    ∃ i : ZMod 5, s(cyc s t i, cyc s t (i + 1)) ∉ H.edgeSet := by
  by_contra hcon
  push_neg at hcon
  have hAdj : ∀ i : ZMod 5, H.Adj (cyc s t i) (cyc s t (i + 1)) := fun i =>
    (H.mem_edgeSet).mp (hcon i)
  have hne : ∀ i : ZMod 5, col (cyc s t i) ≠ col (cyc s t (i + 1)) := fun i =>
    col.valid (hAdj i)
  have h0 := hne 0
  have h1 := hne 1
  have h2 := hne 2
  have h3 := hne 3
  have h4 := hne 4
  have e0 : (0 : ZMod 5) + 1 = 1 := by decide
  have e1 : (1 : ZMod 5) + 1 = 2 := by decide
  have e2 : (2 : ZMod 5) + 1 = 3 := by decide
  have e3 : (3 : ZMod 5) + 1 = 4 := by decide
  have e4 : (4 : ZMod 5) + 1 = 0 := by decide
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  exact fin2_cycle _ _ _ _ _ ⟨h0, h1, h2, h3, h4⟩

section Main

open Classical

/-- **Erdős Problem 23, `n = 5` tightness.**
There exists a triangle-free graph on 25 vertices such that at least 25 edges must be
removed to make it bipartite. -/
theorem n5_tight :
    ∃ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 25)),
        H ≤ G → H.IsBipartite → 25 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  refine ⟨G25, G25_cliqueFree, fun H _ hBip => ?_⟩
  have hcol : Nonempty (H.Coloring (Fin 2)) := hBip
  obtain ⟨col⟩ := hcol
  have hmiss : ∀ p : ZMod 5 × ZMod 5,
      ∃ i : ZMod 5, s(cyc p.1 p.2 i, cyc p.1 p.2 (i + 1)) ∉ H.edgeSet := fun p =>
    exists_missing H col p.1 p.2
  choose idx hidx using hmiss
  have hcard : (25 : ℕ) = (Finset.univ : Finset (ZMod 5 × ZMod 5)).card := by decide
  refine le_of_eq_of_le hcard ?_
  refine Finset.card_le_card_of_injOn
    (fun p => s(cyc p.1 p.2 (idx p), cyc p.1 p.2 (idx p + 1))) ?_ ?_
  · intro p _
    simp only [Finset.mem_coe, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨(G25.mem_edgeSet).mpr (cyc_adj p.1 p.2 (idx p)), hidx p⟩
  · intro p _ q _ hpq
    simp only [Sym2.eq_iff] at hpq
    obtain ⟨hs, ht⟩ := cyc_disj p.1 p.2 (idx p) q.1 q.2 (idx q) hpq
    exact Prod.ext hs ht

end Main

end Contribution.ErdosTwentyThreeN5Tight
