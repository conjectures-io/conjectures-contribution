import Mathlib
import FormalConjectures.ErdosProblems.«617»

/-!
# Erdős 617: sparse minimal cores, weighted extension, and five colours

For a capped r-colouring of K_(r²+1), r >= 4, this development constructs an
actual colour layer and a proper minimal core W with a = alpha_i(W),
|W| = r*a+1, 4 <= a <= r-2, and 2r-2 <= S <= r(r-a).
Here S is the sum of the selected core degrees minus r. Nonnegativity follows
from minimality; the colouring and carrier remain common to every lemma.

The main interface is `sparse_core_reduction`. Its corollary
`five_colour_case` is the exact five-colour specialization of the target.
The weighted extension development also proves `missing_colour_of_excess`,
which does not assume a capped colouring in its statement.

This is not a proof of the full all-r conjecture. The surviving sparse-core
range for larger r is not excluded. See sources.md for attribution, the
relationship to the existing contribution, and explicit use cases.
-/

noncomputable section
namespace Contribution.Erdos617SparseCore

/- ## SmallBlocker -/
section
/- Common-colouring extension obstructions and minimal-core foundations.
No general resilience theorem is assumed. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}
abbrev Coloring (V : Type) (r : ℕ) := Sym2 V → Fin r

def Independent (c : Coloring V r) (i : Fin r) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x,y) ≠ i

def Clique (c : Coloring V r) (i : Fin r) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x,y) = i

def Caps (c : Coloring V r) : Prop :=
  ∀ i S, Independent c i S → S.card ≤ r

def alphaOn (c : Coloring V r) (i : Fin r) (W : Finset V) : ℕ :=
  (W.powerset.filter (Independent c i)).sup Finset.card

lemma independent_mono {c : Coloring V r} {i : Fin r} {S W : Finset V}
    (h : S ⊆ W) (hi : Independent c i W) : Independent c i S := by
  intro x hx y hy hxy
  exact hi x (h hx) y (h hy) hxy

lemma independent_insert {c : Coloring V r} {i : Fin r} {S : Finset V} {x : V}
    (hS : Independent c i S) (hx : ∀ y ∈ S, c s(x,y) ≠ i) :
    Independent c i (insert x S) := by
  intro u hu v hv huv
  by_cases hux : u = x
  · subst u
    have hvS : v ∈ S := (mem_insert.mp hv).resolve_left (Ne.symm huv)
    exact hx v hvS
  · have huS : u ∈ S := (mem_insert.mp hu).resolve_left hux
    by_cases hvx : v = x
    · subst v
      rw [Sym2.eq_swap]
      exact hx u huS
    · exact hS u huS v ((mem_insert.mp hv).resolve_left hvx) huv

lemma alpha_witness (c : Coloring V r) (i : Fin r) (W : Finset V) :
    ∃ A ⊆ W, Independent c i A ∧ A.card = alphaOn c i W := by
  have he : (∅ : Finset V) ∈ W.powerset.filter (Independent c i) := by
    simp [Independent]
  obtain ⟨A,hA,hc⟩ := exists_mem_eq_sup _ ⟨∅,he⟩ Finset.card
  exact ⟨A,mem_powerset.mp (mem_filter.mp hA).1,(mem_filter.mp hA).2,hc.symm⟩

lemma card_le_alpha {c : Coloring V r} {i : Fin r} {S W : Finset V}
    (hS : S ⊆ W) (hi : Independent c i S) : S.card ≤ alphaOn c i W := by
  exact le_sup (mem_filter.mpr ⟨mem_powerset.mpr hS,hi⟩)

lemma alpha_mono (c : Coloring V r) (i : Fin r) {S W : Finset V}
    (h : S ⊆ W) : alphaOn c i S ≤ alphaOn c i W := by
  obtain ⟨A,hA,hi,hc⟩ := alpha_witness c i S
  rw [← hc]
  exact card_le_alpha (hA.trans h) hi


lemma alpha_pos (c : Coloring V r) (i : Fin r) {W : Finset V}
    (hw : W.Nonempty) : 0 < alphaOn c i W := by
  obtain ⟨x,hx⟩ := hw
  have hs : Independent c i {x} := by
    intro u hu v hv huv
    have hu' := mem_singleton.mp hu
    have hv' := mem_singleton.mp hv
    exact (huv (hu'.trans hv'.symm)).elim
  have h := card_le_alpha (singleton_subset_iff.mpr hx) hs
  have hh : 1 ≤ alphaOn c i W := by simpa using h
  omega

/-- Inclusion-minimal violation of |X| <= r alpha(X). -/
def Minimal (c : Coloring V r) (i : Fin r) (W : Finset V) : Prop :=
  r * alphaOn c i W < W.card ∧
  ∀ X, X ⊂ W → X.card ≤ r * alphaOn c i X

lemma minimal_exists (c : Coloring V r) (i : Fin r) (U : Finset V)
    (hU : r * alphaOn c i U < U.card) :
    ∃ W ⊆ U, Minimal c i W := by
  let F := U.powerset.filter (fun W => r * alphaOn c i W < W.card)
  have hu : U ∈ F := by simp [F,hU]
  obtain ⟨W,hW,hmin⟩ := exists_min_image F Finset.card ⟨U,hu⟩
  have hw := mem_filter.mp hW
  refine ⟨W,mem_powerset.mp hw.1,hw.2,?_⟩
  intro X hX
  by_contra hx
  have hxf : X ∈ F := mem_filter.mpr
    ⟨mem_powerset.mpr (hX.subset.trans (mem_powerset.mp hw.1)),by omega⟩
  have hle := hmin X hxf
  have hlt := card_lt_card hX
  omega

lemma minimal_card (c : Coloring V r) (i : Fin r) {W : Finset V}
    (h : Minimal c i W) : W.card = r * alphaOn c i W + 1 := by
  have hp : 0 < W.card := by have hh := h.1; omega
  obtain ⟨x,hx⟩ := card_pos.mp hp
  have hprev := h.2 (W.erase x) (erase_ssubset hx)
  have hm := Nat.mul_le_mul_left r (alpha_mono c i (erase_subset x W))
  rw [card_erase_of_mem hx] at hprev
  have hb := h.1
  omega

/-- A deletion of at most r vertices preserves independence in the minimal core. -/
lemma minimal_deletion (c : Coloring V r) (i : Fin r) {W : Finset V}
    (h : Minimal c i W) (D : Finset V) (hd : D.card ≤ r) :
    alphaOn c i (W \ D) = alphaOn c i W := by
  apply le_antisymm (alpha_mono c i sdiff_subset)
  by_cases he : W \ D = W
  · rw [he]
  have hs : W \ D ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,he⟩
  have hp := h.2 _ hs
  have hc := card_sdiff_add_card_inter W D
  have hi : (W ∩ D).card ≤ r := (card_le_card inter_subset_right).trans hd
  have hm := minimal_card c i h
  by_contra ha
  have hb : alphaOn c i (W \ D) + 1 ≤ alphaOn c i W := by omega
  have hmul := Nat.mul_le_mul_left r hb
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

/-- Degree in the actual induced colour graph on W, excluding diagonal pairs. -/
def degreeOn (c : Coloring V r) (i : Fin r) (W : Finset V) (x : V) : ℕ :=
  (W.filter (fun y => y ≠ x ∧ c s(x,y) = i)).card

lemma minimal_degree (c : Coloring V r) (i : Fin r) {W : Finset V}
    (h : Minimal c i W) {x : V} (hx : x ∈ W) : r ≤ degreeOn c i W x := by
  let D := insert x (W.filter (fun y => y ≠ x ∧ c s(x,y) = i))
  have hc : D.card = degreeOn c i W x + 1 := by simp [D,degreeOn]
  by_contra hd
  have hdr : D.card ≤ r := by omega
  have he := minimal_deletion c i h D hdr
  obtain ⟨A,hA,hI,ha⟩ := alpha_witness c i (W \ D)
  have hxA : x ∉ A := by
    intro ha
    have hh := (mem_sdiff.mp (hA ha)).2
    exact hh (mem_insert_self x _)
  have hi : Independent c i (insert x A) := by
    apply independent_insert hI
    intro y hy hcol
    have hym := mem_sdiff.mp (hA hy)
    have hyx : y ≠ x := by intro he; exact hxA (he ▸ hy)
    exact hym.2 (mem_insert_of_mem (mem_filter.mpr ⟨hym.1,hyx,hcol⟩))
  have hsub : insert x A ⊆ W := insert_subset hx (hA.trans sdiff_subset)
  have hb := card_le_alpha hsub hi
  rw [card_insert_of_notMem hxA,ha,he] at hb
  omega


/-- Adapted from the supplied clique-reduction formalization; provenance is recorded in sources.md.
The same colouring c supplies every colour cap. -/
lemma outside_at_most_one (c : Coloring V r) (i : Fin r) (H : Caps c)
    (C : Finset V) (hC : C.card = r) (hc : Clique c i C)
    (x : V) (hx : x ∉ C) :
    ∀ y ∈ C, ∀ z ∈ C, c s(x,y) = i → c s(x,z) = i → y = z := by
  have hit : ∀ k : Fin r, k ≠ i → ∃ z ∈ C, c s(x,z) = k := by
    intro k hk
    by_contra hb
    push Not at hb
    have hI : Independent c k (insert x C) := by
      apply independent_insert
      · intro u hu v hv huv
        rw [hc u hu v hv huv]
        exact Ne.symm hk
      · exact hb
    have hn := H k (insert x C) hI
    rw [card_insert_of_notMem hx,hC] at hn
    omega
  let D := C.filter (fun z => c s(x,z) ≠ i)
  have image_contains : univ.erase i ⊆ D.image (fun z => c s(x,z)) := by
    intro k hk
    obtain ⟨z,hz,he⟩ := hit k (mem_erase.mp hk).1
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,by simpa [he] using (mem_erase.mp hk).1⟩,he⟩
  have lower : r-1 ≤ D.card := by
    have hh := (card_le_card image_contains).trans (card_image_le)
    simpa using hh
  intro y hy z hz hey hez
  by_contra hyz
  have sub : D ⊆ (C.erase y).erase z := by
    intro v hv
    have hm := mem_filter.mp hv
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,hm.1⟩⟩
    · intro hh; subst v; exact hm.2 hez
    · intro hh; subst v; exact hm.2 hey
  have upper := card_le_card sub
  have hze : z ∈ C.erase y := mem_erase.mpr ⟨Ne.symm hyz,hz⟩
  rw [card_erase_of_mem hze,card_erase_of_mem hy,hC] at upper
  have htwo : 2 ≤ r := by
    have hh : ({y,z} : Finset V) ⊆ C := insert_subset hy (singleton_subset_iff.mpr hz)
    have hh' := card_le_card hh
    simpa [hyz,hC] using hh'
  omega

/-- Unlike a previous-mixed-level assumption, minimality gives the needed
independent set outside the clique intrinsically. -/
lemma minimal_no_r_clique (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    {C : Finset V} (hCW : C ⊆ W) (hC : C.card = r) : ¬Clique c i C := by
  intro hc
  have he := minimal_deletion c i hW C (le_of_eq hC)
  obtain ⟨A,hA,hI,hAc⟩ := alpha_witness c i (W \ C)
  have hAW : A ⊆ W := hA.trans sdiff_subset
  have hxA : ∀ x ∈ C, x ∉ A := by
    intro x hx hax
    exact (mem_sdiff.mp (hA hax)).2 hx
  have dominates : ∀ x ∈ C, ∃ y ∈ A, c s(x,y) = i := by
    intro x hx
    by_contra hn
    push Not at hn
    have hi := independent_insert hI hn
    have hb := card_le_alpha (insert_subset (hCW hx) hAW) hi
    rw [card_insert_of_notMem (hxA x hx),hAc,he] at hb
    omega
  have choose_neighbour : ∀ x : C, ∃ y : A, c s(x.val,y.val) = i := by
    intro x
    obtain ⟨y,hy,hcol⟩ := dominates x.val x.property
    exact ⟨⟨y,hy⟩,hcol⟩
  choose f hf using choose_neighbour
  have finj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hout : (f x).val ∉ C := (mem_sdiff.mp (hA (f x).property)).2
    apply outside_at_most_one c i H C hC hc (f x).val hout
      x.val x.property y.val y.property
    · rw [Sym2.eq_swap]
      exact hf x
    · rw [Sym2.eq_swap]
      have hy := hf y
      rwa [← hxy] at hy
  have hh := Fintype.card_le_of_injective f finj
  have hcard : C.card ≤ A.card := by simpa using hh
  rw [hC,hAc,he] at hcard
  omega

lemma minimal_clique_bound (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    {C : Finset V} (hCW : C ⊆ W) (hc : Clique c i C) : C.card < r := by
  by_contra hlarge
  obtain ⟨D,hDC,hD⟩ := exists_subset_card_eq (by omega : r ≤ C.card)
  apply minimal_no_r_clique c i H hW ha (hDC.trans hCW) hD
  intro x hx y hy hxy
  exact hc x (hDC hx) y (hDC hy) hxy

lemma other_clique_bound (c : Coloring V r) (i j : Fin r) (hji : j ≠ i)
    {W C : Finset V} (hCW : C ⊆ W) (hc : Clique c j C) :
    C.card ≤ alphaOn c i W := by
  apply card_le_alpha hCW
  intro x hx y hy hxy
  rw [hc x hx y hy hxy]
  exact hji

/-- Hits every independent set of the original required size r, not of a changed size. -/
def Hits (c : Coloring V r) (i : Fin r) (T : Finset V) : Prop :=
  ∀ A : Finset V, A.card = r → Independent c i A → (A ∩ T).Nonempty

section FiniteBase
variable [Fintype V]

lemma hits_iff_alpha_delete_lt (c : Coloring V r) (i : Fin r) (T : Finset V) :
    Hits c i T ↔ alphaOn c i (univ \ T) < r := by
  constructor
  · intro h
    by_contra hb
    obtain ⟨A,hA,hI,ha⟩ := alpha_witness c i (univ \ T)
    obtain ⟨S,hSA,hS⟩ := exists_subset_card_eq (by omega : r ≤ A.card)
    obtain ⟨x,hx⟩ := h S hS (independent_mono hSA hI)
    have hh := mem_inter.mp hx
    exact (mem_sdiff.mp (hA (hSA hh.1))).2 hh.2
  · intro h A ha hI
    by_contra hn
    have hsub : A ⊆ univ \ T := by
      intro x hx
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro hxt
      exact hn ⟨x,mem_inter.mpr ⟨hx,hxt⟩⟩
    have hc := card_le_alpha hsub hI
    omega

/-- A small blocker produces a genuine hereditary ratio violation in its complement. -/
lemma ratio_violation_of_small_blocker (c : Coloring V r) (i : Fin r)
    (hV : Fintype.card V = r^2) (T : Finset V) (ht : T.card < r)
    (hhit : Hits c i T) :
    r * alphaOn c i (univ \ T) < (univ \ T).card := by
  have ha := (hits_iff_alpha_delete_lt c i T).mp hhit
  have hm := Nat.mul_le_mul_left r (Nat.succ_le_of_lt ha)
  have hn := card_sdiff_add_card_inter (univ : Finset V) T
  simp only [univ_inter,card_univ,hV] at hn
  rw [Nat.mul_succ] at hm
  nlinarith

/-- All-r reduction under the literal shared-colouring hypotheses. It is a
necessary structure theorem, not a proof that these cores are absent. -/
theorem core_from_small_blocker (c : Coloring V r) (i : Fin r)
    (H : Caps c) (hV : Fintype.card V = r^2)
    (T : Finset V) (ht : T.card < r) (hhit : Hits c i T) :
    ∃ W : Finset V, W ⊆ univ \ T ∧ Minimal c i W ∧
      0 < alphaOn c i W ∧ alphaOn c i W < r ∧
      W.card = r * alphaOn c i W + 1 ∧
      (∀ x ∈ W, r ≤ degreeOn c i W x) ∧
      (∀ C ⊆ W, Clique c i C → C.card < r) ∧
      (∀ j, j ≠ i → ∀ C ⊆ W, Clique c j C → C.card ≤ alphaOn c i W) := by
  have hU := ratio_violation_of_small_blocker c i hV T ht hhit
  obtain ⟨W,hWU,hW⟩ := minimal_exists c i (univ \ T) hU
  have hp : W.Nonempty := card_pos.mp (by have hh := hW.1; omega)
  have ha : alphaOn c i W < r :=
    lt_of_le_of_lt (alpha_mono c i hWU) ((hits_iff_alpha_delete_lt c i T).mp hhit)
  exact ⟨W,hWU,hW,alpha_pos c i hp,ha,minimal_card c i hW,
    fun _ hx => minimal_degree c i hW hx,
    fun _ hs hc => minimal_clique_bound c i H hW ha hs hc,
    fun j hji _ hs hc => other_clique_bound c i j hji hs hc⟩
end FiniteBase


lemma minimal_alpha_two (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    2 ≤ alphaOn c i W := by
  have hp : W.Nonempty := card_pos.mp (by have hh := hW.1; omega)
  have hpos := alpha_pos c i hp
  by_contra hsmall
  have hone : alphaOn c i W = 1 := by omega
  have hc : Clique c i W := by
    intro x hx y hy hxy
    by_contra hcol
    have hi : Independent c i {x,y} := by
      intro u hu v hv huv
      have hu' : u = x ∨ u = y := by simpa using hu
      have hv' : v = x ∨ v = y := by simpa using hv
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact (huv rfl).elim
      · exact hcol
      · rw [Sym2.eq_swap]; exact hcol
      · exact (huv rfl).elim
    have hb := card_le_alpha (insert_subset hx (singleton_subset_iff.mpr hy)) hi
    have hpair : ({x,y} : Finset V).card = 2 := by simp [hxy]
    rw [hpair,hone] at hb
    omega
  have hl := minimal_clique_bound c i H hW ha (Subset.refl W) hc
  have hn := minimal_card c i hW
  rw [hone,Nat.mul_one] at hn
  omega

/-- Connectivity in cut form: every nontrivial partition of the core has
an edge of the selected colour across it. -/
lemma minimal_cross_edge (c : Coloring V r) (i : Fin r)
    {W X Y : Finset V} (hW : Minimal c i W)
    (hX : X.Nonempty) (hY : Y.Nonempty)
    (hd : Disjoint X Y) (hu : X ∪ Y = W) :
    ∃ x ∈ X, ∃ y ∈ Y, c s(x,y) = i := by
  have hxw : X ⊆ W := by rw [← hu]; exact subset_union_left
  have hyw : Y ⊆ W := by rw [← hu]; exact subset_union_right
  have hxs : X ⊂ W := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hxw,?_⟩
    intro he
    obtain ⟨y,hy⟩ := hY
    exact disjoint_left.mp hd (he ▸ hyw hy) hy
  have hys : Y ⊂ W := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hyw,?_⟩
    intro he
    obtain ⟨x,hx⟩ := hX
    exact disjoint_left.mp hd hx (he ▸ hxw hx)
  obtain ⟨A,hAX,hAI,ha⟩ := alpha_witness c i X
  obtain ⟨B,hBY,hBI,hb⟩ := alpha_witness c i Y
  have hab : Disjoint A B := hd.mono hAX hBY
  by_contra hn
  push Not at hn
  have hi : Independent c i (A ∪ B) := by
    intro x hx y hy hxy
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hy with hy | hy
      · exact hAI x hx y hy hxy
      · exact hn x (hAX hx) y (hBY hy)
    · rcases mem_union.mp hy with hy | hy
      · rw [Sym2.eq_swap]
        exact hn y (hAX hy) x (hBY hx)
      · exact hBI x hx y hy hxy
  have sub : A ∪ B ⊆ W := union_subset (hAX.trans hxw) (hBY.trans hyw)
  have hl := card_le_alpha sub hi
  rw [card_union_of_disjoint hab,ha,hb] at hl
  have hlm := Nat.mul_le_mul_left r hl
  rw [Nat.mul_add] at hlm
  have hx := hW.2 X hxs
  have hy := hW.2 Y hys
  have hncard : X.card + Y.card = W.card := by rw [← card_union_of_disjoint hd,hu]
  have hbad := hW.1
  omega
end CoreTheory.MinimalCore

/- Root-extension foundation adapted from an earlier supplied formalization.
Original target copyright: The Formal Conjectures Authors (2026).
Additional credited adapters in the source: Ramazan Kara (Apache-2.0).
Source SHA256: ef0a724ba0cf5ea56c9a3c3ad7697a7f8ebffb6406d9a1960ab15a9b16d1bfa1.
This file reuses only the independent foundation, not the admitted target.
The new CoreTheory declarations below expose the exact partition-to-extension bridge. -/
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
namespace ColourExtension
open Finset
variable {V C : Type} [DecidableEq V] [DecidableEq C]
abbrev Coloring (V C : Type) := Sym2 V → C

def Independent (c : Coloring V C) (i : C) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ i

def Admissible (r : ℕ) (c : Coloring V C) : Prop :=
  ∀ S : Finset V, S.card = r+1 → ∀ i : C, ¬ Independent c i S

def RootHits (r : ℕ) (c : Coloring V C) (f : V → C) : Prop :=
  ∀ i : C, ∀ S : Finset V, S.card = r → Independent c i S →
    ∃ v ∈ S, f v = i

def rawExtend (c : Coloring V C) (f : V → C) (d : C) : Option V → Option V → C
  | some u, some v => c s(u,v)
  | none, some v => f v
  | some v, none => f v
  | none, none => d

def extend (c : Coloring V C) (f : V → C) (d : C) : Coloring (Option V) C :=
  Sym2.lift ⟨rawExtend c f d, by
    intro u v
    cases u <;> cases v <;> simp [rawExtend, Sym2.eq_swap]⟩

@[simp] theorem extend_ss (c : Coloring V C) (f : V → C) (d : C) (u v : V) :
    extend c f d s(some u,some v) = c s(u,v) := rfl
@[simp] theorem extend_ns (c : Coloring V C) (f : V → C) (d : C) (v : V) :
    extend c f d s(none,some v) = f v := rfl
@[simp] theorem extend_sn (c : Coloring V C) (f : V → C) (d : C) (v : V) :
    extend c f d s(some v,none) = f v := rfl

theorem independent_image_some (c : Coloring V C) (f : V → C) (d i : C)
    (S : Finset V) :
    Independent (extend c f d) i (S.image some) ↔ Independent c i S := by
  classical
  simp [Independent]

theorem independent_insertNone (c : Coloring V C) (f : V → C) (d i : C)
    (S : Finset V) :
    Independent (extend c f d) i (insertNone S) ↔
      Independent c i S ∧ ∀ v ∈ S, f v ≠ i := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      exact h (some u) (by simpa using hu) (some v) (by simpa using hv)
        (by simpa using huv)
    · intro v hv
      exact h none (by simp) (some v) (by simpa using hv) (by simp)
  · rintro ⟨h, hf⟩ u hu v hv huv
    cases u with
    | none =>
      cases v with
      | none => exact (huv rfl).elim
      | some v => exact hf v (by simpa using hv)
    | some u =>
      cases v with
      | none => exact hf u (by simpa using hu)
      | some v =>
        exact h u (by simpa using hu) v (by simpa using hv) (by simpa using huv)

theorem independent_eraseNone (c : Coloring V C) (f : V → C) (d i : C)
    (S : Finset (Option V)) (h : Independent (extend c f d) i S) :
    Independent c i S.eraseNone := by
  intro u hu v hv huv
  exact h (some u) (by simpa using hu) (some v) (by simpa using hv)
    (by simpa using huv)

theorem admissible_extend_iff (r : ℕ) (c : Coloring V C) (f : V → C) (d : C) :
    Admissible r (extend c f d) ↔ Admissible r c ∧ RootHits r c f := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro S hs i hi
      apply h (S.image some) (by rw [Finset.card_image_of_injective S (Option.some_injective V)]; exact hs) i
      exact (independent_image_some c f d i S).mpr hi
    · intro i S hs hi
      by_contra hh
      push Not at hh
      apply h (insertNone S) (by simpa using hs) i
      exact (independent_insertNone c f d i S).mpr ⟨hi, hh⟩
  · rintro ⟨hb, hr⟩ S hs i hi
    have hh := independent_eraseNone c f d i S hi
    by_cases hn : none ∈ S
    · have hc : S.eraseNone.card = r := by
        rw [Finset.card_eraseNone_of_mem hn, hs]
        omega
      obtain ⟨v, hv, hf⟩ := hr i S.eraseNone hc hh
      exact hi none hn (some v) (by simpa using hv) (by simp) hf
    · have hc : S.eraseNone.card = r+1 := by
        rw [Finset.card_eraseNone_of_not_mem hn, hs]
      exact hb S.eraseNone hc i hh

end ColourExtension

namespace CoreTheory.RootBridge
open Finset ColourExtension
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Every vertex belongs to exactly one class. -/
def Partition (T : Fin r → Finset V) : Prop :=
  ∀ v : V, ∃! i : Fin r, v ∈ T i

/-- Each class hits all independent r-sets of its colour. -/
def HitsAll (c : Coloring V (Fin r)) (T : Fin r → Finset V) : Prop :=
  ∀ i S, S.card = r → Independent c i S → ∃ v ∈ S, v ∈ T i

lemma partition_selector (T : Fin r → Finset V) (h : Partition T) :
    ∃ f : V → Fin r, ∀ v i, f v = i ↔ v ∈ T i := by
  classical
  have he : ∀ v : V, ∃ i, v ∈ T i := fun v => (h v).exists
  choose f hf using he
  refine ⟨f,?_⟩
  intro v i
  constructor
  · intro hi
    simpa [hi] using hf v
  · intro hi
    obtain ⟨j,hj,hunique⟩ := h v
    exact (hunique (f v) (hf v)).trans (hunique i hi).symm

/-- A complete partition, not an isolated small hitter, constructs the extra vertex. -/
theorem complete_partition_extends (c : Coloring V (Fin r))
    (hcap : Admissible r c) (T : Fin r → Finset V)
    (hp : Partition T) (hh : HitsAll c T) (i0 : Fin r) :
    ∃ f : V → Fin r,
      (∀ i, T i = univ.filter (fun v => f v = i)) ∧
      Admissible r (extend c f i0) := by
  classical
  obtain ⟨f,hf⟩ := partition_selector T hp
  refine ⟨f,?_,(admissible_extend_iff r c f i0).mpr ⟨hcap,?_⟩⟩
  · intro i
    ext v
    simp only [mem_filter,mem_univ,true_and]
    exact (hf v i).symm
  · intro i S hS hI
    obtain ⟨v,hv,ht⟩ := hh i S hS hI
    exact ⟨v,hv,(hf v i).mpr ht⟩


/-- Uniform survival of an independent r-set after fewer than r deletions. -/
def Resilient (c : Coloring V (Fin r)) : Prop :=
  ∀ i D, D.card < r → ∃ S : Finset V,
    S.card = r ∧ Independent c i S ∧ Disjoint S D


/-- Exact equivalence, retaining the same designated small class in both directions. -/
theorem small_partition_iff_small_extension (c : Coloring V (Fin r))
    (hcap : Admissible r c) (i0 : Fin r) :
    (∃ T : Fin r → Finset V, Partition T ∧ HitsAll c T ∧ (T i0).card < r) ↔
    (∃ f : V → Fin r, Admissible r (extend c f i0) ∧
      (univ.filter (fun v => f v = i0)).card < r) := by
  classical
  constructor
  · rintro ⟨T,hp,hh,ht⟩
    obtain ⟨f,hf,he⟩ := complete_partition_extends c hcap T hp hh i0
    exact ⟨f,he,by simpa [← hf i0] using ht⟩
  · rintro ⟨f,he,ht⟩
    let T : Fin r → Finset V := fun i => univ.filter (fun v => f v = i)
    refine ⟨T,?_,?_,ht⟩
    · intro v
      refine ⟨f v,by simp [T],?_⟩
      intro j hj
      have hj' : f v = j := by simpa [T] using hj
      exact hj'.symm
    · intro i S hS hI
      obtain ⟨v,hv,hi⟩ := ((admissible_extend_iff r c f i0).mp he).2 i S hS hI
      exact ⟨v,hv,by simp [T,hi]⟩
end CoreTheory.RootBridge

namespace CoreTheory.CommonBlocker
open Finset
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

/-- The supplied exact (r+1)-set admissibility predicate implies all independence caps. -/
lemma caps_of_admissible (c : ColourExtension.Coloring V (Fin r))
    (h : ColourExtension.Admissible r c) : CoreTheory.MinimalCore.Caps c := by
  intro i S hi
  by_contra hbig
  obtain ⟨A,hAS,ha⟩ := Finset.exists_subset_card_eq (by omega : r+1 ≤ S.card)
  apply h A ha i
  intro x hx y hy hxy
  exact hi x (hAS hx) y (hAS hy) hxy

end CoreTheory.CommonBlocker

namespace CoreTheory.RegularityBridge
open CoreTheory.MinimalCore
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Resilience on an actual induced base, retaining the common colouring. -/
def ResilientOn (c : Coloring V r) (B : Finset V) : Prop :=
  ∀ i (D : Finset V), D.card < r →
    ∃ A : Finset V, A ⊆ B \ D ∧ A.card = r ∧ Independent c i A

/-- Finset formulation of universal boundary resilience. -/
def UniversalResilience (r : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (c : Coloring W r) (B : Finset W),
    B.card = r^2 →
    (∀ i A, A ⊆ B → Independent c i A → A.card ≤ r) → ResilientOn c B

lemma root_degree_lower (c : Coloring V r) (H : Caps c) (v : V)
    (hres : ResilientOn c (univ.erase v)) (i : Fin r) :
    r ≤ degreeOn c i univ v := by
  by_contra hn
  have hs : (univ.filter (fun y => y ≠ v ∧ c s(v,y) = i)).card < r := by
    exact Nat.lt_of_not_ge hn
  obtain ⟨A,hA,hcard,hind⟩ := hres i _ hs
  have hv : v ∉ A := by
    intro h
    exact (mem_erase.mp (mem_sdiff.mp (hA h)).1).1 rfl
  have hfree : ∀ x ∈ A, c s(v,x) ≠ i := by
    intro x hx he
    have hm := mem_sdiff.mp (hA hx)
    apply hm.2
    exact mem_filter.mpr ⟨mem_univ _,⟨(mem_erase.mp hm.1).1,he⟩⟩
  have hi : Independent c i (insert v A) := independent_insert hind hfree
  have hh := H i (insert v A) hi
  rw [card_insert_of_notMem hv,hcard] at hh
  omega

lemma sum_root_degrees (c : Coloring V r) (v : V) :
    (∑ i : Fin r, degreeOn c i univ v) = Fintype.card V - 1 := by
  have hf : ∀ i : Fin r, degreeOn c i univ v =
      ((univ.erase v).filter (fun x => c s(v,x) = i)).card := by
    intro i
    unfold degreeOn
    apply congrArg Finset.card
    ext x
    simp
  simp_rw [hf]
  have h := card_eq_sum_card_fiberwise
    (f := fun x : V => c s(v,x)) (s := univ.erase v) (t := univ)
    (by intro x hx; exact mem_univ _)
  rw [← h]
  simp

lemma regular_of_root_lower (c : Coloring V r) (hV : Fintype.card V = r^2+1)
    (hlower : ∀ v i, r ≤ degreeOn c i univ v) :
    ∀ v i, degreeOn c i univ v = r := by
  intro v i
  have hs := sum_root_degrees c v
  rw [hV] at hs
  have he : (∑ _j : Fin r, r) = ∑ j : Fin r, degreeOn c j univ v := by
    simp [hs,pow_two]
  have ht := (sum_eq_sum_iff_of_le
    (s := (univ : Finset (Fin r))) (f := fun _ => r)
    (g := fun j => degreeOn c j univ v)
    (by intro j hj; exact hlower v j)).mp he
  exact (ht i (mem_univ _)).symm

theorem small_root_or_regular (c : Coloring V r) (hV : Fintype.card V = r^2+1) :
    (∃ v i, degreeOn c i univ v < r) ∨
    (∀ v i, degreeOn c i univ v = r) := by
  by_cases h : ∃ v i, degreeOn c i univ v < r
  · exact Or.inl h
  · right
    apply regular_of_root_lower c hV
    intro v i
    exact Nat.le_of_not_gt (by intro hh; exact h ⟨v,i,hh⟩)

theorem resilience_forces_regularity (hres : UniversalResilience r)
    (c : Coloring V r) (hV : Fintype.card V = r^2+1) (H : Caps c) :
    ∀ v i, degreeOn c i univ v = r := by
  apply regular_of_root_lower c hV
  intro v i
  apply root_degree_lower c H v
  apply hres V c (univ.erase v)
  · simp [hV]
  · intro j A hA hi
    exact H j A hi

/-- Ordinary vertex colouring of a single edge-colour layer. -/
def ProperLayerColouring (c : Coloring V r) (i : Fin r) (f : V → Fin r) : Prop :=
  ∀ x y, x ≠ y → c s(x,y) = i → f x ≠ f y

lemma no_proper_layer_colouring (c : Coloring V r)
    (hV : Fintype.card V = r^2+1) (H : Caps c) (i : Fin r) :
    ¬∃ f : V → Fin r, ProperLayerColouring c i f := by
  rintro ⟨f,hf⟩
  have hclasses : ∀ j : Fin r, (univ.filter (fun x => f x = j)).card ≤ r := by
    intro j
    apply H i
    intro x hx y hy hne hc
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    exact hf x y hne hc (hx'.trans hy'.symm)
  have hs := card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ)
    (by intro x hx; exact mem_univ _)
  have hl : Fintype.card V ≤ r^2 := by
    calc
      Fintype.card V = ∑ j : Fin r, (univ.filter (fun x => f x = j)).card := hs
      _ ≤ ∑ _j : Fin r, r := sum_le_sum (by intro j hj; exact hclasses j)
      _ = r^2 := by simp [pow_two]
  omega

/-- Explicit Brooks interface, NOT asserted as a new axiom or proved here.
For r >= 3 this is the usual regular, clique-excluded case of Brooks. -/
def BrooksInterface (r : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (c : Coloring W r) (i : Fin r),
    (∀ v, degreeOn c i univ v = r) →
    (∀ C, Clique c i C → C.card ≤ r) →
    ∃ f : W → Fin r, ProperLayerColouring c i f

lemma full_clique_bound (hr : 2 ≤ r) (c : Coloring V r) (H : Caps c)
    (i : Fin r) (C : Finset V) (hC : Clique c i C) : C.card ≤ r := by
  obtain ⟨j,hj⟩ : ∃ j : Fin r, j ≠ i := by
    by_cases h0 : i = ⟨0,by omega⟩
    · exact ⟨⟨1,by omega⟩,by intro he; have h := congrArg Fin.val (he.trans h0); simp at h⟩
    · exact ⟨⟨0,by omega⟩,Ne.symm h0⟩
  apply H j C
  intro x hx y hy hxy he
  have hi := hC x hx y hy hxy
  exact hj (he.symm.trans hi)

/-- All assumptions remain explicit: resilience alone is not proved. -/
theorem resilience_and_brooks_exclude_counterexample (hr : 3 ≤ r)
    (hres : UniversalResilience r) (hBrooks : BrooksInterface r)
    (c : Coloring V r) (hV : Fintype.card V = r^2+1) (H : Caps c) : False := by
  let i : Fin r := ⟨0,by omega⟩
  have hregular := resilience_forces_regularity hres c hV H
  have hproper := hBrooks V c i (fun v => hregular v i)
    (fun C hC => full_clique_bound (by omega) c H i C hC)
  exact no_proper_layer_colouring c hV H i hproper
end CoreTheory.RegularityBridge
end
end

/- ## CoreIncidence -/
section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace CoreTheory.CoreIncidence
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

/-- Closed neighbourhood trace in a fixed maximum independent set. -/
def support (c : Coloring V r) (i : Fin r) (A : Finset V) (x : V) : Finset V :=
  A.filter (fun y => y = x ∨ c s(x,y) = i)

/-- This region is defined by actual neighbourhoods, not an assumed partition. -/
def region (c : Coloring V r) (i : Fin r) (W A Q : Finset V) : Finset V :=
  W.filter (fun x => support c i A x ⊆ Q)

lemma support_nonempty (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W)
    {x : V} (hx : x ∈ W) : (support c i A x).Nonempty := by
  by_contra hn
  have hxA : x ∉ A := by
    intro ha
    exact hn ⟨x,mem_filter.mpr ⟨ha,Or.inl rfl⟩⟩
  have hf : ∀ y ∈ A, c s(x,y) ≠ i := by
    intro y hy he
    exact hn ⟨y,mem_filter.mpr ⟨hy,Or.inr he⟩⟩
  have hi := independent_insert hI hf
  have hb := card_le_alpha (insert_subset hx hAW) hi
  rw [card_insert_of_notMem hxA,hA] at hb
  omega

lemma region_subset (c : Coloring V r) (i : Fin r) (W A Q : Finset V) :
    region c i W A Q ⊆ W := filter_subset _ _

/-- An independent set in the region can replace Q inside A. -/
lemma region_alpha_le (c : Coloring V r) (i : Fin r) {W A Q : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W)
    (hQ : Q ⊆ A) : alphaOn c i (region c i W A Q) ≤ Q.card := by
  obtain ⟨B,hBR,hBI,hB⟩ := alpha_witness c i (region c i W A Q)
  have hBW : B ⊆ W := hBR.trans (region_subset c i W A Q)
  have disj : Disjoint B (A \ Q) := by
    apply disjoint_left.mpr
    intro x hx hxb
    have hreg := (mem_filter.mp (hBR hx)).2
    have hsup : x ∈ support c i A x := mem_filter.mpr ⟨(mem_sdiff.mp hxb).1,Or.inl rfl⟩
    exact (mem_sdiff.mp hxb).2 (hreg hsup)
  have cross : ∀ x ∈ B, ∀ y ∈ A \ Q, c s(x,y) ≠ i := by
    intro x hx y hy he
    have hreg := (mem_filter.mp (hBR hx)).2
    exact (mem_sdiff.mp hy).2 (hreg (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,Or.inr he⟩))
  have hu : Independent c i (B ∪ (A \ Q)) := by
    intro x hx y hy hxy
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hy with hy | hy
      · exact hBI x hx y hy hxy
      · exact cross x hx y hy
    · rcases mem_union.mp hy with hy | hy
      · rw [Sym2.eq_swap]; exact cross y hy x hx
      · exact hI x (mem_sdiff.mp hx).1 y (mem_sdiff.mp hy).1 hxy
  have hb := card_le_alpha (union_subset hBW (sdiff_subset.trans hAW)) hu
  rw [card_union_of_disjoint disj,hB,← hA] at hb
  have hc := card_sdiff_add_card_inter A Q
  rw [inter_eq_right.mpr hQ] at hc
  omega

/-- Hall-type expansion follows from intrinsic minimality. -/
theorem proper_region_bound (c : Coloring V r) (i : Fin r) {W A Q : Finset V}
    (hW : Minimal c i W) (hAW : A ⊆ W) (hI : Independent c i A)
    (hA : A.card = alphaOn c i W) (hQ : Q ⊂ A) :
    (region c i W A Q).card ≤ r * Q.card := by
  have hs : region c i W A Q ⊂ W := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨region_subset c i W A Q,?_⟩
    intro he
    have hAQ : A ⊆ Q := by
      intro x hx
      have hxr : x ∈ region c i W A Q := by
        rw [he]
        exact hAW hx
      exact (mem_filter.mp hxr).2 (mem_filter.mpr ⟨hx,Or.inl rfl⟩)
    exact hQ.ne (Subset.antisymm hQ.subset hAQ)
  exact (hW.2 _ hs).trans (Nat.mul_le_mul_left r (region_alpha_le c i hAW hI hA hQ.subset))

lemma independent_pair {c : Coloring V r} {i : Fin r} {x y : V}
    (h : c s(x,y) ≠ i) : Independent c i {x,y} := by
  intro u hu v hv huv
  simp only [mem_insert,mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (huv rfl).elim
  · exact h
  · rw [Sym2.eq_swap]; exact h
  · exact (huv rfl).elim

lemma singleton_region_clique (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W)
    {v : V} (hv : v ∈ A) : Clique c i (region c i W A {v}) := by
  have hb := region_alpha_le c i hAW hI hA (singleton_subset_iff.mpr hv)
  simp only [card_singleton] at hb
  intro x hx y hy hxy
  by_contra hc
  have hp := card_le_alpha (insert_subset hx (singleton_subset_iff.mpr hy)) (independent_pair hc)
  have he : ({x,y} : Finset V).card = 2 := by simp [hxy]
  rw [he] at hp
  omega

lemma singleton_region_bound (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W)
    {v : V} (hv : v ∈ A) : (region c i W A {v}).card + 1 ≤ r := by
  have hh := minimal_clique_bound c i H hW ha (region_subset c i W A {v})
    (singleton_region_clique c i hAW hI hA hv)
  omega

/-- Vertices with trace cardinality at least two. -/
def multiple (c : Coloring V r) (i : Fin r) (W A : Finset V) : Finset V :=
  W.filter (fun x => 2 ≤ (support c i A x).card)

/-- A necessary condition for every maximum independent set of the core. -/
theorem multiple_lower_bound (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    A.card + 1 ≤ (multiple c i W A).card := by
  let P := A.biUnion (fun v => region c i W A {v})
  have hcover : W ⊆ multiple c i W A ∪ P := by
    intro x hx
    by_cases hm : 2 ≤ (support c i A x).card
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hm⟩)
    · have hn := card_pos.mpr (support_nonempty c i hAW hI hA hx)
      have hc : (support c i A x).card = 1 := by omega
      obtain ⟨v,hv⟩ := card_eq_one.mp hc
      have hvA : v ∈ A := (mem_filter.mp (by rw [hv]; simp : v ∈ support c i A x)).1
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨v,hvA,mem_filter.mpr ⟨hx,?_⟩⟩
      rw [hv]
  have hc : W.card ≤ (multiple c i W A).card + ∑ v ∈ A, (region c i W A {v}).card := by
    exact (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
  have hcells : (∑ v ∈ A, (region c i W A {v}).card) + A.card ≤ r*A.card := by
    have hh : ∑ v ∈ A, ((region c i W A {v}).card + 1) ≤ ∑ _v ∈ A, r := by
      apply sum_le_sum
      intro v hv
      exact singleton_region_bound c i H hW ha hAW hI hA hv
    simpa [sum_add_distrib,Nat.mul_comm] using hh
  have hw := minimal_card c i hW
  rw [← hA] at hw
  omega
end CoreTheory.CoreIncidence

namespace CoreTheory.CoreIncidence
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

lemma support_sum_identity (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) :
    (∑ x ∈ W, (support c i A x).card) = (∑ v ∈ A, degreeOn c i W v) + A.card := by
  have hc : ∀ x, (support c i A x).card =
      ∑ v ∈ A, if v = x ∨ c s(x,v) = i then 1 else 0 := by
    intro x
    simp only [support,card_eq_sum_ones,sum_filter]
  simp_rw [hc]
  rw [sum_comm]
  have hh : ∀ v ∈ A, (∑ x ∈ W, if v = x ∨ c s(x,v) = i then 1 else 0) =
      degreeOn c i W v + 1 := by
    intro v hv
    have he : W.filter (fun x => v = x ∨ c s(x,v) = i) =
        insert v (W.filter (fun x => x ≠ v ∧ c s(v,x) = i)) := by
      ext x
      by_cases hx : x = v
      · subst x
        simp [hAW hv]
      · have hswap : c s(x,v) = c s(v,x) := congrArg c Sym2.eq_swap
        simp [hx,Ne.symm hx,hswap]
    have hn : v ∉ W.filter (fun x => x ≠ v ∧ c s(v,x) = i) := by simp
    calc
      _ = (W.filter (fun x => v = x ∨ c s(x,v) = i)).card := by
        simp only [card_eq_sum_ones,sum_filter]
      _ = (insert v (W.filter (fun x => x ≠ v ∧ c s(v,x) = i))).card := congrArg card he
      _ = degreeOn c i W v + 1 := by rw [card_insert_of_notMem hn]; rfl
  calc
    _ = ∑ v ∈ A, (degreeOn c i W v + 1) := sum_congr rfl hh
    _ = _ := by simp [sum_add_distrib]

/-- Every maximum independent set carries at least two units of degree surplus. -/
theorem maximum_degree_sum (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    r*A.card + 2 ≤ ∑ v ∈ A, degreeOn c i W v := by
  have hpoint : ∀ x ∈ W, 1 + (if 2 ≤ (support c i A x).card then 1 else 0) ≤
      (support c i A x).card := by
    intro x hx
    have hp := card_pos.mpr (support_nonempty c i hAW hI hA hx)
    split_ifs <;> omega
  have hsum := sum_le_sum hpoint
  have hc : (∑ x ∈ W, if 2 ≤ (support c i A x).card then 1 else 0) =
      (multiple c i W A).card := by simp only [multiple,card_eq_sum_ones,sum_filter]
  simp only [sum_add_distrib,sum_const,smul_eq_mul,Nat.mul_one] at hsum
  rw [hc,support_sum_identity c i hAW] at hsum
  have hm := multiple_lower_bound c i H hW ha hAW hI hA
  have hw := minimal_card c i hW
  rw [← hA] at hw
  omega

/-- High-degree vertices are defined in the actual induced selected layer. -/
def high (c : Coloring V r) (i : Fin r) (W : Finset V) : Finset V :=
  W.filter (fun x => r < degreeOn c i W x)

/-- Removing at most r high-degree vertices cannot cover all degree surplus. -/
theorem high_count (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    r + 1 ≤ (high c i W).card := by
  by_contra hn
  have hd : (high c i W).card ≤ r := by omega
  have he := minimal_deletion c i hW (high c i W) hd
  obtain ⟨A,hA,hI,hc⟩ := alpha_witness c i (W \ high c i W)
  have hAW : A ⊆ W := hA.trans sdiff_subset
  have hmax : A.card = alphaOn c i W := hc.trans he
  have lower := maximum_degree_sum c i H hW ha hAW hI hmax
  have upper : (∑ v ∈ A, degreeOn c i W v) ≤ r*A.card := by
    calc
      _ ≤ ∑ _v ∈ A, r := by
        apply sum_le_sum
        intro v hv
        have hm := mem_sdiff.mp (hA hv)
        by_contra hb
        exact hm.2 (mem_filter.mpr ⟨hm.1,by omega⟩)
      _ = r*A.card := by simp [Nat.mul_comm]
  omega
end CoreTheory.CoreIncidence
end
end

/- ## CoreSurplus -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable

namespace Surplus
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [DecidableEq V] {r : ℕ}

/-- Nonnegative degree surplus in the actual selected induced colour layer. -/
def surplus (c : Coloring V r) (i : Fin r) (W : Finset V) (v : V) : ℕ :=
  degreeOn c i W v - r

lemma degree_sum_eq (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hW : Minimal c i W) (hAW : A ⊆ W) :
    (∑ v ∈ A, degreeOn c i W v) = r * A.card + ∑ v ∈ A, surplus c i W v := by
  have h : ∀ v ∈ A, degreeOn c i W v = r + surplus c i W v := by
    intro v hv
    have hd := minimal_degree c i hW (hAW hv)
    simp only [surplus]
    omega
  calc
    _ = ∑ v ∈ A, (r + surplus c i W v) := sum_congr rfl h
    _ = _ := by simp [sum_add_distrib, Nat.mul_comm]

/-- Every maximum independent set carries at least two units of surplus. -/
theorem maximum_surplus (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    2 ≤ ∑ v ∈ A, surplus c i W v := by
  have h := maximum_degree_sum c i H hW ha hAW hI hA
  rw [degree_sum_eq c i hW hAW] at h
  omega

/-- Even after ANY at-most-r deletion, at least two surplus units survive.
This is stronger than merely counting vertices of degree greater than r. -/
theorem surplus_tail (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (D : Finset V) (hD : D.card ≤ r) :
    2 ≤ ∑ v ∈ W \ D, surplus c i W v := by
  obtain ⟨A,hAWD,hI,hA⟩ := alpha_witness c i (W \ D)
  have hmax : A.card = alphaOn c i W :=
    hA.trans (minimal_deletion c i hW D hD)
  exact (maximum_surplus c i H hW ha (hAWD.trans sdiff_subset) hI hmax).trans
    (sum_le_sum_of_subset hAWD)

/-- Uniform strengthening: total degree surplus is at least r+2. -/
theorem total_surplus (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    r + 2 ≤ ∑ v ∈ W, surplus c i W v := by
  have hh := high_count c i H hW ha
  obtain ⟨D,hDH,hDc⟩ := exists_subset_card_eq (by omega : r ≤ (high c i W).card)
  have hDW : D ⊆ W := hDH.trans (filter_subset _ _)
  have hpositive : ∀ v ∈ D, 1 ≤ surplus c i W v := by
    intro v hv
    have hvh := (mem_filter.mp (hDH hv)).2
    dsimp only [surplus]
    omega
  have hDsum : r ≤ ∑ v ∈ D, surplus c i W v := by
    calc r = ∑ _v ∈ D, 1 := by simp [hDc]
         _ ≤ _ := sum_le_sum hpositive
  have ht := surplus_tail c i H hW ha D (le_of_eq hDc)
  have hs : (∑ v ∈ D, surplus c i W v) + (∑ v ∈ W \ D, surplus c i W v) =
      ∑ v ∈ W, surplus c i W v := by
    rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hDW]
  omega

/-- Degree-sum form, ready to combine with other-colour edge bounds. -/
theorem core_degree_sum (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    r * W.card + r + 2 ≤ ∑ v ∈ W, degreeOn c i W v := by
  have h := total_surplus c i H hW ha
  rw [degree_sum_eq c i hW (Subset.refl W)]
  omega


/-- Concentrating surplus at one vertex costs at least r additional units elsewhere. -/
theorem pointwise_surplus (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    {v : V} (hv : v ∈ W) :
    surplus c i W v + r + 1 ≤ ∑ w ∈ W, surplus c i W w := by
  by_cases hp : surplus c i W v = 0
  · have ht := total_surplus c i H hW ha
    omega
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) ha
  have hvh : v ∈ high c i W := by
    apply mem_filter.mpr
    refine ⟨hv, ?_⟩
    dsimp only [surplus] at hp
    omega
  have hh := high_count c i H hW ha
  have hnum : r-1 ≤ ((high c i W).erase v).card := by
    rw [card_erase_of_mem hvh]
    omega
  obtain ⟨D,hDH,hDc⟩ := exists_subset_card_eq hnum
  have hvD : v ∉ D := by
    intro h
    exact (mem_erase.mp (hDH h)).1 rfl
  have hDW : D ⊆ W := hDH.trans ((erase_subset _ _).trans (filter_subset _ _))
  have hDsum : r-1 ≤ ∑ w ∈ D, surplus c i W w := by
    calc r-1 = ∑ _w ∈ D, 1 := by simp [hDc]
         _ ≤ _ := by
           apply sum_le_sum
           intro w hw
           have hwH := (mem_filter.mp (mem_erase.mp (hDH hw)).2).2
           dsimp only [surplus]
           omega
  have hc : (insert v D).card ≤ r := by
    rw [card_insert_of_notMem hvD, hDc]
    omega
  have hEW : insert v D ⊆ W := insert_subset hv hDW
  have ht := surplus_tail c i H hW ha (insert v D) hc
  have hs : (∑ w ∈ insert v D, surplus c i W w) +
      (∑ w ∈ W \ insert v D, surplus c i W w) = ∑ w ∈ W, surplus c i W w := by
    rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hEW]
  rw [sum_insert hvD] at hs
  omega

/-- Conditional interface for the paper-proved K5-free sparse bound. -/
theorem alpha_four_surplus_le [Fintype V]
    (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hW : Minimal c i (univ : Finset V))
    (ha : alphaOn c i univ = 4) (hr : 5 ≤ r)
    (hother : ∀ j : Fin r, j ≠ i →
      12*r+14 ≤ ∑ v : V, degreeOn c j univ v) :
    (∑ v : V, surplus c i univ v) ≤ r+14 := by
  have hn := minimal_card c i hW
  simp only [card_univ, ha] at hn
  have hi := degree_sum_eq c i hW (Subset.refl (univ : Finset V))
  simp only [card_univ, hn] at hi
  have ho := sum_le_sum (s := (univ : Finset (Fin r)).erase i)
    (fun j hj => hother j (mem_erase.mp hj).1)
  have ht : (∑ j : Fin r, ∑ v : V, degreeOn c j univ v) =
      Fintype.card V * (Fintype.card V - 1) := by
    rw [sum_comm]
    simp_rw [CoreTheory.RegularityBridge.sum_root_degrees c]
    simp
  have he := sum_erase_add (s := (univ : Finset (Fin r)))
    (fun j => ∑ v : V, degreeOn c j univ v) (mem_univ i)
  rw [ht, hn] at he
  simp only [sum_const, card_erase_of_mem (mem_univ i), card_univ,
    Fintype.card_fin, smul_eq_mul] at ho
  have hpred : r-1+1=r := by omega
  have hnm : r*4+1-1=r*4 := by omega
  rw [hnm] at he
  nlinarith

/-- Every vertex in an alpha-four core has degree at most r+13. -/
theorem alpha_four_degree_le [Fintype V]
    (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hW : Minimal c i (univ : Finset V))
    (ha : alphaOn c i univ = 4) (hr : 5 ≤ r)
    (hother : ∀ j : Fin r, j ≠ i →
      12*r+14 ≤ ∑ v : V, degreeOn c j univ v) (v : V) :
    degreeOn c i univ v ≤ r+13 := by
  have hu := alpha_four_surplus_le c i H hW ha hr hother
  have hp := pointwise_surplus c i H hW (by omega) (mem_univ v)
  have hd := minimal_degree c i hW (mem_univ v)
  dsimp only [surplus] at hu hp
  omega

end Surplus
end
end

/- ## PrivateCore -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.PrivateStructure
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [DecidableEq V] {r : ℕ}

abbrev cell (c : Coloring V r) (i : Fin r) (W A : Finset V) (v : V) :=
  region c i W A {v}

def weight (c : Coloring V r) (i : Fin r) (W X : Finset V) : ℕ :=
  ∑ v ∈ X, surplus c i W v

def deficit (c : Coloring V r) (i : Fin r) (W A : Finset V) (v : V) : ℕ :=
  r-1-(cell c i W A v).card

/-- Minimum-weight maximum independent set; a finite construction. -/
def IsMin (c : Coloring V r) (i : Fin r) (W A : Finset V) : Prop :=
  A ⊆ W ∧ Independent c i A ∧ A.card = alphaOn c i W ∧
  ∀ B ⊆ W, Independent c i B → B.card = A.card → weight c i W A ≤ weight c i W B

lemma min_exists (c : Coloring V r) (i : Fin r) (W : Finset V) :
    ∃ A, IsMin c i W A := by
  obtain ⟨A,hAW,hI,hA⟩ := alpha_witness c i W
  let F := W.powerset.filter (fun B => Independent c i B ∧ B.card = alphaOn c i W)
  have hAF : A ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hAW,hI,hA⟩
  obtain ⟨B,hBF,hmin⟩ := F.exists_min_image (weight c i W) ⟨A,hAF⟩
  have hb := mem_filter.mp hBF
  refine ⟨B,mem_powerset.mp hb.1,hb.2.1,hb.2.2,?_⟩
  intro C hCW hCI hCB
  exact hmin C (mem_filter.mpr ⟨mem_powerset.mpr hCW,hCI,hCB.trans hb.2.2⟩)

lemma cell_disjoint (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W)
    {u v : V} (hne : u ≠ v) : Disjoint (cell c i W A u) (cell c i W A v) := by
  apply disjoint_left.mpr
  intro x hxu hxv
  obtain ⟨y,hy⟩ := support_nonempty c i hAW hI hA (mem_filter.mp hxu).1
  have hu := mem_singleton.mp ((mem_filter.mp hxu).2 hy)
  have hv := mem_singleton.mp ((mem_filter.mp hxv).2 hy)
  exact hne (hu.symm.trans hv)

lemma cell_multi_disjoint (c : Coloring V r) (i : Fin r) (W A : Finset V) (v : V) :
    Disjoint (cell c i W A v) (multiple c i W A) := by
  apply disjoint_left.mpr
  intro x hx hm
  have hc := card_le_card (mem_filter.mp hx).2
  have hl := (mem_filter.mp hm).2
  simp only [card_singleton] at hc
  omega

lemma partition_identity (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    W.card = (∑ v ∈ A, (cell c i W A v).card) + (multiple c i W A).card := by
  let U := A.biUnion (cell c i W A)
  have hp : (↑A : Set V).PairwiseDisjoint (cell c i W A) := by
    intro u _ v _ hne
    exact cell_disjoint c i hAW hI hA hne
  have hU : U.card = ∑ v ∈ A, (cell c i W A v).card := card_biUnion hp
  have hd : Disjoint U (multiple c i W A) := by
    apply disjoint_left.mpr
    intro x hx hm
    obtain ⟨v,hv,hxv⟩ := mem_biUnion.mp hx
    exact disjoint_left.mp (cell_multi_disjoint c i W A v) hxv hm
  have hc : U ∪ multiple c i W A = W := by
    ext x
    constructor
    · intro hx
      rcases mem_union.mp hx with hu | hm
      · obtain ⟨v,_,hxv⟩ := mem_biUnion.mp hu
        exact (mem_filter.mp hxv).1
      · exact (mem_filter.mp hm).1
    · intro hx
      by_cases hm : 2 ≤ (support c i A x).card
      · exact mem_union_right _ (mem_filter.mpr ⟨hx,hm⟩)
      have hn := card_pos.mpr (support_nonempty c i hAW hI hA hx)
      obtain ⟨v,hv⟩ := card_eq_one.mp (by omega : (support c i A x).card = 1)
      have hvA : v ∈ A := (mem_filter.mp (by rw [hv]; simp : v ∈ support c i A x)).1
      apply mem_union_left
      apply mem_biUnion.mpr
      exact ⟨v,hvA,mem_filter.mpr ⟨hx,by rw [hv]⟩⟩
  calc W.card = (U ∪ multiple c i W A).card := congrArg Finset.card hc.symm
       _ = _ := by rw [card_union_of_disjoint hd,hU]

/-- Exact relation between missing private vertices and multi-support vertices. -/
lemma deficit_count (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    (multiple c i W A).card = A.card + 1 + ∑ v ∈ A, deficit c i W A v := by
  have he : ∀ v ∈ A, deficit c i W A v + (cell c i W A v).card + 1 = r := by
    intro v hv
    have h := singleton_region_bound c i H hW ha hAW hI hA hv
    change (cell c i W A v).card + 1 ≤ r at h
    dsimp only [deficit]
    omega
  have hs := sum_congr rfl he
  simp only [sum_add_distrib,sum_const,sum_const_zero,smul_eq_mul,Nat.mul_one] at hs
  have hp := partition_identity c i hAW hI hA
  have hn := minimal_card c i hW
  rw [← hA] at hn
  nlinarith

lemma deficit_budget (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    (∑ v ∈ A, deficit c i W A v) + 2 ≤ weight c i W A := by
  have hpoint : ∀ x ∈ W, 1 + (if 2 ≤ (support c i A x).card then 1 else 0) ≤
      (support c i A x).card := by
    intro x hx
    have hp := card_pos.mpr (support_nonempty c i hAW hI hA hx)
    split_ifs <;> omega
  have hs := sum_le_sum hpoint
  have hm : (∑ x ∈ W, if 2 ≤ (support c i A x).card then 1 else 0) =
      (multiple c i W A).card := by simp only [multiple,card_eq_sum_ones,sum_filter]
  simp only [sum_add_distrib,sum_const,smul_eq_mul,Nat.mul_one] at hs
  rw [hm,support_sum_identity c i hAW,degree_sum_eq c i hW hAW] at hs
  have hn := minimal_card c i hW
  rw [← hA] at hn
  have hd := deficit_count c i H hW ha hAW hI hA
  dsimp only [weight]
  omega

/-- A private vertex can replace its anchor in a maximum independent set. -/
lemma private_exchange (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hmin : IsMin c i W A) {v x : V} (hv : v ∈ A) (hx : x ∈ cell c i W A v) :
    surplus c i W v ≤ surplus c i W x := by
  have hxW := (mem_filter.mp hx).1
  have hsup := (mem_filter.mp hx).2
  have hn : x ∉ A.erase v := by
    intro he
    have hxx : x ∈ support c i A x := mem_filter.mpr ⟨mem_of_mem_erase he,Or.inl rfl⟩
    exact (mem_erase.mp he).1 (mem_singleton.mp (hsup hxx))
  have hi : Independent c i (insert x (A.erase v)) := by
    apply independent_insert (independent_mono (erase_subset _ _) hmin.2.1)
    intro y hy hcol
    have hys : y ∈ support c i A x := mem_filter.mpr ⟨mem_of_mem_erase hy,Or.inr hcol⟩
    exact (mem_erase.mp hy).1 (mem_singleton.mp (hsup hys))
  have hc : (insert x (A.erase v)).card = A.card := by
    rw [card_insert_of_notMem hn,card_erase_of_mem hv]
    have hp := card_pos.mpr ⟨v,hv⟩
    omega
  have hm := hmin.2.2.2 _ (insert_subset hxW ((erase_subset _ _).trans hmin.1)) hi hc
  have he := add_sum_erase A (surplus c i W) hv
  dsimp only [weight] at hm
  rw [sum_insert hn] at hm
  omega

/-- The private cliques transport the minimum transversal weight into W. -/
lemma private_weight_lower (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hmin : IsMin c i W A) :
    (∑ v ∈ A, (cell c i W A v).card * surplus c i W v) ≤ weight c i W W := by
  have hp : (↑A : Set V).PairwiseDisjoint (cell c i W A) := by
    intro u _ v _ hne
    exact cell_disjoint c i hmin.1 hmin.2.1 hmin.2.2.1 hne
  have hsub : A.biUnion (cell c i W A) ⊆ W := by
    intro x hx
    obtain ⟨v,_,hxv⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hxv).1
  have hu : (∑ v ∈ A, ∑ x ∈ cell c i W A v, surplus c i W x) ≤ weight c i W W := by
    rw [← sum_biUnion hp]
    exact sum_le_sum_of_subset hsub
  apply le_trans _ hu
  apply sum_le_sum
  intro v hv
  calc
    _ = ∑ _x ∈ cell c i W A v, surplus c i W v := by simp
    _ ≤ _ := sum_le_sum (fun x hx => private_exchange c i hmin hv hx)

/-- Exact deficit accounting and exchange give a quadratic in the minimum weight. -/
lemma min_weight_quadratic (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hmin : IsMin c i W A) :
    (r+1)*weight c i W A ≤ weight c i W W + (weight c i W A)^2 := by
  let m := weight c i W A
  let D := ∑ v ∈ A, deficit c i W A v
  have hb : D+2 ≤ m := deficit_budget c i H hW ha hmin.1 hmin.2.1 hmin.2.2.1
  have hl := private_weight_lower c i hmin
  have hw : ∀ v ∈ A, surplus c i W v ≤ m := by
    intro v hv
    exact single_le_sum (fun _ _ => Nat.zero_le _) hv
  have he : ∀ v ∈ A, (cell c i W A v).card + deficit c i W A v + 1 = r := by
    intro v hv
    have h := singleton_region_bound c i H hW ha hmin.1 hmin.2.1 hmin.2.2.1 hv
    change (cell c i W A v).card + 1 ≤ r at h
    dsimp only [deficit]
    omega
  have hid : (∑ v ∈ A, (cell c i W A v).card * surplus c i W v) +
      (∑ v ∈ A, deficit c i W A v * surplus c i W v) + m = r*m := by
    simp only [m,weight,←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro v hv
    nlinarith [he v hv]
  have hu : (∑ v ∈ A, deficit c i W A v * surplus c i W v) ≤ D*m := by
    calc
      _ ≤ ∑ v ∈ A, deficit c i W A v * m :=
        sum_le_sum (fun v hv => Nat.mul_le_mul_left _ (hw v hv))
      _ = D*m := by rw [sum_mul]
  change (r+1)*m ≤ weight c i W W+m^2
  nlinarith

/-- Deleting the chosen set leaves a disjoint maximum set of no smaller weight. -/
lemma twice_min_weight (c : Coloring V r) (i : Fin r)
    {W A : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (hmin : IsMin c i W A) : 2*weight c i W A ≤ weight c i W W := by
  have hAc : A.card ≤ r := by rw [hmin.2.2.1]; omega
  have hd := minimal_deletion c i hW A hAc
  obtain ⟨B,hB,hI,hcard⟩ := alpha_witness c i (W \ A)
  have heq : B.card = A.card := by rw [hcard,hd,hmin.2.2.1]
  have hle := hmin.2.2.2 B (hB.trans sdiff_subset) hI heq
  have hu : weight c i W B ≤ weight c i W (W \ A) := sum_le_sum_of_subset hB
  have hs : weight c i W A + weight c i W (W \ A) = weight c i W W := by
    dsimp only [weight]
    rw [←sum_union disjoint_sdiff,union_sdiff_of_subset hmin.1]
  omega

/-- Uniform all-r result. No lower-level F theorem or colour decomposition premise. -/
theorem surplus_twice_parameter (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hr : 3 ≤ r) {W : Finset V} (hW : Minimal c i W)
    (ha : alphaOn c i W < r) : 2*r ≤ (∑ v ∈ W, surplus c i W v)+2 := by
  obtain ⟨A,hmin⟩ := min_exists c i W
  let m := weight c i W A
  let S := weight c i W W
  have hm : 2 ≤ m := maximum_surplus c i H hW ha hmin.1 hmin.2.1 hmin.2.2.1
  have hquad : (r+1)*m ≤ S+m^2 := min_weight_quadratic c i H hW ha hmin
  have hdouble : 2*m ≤ S := twice_min_weight c i hW ha hmin
  change 2*r ≤ S+2
  by_cases hlarge : r-1 ≤ m
  · omega
  · have hnon : 0 ≤ (m-2)*(r-1-m) := Nat.zero_le _
    have hm2 : m-2+2=m := by omega
    have hrm : r-1-m+m+1=r := by omega
    nlinarith
end Surplus.PrivateStructure
end
end

/- ## ExtensionRank -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.PrivateStructure.Extension
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

def avoid (c : Coloring V r) (i : Fin r) (W I : Finset V) : Finset V :=
  W.filter (fun x => ∀ u ∈ I, c s(u,x) ≠ i)

/-- The actual shared graph, not an independently chosen residual graph. -/
lemma avoid_independence (c : Coloring V r) (i : Fin r) (H : Caps c)
    (W I : Finset V) (hI : Independent c i I) (hd : Disjoint I W) :
    alphaOn c i (avoid c i W I) + I.card ≤ r := by
  obtain ⟨B,hB,hBI,hBc⟩ := alpha_witness c i (avoid c i W I)
  have hBW : B ⊆ W := hB.trans (filter_subset _ _)
  have hdis : Disjoint I B := hd.mono_right hBW
  have hi : Independent c i (I ∪ B) := by
    intro x hx y hy hxy
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hI x hx y hy hxy
    · exact (mem_filter.mp (hB hy)).2 x hx
    · rw [Sym2.eq_swap]
      exact (mem_filter.mp (hB hx)).2 y hy
    · exact hBI x hx y hy hxy
  have h := H i (I ∪ B) hi
  rw [card_union_of_disjoint hdis,hBc] at h
  omega

lemma avoid_cover (c : Coloring V r) (i : Fin r) (W I : Finset V)
    (hd : Disjoint I W) :
    W.card ≤ (avoid c i W I).card + ∑ u ∈ I, degreeOn c i W u := by
  let N := I.biUnion (fun u => W.filter (fun x => x ≠ u ∧ c s(u,x)=i))
  have hn : N.card ≤ ∑ u ∈ I, degreeOn c i W u := card_biUnion_le
  have hc : W ⊆ avoid c i W I ∪ N := by
    intro x hx
    by_cases he : ∀ u ∈ I, c s(u,x) ≠ i
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,he⟩)
    · push_neg at he
      obtain ⟨u,hu,hcol⟩ := he
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨u,hu,mem_filter.mpr ⟨hx,?_,hcol⟩⟩
      intro hxu
      exact disjoint_left.mp hd hu (hxu ▸ hx)
  have h := (card_le_card hc).trans (card_union_le _ _)
  omega

/-- Every oversized independent set outside a minimal core has a large cut into it. -/
theorem outside_rank_cut (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (I : Finset V)
    (hI : Independent c i I) (hd : Disjoint I W)
    (hbig : r < alphaOn c i W + I.card) :
    W.card ≤ r*(r-I.card) + ∑ u ∈ I, degreeOn c i W u := by
  have ha := avoid_independence c i H W I hI hd
  have hc := avoid_cover c i W I hd
  have hproper : avoid c i W I ⊂ W := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨filter_subset _ _,?_⟩
    intro he
    rw [he] at ha
    omega
  have hm := hW.2 _ hproper
  have hIcap := H i I hI
  have ht : alphaOn c i (avoid c i W I) ≤ r-I.card := by omega
  have hmul := Nat.mul_le_mul_left r ht
  omega

/-- Weighted cap used by the all-r extension constructor.
Only vertices whose cut degree is at most r are needed: higher-degree vertices
have weight zero and can be omitted before applying this theorem. -/
theorem outside_weight_budget (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (I : Finset V) (hI : Independent c i I) (hd : Disjoint I W)
    (hdeg : ∀ u ∈ I, degreeOn c i W u ≤ r) :
    (∑ u ∈ I, (r-degreeOn c i W u)) ≤ r*(r-alphaOn c i W) := by
  have he : (∑ u ∈ I, (r-degreeOn c i W u)) +
      (∑ u ∈ I, degreeOn c i W u) = r*I.card := by
    rw [←sum_add_distrib]
    calc _ = ∑ _u ∈ I, r := sum_congr rfl (fun u hu => by have h := hdeg u hu; omega)
         _ = _ := by simp [Nat.mul_comm]
  by_cases hi : I.card ≤ r-alphaOn c i W
  · have h := Nat.mul_le_mul_left r hi
    omega
  · have hb : r < alphaOn c i W+I.card := by omega
    have hc := outside_rank_cut c i H hW I hI hd hb
    have hn := minimal_card c i hW
    rw [hn] at hc
    have hIcap := H i I hI
    have hx : r-I.card+I.card=r := by omega
    have hy : r-alphaOn c i W+alphaOn c i W=r := by omega
    nlinarith
end Surplus.PrivateStructure.Extension
end
end

/- ## WeightedGreedy -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.PrivateStructure.Greedy
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

def nbh (c : Coloring V r) (i : Fin r) (W : Finset V) (v : V) : Finset V :=
  W.filter (fun x => x=v ∨ c s(v,x)=i)

def potential (c : Coloring V r) (i : Fin r) (W : Finset V) (w : V → ℚ) : ℚ :=
  ∑ v ∈ W, w v / ((degreeOn c i W v : ℚ)+1)

lemma nbh_card (c : Coloring V r) (i : Fin r) (W : Finset V)
    {v : V} (hv : v ∈ W) : (nbh c i W v).card = degreeOn c i W v+1 := by
  have he : nbh c i W v = insert v (W.filter (fun x => x ≠ v ∧ c s(v,x)=i)) := by
    ext x
    by_cases hx : x=v
    · subst x; simp [nbh,hv]
    · simp [nbh,hx]
  rw [he,card_insert_of_notMem (by simp)]
  rfl

lemma closed_double_count (c : Coloring V r) (i : Fin r) (W : Finset V) (w : V → ℚ) :
    (∑ v ∈ W, ∑ x ∈ nbh c i W v, w x / ((degreeOn c i W x : ℚ)+1)) = ∑ x ∈ W, w x := by
  have hs : (∑ v ∈ W, ∑ x ∈ nbh c i W v, w x / ((degreeOn c i W x : ℚ)+1)) =
      ∑ x ∈ W, ∑ v ∈ nbh c i W x, w x / ((degreeOn c i W x : ℚ)+1) := by
    simp only [nbh,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro v _
    have he : (x=v ∨ c s(v,x)=i) ↔ (v=x ∨ c s(x,v)=i) := by
      rw [eq_comm,Sym2.eq_swap]
    simp only [he]
  rw [hs]
  apply sum_congr rfl
  intro x hx
  rw [sum_const,nsmul_eq_mul,nbh_card c i W hx]
  simp only [Nat.cast_add,Nat.cast_one]
  field_simp

lemma good_vertex (c : Coloring V r) (i : Fin r) (W : Finset V) (w : V → ℚ)
    (hW : W.Nonempty) : ∃ v ∈ W,
      (∑ x ∈ nbh c i W v, w x / ((degreeOn c i W x : ℚ)+1)) ≤ w v := by
  by_contra hn
  push_neg at hn
  have hs := sum_lt_sum (fun v hv => le_of_lt (hn v hv))
    (by obtain ⟨v,hv⟩ := hW; exact ⟨v,hv,hn v hv⟩)
  rw [closed_double_count c i W w] at hs
  exact (lt_irrefl _ hs)

/-- Weighted Caro-Wei, proved constructively by a nonnegative-gain deletion step.
No probability, optimization oracle, or graph-theoretic premise is imported. -/
theorem weighted_independent (c : Coloring V r) (i : Fin r) (w : V → ℚ)
    (hw : ∀ x, 0 ≤ w x) (W : Finset V) :
    ∃ I ⊆ W, Independent c i I ∧ potential c i W w ≤ ∑ x ∈ I, w x := by
  refine Finset.strongInductionOn W ?_
  intro X ih
  by_cases he : X=∅
  · subst X
    exact ⟨∅,Subset.refl _,by simp [Independent],by simp [potential]⟩
  obtain ⟨v,hv,hgain⟩ := good_vertex c i X w (nonempty_iff_ne_empty.mpr he)
  let U := X \ nbh c i X v
  have hN : nbh c i X v ⊆ X := filter_subset _ _
  have hvN : v ∈ nbh c i X v := mem_filter.mpr ⟨hv,Or.inl rfl⟩
  have hUX : U ⊂ X := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨sdiff_subset,?_⟩
    intro hu
    have h : v ∈ U := hu.symm ▸ hv
    exact (mem_sdiff.mp h).2 hvN
  obtain ⟨I,hIU,hI,hweight⟩ := ih U hUX
  have hvI : v ∉ I := by
    intro h
    exact (mem_sdiff.mp (hIU h)).2 hvN
  have hi : Independent c i (insert v I) := by
    apply independent_insert hI
    intro x hx hcol
    have h := mem_sdiff.mp (hIU hx)
    exact h.2 (mem_filter.mpr ⟨h.1,Or.inr hcol⟩)
  have hu : (∑ x ∈ U, w x / ((degreeOn c i X x : ℚ)+1)) ≤ potential c i U w := by
    apply sum_le_sum
    intro x hx
    have hd : degreeOn c i U x ≤ degreeOn c i X x := by
      apply card_le_card
      intro y hy
      exact mem_filter.mpr ⟨(mem_sdiff.mp (mem_filter.mp hy).1).1,(mem_filter.mp hy).2⟩
    apply div_le_div_of_nonneg_left (hw x) (by positivity)
    exact_mod_cast Nat.add_le_add_right hd 1
  have hsplit : potential c i X w =
      (∑ x ∈ nbh c i X v, w x / ((degreeOn c i X x : ℚ)+1)) +
      ∑ x ∈ U, w x / ((degreeOn c i X x : ℚ)+1) := by
    dsimp only [potential,U]
    rw [←sum_union disjoint_sdiff,union_sdiff_of_subset hN]
  refine ⟨insert v I,insert_subset hv (hIU.trans sdiff_subset),hi,?_⟩
  rw [sum_insert hvI]
  linarith
end Surplus.PrivateStructure.Greedy
end
end

/- ## SparseGraphBounds -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.SparseGraphBounds
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}
section Counting
variable {c : Coloring V r} {j : Fin r} {W : Finset V}
-- The first four counting lemmas are copied, with provenance, from
-- toolbox/src/AlphaTwoCore.lean. Their proofs are rechecked here.
/-- The degree sum splits over a subset and its complement. -/
lemma sum_split (A : Finset V) (hA : A ⊆ W) :
    ∑ x ∈ W, degreeOn c j W x
      = (∑ x ∈ A, degreeOn c j W x) + ∑ x ∈ W \ A, degreeOn c j W x := by
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  congr 1
  rw [Finset.union_sdiff_of_subset hA]

/-- The neighbour count splits over a subset and its complement. -/
lemma nbr_split (A : Finset V) (hA : A ⊆ W) (x : V) :
    degreeOn c j W x = degreeOn c j A x + degreeOn c j (W \ A) x := by
  classical
  unfold degreeOn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.union_sdiff_of_subset hA]
  · exact Finset.disjoint_filter_filter Finset.disjoint_sdiff

/-- The number of ordered `j`-pairs inside `B` is the sum of the `j`-degrees. -/
lemma card_pairsIn (c : Coloring V r) (j : Fin r) (B : Finset V) :
    (((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j))).card
      = ∑ v ∈ B, degreeOn c j B v := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (t := B)
      (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hfib : (((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)).filter
        (fun p => p.1 = v))
      = {v} ×ˢ (B.filter (fun y => y ≠ v ∧ c s(v, y) = j)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨_, hb⟩, hne, hc⟩, rfl⟩
      exact ⟨rfl, hb, Ne.symm hne, hc⟩
    · rintro ⟨rfl, hb, hne, hc⟩
      exact ⟨⟨⟨hv, hb⟩, Ne.symm hne, hc⟩, rfl⟩
  rw [hfib, Finset.card_product, Finset.card_singleton, one_mul, degreeOn]

/-- Double counting of the `j`-edges between `A` and `B`. -/
lemma bipartite_count (c : Coloring V r) (j : Fin r) (A B : Finset V) :
    ∑ a ∈ A, degreeOn c j B a = ∑ b ∈ B, degreeOn c j A b := by
  classical
  simp only [degreeOn, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  have hiff : (b ≠ a ∧ c s(a, b) = j) ↔ (a ≠ b ∧ c s(b, a) = j) := by
    rw [ne_comm, Sym2.eq_swap]
  simp only [hiff]


end Counting

def ds (c : Coloring V r) (j : Fin r) (W : Finset V) : ℕ :=
  ∑ x ∈ W, degreeOn c j W x

def closed (c : Coloring V r) (j : Fin r) (W : Finset V) (x : V) : Finset V :=
  insert x (W.filter (fun y => y ≠ x ∧ c s(x,y) = j))

lemma closed_sub (c : Coloring V r) (j : Fin r) {W : Finset V} {x : V}
    (hx : x ∈ W) : closed c j W x ⊆ W := insert_subset hx (filter_subset _ _)

lemma closed_card (c : Coloring V r) (j : Fin r) (W : Finset V) (x : V) :
    (closed c j W x).card = degreeOn c j W x + 1 := by
  unfold closed degreeOn
  rw [card_insert_of_notMem (by simp)]

lemma degree_bound (c : Coloring V r) (j : Fin r) {A : Finset V} {x : V}
    (hx : x ∈ A) : degreeOn c j A x + 1 ≤ A.card := by
  have hsub : A.filter (fun y => y ≠ x ∧ c s(x,y) = j) ⊆ A.erase x := by
    intro y hy
    exact mem_erase.mpr ⟨(mem_filter.mp hy).2.1,(mem_filter.mp hy).1⟩
  have h := card_le_card hsub
  rw [card_erase_of_mem hx] at h
  have hp := card_pos.mpr ⟨x,hx⟩
  unfold degreeOn
  omega

lemma ds_bound (c : Coloring V r) (j : Fin r) (A : Finset V) :
    ds c j A + A.card ≤ A.card * A.card := by
  have h := sum_le_sum (s := A) (fun x hx => degree_bound c j hx)
  simpa [ds,sum_add_distrib,Nat.mul_comm] using h

lemma ds_decomposition (c : Coloring V r) (j : Fin r) {W A : Finset V}
    (hA : A ⊆ W) :
    ds c j W + ds c j A = ds c j (W \ A) + 2 * (∑ x ∈ A, degreeOn c j W x) := by
  have hs := sum_split (c:=c) (j:=j) A hA
  have hn : (∑ x ∈ W \ A, degreeOn c j W x) =
      (∑ x ∈ W \ A, degreeOn c j A x) + ds c j (W \ A) := by
    simp only [ds,←sum_add_distrib]
    exact sum_congr rfl (fun x _ => nbr_split (c:=c) (j:=j) A hA x)
  have hnA : (∑ x ∈ A, degreeOn c j W x) = ds c j A +
      (∑ x ∈ A, degreeOn c j (W \ A) x) := by
    simp only [ds,←sum_add_distrib]
    exact sum_congr rfl (fun x _ => nbr_split (c:=c) (j:=j) A hA x)
  rw [bipartite_count c j A (W \ A)] at hnA
  unfold ds at *
  omega

lemma closed_cap (c : Coloring V r) (j : Fin r) {W : Finset V} {x : V}
    {b : ℕ} (hx : x ∈ W)
    (hb : ∀ A ⊆ W, Independent c j A → A.card ≤ b) :
    ∀ A ⊆ W \ closed c j W x, Independent c j A → A.card ≤ b-1 := by
  intro A hA hI
  have hxA : x ∉ A := by
    intro h
    have hc := (mem_sdiff.mp (hA h)).2
    exact hc (mem_insert_self _ _)
  have hno : ∀ y ∈ A, c s(x,y) ≠ j := by
    intro y hy he
    have hh := mem_sdiff.mp (hA hy)
    have hxy : y ≠ x := by intro e; subst y; exact hxA hy
    exact hh.2 (mem_insert_of_mem (mem_filter.mpr ⟨hh.1,hxy,he⟩))
  have hu := hb (insert x A) (insert_subset hx (hA.trans sdiff_subset))
    (independent_insert hI hno)
  rw [card_insert_of_notMem hxA] at hu
  omega

lemma minimum_closed_removal (c : Coloring V r) (j : Fin r)
    {W : Finset V} {x : V} (hx : x ∈ W)
    (hmin : ∀ y ∈ W, degreeOn c j W x ≤ degreeOn c j W y) :
    ds c j (W \ closed c j W x) + degreeOn c j W x * (degreeOn c j W x+1)
      ≤ ds c j W := by
  let A := closed c j W x
  have hA := closed_sub c j hx
  have hn := closed_card c j W x
  have hsum := sum_le_sum (s:=A) (fun y hy => hmin y (hA hy))
  simp only [sum_const,smul_eq_mul] at hsum
  have hd := ds_decomposition c j hA
  have hi := ds_bound c j A
  change A.card = degreeOn c j W x + 1 at hn
  change ds c j W + ds c j A = ds c j (W \ A) +
    2 * (∑ y ∈ A, degreeOn c j W y) at hd
  rw [hn] at hi hsum
  nlinarith

/-- Exact integral tangent to Turan's lower edge bound, proved here from scratch.
No equality characterization, external theorem, or graph certificate is assumed. -/
theorem linear_turan (c : Coloring V r) (j : Fin r) (k b : ℕ)
    (W : Finset V) (hcap : ∀ A ⊆ W, Independent c j A → A.card ≤ b) :
    2*k*W.card ≤ ds c j W + k*(k+1)*b := by
  induction b using Nat.strong_induction_on generalizing W with
  | h b ih =>
    by_cases he : W = ∅
    · subst W
      simp [ds]
    have hne : W.Nonempty := nonempty_iff_ne_empty.mpr he
    obtain ⟨x,hx,hmin⟩ := W.exists_min_image (degreeOn c j W) hne
    have hbpos : 0 < b := by
      have hsing : Independent c j {x} := by
        intro u hu v hv huv
        simp only [mem_singleton] at hu hv
        subst u; subst v
        exact (huv rfl).elim
      have h := hcap {x} (singleton_subset_iff.mpr hx) hsing
      simp only [card_singleton] at h
      omega
    let d := degreeOn c j W x
    let B := W \ closed c j W x
    have hcB := closed_cap c j hx hcap
    have hind := ih (b-1) (by omega) B hcB
    have hrem := minimum_closed_removal c j hx hmin
    have hsize : W.card = B.card + d + 1 := by
      have hs := card_sdiff_add_card_eq_card (closed_sub c j hx)
      rw [closed_card] at hs
      dsimp only [B,d]
      omega
    have hpoly : 2*k*(d+1) ≤ d*(d+1)+k*(k+1) := by
      by_cases hkd : k ≤ d
      · have ht : 0 ≤ (d-k)*(d-k+1) := Nat.zero_le _
        have heq : d-k+k=d := Nat.sub_add_cancel hkd
        nlinarith
      · have hd : d+1 ≤ k := by omega
        have ht : 0 ≤ (k-(d+1))*(k-(d+1)+1) := Nat.zero_le _
        have heq : k-(d+1)+(d+1)=k := Nat.sub_add_cancel hd
        nlinarith
    have heq : b-1+1=b := by omega
    change ds c j B + d*(d+1) ≤ ds c j W at hrem
    rw [hsize, ←heq]
    nlinarith
end Surplus.SparseGraphBounds
end
end

/- ## MarginalCost -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.PrivateStructure.Extension
open CoreTheory.MinimalCore Surplus.SparseGraphBounds
variable {V : Type} [DecidableEq V] {r : ℕ}

lemma clipped_weight_budget (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (I : Finset V) (hI : Independent c i I) (hd : Disjoint I W) :
    (∑ u ∈ I, (r-degreeOn c i W u)) ≤ r*(r-alphaOn c i W) := by
  let J := I.filter (fun u => degreeOn c i W u ≤ r)
  have hJI : J ⊆ I := filter_subset _ _
  have he : (∑ u ∈ J, (r-degreeOn c i W u)) = ∑ u ∈ I, (r-degreeOn c i W u) := by
    apply sum_subset hJI
    intro u hu hn
    have hlt : r < degreeOn c i W u := by
      by_contra h
      exact hn (mem_filter.mpr ⟨hu,by omega⟩)
    exact Nat.sub_eq_zero_of_le (by omega)
  rw [←he]
  exact outside_weight_budget c i H hW ha J (independent_mono hJI hI)
    (hd.mono_left hJI) (fun u hu => (mem_filter.mp hu).2)

/-- Elementary rational tangent, with clipped weights and both denominator signs checked. -/
lemma clipped_tangent (r d c : ℕ) (hr : 0 < r) :
    ((2:ℚ)*r-((d:ℚ)+1)-2*c)/r ≤ ((r-c : ℕ):ℚ)/((d:ℚ)+1) := by
  have hrq : (0:ℚ)<r := by exact_mod_cast hr
  have hx : (0:ℚ)<(d:ℚ)+1 := by positivity
  by_cases hc : c ≤ r
  · rw [Nat.cast_sub hc]
    apply (div_le_div_iff₀ hrq hx).mpr
    by_cases hlarge : (r:ℚ) ≤ 2*((d:ℚ)+1)
    · have h := mul_nonneg (show (0:ℚ)≤c by positivity)
        (show (0:ℚ)≤2*((d:ℚ)+1)-r by linarith)
      nlinarith [sq_nonneg (((d:ℚ)+1)-r)]
    · have hcr : (0:ℚ)≤(r:ℚ)-c := by exact sub_nonneg.mpr (by exact_mod_cast hc)
      have h := mul_nonneg hcr (show (0:ℚ)≤r-2*((d:ℚ)+1) by linarith)
      nlinarith [sq_nonneg ((d:ℚ)+1)]
  · have hrc : r ≤ c := by omega
    rw [Nat.sub_eq_zero_of_le hrc,Nat.cast_zero,zero_div]
    apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hrq)
    have hcq : (r:ℚ)≤c := by exact_mod_cast hrc
    linarith

/-- The exact extra edge cost of adjoining rb vertices outside a minimal core. -/
theorem marginal_degree_cost (c : Coloring V r) (i : Fin r) (H : Caps c)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r)
    (U : Finset V) (hd : Disjoint U W) (hn : U.card = r*(r-alphaOn c i W)) :
    r*U.card ≤ ds c i U + U.card + 2*(∑ u ∈ U, degreeOn c i W u) := by
  let w : V → ℚ := fun u => ((r-degreeOn c i W u : ℕ):ℚ)
  have hw : ∀ u, 0 ≤ w u := by intro u; positivity
  obtain ⟨I,hIU,hI,hpot⟩ := Greedy.weighted_independent c i w hw U
  have hb := clipped_weight_budget c i H hW ha I hI (hd.mono_left hIU)
  have hweight : (∑ u ∈ I, w u) ≤ (U.card:ℚ) := by
    dsimp only [w]
    rw [←Nat.cast_sum,hn]
    exact_mod_cast hb
  have hr : 0<r := by omega
  have hrq : (0:ℚ)<r := by exact_mod_cast hr
  have hl := sum_le_sum (s:=U) (fun u _ =>
    clipped_tangent r (degreeOn c i U u) (degreeOn c i W u) hr)
  have hle : (∑ u ∈ U, ((2:ℚ)*r-((degreeOn c i U u:ℚ)+1)-2*degreeOn c i W u)/r)
      ≤ (U.card:ℚ) := hl.trans (hpot.trans hweight)
  rw [←sum_div] at hle
  have hnum : (∑ u ∈ U, ((2:ℚ)*r-((degreeOn c i U u:ℚ)+1)-2*degreeOn c i W u)) =
      ((2:ℚ)*r-1)*U.card - (ds c i U:ℚ) - 2*((∑ u ∈ U, degreeOn c i W u:ℕ):ℚ) := by
    simp only [ds,Nat.cast_sum,sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
    ring
  rw [hnum] at hle
  have h := (div_le_iff₀ hrq).mp hle
  have hfinal : (r:ℚ)*U.card ≤ (ds c i U:ℚ) + U.card +
      2*((∑ u ∈ U, degreeOn c i W u:ℕ):ℚ) := by linarith
  exact_mod_cast hfinal

/-- Sparse full layers bound the surplus of each proper minimal core. -/
theorem sparse_core_capacity [Fintype V] (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hV : Fintype.card V=r^2+1) (hsparse : ds c i univ ≤ r*Fintype.card V)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    (∑ v ∈ W, surplus c i W v) ≤ r*(r-alphaOn c i W) := by
  let U := (univ:Finset V) \ W
  have hwsub : W ⊆ (univ:Finset V) := subset_univ W
  have hcards : U.card+W.card=Fintype.card V := by
    simpa only [U,card_univ] using card_sdiff_add_card_eq_card hwsub
  have hWC := minimal_card c i hW
  have hr : r-alphaOn c i W+alphaOn c i W=r := by omega
  have hUC : U.card=r*(r-alphaOn c i W) := by nlinarith
  have hd : Disjoint U W := disjoint_sdiff.symm
  have hm := marginal_degree_cost c i H hW ha U hd hUC
  have hsplit := ds_decomposition c i hwsub
  have hsum : (∑ v ∈ W, degreeOn c i univ v) =
      ds c i W + ∑ v ∈ U, degreeOn c i W v := by
    rw [←bipartite_count c i W U]
    simp only [ds,←sum_add_distrib]
    exact sum_congr rfl (fun v _ => nbr_split (c:=c) (j:=i) W hwsub v)
  rw [hsum] at hsplit
  have hdW := degree_sum_eq c i hW (Subset.refl W)
  change ds c i W=r*W.card+∑ v ∈ W, surplus c i W v at hdW
  change ds c i univ+ds c i W=ds c i U+2*(ds c i W+∑ v ∈ U, degreeOn c i W v) at hsplit
  nlinarith

/-- The former last core level a=r-1 is uniformly impossible in a sparse layer. -/
theorem sparse_core_parameter [Fintype V] (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hr : 3 ≤ r) (hV : Fintype.card V=r^2+1)
    (hsparse : ds c i univ ≤ r*Fintype.card V)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    alphaOn c i W+2 ≤ r := by
  have hu := sparse_core_capacity c i H hV hsparse hW ha
  have hl := surplus_twice_parameter c i H hr hW ha
  by_contra hn
  have he : r-alphaOn c i W=1 := by omega
  rw [he,Nat.mul_one] at hu
  omega
end Surplus.PrivateStructure.Extension
end
end

/- ## SparseThree -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.SparseGraphBounds
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

lemma even_ds (c : Coloring V r) (j : Fin r) (W : Finset V) : Even (ds c j W) := by
  induction W using Finset.induction_on with
  | empty => simp [ds]
  | @insert x W hx ih =>
    have hA : ({x} : Finset V) ⊆ insert x W := singleton_subset_iff.mpr (mem_insert_self _ _)
    have hd := ds_decomposition c j hA
    have hz : ds c j {x} = 0 := by simp [ds,degreeOn]
    have he : insert x W \ {x} = W := by ext v; simp; aesop
    rw [hz,he,sum_singleton,Nat.add_zero] at hd
    obtain ⟨k,hk⟩ := ih
    refine ⟨k + degreeOn c j (insert x W) x, ?_⟩
    omega

lemma alpha_two_degree (c : Coloring V r) (j : Fin r) (W : Finset V)
    (hcap : ∀ A ⊆ W, Independent c j A → A.card ≤ 2)
    (hcl : ∀ A ⊆ W, Clique c j A → A.card ≤ 3)
    {x : V} (hx : x ∈ W) : W.card ≤ degreeOn c j W x + 4 := by
  let B := W.filter (fun y => y ≠ x ∧ c s(x,y) ≠ j)
  have hB : B ⊆ W := filter_subset _ _
  have hBC : Clique c j B := by
    intro u hu v hv huv
    by_contra he
    have hu' := mem_filter.mp hu
    have hv' := mem_filter.mp hv
    have hp := CoreTheory.CoreIncidence.independent_pair he
    have hi : Independent c j (insert x {u,v}) := by
      apply independent_insert hp
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hu'.2.2
      · exact hv'.2.2
    have hs : insert x {u,v} ⊆ W := insert_subset hx (insert_subset (hB hu) (singleton_subset_iff.mpr (hB hv)))
    have hc := hcap _ hs hi
    have hcard : (insert x {u,v} : Finset V).card = 3 := by
      simp [huv,Ne.symm hu'.2.1,Ne.symm hv'.2.1]
    omega
  have hBc := hcl B hB hBC
  let N := W.filter (fun y => y ≠ x ∧ c s(x,y) = j)
  have hcover : W ⊆ insert x (N ∪ B) := by
    intro y hy
    by_cases hyx : y=x
    · subst y; exact mem_insert_self _ _
    apply mem_insert_of_mem
    by_cases he : c s(x,y)=j
    · exact mem_union_left _ (mem_filter.mpr ⟨hy,hyx,he⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hy,hyx,he⟩)
  have hc := card_le_card hcover
  have hi := card_insert_le x (N ∪ B)
  have hu := card_union_le N B
  change W.card ≤ N.card+4
  omega

lemma alpha_two_sum (c : Coloring V r) (j : Fin r) (W : Finset V)
    (hcap : ∀ A ⊆ W, Independent c j A → A.card ≤ 2)
    (hcl : ∀ A ⊆ W, Clique c j A → A.card ≤ 3) :
    W.card*W.card ≤ ds c j W + 4*W.card := by
  have h := sum_le_sum (s:=W) (fun x hx => alpha_two_degree c j W hcap hcl hx)
  simpa [ds,sum_add_distrib,Nat.mul_comm] using h
end Surplus.SparseGraphBounds

namespace Surplus.SparseGraphBounds
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

/-- Auxiliary residue class needed by the main deletion induction. -/
theorem sparse_three_offset_two (c : Coloring V r) (j : Fin r) (b : ℕ)
    (hb : 2 ≤ b) (W : Finset V) (hn : W.card = 3*b+2)
    (hcap : ∀ A ⊆ W, Independent c j A → A.card ≤ b)
    (hcl : ∀ A ⊆ W, Clique c j A → A.card ≤ 3) :
    6*b+14 ≤ ds c j W := by
  induction b using Nat.strong_induction_on generalizing W with
  | h b ih =>
    by_cases hb2 : b=2
    · subst b
      have h := alpha_two_sum c j W hcap hcl
      rw [hn] at h
      omega
    have hb3 : 3 ≤ b := by omega
    have hne : W.Nonempty := card_pos.mp (by omega)
    obtain ⟨x,hx,hmin⟩ := W.exists_min_image (degreeOn c j W) hne
    let d := degreeOn c j W x
    have hlow : W.card*d ≤ ds c j W := by
      have h := sum_le_sum (s:=W) hmin
      simpa [d,ds] using h
    by_cases hd : 3 ≤ d
    · have h := (Nat.mul_le_mul_left W.card hd).trans hlow
      rw [hn] at h
      omega
    let B := W \ closed c j W x
    have hc := closed_cap c j hx hcap
    have hclB : ∀ A ⊆ B, Clique c j A → A.card ≤ 3 :=
      fun A hA => hcl A (hA.trans sdiff_subset)
    have hs : B.card+d+1=W.card := by
      have h := card_sdiff_add_card_eq_card (closed_sub c j hx)
      rw [closed_card] at h
      dsimp only [B,d]
      omega
    have hm := minimum_closed_removal c j hx hmin
    change ds c j B+d*(d+1) ≤ ds c j W at hm
    have cases : d=0 ∨ d=1 ∨ d=2 := by omega
    rcases cases with hd0 | hd1 | hd2
    · have h := linear_turan c j 3 (b-1) B hc
      rw [hd0] at hs hm
      omega
    · have h := linear_turan c j 3 (b-1) B hc
      rw [hd1] at hs hm
      omega
    · have hBn : B.card=3*(b-1)+2 := by omega
      have h := ih (b-1) (by omega) (by omega) B hBn hc hclB
      rw [hd2] at hm
      omega
end Surplus.SparseGraphBounds

namespace Surplus.SparseGraphBounds
open CoreTheory.MinimalCore
variable {V : Type} [DecidableEq V] {r : ℕ}

/-- A K4-free colour layer on 3b+1 vertices with independence cap b
has at least 3b+5 edges. All graph-theoretic premises are explicit. -/
theorem sparse_three_lower (c : Coloring V r) (j : Fin r) (b : ℕ)
    (hb : 2 ≤ b) (W : Finset V) (hn : W.card = 3*b+1)
    (hcap : ∀ A ⊆ W, Independent c j A → A.card ≤ b)
    (hcl : ∀ A ⊆ W, Clique c j A → A.card ≤ 3) :
    6*b+10 ≤ ds c j W := by
  induction b using Nat.strong_induction_on generalizing W with
  | h b ih =>
    by_cases hb2 : b=2
    · subst b
      have h := alpha_two_sum c j W hcap hcl
      rw [hn] at h
      obtain ⟨k,hk⟩ := even_ds c j W
      omega
    have hb3 : 3 ≤ b := by omega
    have hne : W.Nonempty := card_pos.mp (by omega)
    obtain ⟨x,hx,hmin⟩ := W.exists_min_image (degreeOn c j W) hne
    let d := degreeOn c j W x
    have hlow : W.card*d ≤ ds c j W := by
      have h := sum_le_sum (s:=W) hmin
      simpa [d,ds] using h
    by_cases hd : 3 ≤ d
    · have h := (Nat.mul_le_mul_left W.card hd).trans hlow
      rw [hn] at h
      omega
    let B := W \ closed c j W x
    have hc := closed_cap c j hx hcap
    have hclB : ∀ A ⊆ B, Clique c j A → A.card ≤ 3 :=
      fun A hA => hcl A (hA.trans sdiff_subset)
    have hs : B.card+d+1=W.card := by
      have h := card_sdiff_add_card_eq_card (closed_sub c j hx)
      rw [closed_card] at h
      dsimp only [B,d]
      omega
    have hm := minimum_closed_removal c j hx hmin
    change ds c j B+d*(d+1) ≤ ds c j W at hm
    have cases : d=0 ∨ d=1 ∨ d=2 := by omega
    rcases cases with hd0 | hd1 | hd2
    · have h := linear_turan c j 3 (b-1) B hc
      rw [hd0] at hs hm
      omega
    · have hBn : B.card=3*(b-1)+2 := by omega
      have h := sparse_three_offset_two c j (b-1) (by omega) B hBn hc hclB
      rw [hd1] at hm
      omega
    · have hBn : B.card=3*(b-1)+1 := by omega
      have h := ih (b-1) (by omega) (by omega) B hBn hc hclB
      rw [hd2] at hm
      omega
end Surplus.SparseGraphBounds
end
end

/- ## AlphaTwoCore -/
section
/-
## Excluding independence-two minimal cores

This section adapts the Harmonic Aristotle-assisted independence-two argument
and consolidates its definitions with the preceding minimal-core interface.
For r >= 3, capped colourings with a selected independence cap of two have at
most 2r vertices. The proof combines a non-neighbourhood bound with an improved
edge lower bound in the other colours. The restriction r >= 3 is essential.
This is a partial structural result, not the full conjecture.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CoreTheory.AlphaTwoCore

open Finset CoreTheory.MinimalCore CoreTheory.RegularityBridge

attribute [local instance] Classical.propDecidable

section
variable {V : Type} [DecidableEq V] {r : ℕ}

/-- Number of vertices of `W` joined to `x` by a pair whose colour is not `i`.
(The complementary count to `CoreTheory.MinimalCore.degreeOn`; in the preceding interface.) -/
noncomputable def nonDegree (c : Coloring V r) (i : Fin r) (W : Finset V) (x : V) : ℕ :=
  (W.filter (fun y => y ≠ x ∧ c s(x, y) ≠ i)).card

/- ## §3  The sparse-colour lemma

A colour class with independence number `≤ r` on `2 * r + 1` vertices and with no
monochromatic triangle has at least `r + 3` edges.  (The clique-partition /
Turán bound is `r + 2`, attained only by `K_3 ⊔ (r-1) K_2`, which has a triangle.)

Edges are counted through the degree sum, so the statement proved is
`2 * r + 6 ≤ ∑ x ∈ W, degreeOn c j W x`. -/


section Sparse

variable {c : Coloring V r} {j : Fin r} {W : Finset V}

/-- The degree sum splits over a subset and its complement. -/
private lemma sum_split (A : Finset V) (hA : A ⊆ W) :
    ∑ x ∈ W, degreeOn c j W x
      = (∑ x ∈ A, degreeOn c j W x) + ∑ x ∈ W \ A, degreeOn c j W x := by
  rw [← Finset.sum_union (Finset.disjoint_sdiff)]
  congr 1
  rw [Finset.union_sdiff_of_subset hA]

/-- The neighbour count splits over a subset and its complement. -/
private lemma nbr_split (A : Finset V) (hA : A ⊆ W) (x : V) :
    degreeOn c j W x = degreeOn c j A x + degreeOn c j (W \ A) x := by
  classical
  unfold degreeOn
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.filter_union, Finset.union_sdiff_of_subset hA]
  · exact Finset.disjoint_filter_filter Finset.disjoint_sdiff

/-- The number of ordered `j`-pairs inside `B` is the sum of the `j`-degrees. -/
private lemma card_pairsIn (c : Coloring V r) (j : Fin r) (B : Finset V) :
    (((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j))).card
      = ∑ v ∈ B, degreeOn c j B v := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (t := B)
      (fun p hp => (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hfib : (((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)).filter
        (fun p => p.1 = v))
      = {v} ×ˢ (B.filter (fun y => y ≠ v ∧ c s(v, y) = j)) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨_, hb⟩, hne, hc⟩, rfl⟩
      exact ⟨rfl, hb, Ne.symm hne, hc⟩
    · rintro ⟨rfl, hb, hne, hc⟩
      exact ⟨⟨⟨hv, hb⟩, Ne.symm hne, hc⟩, rfl⟩
  rw [hfib, Finset.card_product, Finset.card_singleton, one_mul, degreeOn]

/-- Double counting of the `j`-edges between `A` and `B`. -/
private lemma bipartite_count (c : Coloring V r) (j : Fin r) (A B : Finset V) :
    ∑ a ∈ A, degreeOn c j B a = ∑ b ∈ B, degreeOn c j A b := by
  classical
  simp only [degreeOn, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  have hiff : (b ≠ a ∧ c s(a, b) = j) ↔ (a ≠ b ∧ c s(b, a) = j) := by
    rw [ne_comm, Sym2.eq_swap]
  simp only [hiff]

/-- Two distinct `j`-edges inside `B` give four ordered `j`-pairs. -/
private lemma four_ordered (c : Coloring V r) (j : Fin r) (B : Finset V) (b1 b2 x y : V)
    (hb1 : b1 ∈ B) (hb2 : b2 ∈ B) (hx : x ∈ B) (hy : y ∈ B)
    (h12 : b1 ≠ b2) (hxy : x ≠ y)
    (hne1 : ¬(b1 = x ∧ b2 = y)) (hne2 : ¬(b1 = y ∧ b2 = x))
    (e1 : c s(b1, b2) = j) (e2 : c s(x, y) = j) :
    4 ≤ ∑ v ∈ B, degreeOn c j B v := by
  classical
  rw [← card_pairsIn c j B]
  have hsub : ({(b1, b2), (b2, b1), (x, y), (y, x)} : Finset (V × V))
      ⊆ (B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    have hswap1 : c s(b2, b1) = j := by rw [Sym2.eq_swap]; exact e1
    have hswap2 : c s(y, x) = j := by rw [Sym2.eq_swap]; exact e2
    rcases hp with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb1, hb2⟩, h12, e1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb2, hb1⟩, h12.symm, hswap1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy, e2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, hxy.symm, hswap2⟩
  have hcard : ({(b1, b2), (b2, b1), (x, y), (y, x)} : Finset (V × V)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, not_or]
        exact ⟨fun h => h12 h.1, hne1, hne2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, not_or]
        exact ⟨fun h => hne2 ⟨h.2, h.1⟩, fun h => hne1 ⟨h.2, h.1⟩⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton, Prod.ext_iff]
        exact fun h => hxy h.1), Finset.card_singleton]
  calc (4 : ℕ) = ({(b1, b2), (b2, b1), (x, y), (y, x)} : Finset (V × V)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The endgame of the sparse colour lemma: if `A` is a maximum `j`-independent set
of size `r`, `B` is its complement of size `r + 1`, every vertex of `B` has exactly
one `j`-neighbour in `A`, and the only `j`-edge inside `B` is `b1b2`, then `b1` and
`b2` have a common `j`-neighbour in `A`, i.e. there is a `j`-triangle. -/
private lemma endgame_triangle (c : Coloring V r) (j : Fin r) (W A B : Finset V)
    (b1 b2 : V)
    (hAW : A ⊆ W) (hBW : B ⊆ W) (hdisj : ∀ b ∈ B, b ∉ A)
    (hcap : ∀ A' ⊆ W, Independent c j A' → A'.card ≤ r)
    (htri : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, x ≠ y → x ≠ z → y ≠ z →
      c s(x, y) = j → c s(x, z) = j → c s(y, z) = j → False)
    (hAr : A.card = r) (hBr : B.card = r + 1)
    (hall : ∀ b ∈ B, degreeOn c j A b = 1)
    (hb1 : b1 ∈ B) (hb2 : b2 ∈ B) (h12 : b1 ≠ b2) (e12 : c s(b1, b2) = j)
    (h1ind : Independent c j (B.erase b1)) (h2ind : Independent c j (B.erase b2)) :
    False := by
  classical
  have hex : ∀ b ∈ B, ∃ a, a ∈ A ∧ c s(b, a) = j := by
    intro b hb
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hall b hb)
    have hmem : a ∈ A.filter (fun y => y ≠ b ∧ c s(b, y) = j) := by rw [ha]; simp
    exact ⟨a, (Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2.2⟩
  choose! g hgA hgc using hex
  have huniq : ∀ b ∈ B, ∀ a ∈ A, c s(b, a) = j → a = g b := by
    intro b hb a ha hc
    have hane : a ≠ b := fun h => hdisj b hb (h ▸ ha)
    have hgne : g b ≠ b := fun h => hdisj b hb (h ▸ hgA b hb)
    have h1 : a ∈ A.filter (fun y => y ≠ b ∧ c s(b, y) = j) :=
      Finset.mem_filter.mpr ⟨ha, hane, hc⟩
    have h2 : g b ∈ A.filter (fun y => y ≠ b ∧ c s(b, y) = j) :=
      Finset.mem_filter.mpr ⟨hgA b hb, hgne, hgc b hb⟩
    exact Finset.card_le_one.mp (le_of_eq (hall b hb)) a h1 (g b) h2
  have hsurj : ∀ b0 ∈ B, Independent c j (B.erase b0) →
      ∀ a ∈ A, ∃ b ∈ B.erase b0, g b = a := by
    intro b0 hb0 hind a ha
    by_contra hcon
    push Not at hcon
    have hno : ∀ y ∈ B.erase b0, c s(a, y) ≠ j := by
      intro y hy hc
      have hyB := Finset.mem_of_mem_erase hy
      have heq : a = g y := huniq y hyB a ha (by rw [Sym2.eq_swap]; exact hc)
      exact hcon y hy heq.symm
    have hins : Independent c j (insert a (B.erase b0)) := independent_insert hind hno
    have hsub : insert a (B.erase b0) ⊆ W :=
      Finset.insert_subset (hAW ha) ((Finset.erase_subset _ _).trans hBW)
    have hcard : (insert a (B.erase b0)).card = r + 1 := by
      rw [Finset.card_insert_of_notMem (fun h => hdisj a (Finset.mem_of_mem_erase h) ha),
        Finset.card_erase_of_mem hb0, hBr]
      omega
    have := hcap _ hsub hins
    omega
  have hinj : ∀ b0 ∈ B, Independent c j (B.erase b0) → Set.InjOn g (B.erase b0) := by
    intro b0 hb0 hind
    apply Finset.injOn_of_card_image_eq
    have hsubA : (B.erase b0).image g ⊆ A := by
      intro v hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      exact hgA b (Finset.mem_of_mem_erase hb)
    have hAsub : A ⊆ (B.erase b0).image g := by
      intro a ha
      obtain ⟨b, hb, hgb⟩ := hsurj b0 hb0 hind a ha
      exact Finset.mem_image.mpr ⟨b, hb, hgb⟩
    rw [Finset.Subset.antisymm hsubA hAsub, hAr, Finset.card_erase_of_mem hb0, hBr]
    omega
  obtain ⟨b, hb, hgb⟩ := hsurj b1 hb1 h1ind (g b1) (hgA b1 hb1)
  have hbB := Finset.mem_of_mem_erase hb
  have hbne1 : b ≠ b1 := Finset.ne_of_mem_erase hb
  have hbb2 : b = b2 := by
    by_contra hne
    have hmem1 : b ∈ B.erase b2 := Finset.mem_erase.mpr ⟨hne, hbB⟩
    have hmem2 : b1 ∈ B.erase b2 := Finset.mem_erase.mpr ⟨h12, hb1⟩
    exact hbne1 (hinj b2 hb2 h2ind (Finset.mem_coe.mpr hmem1) (Finset.mem_coe.mpr hmem2) hgb)
  subst hbb2
  have haA : g b1 ∈ A := hgA b1 hb1
  have hab1 : c s(g b1, b1) = j := by rw [Sym2.eq_swap]; exact hgc b1 hb1
  have hab2 : c s(g b1, b) = j := by
    rw [Sym2.eq_swap, ← hgb]
    exact hgc b hbB
  exact htri (g b1) (hAW haA) b1 (hBW hb1) b (hBW hbB)
    (fun h => hdisj b1 hb1 (h ▸ haA)) (fun h => hdisj b hbB (h ▸ haA))
    (Ne.symm hbne1) hab1 hab2 e12

end Sparse

/-- **Sparse colour lemma.**  A colour `j` whose independent sets inside `W` have
at most `r` vertices and which spans no triangle inside `W`, where
`W.card = 2 * r + 1`, has at least `r + 3` edges inside `W`: the degree sum is at
least `2 * r + 6`.

Without the triangle hypothesis the sharp bound is `r + 2` edges, attained by
`K_3 ⊔ (r-1) K_2`; the triangle hypothesis is what forces one more edge. -/
theorem sparse_colour_lower (c : Coloring V r) (j : Fin r) (W : Finset V)
    (hW : W.card = 2 * r + 1)
    (hcap : ∀ A ⊆ W, Independent c j A → A.card ≤ r)
    (htri : ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, x ≠ y → x ≠ z → y ≠ z →
      c s(x, y) = j → c s(x, z) = j → c s(y, z) = j → False) :
    2 * r + 6 ≤ ∑ x ∈ W, degreeOn c j W x := by
  classical
  obtain ⟨A, hAW, hAind, hAcard⟩ := alpha_witness c j W
  have hBW : W \ A ⊆ W := Finset.sdiff_subset
  have hdisj : ∀ b ∈ W \ A, b ∉ A := fun b hb => (Finset.mem_sdiff.mp hb).2
  have hAle : A.card ≤ r := hcap A hAW hAind
  have hBcard : (W \ A).card = W.card - A.card := Finset.card_sdiff_of_subset hAW
  have hAzero : ∀ x ∈ A, degreeOn c j A x = 0 := by
    intro x hx
    have hemp : A.filter (fun y => y ≠ x ∧ c s(x, y) = j) = ∅ := by
      apply Finset.filter_false_of_mem
      rintro y hy ⟨hyx, hc⟩
      exact hAind x hx y hy (Ne.symm hyx) hc
    rw [degreeOn, hemp, Finset.card_empty]
  -- the degree sum is `2 * m + S`
  have hsplit : ∑ x ∈ W, degreeOn c j W x
      = 2 * (∑ b ∈ W \ A, degreeOn c j A b) + ∑ b ∈ W \ A, degreeOn c j (W \ A) b := by
    rw [sum_split A hAW]
    have h1 : ∑ x ∈ A, degreeOn c j W x = ∑ x ∈ A, degreeOn c j (W \ A) x :=
      Finset.sum_congr rfl fun x hx => by rw [nbr_split A hAW x, hAzero x hx, Nat.zero_add]
    have h2 : ∑ x ∈ W \ A, degreeOn c j W x
        = (∑ x ∈ W \ A, degreeOn c j A x) + ∑ x ∈ W \ A, degreeOn c j (W \ A) x := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => nbr_split A hAW x
    rw [h1, h2, bipartite_count c j A (W \ A)]
    ring
  rw [hsplit]
  -- every vertex outside `A` has a `j`-neighbour in `A`
  have hB1 : ∀ b ∈ W \ A, 1 ≤ degreeOn c j A b := by
    intro b hb
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hno : ∀ y ∈ A, c s(b, y) ≠ j := by
      intro y hy hc
      have hmem : y ∈ A.filter (fun z => z ≠ b ∧ c s(b, z) = j) :=
        Finset.mem_filter.mpr ⟨hy, fun h => hdisj b hb (h ▸ hy), hc⟩
      exact (Finset.card_ne_zero_of_mem hmem) hzero
    have hins : Independent c j (insert b A) := independent_insert hAind hno
    have hsub : insert b A ⊆ W := Finset.insert_subset (hBW hb) hAW
    have hle := card_le_alpha (i := j) hsub hins
    rw [Finset.card_insert_of_notMem (hdisj b hb), hAcard] at hle
    omega
  have hmB : (W \ A).card ≤ ∑ b ∈ W \ A, degreeOn c j A b := by
    calc (W \ A).card = ∑ _b ∈ W \ A, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hB1
  have hBbig : r + 1 ≤ (W \ A).card := by omega
  -- `W \ A` is too big to be independent
  obtain ⟨b1, hb1, b2, hb2, h12, e12⟩ :
      ∃ b1 ∈ W \ A, ∃ b2 ∈ W \ A, b1 ≠ b2 ∧ c s(b1, b2) = j := by
    by_contra hcon
    push Not at hcon
    have hind : Independent c j (W \ A) := fun x hx y hy hxy hc => (hcon x hx y hy hxy) hc
    have := hcap (W \ A) hBW hind
    omega
  have hS2 : 2 ≤ ∑ b ∈ W \ A, degreeOn c j (W \ A) b := by
    have hsub : ({b1, b2} : Finset V) ⊆ W \ A := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hb1
      · exact hb2
    have hb1n : 1 ≤ degreeOn c j (W \ A) b1 := by
      have hmem : b2 ∈ (W \ A).filter (fun y => y ≠ b1 ∧ c s(b1, y) = j) :=
        Finset.mem_filter.mpr ⟨hb2, Ne.symm h12, e12⟩
      exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem hmem)
    have hb2n : 1 ≤ degreeOn c j (W \ A) b2 := by
      have hmem : b1 ∈ (W \ A).filter (fun y => y ≠ b2 ∧ c s(b2, y) = j) :=
        Finset.mem_filter.mpr ⟨hb1, h12, by rw [Sym2.eq_swap]; exact e12⟩
      exact Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero_of_mem hmem)
    calc (2 : ℕ) ≤ degreeOn c j (W \ A) b1 + degreeOn c j (W \ A) b2 := by omega
      _ = ∑ v ∈ ({b1, b2} : Finset V), degreeOn c j (W \ A) v := by
          rw [Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  -- case analysis
  rcases Nat.lt_or_ge (r + 1) (W \ A).card with hcase | hcase
  · -- `|W \ A| ≥ r + 2`
    have : r + 2 ≤ ∑ b ∈ W \ A, degreeOn c j A b := le_trans (by omega) hmB
    omega
  · have hBr : (W \ A).card = r + 1 := le_antisymm hcase hBbig
    have hAr : A.card = r := by omega
    by_cases hbig : ∃ b ∈ W \ A, 2 ≤ degreeOn c j A b
    · obtain ⟨b0, hb0, hb0two⟩ := hbig
      have hrest : r ≤ ∑ b ∈ (W \ A).erase b0, degreeOn c j A b := by
        calc r = ((W \ A).erase b0).card := by
              rw [Finset.card_erase_of_mem hb0, hBr]
              omega
          _ = ∑ _b ∈ (W \ A).erase b0, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum fun b hb => hB1 b (Finset.mem_of_mem_erase hb)
      have hsum : ∑ b ∈ W \ A, degreeOn c j A b
          = degreeOn c j A b0 + ∑ b ∈ (W \ A).erase b0, degreeOn c j A b :=
        (Finset.add_sum_erase _ _ hb0).symm
      omega
    · push Not at hbig
      have hall : ∀ b ∈ W \ A, degreeOn c j A b = 1 := fun b hb =>
        le_antisymm (by have := hbig b hb; omega) (hB1 b hb)
      by_cases h1ind : Independent c j ((W \ A).erase b1)
      · by_cases h2ind : Independent c j ((W \ A).erase b2)
        · exact absurd (endgame_triangle c j W A (W \ A) b1 b2 hAW hBW hdisj hcap htri
            hAr hBr hall hb1 hb2 h12 e12 h1ind h2ind) not_false
        · obtain ⟨x, hx, y, hy, hxy, exy⟩ :
              ∃ x ∈ (W \ A).erase b2, ∃ y ∈ (W \ A).erase b2, x ≠ y ∧ c s(x, y) = j := by
            by_contra hcon
            push Not at hcon
            exact h2ind (fun x hx y hy hxy hc => (hcon x hx y hy hxy) hc)
          have hxB := Finset.mem_of_mem_erase hx
          have hyB := Finset.mem_of_mem_erase hy
          have hxne : x ≠ b2 := Finset.ne_of_mem_erase hx
          have hyne : y ≠ b2 := Finset.ne_of_mem_erase hy
          have h4 : 4 ≤ ∑ b ∈ W \ A, degreeOn c j (W \ A) b :=
            four_ordered c j (W \ A) b1 b2 x y hb1 hb2 hxB hyB h12 hxy
              (fun h => hyne h.2.symm) (fun h => hxne h.2.symm) e12 exy
          have : r + 1 ≤ ∑ b ∈ W \ A, degreeOn c j A b := by omega
          omega
      · obtain ⟨x, hx, y, hy, hxy, exy⟩ :
            ∃ x ∈ (W \ A).erase b1, ∃ y ∈ (W \ A).erase b1, x ≠ y ∧ c s(x, y) = j := by
          by_contra hcon
          push Not at hcon
          exact h1ind (fun x hx y hy hxy hc => (hcon x hx y hy hxy) hc)
        have hxB := Finset.mem_of_mem_erase hx
        have hyB := Finset.mem_of_mem_erase hy
        have hxne : x ≠ b1 := Finset.ne_of_mem_erase hx
        have hyne : y ≠ b1 := Finset.ne_of_mem_erase hy
        have h4 : 4 ≤ ∑ b ∈ W \ A, degreeOn c j (W \ A) b :=
          four_ordered c j (W \ A) b1 b2 x y hb1 hb2 hxB hyB h12 hxy
            (fun h => hxne h.1.symm) (fun h => hyne h.1.symm) e12 exy
        have : r + 1 ≤ ∑ b ∈ W \ A, degreeOn c j A b := by omega
        omega

/- ## §4  No minimal core with `a = 2` -/

/-- If colour `i` has independence number at most `2` on `W` and every colour is
capped by `r` on `W`, then every vertex of `W` has at most `r` non-`i` neighbours
in `W`: its non-`i` neighbourhood is an `i`-clique, hence independent in any
other colour. -/
theorem nonDegree_le (c : Coloring V r) (i : Fin r) (W : Finset V) (hr : 2 ≤ r)
    (hcap : ∀ (k : Fin r), ∀ A ⊆ W, Independent c k A → A.card ≤ r)
    (hi : ∀ A ⊆ W, Independent c i A → A.card ≤ 2)
    {x : V} (hx : x ∈ W) : nonDegree c i W x ≤ r := by
  classical
  set S := W.filter (fun y => y ≠ x ∧ c s(x, y) ≠ i) with hS
  have hSW : S ⊆ W := Finset.filter_subset _ _
  -- `S` is an `i`-clique
  have hclique : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → c s(y, z) = i := by
    intro y hy z hz hyz
    by_contra hne
    have hy' := Finset.mem_filter.mp hy
    have hz' := Finset.mem_filter.mp hz
    have hxy : x ≠ y := (Ne.symm hy'.2.1)
    have hxz : x ≠ z := (Ne.symm hz'.2.1)
    have hsub : ({x, y, z} : Finset V) ⊆ W := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hx
      · exact hy'.1
      · exact hz'.1
    have hind : Independent c i ({x, y, z} : Finset V) := by
      intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first
          | exact absurd rfl huv
          | exact hy'.2.2
          | exact hz'.2.2
          | exact hne
          | (rw [Sym2.eq_swap]; first | exact hy'.2.2 | exact hz'.2.2 | exact hne)
    have hcard : ({x, y, z} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    have := hi _ hsub hind
    omega
  -- pick another colour
  obtain ⟨k, hk⟩ : ∃ k : Fin r, k ≠ i := by
    by_cases h0 : i = ⟨0, by omega⟩
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro he
      have h := congrArg Fin.val (he.trans h0)
      simp at h
    · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
  have hkind : Independent c k S := by
    intro y hy z hz hyz
    rw [hclique y hy z hz hyz]
    exact Ne.symm hk
  exact hcap k S hSW hkind

/-- **Main theorem, contradiction form; `r ≥ 3` only.**  For `r ≥ 3`: in an `r`-colouring
in which every colour class has independence number at most `r` on `W`, if some colour has
independence number at most `2` on `W` then `W.card = 2 * r + 1` is impossible.

Consequently, for `r ≥ 3`, no minimal core of the resilience problem has
`alphaOn c i W = 2`. The hypothesis `hr : 3 ≤ r` is not cosmetic: at `r = 2` the
conclusion fails (`K_5 = C_5 + complement`, `caps ≤ 2`, `α_i = 2`, `|W| = 5 > 4`; see the
file header), and nothing below is claimed for `r = 2`. -/
theorem alpha_two_absurd (c : Coloring V r) (i : Fin r) (W : Finset V) (hr : 3 ≤ r)
    (hW : W.card = 2 * r + 1)
    (hcap : ∀ (k : Fin r), ∀ A ⊆ W, Independent c k A → A.card ≤ r)
    (hi : ∀ A ⊆ W, Independent c i A → A.card ≤ 2) : False := by
  classical
  -- no colour `j ≠ i` spans a triangle inside `W`
  have htri : ∀ j : Fin r, j ≠ i → ∀ x ∈ W, ∀ y ∈ W, ∀ z ∈ W, x ≠ y → x ≠ z → y ≠ z →
      c s(x, y) = j → c s(x, z) = j → c s(y, z) = j → False := by
    intro j hj x hx y hy z hz hxy hxz hyz e1 e2 e3
    have hsub : ({x, y, z} : Finset V) ⊆ W := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    have hind : Independent c i ({x, y, z} : Finset V) := by
      intro u hu v hv huv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      have hswap : ∀ {p q : V}, c s(p, q) = j → c s(q, p) = j := by
        intro p q h; rw [Sym2.eq_swap]; exact h
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        first
          | exact absurd rfl huv
          | (rw [e1]; exact hj)
          | (rw [e2]; exact hj)
          | (rw [e3]; exact hj)
          | (rw [hswap e1]; exact hj)
          | (rw [hswap e2]; exact hj)
          | (rw [hswap e3]; exact hj)
    have hcard : ({x, y, z} : Finset V).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
        Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
    have := hi _ hsub hind
    omega
  -- each colour `j ≠ i` has at least `r + 3` edges inside `W`
  have hlow : ∀ j ∈ Finset.univ.erase i, 2 * r + 6 ≤ ∑ x ∈ W, degreeOn c j W x := by
    intro j hj
    exact sparse_colour_lower c j W hW (hcap j) (htri j (Finset.mem_erase.mp hj).1)
  have hcards : (Finset.univ.erase i).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hsum1 : (r - 1) * (2 * r + 6)
      ≤ ∑ j ∈ Finset.univ.erase i, ∑ x ∈ W, degreeOn c j W x := by
    calc (r - 1) * (2 * r + 6) = ∑ _j ∈ Finset.univ.erase i, (2 * r + 6) := by
          rw [Finset.sum_const, smul_eq_mul, hcards]
      _ ≤ _ := Finset.sum_le_sum hlow
  -- summing the non-`i` degrees the other way round
  have hswap : ∑ j ∈ Finset.univ.erase i, ∑ x ∈ W, degreeOn c j W x
      = ∑ x ∈ W, nonDegree c i W x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold nonDegree degreeOn
    rw [Finset.card_eq_sum_card_fiberwise (f := fun y => c s(x, y)) (t := Finset.univ.erase i)
      (fun y hy => Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hy).2.2, Finset.mem_univ _⟩)]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hyW, hyx, hcj⟩
      exact ⟨⟨hyW, hyx, by rw [hcj]; exact (Finset.mem_erase.mp hj).1⟩, hcj⟩
    · rintro ⟨⟨hyW, hyx, _⟩, hcj⟩
      exact ⟨hyW, hyx, hcj⟩
  have hup : ∑ x ∈ W, nonDegree c i W x ≤ (2 * r + 1) * r := by
    calc ∑ x ∈ W, nonDegree c i W x ≤ ∑ _x ∈ W, r :=
          Finset.sum_le_sum fun x hx => nonDegree_le c i W (by omega) hcap hi hx
      _ = (2 * r + 1) * r := by rw [Finset.sum_const, smul_eq_mul, hW]
  rw [hswap] at hsum1
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 3 := ⟨r - 3, by omega⟩
  have hfinal : (s + 2) * (2 * (s + 3) + 6) ≤ (2 * (s + 3) + 1) * (s + 3) := by
    have : s + 3 - 1 = s + 2 := by omega
    rw [this] at hsum1
    exact le_trans hsum1 hup
  nlinarith [hfinal]

/-- **Main theorem; `r ≥ 3` only.**  For `r ≥ 3`: in an `r`-colouring in which every colour
class has independence number at most `r` on `W`, if some colour has independence number at
most `2` on `W` then `W.card ≤ 2 * r`.

The bound is stated for `r ≥ 3` and is false at `r = 2` (`K_5 = C_5 + complement`:
`caps ≤ 2`, `α_i = 2`, `|W| = 5 > 4 = 2 * r`), see the file header for where the counting
argument degenerates. -/
theorem alpha_two_card_le (c : Coloring V r) (i : Fin r) (W : Finset V) (hr : 3 ≤ r)
    (hcap : ∀ (k : Fin r), ∀ A ⊆ W, Independent c k A → A.card ≤ r)
    (hi : ∀ A ⊆ W, Independent c i A → A.card ≤ 2) :
    W.card ≤ 2 * r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨W', hW'W, hW'card⟩ := Finset.exists_subset_card_eq (by omega : 2 * r + 1 ≤ W.card)
  exact alpha_two_absurd c i W' hr hW'card
    (fun k A hA => hcap k A (hA.trans hW'W)) (fun A hA => hi A (hA.trans hW'W))

/- ## §5  Consequences for the resilience problem (P6)

A violation of resilience produces a minimal core `W` with `W.card = r * a + 1`
and `alphaOn c i W = a`, `2 ≤ a < r`.  §4 removes `a = 2` **for every `r ≥ 3`** (and only
there — at `r = 2` the bound of §4 is false, see the file header), so for `r ≥ 3` every
core has `a ≥ 3`, hence at least `3 * r + 1` vertices.  For `r = 3` no value of
`a` is left, which reproves resilience at `r = 3`. -/


/-- **For `r ≥ 3`, every minimal core has independence parameter at least `3`.**

If colour `i` has no independent `r`-set outside a deletion set `D` of size `< r`,
then the minimal core `W` produced from that blocker satisfies
`3 ≤ alphaOn c i W < r` and `W.card = r * alphaOn c i W + 1 ≥ 3 * r + 1`.

The values `a = 1` (an `i`-clique of size `r+1`, excluded by the cap of another
colour) and `a = 2` (excluded by `alpha_two_card_le`, hence only for `r ≥ 3`) are both
impossible. -/
theorem core_alpha_ge_three (c : Coloring V r) (hr : 3 ≤ r) (B : Finset V)
    (hB : B.card = r ^ 2)
    (hcap : ∀ (k : Fin r), ∀ A ⊆ B, Independent c k A → A.card ≤ r)
    (i : Fin r) (D : Finset V) (hD : D.card < r)
    (hblock : ∀ A ⊆ B \ D, A.card = r → ¬ Independent c i A) :
    ∃ W ⊆ B \ D, Minimal c i W ∧ 3 ≤ alphaOn c i W ∧ alphaOn c i W < r ∧
      W.card = r * alphaOn c i W + 1 := by
  classical
  -- the deleted complement has small independence number
  have halpha : alphaOn c i (B \ D) < r := by
    by_contra hge
    push Not at hge
    obtain ⟨A, hAB, hAind, hAcard⟩ := alpha_witness c i (B \ D)
    obtain ⟨A', hA'A, hA'card⟩ := Finset.exists_subset_card_eq (by omega : r ≤ A.card)
    exact hblock A' (hA'A.trans hAB) hA'card (independent_mono hA'A hAind)
  -- so the ratio `|X| ≤ r * α(X)` fails on `B \ D`
  have hviol : r * alphaOn c i (B \ D) < (B \ D).card := by
    have hmul : r * (alphaOn c i (B \ D) + 1) ≤ r * r :=
      Nat.mul_le_mul_left r (by omega)
    have hmul' : r * alphaOn c i (B \ D) + r ≤ r * r := by
      rw [Nat.mul_add, Nat.mul_one] at hmul; exact hmul
    have hsq : B.card = r * r := by rw [hB]; ring
    have hcards := Finset.card_sdiff_add_card_inter B D
    have hID : (B ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
    omega
  obtain ⟨W, hWsub, hW⟩ := minimal_exists c i (B \ D) hviol
  have hWB : W ⊆ B := hWsub.trans (Finset.sdiff_subset)
  have hcardW := minimal_card c i hW
  have hWpos : W.Nonempty := Finset.card_pos.mp (by have := hW.1; omega)
  have haW : alphaOn c i W < r := lt_of_le_of_lt (alpha_mono c i hWsub) halpha
  -- `a ≥ 1`
  have h1 : 1 ≤ alphaOn c i W := alpha_pos c i hWpos
  -- `a ≠ 1` : otherwise `W` is an `i`-clique with `r + 1` vertices
  have h2 : alphaOn c i W ≠ 1 := by
    intro hone
    obtain ⟨k, hk⟩ : ∃ k : Fin r, k ≠ i := by
      by_cases h0 : i = ⟨0, by omega⟩
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro he
        have h := congrArg Fin.val (he.trans h0)
        simp at h
      · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
    have hkind : Independent c k W := by
      intro x hx y hy hxy hck
      have hind : Independent c i ({x, y} : Finset V) := by
        intro u hu v hv huv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact absurd rfl huv
        · rw [hck]; exact hk
        · rw [Sym2.eq_swap, hck]; exact hk
        · exact absurd rfl huv
      have hsub : ({x, y} : Finset V) ⊆ W := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx
        · exact hy
      have := card_le_alpha hsub hind
      rw [Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton, hone] at this
      omega
    have hcardW' : W.card = r + 1 := by rw [hcardW, hone]; ring
    have := hcap k W hWB hkind
    omega
  -- `a ≠ 2` : the main theorem of §4
  have h3 : alphaOn c i W ≠ 2 := by
    intro htwo
    have hi2 : ∀ A ⊆ W, Independent c i A → A.card ≤ 2 := by
      intro A hA hAind
      have := card_le_alpha hA hAind
      omega
    have hcardW' : W.card = 2 * r + 1 := by rw [hcardW, htwo]; ring
    have := alpha_two_card_le c i W hr (fun k A hA => hcap k A (hA.trans hWB)) hi2
    omega
  exact ⟨W, hWsub, hW, by omega, haW, hcardW⟩

/-- **Resilience holds at `r = 3`.**  A `3`-colouring of the pairs of a `9`-set in
which every colour class has independence number at most `3` stays `3`-resilient:
deleting at most two vertices leaves an independent triple of every colour.

(For `r = 3` the only possible core parameter is `a = 2`, which §4 excludes.) -/
theorem resilient_three (c : Coloring V 3) (B : Finset V) (hB : B.card = 3 ^ 2)
    (hcap : ∀ (k : Fin 3), ∀ A ⊆ B, Independent c k A → A.card ≤ 3) :
    ResilientOn c B := by
  intro i Dset hD
  by_contra hcon
  push Not at hcon
  have hblock : ∀ A ⊆ B \ Dset, A.card = 3 → ¬ Independent c i A := by
    intro A hA hAcard hAind
    exact absurd hAind (hcon A hA hAcard)
  obtain ⟨W, _, _, h3, hlt, _⟩ :=
    core_alpha_ge_three c (le_refl 3) B hB hcap i Dset hD hblock
  omega


end

end CoreTheory.AlphaTwoCore
end

/- ## CorePalette -/
section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace CoreTheory.CorePalette
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Actual layers of one common colouring. The counting adapters follow Bradley's supplied PaletteCaps.lean. -/
def layer (c : Coloring V r) (i : Fin r) : SimpleGraph V where
  Adj x y := x ≠ y ∧ c s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

lemma degree_layer (c : Coloring V r) (i : Fin r) (v : V) :
    (layer c i).degree v = degreeOn c i univ v := by
  -- REPAIR (toolchain drift, Lean 4.32.0/mathlib 81a5d257 -> pinned 4.33.1/mathlib 0df444a3):
  -- the original script was
  --   rw [← SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_eq_filter]
  --   unfold degreeOn; apply congrArg card; ext x; simp [layer,ne_comm]
  -- Under the pinned Mathlib the `attribute [local instance] Classical.propDecidable` above makes
  -- `DecidableRel (layer c i).Adj` resolve to `Classical.propDecidable`, and passing `layer` to
  -- `simp` unfolds the structure head while the `Fintype (neighborSet ..)` / `DecidablePred`
  -- instances stay folded. `Finset.mem_filter` and `SimpleGraph.mem_neighborFinset` then no longer
  -- match syntactically and `simp` leaves the goal untouched. Keeping `layer` folded and closing
  -- the membership iff by hand avoids the instance mismatch. Statement is unchanged.
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degreeOn
  apply congrArg card
  ext x
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨mem_univ _, Ne.symm h.1, h.2⟩, fun h => ⟨Ne.symm h.2.1, h.2.2⟩⟩

lemma card_edges_compl (G : SimpleGraph V) :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    apply disjoint_left.mpr
    intro e h h'
    rw [SimpleGraph.mem_edgeFinset] at h h'
    induction e using Sym2.ind with
    | _ u v => exact h'.2 h
  have hu : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    simp only [mem_union,SimpleGraph.mem_edgeFinset]
    induction e using Sym2.ind with
    | _ u v =>
      change G.Adj u v ∨ (u ≠ v ∧ ¬G.Adj u v) ↔ u ≠ v
      constructor
      · rintro (h | h)
        · exact G.ne_of_adj h
        · exact h.1
      · intro h
        by_cases ha : G.Adj u v
        · exact Or.inl ha
        · exact Or.inr ⟨h,ha⟩
  have he := card_union_of_disjoint hd
  rw [hu,SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at he
  exact he.symm

lemma complement_cliqueFree (c : Coloring V r) (H : Caps c) (i : Fin r) :
    (layer c i)ᶜ.CliqueFree (r+1) := by
  intro S hS
  have hi : Independent c i S := by
    intro x hx y hy hxy hc
    exact (hS.isClique hx hy hxy).2 ⟨hxy,hc⟩
  have hh := H i S hi
  rw [hS.card_eq] at hh
  omega

lemma sum_edges (c : Coloring V r) :
    (∑ i, (layer c i).edgeFinset.card) = (Fintype.card V).choose 2 := by
  have he : ∀ i, (layer c i).edgeFinset =
      (⊤ : SimpleGraph V).edgeFinset.filter (fun e => c e = i) := by
    intro i
    ext e
    simp only [mem_filter,SimpleGraph.mem_edgeFinset]
    induction e using Sym2.ind with
    | _ x y => rfl
  simp_rw [he]
  rw [← card_eq_sum_card_fiberwise (s := (⊤ : SimpleGraph V).edgeFinset)
    (t := univ) (f := c) (by intro e he; simp)]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

lemma choose_two_identity (q : ℕ) : (2*q+1).choose 2 = q*(2*q+1) := by
  rw [Nat.choose_two_right]
  have hs : 2*q+1-1 = 2*q := by omega
  rw [hs]
  have he : (2*q+1)*(2*q) = 2*(q*(2*q+1)) := by ring
  rw [he,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma turan_expression (q : ℕ) (hq : 2 ≤ q) :
    (((2*q+1)^2 - ((2*q+1)%q)^2)*(q-1)/(2*q) + ((2*q+1)%q).choose 2) =
      2*(q+1)*(q-1) := by
  have hm : (2*q+1)%q = 1 := by
    have h1 : 1 < q := by omega
    simp [Nat.add_mod,Nat.mod_eq_of_lt h1]
  rw [hm]
  norm_num only [Nat.one_pow,Nat.choose_eq_zero_of_lt (by decide : 1 < 2),Nat.add_zero]
  have hs : (2*q+1)^2-1 = 4*q*(q+1) := by
    have hp : 1 ≤ (2*q+1)^2 := by nlinarith
    have hh := Nat.sub_add_cancel hp
    nlinarith
  rw [hs]
  have he : 4*q*(q+1)*(q-1) = (2*q)*(2*(q+1)*(q-1)) := by ring
  rw [he,Nat.mul_div_cancel_left _ (by omega : 0 < 2*q)]

lemma edge_lower_two_level (c : Coloring V r) (hr : 3 ≤ r) (H : Caps c)
    (hn : Fintype.card V = 2*r+1) (i : Fin r) : r+2 ≤ (layer c i).edgeFinset.card := by
  have hu := (complement_cliqueFree c H i).card_edgeFinset_le
  have he := card_edges_compl (layer c i)
  dsimp only at hu
  rw [hn,turan_expression r (by omega)] at hu
  rw [hn,choose_two_identity] at he
  have hs : r-1+1 = r := by omega
  nlinarith
end CoreTheory.CorePalette

namespace CoreTheory.CorePalette
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

/-- A two-level core cannot occur in a common colouring, for symbolic r >= 3. -/
theorem no_two_level (c : Coloring V r) (hr : 3 ≤ r) (H : Caps c)
    (hn : Fintype.card V = 2*r+1) (i : Fin r)
    (hd : ∀ v, r ≤ degreeOn c i univ v)
    (hh : r+1 ≤ (high c i univ).card) : False := by
  have hsum : r * Fintype.card V + (high c i univ).card ≤
      ∑ v, degreeOn c i univ v := by
    have hp : ∀ v : V, r + (if r < degreeOn c i univ v then 1 else 0) ≤
        degreeOn c i univ v := by
      intro v
      have hv := hd v
      split_ifs <;> omega
    have h := sum_le_sum (s := (univ : Finset V)) (fun v _ => hp v)
    have hc : (∑ v : V, if r < degreeOn c i univ v then 1 else 0) =
        (high c i univ).card := by
      simp only [high,card_eq_sum_ones,sum_filter]
    simpa [sum_add_distrib,hc,Nat.mul_comm] using h
  have he : (∑ v, degreeOn c i univ v) = 2*(layer c i).edgeFinset.card := by
    simp_rw [← degree_layer]
    exact SimpleGraph.sum_degrees_eq_twice_card_edges _
  rw [he,hn] at hsum
  have hothers := sum_le_sum (s := (univ : Finset (Fin r)).erase i)
    (fun j _ => edge_lower_two_level c hr H hn j)
  have hall := sum_erase_add (s := (univ : Finset (Fin r)))
    (fun j => (layer c j).edgeFinset.card) (mem_univ i)
  rw [sum_edges,hn,choose_two_identity] at hall
  simp only [sum_const,card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin,
    smul_eq_mul] at hothers
  have hs : r-1+1=r := by omega
  nlinarith
end CoreTheory.CorePalette
end
end

/- ## BoundaryResilience -/
section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace CoreTheory.BoundaryResilience
open CoreTheory.MinimalCore CoreTheory.CoreIncidence CoreTheory.CorePalette
variable {V : Type} [DecidableEq V] {r : ℕ} {i : Fin r}

/-- Literal restriction of the original common colouring to an induced vertex set. -/
def restrict (c : Coloring V r) (W : Finset V) : Coloring W r :=
  fun e => c (Sym2.map Subtype.val e)

def inclusion (W : Finset V) : W ↪ V := Function.Embedding.subtype (fun v => v ∈ W)

lemma restriction_independent (c : Coloring V r) (W : Finset V) (i : Fin r) (A : Finset W) :
    Independent (restrict c W) i A ↔ Independent c i (A.map (inclusion W)) := by
  constructor
  · intro h x hx y hy hxy
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
    exact h u hu v hv (by intro he; exact hxy (congrArg Subtype.val he))
  · intro h x hx y hy hxy
    apply h x.val (mem_map.mpr ⟨x,hx,rfl⟩) y.val (mem_map.mpr ⟨y,hy,rfl⟩)
    intro he
    exact hxy (Subtype.ext he)

lemma restriction_caps (c : Coloring V r) (H : Caps c) (W : Finset V) :
    Caps (restrict c W) := by
  intro i A hi
  have h := H i (A.map (inclusion W)) ((restriction_independent c W i A).mp hi)
  simpa using h

lemma filter_subtype_card (W : Finset V) (P : V → Prop) :
    ((univ : Finset W).filter (fun v => P v.val)).card = (W.filter P).card := by
  have he : ((univ : Finset W).filter (fun v => P v.val)).map (inclusion W) = W.filter P := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      exact mem_filter.mpr ⟨v.property,(mem_filter.mp hv).2⟩
    · intro hx
      have hm := mem_filter.mp hx
      exact mem_map.mpr ⟨⟨x,hm.1⟩,mem_filter.mpr ⟨mem_univ _,hm.2⟩,rfl⟩
  rw [← he,card_map]

lemma restriction_degree (c : Coloring V r) (W : Finset V) (i : Fin r) (v : W) :
    degreeOn (restrict c W) i univ v = degreeOn c i W v.val := by
  unfold degreeOn
  have he : (univ : Finset W).filter (fun y => y ≠ v ∧ restrict c W s(v,y) = i) =
      univ.filter (fun y => y.val ≠ v.val ∧ c s(v.val,y.val) = i) := by
    ext y
    simp only [mem_filter,mem_univ,true_and]
    change (y ≠ v ∧ c s(v.val,y.val) = i) ↔ (y.val ≠ v.val ∧ c s(v.val,y.val) = i)
    constructor
    · rintro ⟨hne,hc⟩
      exact ⟨fun he => hne (Subtype.ext he),hc⟩
    · rintro ⟨hne,hc⟩
      exact ⟨fun he => hne (congrArg Subtype.val he),hc⟩
  rw [he]
  convert filter_subtype_card W (fun y => y ≠ v.val ∧ c s(v.val,y) = i) using 1 <;> congr 1 <;> ext x <;> simp

lemma restriction_high (c : Coloring V r) (W : Finset V) (i : Fin r) :
    (high (restrict c W) i univ).card = (high c i W).card := by
  unfold high
  simp_rw [restriction_degree]
  convert filter_subtype_card W (fun v => r < degreeOn c i W v) using 1 <;> congr 1 <;> ext x <;> simp

/-- Symbolic exclusion of independence level two in an intrinsic common-colouring core. -/
theorem minimal_alpha_three (c : Coloring V r) (hr : 3 ≤ r) (i : Fin r)
    (H : Caps c) {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W < r) :
    3 ≤ alphaOn c i W := by
  have htwo := minimal_alpha_two c i H hW ha
  by_contra hn
  have he : alphaOn c i W = 2 := by omega
  have hc : Fintype.card W = 2*r+1 := by
    have hw := minimal_card c i hW
    rw [he] at hw
    simpa [Nat.mul_comm] using hw
  apply no_two_level (restrict c W) hr (restriction_caps c H W) hc i
  · intro v
    rw [restriction_degree]
    exact minimal_degree c i hW v.property
  · rw [restriction_high]
    exact high_count c i H hW ha

/-- Every selected colour of an actual three-colour boundary has no small blocker. -/
theorem no_small_blocker_three [Fintype V] (c : Coloring V 3) (H : Caps c)
    (hV : Fintype.card V = 3^2) (i : Fin 3) (T : Finset V) (ht : T.card < 3) :
    ¬ Hits c i T := by
  intro hhit
  obtain ⟨W,hWU,hW,hpos,ha,hrest⟩ := core_from_small_blocker c i H hV T ht hhit
  have h := minimal_alpha_three c (by decide) i H hW ha
  omega

/-- Exactly three independent vertices survive every deletion of at most two vertices. -/
theorem resilience_three [Fintype V] (c : Coloring V 3) (H : Caps c)
    (hV : Fintype.card V = 3^2) (i : Fin 3) (D : Finset V) (hd : D.card < 3) :
    ∃ A : Finset V, A ⊆ univ \ D ∧ A.card = 3 ∧ Independent c i A := by
  have hn : ¬ alphaOn c i (univ \ D) < 3 := by
    intro h
    exact no_small_blocker_three c H hV i D hd ((hits_iff_alpha_delete_lt c i D).mpr h)
  obtain ⟨S,hS,hI,hc⟩ := alpha_witness c i (univ \ D)
  obtain ⟨A,hAS,hA⟩ := exists_subset_card_eq (by omega : 3 ≤ S.card)
  exact ⟨A,hAS.trans hS,hA,independent_mono hAS hI⟩

/-- The finite-set universal resilience definition is met without strengthening its local caps. -/
theorem universal_resilience_three : CoreTheory.RegularityBridge.UniversalResilience 3 := by
  intro W _ _ c B hB hcaps i D hD
  let D' : Finset B := univ.filter (fun x => x.val ∈ D)
  have H : Caps (restrict c B) := by
    intro j S hS
    have hi := (restriction_independent c B j S).mp hS
    have hs : S.map (inclusion B) ⊆ B := by
      intro x hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      exact v.property
    have hh := hcaps j _ hs hi
    simpa using hh
  have hd : D'.card < 3 := by
    have he := filter_subtype_card B (fun v => v ∈ D)
    have hs : B.filter (fun v => v ∈ D) ⊆ D := by
      intro v hv
      exact (mem_filter.mp hv).2
    have hdcard : D'.card = (B.filter (fun v => v ∈ D)).card := by
      dsimp [D']
      convert he using 1 <;> congr 1 <;> ext x <;> simp
    rw [hdcard]
    exact (card_le_card hs).trans_lt hD
  obtain ⟨A,hA,hAc,hAI⟩ := resilience_three (restrict c B) H (by simpa using hB) i D' hd
  refine ⟨A.map (inclusion B),?_,by simpa using hAc,(restriction_independent c B i A).mp hAI⟩
  intro x hx
  obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
  refine mem_sdiff.mpr ⟨v.property,?_⟩
  intro h
  exact (mem_sdiff.mp (hA hv)).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
end CoreTheory.BoundaryResilience

namespace CoreTheory.BoundaryResilience
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem strengthened_core (c : Coloring V r) (hr : 3 ≤ r) (i : Fin r)
    (H : Caps c) (hV : Fintype.card V = r^2) (T : Finset V)
    (ht : T.card < r) (hhit : Hits c i T) :
    ∃ W ⊆ univ \ T, Minimal c i W ∧ 3 ≤ alphaOn c i W ∧ alphaOn c i W < r ∧
      W.card = r*alphaOn c i W+1 ∧ r+1 ≤ (high c i W).card ∧
      ∀ A ⊆ W, Independent c i A → A.card = alphaOn c i W →
        r*A.card+2 ≤ ∑ v ∈ A, degreeOn c i W v := by
  obtain ⟨W,hWU,hW,hpos,ha,hcard,hrest⟩ := core_from_small_blocker c i H hV T ht hhit
  exact ⟨W,hWU,hW,minimal_alpha_three c hr i H hW ha,ha,hcard,
    high_count c i H hW ha,fun _ hs hi hc => maximum_degree_sum c i H hW ha hs hi hc⟩


/-- At r=3 even a single designated small class cannot have its required hitting property. -/
theorem no_small_partition_three (c : Coloring V 3)
    (hV : Fintype.card V = 3^2) (hc : ColourExtension.Admissible 3 c) (i0 : Fin 3) :
    ¬ ∃ T : Fin 3 → Finset V, CoreTheory.RootBridge.Partition T ∧
      CoreTheory.RootBridge.HitsAll c T ∧ (T i0).card < 3 := by
  rintro ⟨T,hp,hh,ht⟩
  apply no_small_blocker_three c (CoreTheory.CommonBlocker.caps_of_admissible c hc) hV i0 (T i0) ht
  intro A ha hi
  obtain ⟨v,hv,hvt⟩ := hh i0 A ha hi
  exact ⟨v,mem_inter.mpr ⟨hv,hvt⟩⟩

end CoreTheory.BoundaryResilience
end
end

/- ## RegularBranch -/
section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace CoreTheory.RegularBranch
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

lemma alpha_le_cap (c : Coloring V r) (H : Caps c) (i : Fin r) (W : Finset V) :
    alphaOn c i W ≤ r := by
  obtain ⟨A,hA,hI,hc⟩ := alpha_witness c i W
  rw [← hc]
  exact H i A hI

lemma degree_mono (c : Coloring V r) (i : Fin r) {U W : Finset V}
    (hUW : U ⊆ W) (v : V) : degreeOn c i U v ≤ degreeOn c i W v := by
  apply card_le_card
  intro x hx
  exact mem_filter.mpr ⟨hUW (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩

lemma subcritical_ratio (c : Coloring V r) (H : Caps c) (i : Fin r)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r) (U : Finset V)
    (ha : alphaOn c i U < r) : U.card ≤ r * alphaOn c i U := by
  by_contra hn
  obtain ⟨W,hWU,hW⟩ := minimal_exists c i U (by omega)
  have hwa := (alpha_mono c i hWU).trans_lt ha
  have hh := high_count c i H hW hwa
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < (high c i W).card)
  have hl := (mem_filter.mp hx).2
  have hu := (degree_mono c i (subset_univ W) x).trans (hdeg x)
  omega

lemma large_subset_independent (c : Coloring V r) (H : Caps c) (i : Fin r)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r) (U : Finset V)
    (hU : r*(r-1) < U.card) :
    ∃ A ⊆ U, Independent c i A ∧ A.card = r := by
  have ha : alphaOn c i U = r := by
    apply le_antisymm (alpha_le_cap c H i U)
    by_contra hn
    have hlt : alphaOn c i U < r := by omega
    have hbound := subcritical_ratio c H i hdeg U hlt
    have hm := Nat.mul_le_mul_left r (by omega : alphaOn c i U ≤ r-1)
    omega
  obtain ⟨A,hA,hI,hc⟩ := alpha_witness c i U
  exact ⟨A,hA,hI,hc.trans ha⟩

lemma private_capacity (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) (hA : A.card = alphaOn c i W) :
    2*W.card ≤ (∑ v ∈ A, degreeOn c i W v) + A.card +
      ∑ v ∈ A, (region c i W A {v}).card := by
  let P := A.biUnion (fun v => region c i W A {v})
  have hcover : W ⊆ multiple c i W A ∪ P := by
    intro x hx
    by_cases hm : 2 ≤ (support c i A x).card
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,hm⟩)
    · have hn := card_pos.mpr (support_nonempty c i hAW hI hA hx)
      have hc : (support c i A x).card = 1 := by omega
      obtain ⟨v,hv⟩ := card_eq_one.mp hc
      have hvA : v ∈ A := (mem_filter.mp (by rw [hv]; simp : v ∈ support c i A x)).1
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨v,hvA,mem_filter.mpr ⟨hx,?_⟩⟩
      rw [hv]
  have hcov : W.card ≤ (multiple c i W A).card + ∑ v ∈ A, (region c i W A {v}).card := by
    exact (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
  have hpoint : ∀ x ∈ W, 1 + (if 2 ≤ (support c i A x).card then 1 else 0) ≤
      (support c i A x).card := by
    intro x hx
    have hp := card_pos.mpr (support_nonempty c i hAW hI hA hx)
    split_ifs <;> omega
  have hsum := sum_le_sum hpoint
  have hc : (∑ x ∈ W, if 2 ≤ (support c i A x).card then 1 else 0) =
      (multiple c i W A).card := by simp only [multiple,card_eq_sum_ones,sum_filter]
  simp only [sum_add_distrib,sum_const,smul_eq_mul,Nat.mul_one] at hsum
  rw [hc,support_sum_identity c i hAW] at hsum
  omega

lemma degree_sum_upper (c : Coloring V r) (i : Fin r)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r) (A : Finset V) :
    (∑ v ∈ A, degreeOn c i univ v) ≤ r*A.card := by
  calc
    _ ≤ ∑ _v ∈ A, r := sum_le_sum (fun v _ => hdeg v)
    _ = r*A.card := by simp [Nat.mul_comm]

lemma full_clique_exists (c : Coloring V r) (H : Caps c) (i : Fin r)
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r) :
    ∃ C : Finset V, C.card = r ∧ Clique c i C := by
  have hU : r*(r-1) < (univ : Finset V).card := by
    rw [card_univ,hV]
    have hm := Nat.mul_le_mul_left r (Nat.sub_le r 1)
    nlinarith
  obtain ⟨A,hAW,hI,hAc⟩ := large_subset_independent c H i hdeg univ hU
  have hmax : A.card = alphaOn c i univ := by
    apply le_antisymm (card_le_alpha hAW hI)
    rw [hAc]
    exact alpha_le_cap c H i univ
  by_contra hn
  have hcell : ∀ v ∈ A, (region c i univ A {v}).card + 1 ≤ r := by
    intro v hv
    by_contra hb
    obtain ⟨C,hCR,hCc⟩ := exists_subset_card_eq
      (by omega : r ≤ (region c i univ A {v}).card)
    have hcl := singleton_region_clique c i hAW hI hmax hv
    apply hn
    refine ⟨C,hCc,?_⟩
    intro x hx y hy hxy
    exact hcl x (hCR hx) y (hCR hy) hxy
  have hcells : (∑ v ∈ A, (region c i univ A {v}).card) + A.card ≤ r*A.card := by
    have hh := sum_le_sum hcell
    simpa [sum_add_distrib,Nat.mul_comm] using hh
  have hcap := private_capacity c i hAW hI hmax
  have hupper := degree_sum_upper c i hdeg A
  simp only [card_univ,hV,hAc] at hcap hupper hcells
  nlinarith
end CoreTheory.RegularBranch

namespace CoreTheory.RegularBranch
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

lemma anchor_mem_region (c : Coloring V r) (i : Fin r) {W A : Finset V}
    (hAW : A ⊆ W) (hI : Independent c i A) {v : V} (hv : v ∈ A) :
    v ∈ region c i W A {v} := by
  apply mem_filter.mpr
  refine ⟨hAW hv,?_⟩
  intro y hy
  have hm := mem_filter.mp hy
  apply mem_singleton.mpr
  rcases hm.2 with he | he
  · exact he
  · by_contra hyv
    exact hI v hv y hm.1 (Ne.symm hyv) he

lemma clique_outside_location (c : Coloring V r) (i : Fin r)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r)
    {C : Finset V} (hC : C.card = r) (hc : Clique c i C)
    {x y : V} (hx : x ∈ C) (hy : y ∉ C) (hxy : c s(x,y) = i) :
    ∀ z, z ≠ x → c s(x,z) = i → z ∈ C ∨ z = y := by
  let N := (univ : Finset V).filter (fun z => z ≠ x ∧ c s(x,z) = i)
  let S := insert y (C.erase x)
  have hyn : y ∉ C.erase x := by intro h; exact hy (mem_erase.mp h).2
  have hSc : S.card = r := by
    dsimp [S]
    rw [card_insert_of_notMem hyn,card_erase_of_mem hx,hC]
    have hp : 0 < r := by rw [← hC]; exact card_pos.mpr ⟨x,hx⟩
    omega
  have hsub : S ⊆ N := by
    intro z hz
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hz with rfl | hz
    · exact ⟨fun he => hy (he ▸ hx),hxy⟩
    · exact ⟨(mem_erase.mp hz).1,hc x hx z (mem_erase.mp hz).2 (Ne.symm (mem_erase.mp hz).1)⟩
  have he : S = N := eq_of_subset_of_card_le hsub (by
    rw [hSc]
    exact hdeg x)
  intro z hzx hz
  have hzm : z ∈ S := by
    rw [he]
    exact mem_filter.mpr ⟨mem_univ _,hzx,hz⟩
  rcases mem_insert.mp hzm with hzy | hzC
  · exact Or.inr hzy
  · exact Or.inl (mem_erase.mp hzC).2

lemma clique_dominates_independent (c : Coloring V r) (H : Caps c) (i : Fin r)
    {C A : Finset V} (hC : C.card = r) (hc : Clique c i C)
    (hA : A.card = r) (hI : Independent c i A) (hdis : Disjoint A C) :
    ∀ v ∈ A, ∃ x ∈ C, c s(v,x) = i := by
  have hit : ∀ x : C, ∃ y : A, c s(x.val,y.val) = i := by
    intro x
    have hxA : x.val ∉ A := fun h => disjoint_left.mp hdis h x.property
    by_contra hn
    have hfree : ∀ y ∈ A, c s(x.val,y) ≠ i := by
      intro y hy he
      exact hn ⟨⟨y,hy⟩,he⟩
    have hb := H i (insert x.val A) (independent_insert hI hfree)
    rw [card_insert_of_notMem hxA,hA] at hb
    omega
  choose f hf using hit
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hout : (f x).val ∉ C := fun h => disjoint_left.mp hdis (f x).property h
    apply outside_at_most_one c i H C hC hc (f x).val hout
      x.val x.property y.val y.property
    · rw [Sym2.eq_swap]
      exact hf x
    · rw [Sym2.eq_swap,hxy]
      exact hf y
  let F : Finset A := (univ : Finset C).image f
  have hcard : F.card = (univ : Finset A).card := by
    dsimp [F]
    rw [card_image_of_injective _ hfinj]
    simp [hC,hA]
  have hF : F = univ := eq_of_subset_of_card_le (subset_univ _) hcard.ge
  intro v hv
  have hmem : (⟨v,hv⟩ : A) ∈ F := by rw [hF]; exact mem_univ _
  obtain ⟨x,hx,he⟩ := mem_image.mp hmem
  have hev : (f x).val = v := congrArg Subtype.val he
  exact ⟨x.val,x.property,by rw [Sym2.eq_swap]; simpa [hev] using hf x⟩
end CoreTheory.RegularBranch

namespace CoreTheory.RegularBranch
open CoreTheory.MinimalCore CoreTheory.CoreIncidence
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

lemma private_cell_two (c : Coloring V r) (H : Caps c) (i : Fin r)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r)
    {C A : Finset V} (hC : C.card = r) (hc : Clique c i C)
    (hA : A.card = r) (hI : Independent c i A) (hdis : Disjoint A C)
    (hmax : A.card = alphaOn c i univ) {v : V} (hv : v ∈ A) :
    (region c i univ A {v}).card ≤ 2 := by
  obtain ⟨x,hx,hvx⟩ := clique_dominates_independent c H i hC hc hA hI hdis v hv
  have hvout : v ∉ C := fun h => disjoint_left.mp hdis hv h
  have hvxne : v ≠ x := fun he => hvout (he.symm ▸ hx)
  have hxv : c s(x,v) = i := by rw [Sym2.eq_swap]; exact hvx
  have hloc := clique_outside_location c i hdeg hC hc hx hvout hxv
  have hxreg : x ∈ region c i univ A {v} := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    intro y hy
    have hm := mem_filter.mp hy
    have hyout : y ∉ C := fun h => disjoint_left.mp hdis hm.1 h
    have hyx : y ≠ x := fun he => hyout (he.symm ▸ hx)
    apply mem_singleton.mpr
    rcases hm.2 with he | he
    · exact (hyx he).elim
    · exact (hloc y hyx he).resolve_left hyout
  have hvreg := anchor_mem_region c i (subset_univ A) hI hv
  have hcl := singleton_region_clique c i (subset_univ A) hI hmax hv
  have hsub : region c i univ A {v} ⊆ {v,x} := by
    intro z hz
    by_cases hzv : z = v
    · simp [hzv]
    by_cases hzx : z = x
    · simp [hzx]
    have hxz := hcl x hxreg z hz (Ne.symm hzx)
    have hzC : z ∈ C := (hloc z hzx hxz).resolve_right hzv
    have hvz := hcl v hvreg z hz (Ne.symm hzv)
    have he := outside_at_most_one c i H C hC hc v hvout x hx z hzC hvx hvz
    exact (hzx he.symm).elim
  have hb := card_le_card hsub
  simpa [hvxne] using hb

/-- The common-colouring regular branch, with no Brooks interface parameter. -/
theorem no_bounded_degree_layer (c : Coloring V r) (H : Caps c) (i : Fin r)
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1)
    (hdeg : ∀ v, degreeOn c i univ v ≤ r) : False := by
  obtain ⟨C,hC,hcl⟩ := full_clique_exists c H i hr hV hdeg
  have hn := card_sdiff_add_card_inter (univ : Finset V) C
  simp only [univ_inter,card_univ,hV,hC] at hn
  have hpred : r-1+1 = r := by omega
  have hU : r*(r-1) < (univ \ C).card := by nlinarith
  obtain ⟨A,hAU,hI,hAc⟩ := large_subset_independent c H i hdeg (univ \ C) hU
  have hAW : A ⊆ univ := subset_univ A
  have hdis : Disjoint A C := disjoint_left.mpr
    (fun _ hx hy => (mem_sdiff.mp (hAU hx)).2 hy)
  have hmax : A.card = alphaOn c i univ := by
    apply le_antisymm (card_le_alpha hAW hI)
    rw [hAc]
    exact alpha_le_cap c H i univ
  have hcells : (∑ v ∈ A, (region c i univ A {v}).card) ≤ 2*A.card := by
    calc
      _ ≤ ∑ _v ∈ A, 2 := sum_le_sum
        (fun v hv => private_cell_two c H i hdeg hC hcl hAc hI hdis hmax hv)
      _ = 2*A.card := by simp [Nat.mul_comm]
  have hcap := private_capacity c i hAW hI hmax
  have hupper := degree_sum_upper c i hdeg A
  simp only [card_univ,hV,hAc] at hcap hupper hcells
  have hh := Nat.mul_le_mul_right r hr
  nlinarith
end CoreTheory.RegularBranch

namespace CoreTheory.RegularBranch
open CoreTheory.MinimalCore CoreTheory.RegularityBridge
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem each_layer_has_high_degree (c : Coloring V r) (H : Caps c)
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1) (i : Fin r) :
    ∃ v : V, r < degreeOn c i univ v := by
  by_contra hn
  apply no_bounded_degree_layer c H i hr hV
  intro v
  exact Nat.le_of_not_gt (fun h => hn ⟨v,h⟩)

theorem small_root_exists (c : Coloring V r) (H : Caps c)
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1) :
    ∃ v : V, ∃ i : Fin r, degreeOn c i univ v < r := by
  rcases small_root_or_regular c hV with hs | hreg
  · exact hs
  · let i : Fin r := ⟨0,by omega⟩
    exact (no_bounded_degree_layer c H i hr hV (fun v => (hreg v i).le)).elim

theorem resilience_excludes_full (c : Coloring V r) (H : Caps c)
    (hr : 3 ≤ r) (hV : Fintype.card V = r^2+1)
    (hres : UniversalResilience r) : False := by
  obtain ⟨v,i,hi⟩ := small_root_exists c H hr hV
  have he := resilience_forces_regularity hres c hV H v i
  omega

/-- The literal target follows from resilience with no unproved graph-theory interface. -/
theorem literal_from_resilience (hr : 3 ≤ r) (hres : UniversalResilience r)
    (c : Coloring V r) (hV : Fintype.card V = r^2+1) :
    ∃ (S : Finset V) (k : Fin r), S.card = r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  by_contra hn
  have H : Caps c := by
    intro i A hI
    by_contra hlarge
    obtain ⟨S,hSA,hSc⟩ := exists_subset_card_eq (by omega : r+1 ≤ A.card)
    exact hn ⟨S,i,hSc,independent_mono hSA hI⟩
  exact resilience_excludes_full c H hr hV hres

end CoreTheory.RegularBranch
end
end

/- ## AlphaThreeCore -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.AlphaThree
open CoreTheory.MinimalCore Surplus.SparseGraphBounds
variable {V : Type} [DecidableEq V] {r : ℕ}

lemma colour_degree_sum (c : Coloring V r) (W : Finset V) {x : V} (hx : x ∈ W) :
    (∑ j : Fin r, degreeOn c j W x) = W.card-1 := by
  have hh := card_eq_sum_card_fiberwise (s:=W.erase x) (t:=(univ : Finset (Fin r)))
    (f:=fun y => c s(x,y)) (fun _ _ => mem_univ _)
  have hf : ∀ j, (W.erase x).filter (fun y => c s(x,y)=j) =
      W.filter (fun y => y ≠ x ∧ c s(x,y)=j) := by
    intro j
    ext y
    simp only [mem_filter,mem_erase]
    tauto
  simp_rw [hf] at hh
  rw [card_erase_of_mem hx] at hh
  exact hh.symm

/-- Unconditional alpha-three core exclusion: no sparse-bound premise remains. -/
theorem no_alpha_three_core (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hr : 4 ≤ r) {W : Finset V} (hW : Minimal c i W)
    (ha : alphaOn c i W = 3) : False := by
  have hn := minimal_card c i hW
  rw [ha] at hn
  have hi := Surplus.core_degree_sum c i H hW (by omega)
  have other : ∀ j : Fin r, j ≠ i → 6*r+10 ≤ ds c j W := by
    intro j hji
    apply sparse_three_lower c j r (by omega) W (by omega)
    · intro A _ hI; exact H j A hI
    · intro A hA hC
      have hI : Independent c i A := by
        intro u hu v hv huv
        rw [hC u hu v hv huv]
        exact hji
      have h := card_le_alpha hA hI
      omega
  have ho := sum_le_sum (s:=(univ : Finset (Fin r)).erase i)
    (fun j hj => other j (mem_erase.mp hj).1)
  simp only [sum_const,card_erase_of_mem (mem_univ i),card_univ,
    Fintype.card_fin,smul_eq_mul] at ho
  have ht : (∑ j : Fin r, ds c j W) = W.card*(W.card-1) := by
    simp only [ds]
    rw [sum_comm]
    calc
      _ = ∑ _x ∈ W, (W.card-1) := sum_congr rfl (fun x hx => colour_degree_sum c W hx)
      _ = _ := by simp
  have he := sum_erase_add (s:=(univ : Finset (Fin r))) (fun j => ds c j W) (mem_univ i)
  rw [ht,hn] at he
  rw [hn] at hi
  change r*(r*3+1)+r+2 ≤ ds c i W at hi
  have hp : r-1+1=r := by omega
  have hm : r*3+1-1=r*3 := by omega
  rw [hm] at he
  nlinarith

/-- F(3,r,...,r) <= 3r, for every r >= 4, in global-cap form. -/
theorem alpha_three_card_le (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hr : 4 ≤ r) (W : Finset V) (ha : alphaOn c i W ≤ 3) : W.card ≤ 3*r := by
  by_contra hn
  have hm := Nat.mul_le_mul_left r ha
  have hviol : r*alphaOn c i W < W.card := by omega
  obtain ⟨U,hUW,hU⟩ := minimal_exists c i W hviol
  have hUa := (alpha_mono c i hUW).trans ha
  have hsmall : alphaOn c i U < r := by omega
  have htwo := minimal_alpha_two c i H hU hsmall
  have hcard := minimal_card c i hU
  by_cases hthree : alphaOn c i U = 3
  · exact no_alpha_three_core c i H hr hU hthree
  have heq : alphaOn c i U = 2 := by omega
  have hbound := CoreTheory.AlphaTwoCore.alpha_two_card_le c i U (by omega)
    (fun j A _ hI => H j A hI)
    (fun A hA hI => by have hh := card_le_alpha hA hI; omega)
  rw [heq] at hcard
  omega

end Surplus.AlphaThree
end
end

/- ## SparseCore -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.PrivateStructure.Full
open CoreTheory.MinimalCore Surplus.SparseGraphBounds
open Surplus.PrivateStructure.Extension
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

lemma total_degree (c : Coloring V r) :
    (∑ i : Fin r, ds c i univ) = Fintype.card V*(Fintype.card V-1) := by
  simp only [ds]
  rw [sum_comm]
  simp_rw [CoreTheory.RegularityBridge.sum_root_degrees c]
  simp

/-- Choose one actual sparse layer by averaging, not an unrelated sparse graph. -/
theorem sparse_colour_exists (c : Coloring V r) (hr : 0<r)
    (hV : Fintype.card V=r^2+1) : ∃ i : Fin r, ds c i univ ≤ r*Fintype.card V := by
  by_contra hn
  push Not at hn
  have hs := sum_le_sum (s:=(univ:Finset (Fin r))) (fun i _ => Nat.succ_le_of_lt (hn i))
  rw [total_degree c] at hs
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,hV] at hs
  have he : r^2+1-1=r^2 := by omega
  rw [he] at hs
  nlinarith

/-- A sparse full layer has a strictly proper minimal core. -/
theorem proper_core_exists (c : Coloring V r) (i : Fin r) (H : Caps c)
    (hr : 3≤r) (hV : Fintype.card V=r^2+1)
    (hsparse : ds c i univ ≤ r*Fintype.card V) :
    ∃ W : Finset V, Minimal c i W ∧ alphaOn c i W<r := by
  obtain ⟨B,hB,hBI,hBc⟩ := alpha_witness c i (univ:Finset V)
  have hb := H i B hBI
  have hα : alphaOn c i univ ≤ r := by omega
  have hviol : r*alphaOn c i univ < (univ:Finset V).card := by
    have hm := Nat.mul_le_mul_left r hα
    simp only [card_univ,hV]
    nlinarith
  obtain ⟨W,hWu,hW⟩ := minimal_exists c i univ hviol
  have haW := (alpha_mono c i hWu).trans hα
  refine ⟨W,hW,?_⟩
  by_contra hn
  have heq : alphaOn c i W=r := by omega
  have hc := minimal_card c i hW
  rw [heq] at hc
  have hcard : W.card=(univ:Finset V).card := by simp only [card_univ,hV]; nlinarith
  have hEq : W=(univ:Finset V) := eq_of_subset_of_card_le hWu (le_of_eq hcard.symm)
  rw [hEq] at hW
  obtain ⟨v,hv⟩ := CoreTheory.RegularBranch.each_layer_has_high_degree c H hr hV i
  have hlow : ∀ u ∈ (univ:Finset V), r ≤ degreeOn c i univ u :=
    fun u hu => minimal_degree c i hW hu
  have hsum := sum_lt_sum hlow ⟨v,mem_univ v,hv⟩
  simp only [sum_const,card_univ,smul_eq_mul] at hsum
  change Fintype.card V*r < ds c i univ at hsum
  nlinarith

/-- Every counterexample has a common-colouring core at least TWO levels below r. -/
theorem sparse_core_reduction (c : Coloring V r) (H : Caps c)
    (hr : 4≤r) (hV : Fintype.card V=r^2+1) :
    ∃ (i : Fin r) (W : Finset V), Minimal c i W ∧
      4 ≤ alphaOn c i W ∧ alphaOn c i W+2 ≤ r ∧
      ds c i univ ≤ r*Fintype.card V ∧
      2*r ≤ (∑ v ∈ W, surplus c i W v)+2 ∧
      (∑ v ∈ W, surplus c i W v) ≤ r*(r-alphaOn c i W) := by
  obtain ⟨i,hs⟩ := sparse_colour_exists c (by omega) hV
  obtain ⟨W,hW,ha⟩ := proper_core_exists c i H (by omega) hV hs
  have h2 := minimal_alpha_two c i H hW ha
  have hnot2 : alphaOn c i W ≠ 2 := by
    intro he
    have hb := CoreTheory.AlphaTwoCore.alpha_two_card_le c i W (by omega)
      (fun j B _ hI => H j B hI)
      (fun B hB hI => (card_le_alpha hB hI).trans (by omega))
    have hc := minimal_card c i hW
    rw [he] at hc
    omega
  have hnot3 : alphaOn c i W ≠ 3 := by
    intro he
    exact Surplus.AlphaThree.no_alpha_three_core c i H hr hW he
  exact ⟨i,W,hW,by omega,sparse_core_parameter c i H (by omega) hV hs hW ha,
    hs,surplus_twice_parameter c i H (by omega) hW ha,sparse_core_capacity c i H hV hs hW ha⟩

/-- Literal r=5 target, now without a sparse-bound, resilience, or Brooks premise. -/
theorem five_colour_case (c : Sym2 V → Fin 5) (hV : Fintype.card V=5^2+1) :
    ∃ (S : Finset V) (k : Fin 5), S.card=6 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  by_contra hn
  have H : Caps c := by
    intro i B hI
    by_contra hb
    obtain ⟨S,hSB,hSc⟩ := exists_subset_card_eq (by omega : 6 ≤ B.card)
    exact hn ⟨S,i,hSc,independent_mono hSB hI⟩
  obtain ⟨i,W,hW,h4,hupper,_⟩ := sparse_core_reduction c H (by omega) hV
  omega
end Surplus.PrivateStructure.Full
end
end

/- ## WitnessConstruction -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
section
open Finset
attribute [local instance] Classical.propDecidable
namespace Surplus.PrivateStructure.Full
open CoreTheory.MinimalCore Surplus.SparseGraphBounds
open Surplus.PrivateStructure.Extension
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

/-- Uniform witness theorem on the excess-surplus branch. Caps is NOT a premise:
a colouring exceeding the certified extension capacity supplies a missing-colour set. -/
theorem missing_colour_of_excess (c : Coloring V r) (i : Fin r)
    (hV : Fintype.card V=r^2+1) (hsparse : ds c i univ ≤ r*Fintype.card V)
    {W : Finset V} (hW : Minimal c i W) (ha : alphaOn c i W<r)
    (hexcess : r*(r-alphaOn c i W) < ∑ v ∈ W, surplus c i W v) :
    ∃ (S : Finset V) (k : Fin r), S.card=r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u,v) ≠ k := by
  by_contra hn
  have H : Caps c := by
    intro j B hI
    by_contra hb
    obtain ⟨S,hSB,hSc⟩ := exists_subset_card_eq (by omega : r+1 ≤ B.card)
    exact hn ⟨S,j,hSc,independent_mono hSB hI⟩
  exact (not_lt_of_ge (sparse_core_capacity c i H hV hsparse hW ha)) hexcess
end Surplus.PrivateStructure.Full
end
end


section PublicInterface
open Finset CoreTheory.MinimalCore Surplus.SparseGraphBounds

/-- A genuine sparse layer and its minimal core, with the order, rank, and
surplus bounds simultaneously recorded. -/
theorem sparse_core_reduction {V : Type} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 4 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Sym2 V → Fin r) (hc : Caps c) :
    ∃ (i : Fin r) (W : Finset V), Minimal c i W ∧
      W.card = r * alphaOn c i W + 1 ∧
      4 ≤ alphaOn c i W ∧ alphaOn c i W + 2 ≤ r ∧
      ds c i univ ≤ r * Fintype.card V ∧
      2 * r ≤ (∑ v ∈ W, Surplus.surplus c i W v) + 2 ∧
      (∑ v ∈ W, Surplus.surplus c i W v) ≤ r * (r - alphaOn c i W) := by
  obtain ⟨i, W, hW, h4, hu, hs, hlo, hhi⟩ :=
    Surplus.PrivateStructure.Full.sparse_core_reduction c hc hr hV
  exact ⟨i, W, hW, minimal_card c i hW, h4, hu, hs, hlo, hhi⟩

/-- The literal specialization of Erdős 617 at r = 5, with no additional
hypothesis on the colouring. -/
theorem five_colour_case {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 5 ^ 2 + 1) (coloring : Sym2 V → Fin 5) :
    ∃ (S : Finset V) (k : Fin 5), S.card = 5 + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  Surplus.PrivateStructure.Full.five_colour_case coloring hV

/-- A concrete use site: the five-colour target on its standard finite carrier. -/
example (coloring : Sym2 (Fin 26) → Fin 5) :
    ∃ (S : Finset (Fin 26)) (k : Fin 5), S.card = 6 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  five_colour_case (by decide) coloring

end PublicInterface
end Contribution.Erdos617SparseCore
end
