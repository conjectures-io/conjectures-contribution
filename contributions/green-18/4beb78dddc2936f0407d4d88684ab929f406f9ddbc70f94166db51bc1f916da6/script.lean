import FormalConjectures.GreensOpenProblems.«18»

/-!
# Green 18: Solymosi's BMZ-corner theorem, and the naive-corner theorem for abelian groups

Green 18 asks whether every `α`-dense `A ⊆ G × G` (`G` any finite group) has `≫_α |G|³` *naive
corners* `(x, y), (gx, y), (x, gy)` with `g ≠ 1`. The pinned file records Solymosi's theorem for
*BMZ corners* `(x, y), (xg, y), (x, gy)` as `green_18.bmz_corners`, stated but left unproved.
This file proves it (`bmz_corners_theorem`) from Mathlib's triangle removal lemma, following
[So13]: a
tripartite graph on `G ⊕ G ⊕ G` whose triangles are exactly the extended BMZ corners, whose
`|A|` trivial triangles are edge-disjoint. Since naive corners coincide with BMZ corners when `G`
is abelian, the target statement `green_18` holds for all finite abelian groups
(`naive_corners_of_comm`): this is the Ajtai–Szemerédi counting theorem, kernel-checked.
-/

open Finset SimpleGraph TripartiteFromTriangles Sum3
open Function hiding graph
open Fintype (card)

namespace Contribution.Green18Solymosi

universe u

variable {G : Type*} [Group G] {A : Finset (G × G)}

/-- Triangle indices: the trivial (`g = 1`) BMZ corners, encoded as `(x, y, x * y)`. -/
def triangleIndices (A : Finset (G × G)) : Finset (G × G × G) :=
  A.map ⟨fun p : G × G => (p.1, p.2, p.1 * p.2), by rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩; rfl⟩

@[simp] lemma mk_mem_triangleIndices {a b c : G} :
    (a, b, c) ∈ triangleIndices A ↔ (a, b) ∈ A ∧ c = a * b := by
  simp only [triangleIndices, Prod.ext_iff, mem_map, Prod.exists, eq_comm]
  refine ⟨?_, fun h ↦ ⟨_, _, h.1, rfl, rfl, h.2⟩⟩
  rintro ⟨_, _, h₁, rfl, rfl, h₂⟩
  exact ⟨h₁, h₂⟩

@[simp] lemma card_triangleIndices : #(triangleIndices A) = #A := card_map _

variable [Fintype G] [DecidableEq G]

/-- The trivial triangles are edge-disjoint (cancellation in `G`). -/
instance instExplicitDisjoint : ExplicitDisjoint (triangleIndices A) where
  inj₀ := by
    intro a b c a' h h'
    rw [mk_mem_triangleIndices] at h h'
    exact mul_right_cancel (h.2.symm.trans h'.2)
  inj₁ := by
    intro a b c b' h h'
    rw [mk_mem_triangleIndices] at h h'
    exact mul_left_cancel (h.2.symm.trans h'.2)
  inj₂ := by
    intro a b c c' h h'
    rw [mk_mem_triangleIndices] at h h'
    exact h.2.trans h'.2.symm

/-- `|A| ≥ ε|G|²` edge-disjoint triangles make the graph `ε/9`-far from triangle-free. -/
lemma farFromTriangleFree_graph {ε : ℝ} (hε : ε * card G ^ 2 ≤ #A) :
    (graph <| triangleIndices A).FarFromTriangleFree (ε / 9) := by
  refine TripartiteFromTriangles.farFromTriangleFree _ ?_
  rw [card_triangleIndices]
  have h9 : ((card G + card G + card G) ^ 2 : ℕ) = 9 * card G ^ 2 := by ring
  rw [h9]
  push_cast
  linarith

/-- Extended BMZ corners: `g = 1` allowed. -/
def extCorners (A : Finset (G × G)) : Finset (G × G × G) :=
  (univ : Finset (G × G × G)).filter
    fun p => (p.1, p.2.1) ∈ A ∧ (p.1 * p.2.2, p.2.1) ∈ A ∧ (p.1, p.2.2 * p.2.1) ∈ A

/-- **Every triangle is a corner.** Each triangle of the graph is the explicit triangle
`{in₀ x, in₁ y, in₂ (x g y)}` of an extended BMZ corner `(x, y, g)`. -/
lemma cliqueFinset_subset_image :
    (graph (triangleIndices A)).cliqueFinset 3 ⊆
      (extCorners A).image (fun p : G × G × G =>
        ({in₀ p.1, in₁ p.2.1, in₂ (p.1 * p.2.2 * p.2.1)} : Finset (G ⊕ G ⊕ G))) := by
  intro s hs
  rw [mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at hs
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hs
  obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := graph_triple hxy hxz hyz
  rw [Graph.in₀₁_iff] at hab
  rw [Graph.in₀₂_iff] at hac
  rw [Graph.in₁₂_iff] at hbc
  obtain ⟨c', hc'⟩ := hab
  obtain ⟨b', hb'⟩ := hac
  obtain ⟨a', ha'⟩ := hbc
  rw [mk_mem_triangleIndices] at hc' hb' ha'
  refine mem_image.mpr ⟨(a, b, a⁻¹ * c * b⁻¹), ?_, ?_⟩
  · rw [extCorners, mem_filter]
    refine ⟨mem_univ _, hc'.1, ?_, ?_⟩
    · have h : a * (a⁻¹ * c * b⁻¹) = a' := by rw [ha'.2]; group
      simp only
      rw [h]; exact ha'.1
    · have h : a⁻¹ * c * b⁻¹ * b = b' := by rw [hb'.2]; group
      simp only
      rw [h]; exact hb'.1
  · rw [← habc]
    simp only
    have h : a * (a⁻¹ * c * b⁻¹) * b = c := by group
    rw [h]

lemma card_cliqueFinset_le :
    #((graph (triangleIndices A)).cliqueFinset 3) ≤ #(extCorners A) :=
  (card_le_card cliqueFinset_subset_image).trans card_image_le

/-- Removing the `g = 1` corners costs at most `|G|²`. -/
lemma card_extCorners_le : #(extCorners A) ≤ Green18.numBmzCorners A + card G ^ 2 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := extCorners A) (p := fun p : G × G × G => p.2.2 = 1)
  have h1 : (extCorners A).filter (fun p : G × G × G => ¬ p.2.2 = 1) =
      (univ : Finset (G × G × G)).filter
        (fun ⟨x, y, g⟩ => g ≠ 1 ∧ (x, y) ∈ A ∧ (x * g, y) ∈ A ∧ (x, g * y) ∈ A) := by
    rw [extCorners, Finset.filter_filter]
    ext ⟨x, y, g⟩
    simp only [mem_filter, mem_univ, true_and, ne_eq]
    tauto
  have h2 : #((extCorners A).filter (fun p : G × G × G => p.2.2 = 1)) ≤ card G ^ 2 := by
    calc #((extCorners A).filter (fun p : G × G × G => p.2.2 = 1))
        ≤ #(univ : Finset (G × G)) := by
          refine Finset.card_le_card_of_injOn (fun p : G × G × G => (p.1, p.2.1))
            (fun _ _ => mem_univ _) ?_
          rintro ⟨x, y, g⟩ hx ⟨x', y', g'⟩ hx' hxy
          simp only [coe_filter, Set.mem_ofPred_eq] at hx hx'
          simp only [Prod.mk.injEq] at hxy
          rw [Prod.mk.injEq, Prod.mk.injEq]
          exact ⟨hxy.1, hxy.2, hx.2.trans hx'.2.symm⟩
      _ = card G ^ 2 := by rw [card_univ, Fintype.card_prod, sq]
  unfold Green18.numBmzCorners
  rw [← h1]
  omega

/-- **Solymosi's theorem** [So13]: `green_18.bmz_corners`, proved. Explicit constants:
`c = 27 δ / 2` and `m₀ = ⌈2 / (27 δ)⌉` with `δ = triangleRemovalBound (α / 9)`. -/
theorem bmz_corners_theorem : ∀ α > 0, ∃ c > 0, ∃ m₀ : ℕ,
    ∀ (G : Type u) [Group G] [Fintype G] [DecidableEq G] (A : Finset (G × G)),
    Fintype.card G ≥ m₀ →
    (A.card : ℝ) ≥ α * (Fintype.card G) ^ 2 →
    (Green18.numBmzCorners A : ℝ) ≥ c * (Fintype.card G) ^ 3 := by
  intro α hα
  have hδpos : 0 < triangleRemovalBound (α / 9) := triangleRemovalBound_pos (by positivity)
  set δ := triangleRemovalBound (α / 9) with hδ
  refine ⟨27 * δ / 2, by positivity, ⌈2 / (27 * δ)⌉₊, ?_⟩
  intro G _ _ _ A hn hA
  have hfar := @farFromTriangleFree_graph G _ A _ _ α (by linarith)
  have h1 := hfar.le_card_cliqueFinset
  have hcard : (card (G ⊕ G ⊕ G) : ℝ) = 3 * card G := by
    simp only [Fintype.card_sum]; push_cast; ring
  rw [hcard, ← hδ] at h1
  have h2 : (#((graph (triangleIndices A)).cliqueFinset 3) : ℝ) ≤
      Green18.numBmzCorners A + (card G : ℝ) ^ 2 := by
    have := (card_cliqueFinset_le (A := A)).trans (card_extCorners_le (A := A))
    exact_mod_cast this
  have hn' : (2 / (27 * δ) : ℝ) ≤ card G := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hpos : (0 : ℝ) < card G := by
    have : (0 : ℝ) < 2 / (27 * δ) := by positivity
    linarith
  have hn3 : (card G : ℝ) ^ 2 ≤ 27 * δ / 2 * (card G) ^ 3 := by
    have h4 : 1 ≤ 27 * δ / 2 * card G := by
      rw [div_le_iff₀ (by positivity)] at hn'
      linarith
    nlinarith [h4, hpos, sq_nonneg (card G : ℝ), mul_pos hpos hpos]
  have h3 : δ * (3 * (card G : ℝ)) ^ 3 = 27 * δ * (card G) ^ 3 := by ring
  rw [h3] at h1
  linarith [h1, h2, hn3]

/-- In an abelian group naive corners and BMZ corners coincide. -/
lemma numNaiveCorners_eq_numBmzCorners {H : Type*} [CommGroup H] [Fintype H] [DecidableEq H]
    (B : Finset (H × H)) : Green18.numNaiveCorners B = Green18.numBmzCorners B := by
  unfold Green18.numNaiveCorners Green18.numBmzCorners
  congr 1
  ext ⟨x, y, g⟩
  simp only [mem_filter, mem_univ, true_and]
  rw [mul_comm g x]

/-- **The target holds for all finite abelian groups** (Ajtai–Szemerédi, counting form): the
right-hand side of `green_18` with `Group` replaced by `CommGroup`. -/
theorem naive_corners_of_comm : ∀ α > 0, ∃ c > 0, ∃ m₀ : ℕ,
    ∀ (G : Type u) [CommGroup G] [Fintype G] [DecidableEq G] (A : Finset (G × G)),
    Fintype.card G ≥ m₀ →
    (A.card : ℝ) ≥ α * (Fintype.card G) ^ 2 →
    (Green18.numNaiveCorners A : ℝ) ≥ c * (Fintype.card G) ^ 3 := by
  intro α hα
  obtain ⟨c, hc, m₀, h⟩ := bmz_corners_theorem.{u} α hα
  refine ⟨c, hc, m₀, ?_⟩
  intro G _ _ _ A hn hA
  rw [numNaiveCorners_eq_numBmzCorners]
  exact h G A hn hA

end Contribution.Green18Solymosi
