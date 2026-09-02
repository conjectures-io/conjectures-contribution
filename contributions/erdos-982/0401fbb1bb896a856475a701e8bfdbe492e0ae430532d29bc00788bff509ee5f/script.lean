import Mathlib
import FormalConjectures.ErdosProblems.«982»

/-!
# Erdős Problem 982: the distance set at a vertex, and the reduction to ccw polygons

Target: `Erdos982.erdos_982` — if `p : Fin n → ℝ²` (`3 ≤ n`) is injective and
`EuclideanGeometry.IsConvexPolygon p`, then some vertex `i` satisfies
`{ d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2`.

## The obstacle

Two things block any attempt on this statement before the geometry even starts.

* The quantity to be bounded is the `Set.ncard` of a *set-builder set of reals*,
  `{ d : ℝ | ∃ j, j ≠ i ∧ d = dist (p i) (p j) }`. `Set.ncard` is `0` on infinite sets, so
  nothing can be said about it until the set has been identified with a `Finset`, and no
  counting tool in Mathlib (pigeonhole, fibrewise cardinality, double counting) accepts a set
  in this shape. Every known argument for this problem is a counting argument, so this
  conversion is on the critical path and must be redone at every vertex.
* `EuclideanGeometry.IsConvexPolygon p` is by definition a *disjunction*,
  `IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i ↦ p (-i)`, whereas every usable convexity
  fact (`IsCcwConvexPolygon.sign_oangle` and its companions) is stated for the
  counter-clockwise branch only. A solver who `rcases`es on it has to run the whole geometric
  argument twice, the second time through the index reversal `i ↦ -i`.

## What is proved here

`distFinset p i` is the `Finset` of distances from `p i` to the other vertices, and
`ncard_eq_card_distFinset` identifies its cardinality with the target's `Set.ncard`
(`coe_distFinset` gives the underlying equality of sets). `equidistFinset p i d` is the fibre:
the vertices `j ≠ i` with `dist (p i) (p j) = d`, i.e. those on the circle of radius `d`
centred at `p i`.

The counting content is `sub_one_le_mul_card_distFinset`: if no circle centred at `p i`
carries more than `k` of the other `n - 1` vertices, then `n - 1 ≤ k * #(distFinset p i)`.
Its two specialisations are `exists_lt_card_equidistFinset` (pigeonhole form) and
`half_le_card_distFinset`, which already proves the target's bound at any vertex whose
distance fibres have size at most `2`; `erdos_982_of_forall_card_equidistFinset_le_two` states
that consequence in the reward theorem's own shape, for an arbitrary family of points, with no
convexity used. Read contrapositively — this is `exists_three_equidistant_of_ncard_lt` — a
counterexample to Erdős 982 must have, at *every* vertex, three further vertices on one circle
centred at that vertex. The floor-division arithmetic `R < n / 2 → 2 * R < n - 1` that makes
this come out right is done once, here.

On the geometric side, `injective_of_isCcwConvexPolygon` and `injective_of_isConvexPolygon`
show that for `3 ≤ n` the reward theorem's hypothesis `Function.Injective p` is *redundant*: a
repeated vertex makes one of the oriented angles `∡` degenerate, so that its sign is `0`, not
`1`. Together with the relabelling lemma `distFinset_comp_equiv` (the distance set at a vertex
does not depend on the labelling) this powers `erdos_982_of_isCcwConvexPolygon`: **it suffices
to prove Erdős 982 for counter-clockwise polygons**, which removes the disjunction in
`IsConvexPolygon` once and for all.

A later solver can use declaration
`Contribution.Erdos982DistinctDistances.erdos_982_of_ccw_reduced` to discharge or simplify
obligation `∃ (i : Fin n), { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2`
in target `Erdos982.erdos_982`: applying it leaves a goal about a *counter-clockwise* polygon
in which every vertex is already known to carry three other vertices on a circle centred at it,
with no `Set.ncard` and no convexity disjunction left anywhere. The individual steps are
available separately — `exists_three_equidistant_of_ncard_lt` (and its unpacked form
`exists_triple_equidistant_of_ncard_lt`, which names the three vertices) turns the negation of
the goal at a single vertex into that geometric configuration, and
`erdos_982_of_isCcwConvexPolygon` removes the disjunction on its own.

The final section contains worked use sites stated with the reward theorem's own binders:
`erdos_982_three` proves the case `n = 3` outright, and `erdos_982_of_ccw_reduced` packages
both reductions into a single statement, so that a solver only ever faces a counter-clockwise
polygon that is already known to carry an equidistant triple at every vertex.

The published partial results on this conjecture (Dumitrescu's `13n/36 - O(1)` and its
improvement by Nivasch, Pach, Pinchasi and Zerbib) proceed by bounding the number of isosceles
triangles spanned by the point set, and an isosceles triangle with apex `p i` is exactly an
unordered pair inside one `equidistFinset p i d`; so the fibres introduced here are the objects
those arguments count.

*References:*
- [erdosproblems.com/982](https://www.erdosproblems.com/982) (conjectured by Erdős in 1946)
- E. Altman, *On a problem of P. Erdős*, Amer. Math. Monthly 70 (1963), 148-157.
- G. Nivasch, J. Pach, R. Pinchasi and S. Zerbib, *The number of distinct distances from a
  vertex of a convex polygon*, J. Comput. Geom. 4 (2013), 1-12,
  [arXiv:1207.1266](https://arxiv.org/abs/1207.1266).
-/

open EuclideanGeometry Finset

namespace Contribution.Erdos982DistinctDistances

/- ### The distance set at a vertex as a `Finset` -/

section DistanceSets

variable {n : ℕ} {P : Type*} [Dist P] {p : Fin n → P} {i : Fin n}

/-- The `Finset` of distances from the vertex `p i` to the other vertices of the family `p`.
Its cardinality is the quantity `R(x_i)` of Erdős problem 982. -/
noncomputable def distFinset (p : Fin n → P) (i : Fin n) : Finset ℝ :=
  (Finset.univ.erase i).image fun j => dist (p i) (p j)

@[simp]
theorem mem_distFinset {d : ℝ} :
    d ∈ distFinset p i ↔ ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) := by
  simp [distFinset, eq_comm]

/-- `distFinset p i` is precisely the distance set appearing in `Erdos982.erdos_982`. -/
theorem coe_distFinset (p : Fin n → P) (i : Fin n) :
    (distFinset p i : Set ℝ) = { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) } := by
  ext d
  simp

/-- The bridge that turns Erdős 982 into a counting problem: the `Set.ncard` appearing in
`Erdos982.erdos_982` is the cardinality of a `Finset`. -/
theorem ncard_eq_card_distFinset (p : Fin n → P) (i : Fin n) :
    { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard = #(distFinset p i) := by
  rw [← coe_distFinset, Set.ncard_coe_finset]

/-- A vertex has at most `n - 1` distinct distances to the other vertices. -/
theorem card_distFinset_le (p : Fin n → P) (i : Fin n) : #(distFinset p i) ≤ n - 1 :=
  le_trans Finset.card_image_le (by simp)

/-- Degenerate case: as soon as there are two vertices, every vertex realises at least one
distance. This is what discharges Erdős 982 for `n ≤ 3`. -/
theorem one_le_card_distFinset (hn : 2 ≤ n) (p : Fin n → P) (i : Fin n) :
    1 ≤ #(distFinset p i) := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by simpa using hn) i
  exact ⟨dist (p i) (p j), mem_distFinset.2 ⟨j, hj, rfl⟩⟩

/-- The vertices `j ≠ i` lying at distance exactly `d` from `p i`: the vertices on the circle
of radius `d` centred at `p i`. This is the fibre of `j ↦ dist (p i) (p j)` over `d`. -/
noncomputable def equidistFinset (p : Fin n → P) (i : Fin n) (d : ℝ) : Finset (Fin n) :=
  {j ∈ Finset.univ.erase i | dist (p i) (p j) = d}

@[simp]
theorem mem_equidistFinset {j : Fin n} {d : ℝ} :
    j ∈ equidistFinset p i d ↔ j ≠ i ∧ dist (p i) (p j) = d := by
  simp [equidistFinset]

/- ### Counting -/

/-- **Fibrewise count at a vertex.** If every circle centred at `p i` carries at most `k` of
the other vertices, then the `n - 1` other vertices are covered by `#(distFinset p i)` fibres
of size at most `k`. This is `Finset.card_le_mul_card_image` specialised to the distance map
of a vertex; the point of the specialisation is that the `n - 1` on the left is the count a
solver actually wants, and that the hypothesis quantifies over *all* radii `d : ℝ` rather than
over the members of an image, which is the form in which "no `k + 1` vertices are equidistant
from `p i`" is available. -/
theorem sub_one_le_mul_card_distFinset (p : Fin n → P) (i : Fin n) (k : ℕ)
    (h : ∀ d : ℝ, #(equidistFinset p i d) ≤ k) : n - 1 ≤ k * #(distFinset p i) := by
  have h1 : #(Finset.univ.erase i) = n - 1 := by simp
  rw [← h1]
  exact Finset.card_le_mul_card_image _ k fun b _ => h b

/-- **Pigeonhole at a vertex.** If `p i` realises few distances to the other vertices, then
some circle centred at `p i` carries more than `k` of them. -/
theorem exists_lt_card_equidistFinset (p : Fin n → P) (i : Fin n) {k : ℕ}
    (h : k * #(distFinset p i) < n - 1) : ∃ d : ℝ, k < #(equidistFinset p i d) := by
  by_contra hcon
  push_neg at hcon
  exact absurd (sub_one_le_mul_card_distFinset p i k hcon) (by omega)

/-- If no three of the other vertices are equidistant from `p i`, then `p i` already realises
`⌊n / 2⌋` distinct distances, i.e. the target's bound holds at the vertex `i`. -/
theorem half_le_card_distFinset (p : Fin n → P) (i : Fin n)
    (h : ∀ d : ℝ, #(equidistFinset p i d) ≤ 2) : n / 2 ≤ #(distFinset p i) := by
  have := sub_one_le_mul_card_distFinset p i 2 h
  omega

/-- Erdős 982's conclusion, in the reward theorem's own shape, for any family of points in
which some vertex sees no three equidistant others. No convexity is used. -/
theorem erdos_982_of_forall_card_equidistFinset_le_two (p : Fin n → P)
    (h : ∃ i : Fin n, ∀ d : ℝ, #(equidistFinset p i d) ≤ 2) :
    ∃ i : Fin n, { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  rw [ge_iff_le, ncard_eq_card_distFinset p i]
  exact half_le_card_distFinset p i hi

/-- **The configuration hiding in a counterexample.** If the vertex `p i` fails the bound of
Erdős 982, then three of the other vertices lie on one circle centred at `p i`. -/
theorem exists_three_equidistant_of_ncard_lt (p : Fin n → P) (i : Fin n)
    (h : { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard < n / 2) :
    ∃ d : ℝ, 3 ≤ #(equidistFinset p i d) := by
  rw [ncard_eq_card_distFinset p i] at h
  obtain ⟨d, hd⟩ := exists_lt_card_equidistFinset p i (k := 2) (by omega)
  exact ⟨d, hd⟩

/-- **The configuration hiding in a counterexample, unpacked.** The same statement as
`exists_three_equidistant_of_ncard_lt`, but handing over three *named, pairwise distinct*
vertices on a common circle centred at `p i`, which is the form geometric arguments consume:
no `Finset` cardinality is left in the conclusion. -/
theorem exists_triple_equidistant_of_ncard_lt (p : Fin n → P) (i : Fin n)
    (h : { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard < n / 2) :
    ∃ (d : ℝ) (j₁ j₂ j₃ : Fin n), j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧ j₁ ≠ i ∧ j₂ ≠ i ∧ j₃ ≠ i ∧
      dist (p i) (p j₁) = d ∧ dist (p i) (p j₂) = d ∧ dist (p i) (p j₃) = d := by
  obtain ⟨d, hd⟩ := exists_three_equidistant_of_ncard_lt p i h
  obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq hd
  obtain ⟨j₁, j₂, j₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.1 ht3
  have hm : ∀ j ∈ ({j₁, j₂, j₃} : Finset (Fin n)), j ≠ i ∧ dist (p i) (p j) = d :=
    fun j hj => mem_equidistFinset.1 (hts hj)
  obtain ⟨hi₁, hd₁⟩ := hm j₁ (by simp)
  obtain ⟨hi₂, hd₂⟩ := hm j₂ (by simp)
  obtain ⟨hi₃, hd₃⟩ := hm j₃ (by simp)
  exact ⟨d, j₁, j₂, j₃, h12, h13, h23, hi₁, hi₂, hi₃, hd₁, hd₂, hd₃⟩

end DistanceSets

/- ### Relabelling the vertices -/

section Reindex

variable {n : ℕ} {P : Type*} [Dist P]

/-- The distance set at a vertex depends on the vertex only, not on the labelling. -/
theorem distFinset_comp_equiv (p : Fin n → P) (e : Fin n ≃ Fin n) (i : Fin n) :
    distFinset (p ∘ e) i = distFinset p (e i) := by
  have key : (Finset.univ.erase i).image (fun j => e j) = Finset.univ.erase (e i) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun hcon => ha (e.injective hcon)
    · intro hj
      refine ⟨e.symm j, fun hcon => hj ?_, by simp⟩
      rw [← Equiv.apply_symm_apply e j, hcon]
  simp only [distFinset, ← key, Finset.image_image]
  rfl

end Reindex

/- ### Convex polygons: injectivity is automatic, and the ccw branch suffices -/

section ConvexPolygons

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)]
  {n : ℕ} {p : Fin n → P}

/-- Two vertices of a counter-clockwise convex polygon with at least three vertices and with
different indices are distinct: a repetition makes one of the oriented angles `∡` degenerate,
and a degenerate angle has sign `0`, not `1`. -/
theorem ne_of_lt_of_isCcwConvexPolygon (hn : 3 ≤ n) (hp : IsCcwConvexPolygon p) {a b : Fin n}
    (hab : a < b) : p a ≠ p b := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c ∉ ({a, b} : Finset (Fin n)) := by
    by_contra hcon
    push_neg at hcon
    have h1 := Finset.card_le_card (fun x _ => hcon x :
      (Finset.univ : Finset (Fin n)) ⊆ {a, b})
    have h2 : #({a, b} : Finset (Fin n)) ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  rcases lt_trichotomy c a with hlt | heq | hgt
  · have hs := hp hlt hab
    rw [h, EuclideanGeometry.oangle_self_right, Real.Angle.sign_zero] at hs
    exact absurd hs (by decide)
  · exact hca heq
  · rcases lt_trichotomy c b with hlt2 | heq2 | hgt2
    · have hs := hp hgt hlt2
      rw [h, EuclideanGeometry.oangle_self_left_right, Real.Angle.sign_zero] at hs
      exact absurd hs (by decide)
    · exact hcb heq2
    · have hs := hp hab hgt2
      rw [h, EuclideanGeometry.oangle_self_left, Real.Angle.sign_zero] at hs
      exact absurd hs (by decide)

/-- The vertices of a counter-clockwise convex polygon with at least three vertices are
pairwise distinct. -/
theorem injective_of_isCcwConvexPolygon (hn : 3 ≤ n) (hp : IsCcwConvexPolygon p) :
    Function.Injective p := by
  intro a b hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact ne_of_lt_of_isCcwConvexPolygon hn hp h hab
  · exact ne_of_lt_of_isCcwConvexPolygon hn hp h hab.symm

/-- **The hypothesis `Function.Injective p` of `Erdos982.erdos_982` is redundant**: it follows
from `EuclideanGeometry.IsConvexPolygon p` as soon as `3 ≤ n`. -/
theorem injective_of_isConvexPolygon (hn : 3 ≤ n) (hp : IsConvexPolygon p) :
    Function.Injective p := by
  haveI : NeZero n := ⟨by omega⟩
  rcases hp with h | h
  · exact injective_of_isCcwConvexPolygon hn h
  · have hrev := injective_of_isCcwConvexPolygon hn h
    intro a b hab
    have hab' : (fun i : Fin n => p (-i)) (-a) = (fun i : Fin n => p (-i)) (-b) := by
      simpa using hab
    simpa using hrev hab'

/-- **It suffices to prove Erdős 982 for counter-clockwise polygons.** The disjunction in
`EuclideanGeometry.IsConvexPolygon` is removed here once and for all: the second branch is
transported to the first one by the relabelling `Equiv.neg (Fin n)`, under which the distance sets
are permuted (`distFinset_comp_equiv`). Note that the target's injectivity hypothesis is not
needed as an input, by `injective_of_isConvexPolygon`. -/
theorem erdos_982_of_isCcwConvexPolygon (hn : 3 ≤ n)
    (H : ∀ q : Fin n → P, Function.Injective q → IsCcwConvexPolygon q →
      ∃ i : Fin n, { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (q i) (q j) }.ncard ≥ n / 2)
    (hp : IsConvexPolygon p) :
    ∃ i : Fin n, { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have hinj := injective_of_isConvexPolygon hn hp
  rcases hp with h | h
  · exact H p hinj h
  · have hccw : IsCcwConvexPolygon (p ∘ Equiv.neg (Fin n)) := h
    obtain ⟨i, hi⟩ := H (p ∘ Equiv.neg (Fin n)) (hinj.comp (Equiv.neg (Fin n)).injective) hccw
    refine ⟨Equiv.neg (Fin n) i, ?_⟩
    rw [ge_iff_le, ncard_eq_card_distFinset p (Equiv.neg (Fin n) i), ← distFinset_comp_equiv p _ i,
      ← ncard_eq_card_distFinset (p ∘ Equiv.neg (Fin n)) i]
    exact hi

end ConvexPolygons

/- ### Worked use sites -/

section UseSites

variable {n : ℕ}

/-- **Use site 1: Erdős 982 for `n = 3`, proved outright**, with the reward theorem's own
binders. With three vertices the bound `⌊3 / 2⌋ = 1` only asks for a single distance, which
`one_le_card_distFinset` supplies; neither hypothesis of the reward theorem is needed. -/
theorem erdos_982_three (p : Fin 3 → ℝ²) (_hp : Function.Injective p)
    (_hp' : IsConvexPolygon p) :
    ∃ i : Fin 3, { d : ℝ | ∃ j : Fin 3, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ 3 / 2 := by
  refine ⟨0, ?_⟩
  rw [ge_iff_le, ncard_eq_card_distFinset p 0]
  simpa using one_le_card_distFinset (by norm_num) p 0

/-- **Use site 2: the two reductions combined**, with the reward theorem's own binders. To
prove `Erdos982.erdos_982` it suffices to refute the following configuration: a
counter-clockwise convex polygon in which every vertex realises fewer than `⌊n / 2⌋` distances
*and* has three named further vertices on a circle centred at it. Both the reversed branch of
`IsConvexPolygon` and all of the `Set.ncard` bookkeeping have disappeared, and the injectivity
hypothesis `_hp` is not used (it is recovered from `hp'` by `injective_of_isConvexPolygon`). -/
theorem erdos_982_of_ccw_reduced (hn : 3 ≤ n)
    (H : ∀ q : Fin n → ℝ², Function.Injective q → IsCcwConvexPolygon q →
      (∀ i : Fin n, #(distFinset q i) < n / 2) →
      (∀ i : Fin n, ∃ (d : ℝ) (j₁ j₂ j₃ : Fin n), j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
        j₁ ≠ i ∧ j₂ ≠ i ∧ j₃ ≠ i ∧ dist (q i) (q j₁) = d ∧ dist (q i) (q j₂) = d ∧
        dist (q i) (q j₃) = d) → False)
    (p : Fin n → ℝ²) (_hp : Function.Injective p) (hp' : IsConvexPolygon p) :
    ∃ i : Fin n, { d : ℝ | ∃ j : Fin n, j ≠ i ∧ d = dist (p i) (p j) }.ncard ≥ n / 2 := by
  refine erdos_982_of_isCcwConvexPolygon hn (fun q hqinj hqccw => ?_) hp'
  by_contra hcon
  push_neg at hcon
  refine H q hqinj hqccw (fun i => ?_) (fun i => ?_)
  · rw [← ncard_eq_card_distFinset q i]
    exact hcon i
  · exact exists_triple_equidistant_of_ncard_lt q i (hcon i)

end UseSites

end Contribution.Erdos982DistinctDistances
