import Mathlib
import FormalConjectures.GreensOpenProblems.«24»

/-!
# Green 24: upper bounds for cyclic profiles by support peeling

For the coefficient triple (1,2,-3), the profile score is
`(1/6) * sum_{s,t} kernel(g(3*t-2*s), 2*g(s), 3*g(t))`.
The submitted proofs control every odd modulus, every modulus coprime to three,
and every support meeting each doubling-kernel coset at most once. A violation
must therefore have modulus divisible by six and an occupied doubling collision.

The main engine is a fully proved finite-support peeling theorem, not an assumed
profile inequality or a numerical certificate. The kernel is proved symmetric
and agrees with the sorted three-interval formula. Uniform profiles attain 1/3.

This is partial progress on the cyclic route, not a proof of Green 24.
`CyclicApproximation` names the still-unformalized analytic bridge; it is only
an EXPLICIT HYPOTHESIS of `gamma_le_of_remaining_profiles`, never an axiom.
That theorem also explicitly requires the remaining mixed-profile bound.
The exact integer-count diagonal correction is proved separately.

Sources: the submitter's September 2026 research, and the cyclic reduction in
Ranđelović--Shao--Xu--Zhang--Zhou, arXiv:2609.06975v1, Definition 1.3 / Theorem 1.4.
See sources.md for the provenance, novelty comparison, and full scope boundary.
-/

noncomputable section
namespace Contribution.Green24CyclicProfiles
set_option autoImplicit false
open Finset

/-- Squared positive part. -/
def positiveSquare (x : ℝ) : ℝ := (max x 0)^2

/-- Symmetric quadratic-plus-hinges form of the three-interval kernel. -/
def kernel (x y z : ℝ) : ℝ :=
  (2*(x*y+x*z+y*z) - (x^2+y^2+z^2) +
    positiveSquare (x-y-z) + positiveSquare (y-x-z) + positiveSquare (z-x-y))/4

lemma kernel_swap_first (x y z : ℝ) : kernel x y z = kernel y x z := by
  have h : z-x-y = z-y-x := by ring
  unfold kernel
  rw [h]
  ring

lemma kernel_swap_last (x y z : ℝ) : kernel x y z = kernel x z y := by
  have h : x-y-z = x-z-y := by ring
  unfold kernel
  rw [h]
  ring

lemma positiveSquare_mono {a b : ℝ} (h : a ≤ b) :
    positiveSquare a ≤ positiveSquare b := by
  have h' : max a 0 ≤ max b 0 := max_le_max h le_rfl
  have ha : 0 ≤ max a 0 := le_max_right _ _
  have hb : 0 ≤ max b 0 := le_max_right _ _
  unfold positiveSquare
  nlinarith

lemma kernel_x_dominates {x y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : y+z ≤ x) : kernel x y z = y*z := by
  have h1 : 0 ≤ x-y-z := by linarith
  have h2 : y-x-z ≤ 0 := by linarith
  have h3 : z-x-y ≤ 0 := by linarith
  simp only [kernel, positiveSquare, max_eq_left h1, max_eq_right h2, max_eq_right h3]
  ring

lemma kernel_y_dominates {x y z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z)
    (h : x+z ≤ y) : kernel x y z = x*z := by
  have h1 : x-y-z ≤ 0 := by linarith
  have h2 : 0 ≤ y-x-z := by linarith
  have h3 : z-x-y ≤ 0 := by linarith
  simp only [kernel, positiveSquare, max_eq_right h1, max_eq_left h2, max_eq_right h3]
  ring

lemma kernel_z_dominates {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x+y ≤ z) : kernel x y z = x*y := by
  have h1 : x-y-z ≤ 0 := by linarith
  have h2 : y-x-z ≤ 0 := by linarith
  have h3 : 0 ≤ z-x-y := by linarith
  simp only [kernel, positiveSquare, max_eq_right h1, max_eq_right h2, max_eq_left h3]
  ring

lemma kernel_triangle {x y z : ℝ} (h1 : x ≤ y+z) (h2 : y ≤ x+z)
    (h3 : z ≤ x+y) : kernel x y z = x*y-(x+y-z)^2/4 := by
  have h1' : x-y-z ≤ 0 := by linarith
  have h2' : y-x-z ≤ 0 := by linarith
  have h3' : z-x-y ≤ 0 := by linarith
  simp only [kernel, positiveSquare, max_eq_right h1', max_eq_right h2', max_eq_right h3']
  ring

/-- Agreement with the sorted-coordinate definition in the source paper. -/
theorem kernel_sorted {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :
    kernel x y z = x*y - positiveSquare (x+y-z)/4 := by
  have hy : 0 ≤ y := hx.trans hxy
  by_cases h : x+y ≤ z
  · rw [kernel_z_dominates hx hy h]
    simp [positiveSquare, max_eq_right (show x+y-z ≤ 0 by linarith)]
  · have h1 : x ≤ y+z := by linarith
    have h2 : y ≤ x+z := by linarith
    rw [kernel_triangle h1 h2 (by linarith)]
    simp [positiveSquare, max_eq_left (show 0 ≤ x+y-z by linarith)]

theorem kernel_le_product {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    kernel x y z ≤ x*y := by
  by_cases h1 : y+z ≤ x
  · rw [kernel_x_dominates hy hz h1]
    nlinarith
  by_cases h2 : x+z ≤ y
  · rw [kernel_y_dominates hx hz h2]
    nlinarith
  by_cases h3 : x+y ≤ z
  · rw [kernel_z_dominates hx hy h3]
  rw [kernel_triangle (by linarith) (by linarith) (by linarith)]
  nlinarith [sq_nonneg (x+y-z)]

theorem kernel_nonneg {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ kernel x y z := by
  by_cases h1 : y+z ≤ x
  · rw [kernel_x_dominates hy hz h1]; positivity
  by_cases h2 : x+z ≤ y
  · rw [kernel_y_dominates hx hz h2]; positivity
  by_cases h3 : x+y ≤ z
  · rw [kernel_z_dominates hx hy h3]; positivity
  rw [kernel_triangle (by linarith) (by linarith) (by linarith)]
  have h : (x+y-z)*(x+y-z) ≤ (2*x)*(2*y) :=
    mul_le_mul (by linarith : x+y-z ≤ 2*x) (by linarith : x+y-z ≤ 2*y)
      (by linarith) (by positivity)
  nlinarith

lemma kernel_zero_left {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) : kernel 0 y z = 0 := by
  exact le_antisymm (by simpa using kernel_le_product (x:=0) (by norm_num) hy hz)
    (kernel_nonneg (by norm_num) hy hz)
lemma kernel_zero_middle {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : kernel x 0 z = 0 := by
  exact le_antisymm (by simpa using kernel_le_product hx (y:=0) (by norm_num) hz)
    (kernel_nonneg hx (by norm_num) hz)
lemma kernel_zero_right {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : kernel x y 0 = 0 := by
  rcases le_total x y with h | h
  · rw [kernel_y_dominates hx (z:=0) (by norm_num) (by simpa using h), mul_zero]
  · rw [kernel_x_dominates hy (z:=0) (by norm_num) (by simpa using h), mul_zero]

/-- The actual coefficient-(1,2,-3) summand. -/
def summand (x y z : ℝ) : ℝ := kernel x (2*y) (3*z)

lemma summand_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    summand x y z ≤ 2*x*y := by
  simpa [summand, mul_assoc, mul_left_comm] using
    kernel_le_product hx (mul_nonneg (by norm_num) hy) (mul_nonneg (by norm_num) hz)

/-- Adding one common support layer has controlled cost; the hinges only decrease. -/
theorem summand_peeling {x y z a : ℝ} (ha : 0 ≤ a) :
    summand (x+a) (y+a) (z+a) ≤ summand x y z + 2*a*(x+y)+2*a^2 := by
  have h1 := positiveSquare_mono (a:=x-2*y-3*z-4*a) (b:=x-2*y-3*z) (by linarith)
  have h2 := positiveSquare_mono (a:=2*y-x-3*z-2*a) (b:=2*y-x-3*z) (by linarith)
  have e1 : (x+a)-2*(y+a)-3*(z+a) = x-2*y-3*z-4*a := by ring
  have e2 : 2*(y+a)-(x+a)-3*(z+a) = 2*y-x-3*z-2*a := by ring
  have e3 : 3*(z+a)-(x+a)-2*(y+a) = 3*z-x-2*y := by ring
  unfold summand kernel
  rw [e1,e2,e3]
  nlinarith



section FinitePeeling
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Total mass; no normalization is built into the score. -/
def mass (g : α → ℝ) : ℝ := ∑ i, g i

/-- Six times the profile score, for a prescribed output-index map. -/
def rawScore (f : α → α → α) (g : α → ℝ) : ℝ :=
  ∑ p : α × α, summand (g (f p.1 p.2)) (g p.1) (g p.2)

/-- Precisely the incidences where all three profile coordinates may contribute. -/
def incidences (f : α → α → α) (S : Finset α) : Finset (α × α) :=
  (S ×ˢ S).filter fun p => f p.1 p.2 ∈ S

lemma summand_zero_x {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) : summand 0 y z = 0 := by
  exact kernel_zero_left (by positivity) (by positivity)
lemma summand_zero_y {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) : summand x 0 z = 0 := by
  simpa [summand] using kernel_zero_middle hx (mul_nonneg (by norm_num) hz)
lemma summand_zero_z {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : summand x y 0 = 0 := by
  simpa [summand] using kernel_zero_right hx (mul_nonneg (by norm_num) hy)

omit [DecidableEq α] in
lemma mass_eq_sum_support (S : Finset α) (g : α → ℝ)
    (hsupp : ∀ i, i ∉ S → g i = 0) : mass g = ∑ i ∈ S, g i := by
  exact (Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hsupp i hi)).symm

lemma rawScore_eq_sum_support (f : α → α → α) (S : Finset α) (g : α → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hsupp : ∀ i, i ∉ S → g i = 0) :
    rawScore f g = ∑ p ∈ incidences f S, summand (g (f p.1 p.2)) (g p.1) (g p.2) := by
  apply (Finset.sum_subset (Finset.subset_univ (incidences f S)) ?_).symm
  intro p _ hp
  by_cases hs : p.1 ∈ S
  · by_cases ht : p.2 ∈ S
    · have hr : f p.1 p.2 ∉ S := by
        intro hr
        exact hp (mem_filter.mpr ⟨mem_product.mpr ⟨hs,ht⟩,hr⟩)
      rw [hsupp _ hr, summand_zero_x (hg _) (hg _)]
    · rw [hsupp _ ht, summand_zero_z (hg _) (hg _)]
  · rw [hsupp _ hs, summand_zero_y (hg _) (hg _)]

omit [Fintype α] [DecidableEq α] in
lemma sum_first_product (S : Finset α) (g : α → ℝ) :
    (∑ p ∈ S ×ˢ S, g p.1) = (S.card : ℝ) * ∑ i ∈ S, g i := by
  simp [sum_product, sum_mul, mul_comm]

omit [Fintype α] in
/-- Injectivity of the output map on each support slice controls weighted incoming incidences. -/
lemma output_weight_le (f : α → α → α) (S : Finset α) (g : α → ℝ)
    (hg : ∀ i, 0 ≤ g i)
    (hinj : ∀ t ∈ S, Set.InjOn (fun s => f s t) (S : Set α)) :
    (∑ p ∈ incidences f S, g (f p.1 p.2)) ≤ (S.card : ℝ) * ∑ i ∈ S, g i := by
  let e : α × α → α × α := fun p => (f p.1 p.2,p.2)
  have he : Set.InjOn e (incidences f S : Set (α × α)) := by
    intro p hp q hq heq
    have hp' := mem_filter.mp hp
    have hq' := mem_filter.mp hq
    change (f p.1 p.2,p.2) = (f q.1 q.2,q.2) at heq
    have ht : p.2 = q.2 := (Prod.mk.inj heq).2
    have hr : f p.1 p.2 = f q.1 q.2 := (Prod.mk.inj heq).1
    have hs : p.1 = q.1 := hinj p.2 (mem_product.mp hp'.1).2
      (mem_product.mp hp'.1).1 (mem_product.mp hq'.1).1 (by simpa [ht] using hr)
    exact Prod.ext hs ht
  have hsub : (incidences f S).image e ⊆ S ×ˢ S := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    have hq' := mem_filter.mp hq
    exact mem_product.mpr ⟨hq'.2,(mem_product.mp hq'.1).2⟩
  calc
    _ = ∑ p ∈ (incidences f S).image e, g p.1 := (sum_image he).symm
    _ ≤ ∑ p ∈ S ×ˢ S, g p.1 := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hg p.1)
    _ = _ := sum_first_product S g

omit [Fintype α] in
lemma input_weight_le (f : α → α → α) (S : Finset α) (g : α → ℝ)
    (hg : ∀ i, 0 ≤ g i) :
    (∑ p ∈ incidences f S, g p.1) ≤ (S.card : ℝ) * ∑ i ∈ S, g i := by
  calc
    _ ≤ ∑ p ∈ S ×ˢ S, g p.1 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hg p.1)
    _ = _ := sum_first_product S g

/-- Finite support peeling: each fixed third coordinate has an injective output map
on the support. This is a general weighted incidence theorem, not a finite grid check. -/
theorem rawScore_le_of_support_injective (f : α → α → α) (S : Finset α) :
    ∀ (g : α → ℝ), (∀ i, 0 ≤ g i) → (∀ i, i ∉ S → g i = 0) →
      (∀ t ∈ S, Set.InjOn (fun s => f s t) (S : Set α)) →
      rawScore f g ≤ 2 * (mass g)^2 := by
  refine Finset.strongInductionOn S ?_
  intro S ih g hg hsupp hinj
  by_cases hS : S.Nonempty
  · obtain ⟨v,hv,hmin⟩ := exists_min_image S g hS
    let a : ℝ := g v
    let h : α → ℝ := fun i => if i ∈ S then g i-a else 0
    have ha : 0 ≤ a := hg v
    have hh : ∀ i, 0 ≤ h i := by
      intro i
      by_cases hi : i ∈ S
      · simp only [h, if_pos hi]
        exact sub_nonneg.mpr (hmin i hi)
      · simp [h,hi]
    have hhs : ∀ i, i ∉ S → h i = 0 := by intro i hi; simp [h,hi]
    have hherase : ∀ i, i ∉ S.erase v → h i = 0 := by
      intro i hi
      by_cases hiv : i = v
      · subst i; simp [h,hv,a]
      · have hiS : i ∉ S := fun hiS => hi (mem_erase.mpr ⟨hiv,hiS⟩)
        exact hhs i hiS
    have hhbound : rawScore f h ≤ 2*(mass h)^2 :=
      ih (S.erase v) (erase_ssubset hv) h hh hherase
        (fun t ht x hx y hy heq => hinj t (mem_of_mem_erase ht)
          (mem_of_mem_erase hx) (mem_of_mem_erase hy) heq)
    have hrebuild : ∀ i ∈ S, g i = h i+a := by
      intro i hi; simp [h,hi]
    have hmass : mass g = mass h + (S.card : ℝ)*a := by
      rw [mass_eq_sum_support S g hsupp, mass_eq_sum_support S h hhs]
      rw [sum_congr rfl (fun i hi => hrebuild i hi), sum_add_distrib]
      simp
    have hstep : rawScore f g ≤ rawScore f h +
        2*a*((∑ p ∈ incidences f S, h (f p.1 p.2))+
          ∑ p ∈ incidences f S, h p.1) +
        2*a^2*((incidences f S).card : ℝ) := by
      rw [rawScore_eq_sum_support f S g hg hsupp, rawScore_eq_sum_support f S h hh hhs]
      have hp : (∑ p ∈ incidences f S, summand (g (f p.1 p.2)) (g p.1) (g p.2)) ≤
            ∑ p ∈ incidences f S,
              (summand (h (f p.1 p.2)) (h p.1) (h p.2) +
                2*a*(h (f p.1 p.2)+h p.1)+2*a^2) :=
          sum_le_sum (fun p hp => by
        have hp' := mem_filter.mp hp
        have hs := (mem_product.mp hp'.1).1
        have ht := (mem_product.mp hp'.1).2
        rw [hrebuild _ hp'.2, hrebuild _ hs, hrebuild _ ht]
        exact summand_peeling (x:=h (f p.1 p.2)) (y:=h p.1) (z:=h p.2) ha)
      simp only [sum_add_distrib, ←mul_sum, sum_const, nsmul_eq_mul] at hp
      nlinarith [hp]
    have hout := output_weight_le f S h hh hinj
    have hin := input_weight_le f S h hh
    rw [←mass_eq_sum_support S h hhs] at hout hin
    have hc : ((incidences f S).card : ℝ) ≤ (S.card : ℝ)^2 := by
      have := card_le_card (filter_subset (fun p : α × α => f p.1 p.2 ∈ S) (S ×ˢ S))
      rw [card_product] at this
      have hn : (incidences f S).card ≤ S.card^2 := by simpa [incidences,pow_two] using this
      exact_mod_cast hn
    have hb1 := mul_le_mul_of_nonneg_left (add_le_add hout hin) (show 0 ≤ 2*a by positivity)
    have hb2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*a^2 by positivity)
    rw [hmass]
    nlinarith [hstep,hhbound,hb1,hb2]
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    have hzero : g = fun _ => 0 := by
      funext i; exact hsupp i (by simp [he])
    subst g
    simp [rawScore,mass,summand,kernel,positiveSquare]
end FinitePeeling


section CyclicProfiles
variable {q : ℕ} [NeZero q]

/-- The finite-cyclic score for the equation r+2s=3t; this is not the integer gamma. -/
def cyclicScore (g : ZMod q → ℝ) : ℝ :=
  rawScore (fun s t => 3*t-2*s) g / 6

/-- Exact match with the relation-indexed expression for coefficients (1,2,-3). -/
theorem cyclicScore_eq_relation_sum (g : ZMod q → ℝ) :
    cyclicScore g = (∑ s : ZMod q, ∑ t : ZMod q, ∑ r : ZMod q,
      if r+2*s=3*t then kernel (g r) (2*g s) (3*g t) else 0)/6 := by
  unfold cyclicScore rawScore
  rw [Fintype.sum_prod_type]
  congr 1
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro t _
  simp_rw [←eq_sub_iff_add_eq]
  simp [summand]

/-- Support in at most one point of each doubling-kernel coset is enough. -/
theorem cyclicScore_le_of_doubling_inj (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hinj : Set.InjOn (fun i : ZMod q => 2*i) {i | 0 < g i}) :
    cyclicScore g ≤ (mass g)^2/3 := by
  classical
  let S : Finset (ZMod q) := univ.filter fun i => 0 < g i
  have hsupp : ∀ i, i ∉ S → g i = 0 := by
    intro i hi
    have hn : ¬0 < g i := by simpa [S] using hi
    exact le_antisymm (le_of_not_gt hn) (hg i)
  have hi : ∀ t ∈ S, Set.InjOn (fun s : ZMod q => 3*t-2*s) (S : Set (ZMod q)) := by
    intro t _ x hx y hy heq
    apply hinj (mem_filter.mp hx).2 (mem_filter.mp hy).2
    linear_combination -heq
  have hb := rawScore_le_of_support_injective (fun s t : ZMod q => 3*t-2*s) S g hg hsupp hi
  unfold cyclicScore
  linarith

/-- Uniform bound for every odd modulus; no assumption about the third coefficient. -/
theorem cyclicScore_le_coprime_two (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hq : Nat.Coprime 2 q) : cyclicScore g ≤ (mass g)^2/3 := by
  apply cyclicScore_le_of_doubling_inj g hg
  have hu : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).mpr hq
  exact hu.mul_right_injective.injOn

theorem cyclicScore_le_odd (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hq : Odd q) : cyclicScore g ≤ (mass g)^2/3 :=
  cyclicScore_le_coprime_two g hg (Nat.coprime_two_left.mpr hq)

/-- The complementary infinite family follows by permuting the third-coordinate slices. -/
theorem cyclicScore_le_coprime_three (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hq : Nat.Coprime 3 q) : cyclicScore g ≤ (mass g)^2/3 := by
  have hu : IsUnit (3 : ZMod q) := (ZMod.isUnit_iff_coprime 3 q).mpr hq
  have hperm : ∀ s : ZMod q, (∑ t : ZMod q, g (3*t-2*s)) = mass g := by
    intro s
    have hi : Function.Injective (fun t : ZMod q => 3*t-2*s) := by
      intro x y hxy
      apply hu.mul_right_injective
      exact sub_left_inj.mp hxy
    have hb := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hi,rfl⟩
    exact Fintype.sum_bijective _ hb _ g (fun _ => rfl)
  have hraw : rawScore (fun s t : ZMod q => 3*t-2*s) g ≤ 2*(mass g)^2 := by
    calc
      _ ≤ ∑ s : ZMod q, (2*g s)*mass g := by
        unfold rawScore
        rw [Fintype.sum_prod_type]
        apply sum_le_sum
        intro s _
        calc
          _ ≤ ∑ t : ZMod q, (2*g s)*g (3*t-2*s) := by
            apply sum_le_sum
            intro t _
            have h := summand_le (hg (3*t-2*s)) (hg s) (hg t)
            nlinarith
          _ = _ := by rw [←mul_sum,hperm]
      _ = _ := by rw [←sum_mul,←mul_sum]; change (2*mass g)*mass g = 2*(mass g)^2; ring
  unfold cyclicScore
  linarith

/-- Both infinite families, packaged without imposing prime-power restrictions. -/
theorem cyclicScore_le_not_six_dvd (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hq : ¬6 ∣ q) : cyclicScore g ≤ (mass g)^2/3 := by
  by_cases h3 : 3 ∣ q
  · have h2 : ¬2 ∣ q := by
      intro h2
      exact hq ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3)
    exact cyclicScore_le_coprime_two g hg (Nat.prime_two.coprime_iff_not_dvd.mpr h2)
  · exact cyclicScore_le_coprime_three g hg (Nat.prime_three.coprime_iff_not_dvd.mpr h3)

/-- Every supercritical cyclic profile has both the modulus and support obstruction. -/
theorem supercritical_obstructions (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hbad : (mass g)^2/3 < cyclicScore g) :
    6 ∣ q ∧ ∃ x y : ZMod q, x ≠ y ∧ 0 < g x ∧ 0 < g y ∧ 2*x=2*y := by
  constructor
  · by_contra hn
    exact (not_lt_of_ge (cyclicScore_le_not_six_dvd g hg hn)) hbad
  · by_contra hn
    have hi : Set.InjOn (fun i : ZMod q => 2*i) {i | 0 < g i} := by
      intro x hx y hy heq
      by_contra hne
      exact hn ⟨x,y,hne,hx,hy,heq⟩
    exact (not_lt_of_ge (cyclicScore_le_of_doubling_inj g hg hi)) hbad

/-- A normalized use site covering all moduli not divisible by six. -/
theorem probabilityProfile_le (g : ZMod q → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hmass : mass g = 1) (hq : ¬6 ∣ q) : cyclicScore g ≤ 1/3 := by
  simpa [hmass] using cyclicScore_le_not_six_dvd g hg hq

end CyclicProfiles


section SharpnessAndTarget

lemma summand_constant {c : ℝ} (hc : 0 ≤ c) : summand c c c = 2*c^2 := by
  unfold summand
  rw [kernel_z_dominates hc (by positivity) (by linarith)]
  ring

/-- All moduli have the same uniform-profile value. This checks normalization. -/
theorem cyclicScore_constant {q : ℕ} [NeZero q] {c : ℝ} (hc : 0 ≤ c) :
    cyclicScore (fun _ : ZMod q => c) = (q : ℝ)^2*c^2/3 := by
  simp only [cyclicScore,rawScore,summand_constant hc,sum_const,card_univ,
    Fintype.card_prod,ZMod.card,nsmul_eq_mul,Nat.cast_mul]
  ring

/-- The unit-mass constant profile. -/
def uniformProfile (q : ℕ) : ZMod q → ℝ := fun _ => 1/(q : ℝ)

lemma uniformProfile_nonneg (q : ℕ) (i : ZMod q) : 0 ≤ uniformProfile q i := by
  unfold uniformProfile
  positivity

lemma mass_uniform {q : ℕ} [NeZero q] : mass (uniformProfile q) = 1 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp [mass,uniformProfile,ZMod.card,hq]

/-- Sharpness is checked on actual nonempty normalized profiles, not inferred from a bound. -/
theorem cyclicScore_uniform {q : ℕ} [NeZero q] : cyclicScore (uniformProfile q) = 1/3 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold uniformProfile
  rw [cyclicScore_constant (by positivity)]
  field_simp

/-- The precise unformalized analytic interface used by the cyclic research route.
The external supremum reduction would imply this after matching the integer count.
It is a named proposition, NOT an axiom or a theorem proved in this contribution. -/
def CyclicApproximation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (g : ZMod (m+1) → ℝ),
    (∀ i, 0 ≤ g i) ∧ mass g = 1 ∧ Green24.variants.gamma-ε < cyclicScore g

/-- After the analytic bridge, only mixed moduli with a doubling collision remain.
Both missing mathematical inputs are explicit hypotheses; the full target is not asserted. -/
theorem gamma_le_of_remaining_profiles (happrox : CyclicApproximation)
    (hremaining : ∀ (m : ℕ) (g : ZMod (m+1) → ℝ),
      (∀ i, 0 ≤ g i) → mass g = 1 → 6 ∣ m+1 →
      (∃ x y : ZMod (m+1), x ≠ y ∧ 0 < g x ∧ 0 < g y ∧ 2*x=2*y) →
      cyclicScore g ≤ 1/3) : Green24.variants.gamma ≤ 1/3 := by
  by_contra hn
  have hgap : 0 < (Green24.variants.gamma-1/3)/2 := by linarith
  obtain ⟨m,g,hg,hmass,hs⟩ := happrox _ hgap
  have hbad : (mass g)^2/3 < cyclicScore g := by rw [hmass]; norm_num; linarith
  obtain ⟨hmod,hcollision⟩ := supercritical_obstructions g hg hbad
  have hupper := hremaining m g hg hmass hmod hcollision
  linarith

/-- A concrete nonvacuous use of the all-odd theorem, with no rational-grid restriction. -/
example (g : ZMod 729 → ℝ) (hg : ∀ i, 0 ≤ g i) (hmass : mass g = 1) :
    cyclicScore g ≤ 1/3 := by
  simpa [hmass] using cyclicScore_le_odd g hg (by decide : Odd 729)

/-- The analogous infinite pure-two-power family. -/
example (b : ℕ) (g : ZMod (2^b) → ℝ) (hg : ∀ i, 0 ≤ g i) (hmass : mass g = 1) :
    cyclicScore g ≤ 1/3 := by
  simpa [hmass] using cyclicScore_le_coprime_three g hg
    ((by decide : Nat.Coprime 3 2).pow_right b)

end SharpnessAndTarget


section IntegerNormalization

/-- The exact pair count occurring inside the official maximum. -/
def affineCount (A : Finset ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ p.1+3*(p.2-p.1) ∈ A)).card

/-- Ordered solution pairs for r+2s=3t, including the diagonal. -/
def linearCount (A : Finset ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun p => 3*p.2-2*p.1 ∈ A)).card

/-- Exact, non-asymptotic normalization between the two counting conventions.
The integer-to-cyclic analytic reduction is still a separate obligation. -/
theorem linearCount_eq_affineCount_add_card (A : Finset ℤ) :
    linearCount A = affineCount A + A.card := by
  let C := (A ×ˢ A).filter (fun p : ℤ × ℤ => 3*p.2-2*p.1 ∈ A)
  have hd : C.filter (fun p => p.1=p.2) = A.image (fun x => (x,x)) := by
    ext ⟨x,y⟩
    simp only [C,mem_filter,mem_product,mem_image,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx,_⟩,_⟩,he⟩
      exact ⟨x,hx,rfl,he⟩
    · rintro ⟨z,hz,rfl,rfl⟩
      have he : (3:ℤ)*z-2*z=z := by ring
      simp [he,hz]
  have hn : C.filter (fun p => ¬p.1=p.2) =
      (A ×ˢ A).filter (fun p => p.1≠p.2 ∧ p.1+3*(p.2-p.1) ∈ A) := by
    ext ⟨x,y⟩
    have he : x+3*(y-x) = 3*y-2*x := by ring
    simp [C,he,and_assoc,and_left_comm,and_comm]
  have hc := card_filter_add_card_filter_not (s:=C) (fun p : ℤ × ℤ => p.1=p.2)
  rw [hd,hn,card_image_of_injective A (fun x y h => (Prod.mk.inj h).1)] at hc
  unfold linearCount affineCount
  change C.card = _
  omega

end IntegerNormalization

end Contribution.Green24CyclicProfiles
