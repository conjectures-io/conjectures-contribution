import Mathlib
import FormalConjectures.ErdosProblems.«212»

/-!
# Erdős 212: normalisation and the quadratic-field structure of rational-distance sets

Target: `Erdos212.erdos_212` — is there a dense `u : Set ℂ` with

`u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast` ?

## The obstacle

The reward statement carries *no* structure at all: it is a bare existential over subsets of `ℂ`
whose only hypothesis is a `Set.Pairwise` condition asserting membership in `Set.range Rat.cast`.
Three concrete things go wrong the moment one tries to work with it.

* `Set.Pairwise` only fires on **distinct** points, so every use of the hypothesis drags a
  `p ≠ q` side goal along, even where it is irrelevant (`dist p p = 0` is rational too).
* `Set.range (Rat.cast : ℚ → ℝ)` is an opaque `Set ℝ`. It *is* closed under `+`, `-`, `*`, `⁻¹`,
  but none of that is available: each arithmetic step has to `obtain` rational witnesses and
  `push_cast` them back by hand. The whole argument below is arithmetic in this set.
* The statement is invariant under the similarity group `z ↦ a * z + b` with `‖a‖` rational, and
  the classical arguments all begin "normalise so that `0` and `1` belong to the set". Nothing in
  the environment performs that normalisation, and doing it by hand requires producing two
  distinct points of a dense set and checking that an affine map preserves both density and
  rationality of distances.

## What is proved here

`ratField` is the image of `ℚ` in `ℝ` packaged as a `Subfield ℝ`, and `mem_ratField_iff` is the
(definitional) bridge from the target's `Set.range Rat.cast`; this single move opens `add_mem`,
`sub_mem`, `mul_mem`, `div_mem`, `pow_mem` on the target's own predicate.
`IsRatDist` names the predicate (`isRatDist_iff_target` checks by `Iff.rfl` that there is no
statement drift), `IsRatDist.dist_mem_ratField` removes the `p ≠ q` side condition once and for
all, and `IsRatDist.image_affine` records invariance under rational similarities.

The mathematical content is the classical two-step structure theorem, which as far as we can tell
had not been formalised:

* `IsRatDist.re_mem_ratField` / `IsRatDist.im_sq_mem_ratField`: if `0, 1 ∈ u` then every `p ∈ u`
  has `p.re ∈ ℚ` and `p.im ^ 2 ∈ ℚ` (subtract the two circle equations centred at `0` and `1`);
* `IsRatDist.im_mul_im_mem_ratField`: moreover `p.im * q.im ∈ ℚ` for all `p q ∈ u`, so all
  imaginary parts lie on a *single* line `ℚ · y` — this is `IsRatDist.exists_subset_ratSlice`,
  which places a normalised rational-distance set inside `RatSlice y = ℚ ⊕ ℚ·(y·i)` with
  `y ^ 2 ∈ ℚ`, i.e. inside a fixed imaginary quadratic field, except in the degenerate collinear
  case `y = 0`, where `RatSlice 0` is just `ℚ ⊆ ℝ`.

Two consequences are then immediate but are not otherwise available.

* `IsRatDist.countable`: **every** rational-distance set in the plane is countable, with *no*
  normalisation hypothesis. (So any witness is countable — a positive answer must be a countable
  dense set; nothing of positive measure or of second category can be a rational-distance set.)
* The headline `exists_dense_isRatDist_iff_rat`: a dense rational-distance set exists **iff**
  there are a rational `d > 0` and a set `S ⊆ ℚ × ℚ`, dense in the plane, such that
  `(a₁ - a₂) ^ 2 + d * (c₁ - c₂) ^ 2` is a square in `ℚ` for every pair of points of `S`.
  Distances, normalisation and irrational numbers have all disappeared from the right-hand side;
  `imScale` / `dense_coord_image_iff` are what remove the last scalar `y` with `y ^ 2 = d` from
  the density condition, and `exists_dense_isRatDist_iff` is the intermediate form that still
  mentions `y`. The `←` direction of the equivalence is `isRatDist_coord_image`, the construction
  interface a *positive* solver would use.

`dense_ratSlice_one` and `exists_infinite_normalized_isRatDist` are honesty checks: the derived
containment is satisfied by a dense set and the normalised hypotheses are satisfied by an infinite
set, so none of the statements above is vacuous, and the reduction does not by itself settle the
problem.

## Handoff (G1)

A later solver can use declaration
`Contribution.Erdos212RationalDistance.exists_dense_isRatDist_iff_rat` to discharge or simplify
the obligation `∃ u : Set ℂ, Dense u ∧ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast`
in target `Erdos212.erdos_212`, replacing it by a statement about rational squares
`r ^ 2 = (a₁ - a₂) ^ 2 + d * (c₁ - c₂) ^ 2` over a subset of `ℚ × ℚ`.
The worked use sites `erdos_212_iff_diophantine`, `erdos_212_true_iff_of_dense_rational_family`,
`erdos_212_of_no_dense_rational_family` and `countable_of_erdos_212_predicate` at the end of this
file carry that out against the reward theorem's own right-hand side.

*References:*
- [erdosproblems.com/212](https://www.erdosproblems.com/212)
- J. Solymosi and F. de Zeeuw, *On a question of Erdős and Ulam*,
  Discrete Comput. Geom. 43 (2010), 393-401, <https://arxiv.org/abs/0806.3095>
- K. Ascher, L. Braune and A. Turchet, *The Erdős–Ulam problem, Lang's conjecture and uniformity*,
  Bull. LMS 52 (2020), 1053-1063, <https://arxiv.org/abs/1901.08054>
-/

namespace Contribution.Erdos212RationalDistance

open Set

/- ### The rationals inside `ℝ`, as a subfield -/

/-- The image of `ℚ` in `ℝ`, packaged as a `Subfield ℝ`. Its underlying set is exactly the
`Set.range Rat.cast` appearing in `Erdos212.erdos_212`, so all of `add_mem`, `sub_mem`, `mul_mem`,
`div_mem`, `pow_mem` become available on the target's own predicate. -/
noncomputable def ratField : Subfield ℝ := (Rat.castHom ℝ).fieldRange

/-- The bridge: membership in `ratField` *is* the target's `∈ Set.range Rat.cast`. -/
theorem mem_ratField_iff {x : ℝ} : x ∈ ratField ↔ x ∈ Set.range (Rat.cast : ℚ → ℝ) := Iff.rfl

/- ### Rational-distance sets -/

/-- `IsRatDist u` : all pairwise distances between points of `u ⊆ ℂ` are rational.
This is *definitionally* the predicate occurring in `Erdos212.erdos_212`. -/
def IsRatDist (u : Set ℂ) : Prop :=
  u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range (Rat.cast : ℚ → ℝ)

/-- No statement drift: `IsRatDist` is the reward theorem's predicate, on the nose. -/
theorem isRatDist_iff_target (u : Set ℂ) :
    IsRatDist u ↔ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast := Iff.rfl

/-- The `p ≠ q` side condition in `Set.Pairwise` is spurious: `dist p q` is rational for *all*
`p q ∈ u`. This is the form in which the hypothesis is actually used below. -/
theorem IsRatDist.dist_mem_ratField {u : Set ℂ} (h : IsRatDist u) {p q : ℂ}
    (hp : p ∈ u) (hq : q ∈ u) : dist p q ∈ ratField := by
  rcases eq_or_ne p q with rfl | hne
  · rw [dist_self]
    exact zero_mem _
  · exact h hp hq hne

/-- Distances between distinct points of a rational-distance set are *positive* rationals;
this is the `rcases`-friendly form (`obtain ⟨r, hrpos, hrdist⟩`), which packages the positivity
that `Set.range Rat.cast` membership alone does not give. -/
theorem IsRatDist.exists_pos_rat_dist {u : Set ℂ} (h : IsRatDist u) {p q : ℂ}
    (hp : p ∈ u) (hq : q ∈ u) (hne : p ≠ q) : ∃ r : ℚ, 0 < r ∧ dist p q = (r : ℝ) := by
  obtain ⟨r, hr⟩ := h hp hq hne
  refine ⟨r, ?_, hr.symm⟩
  have hpos : (0 : ℝ) < dist p q := dist_pos.mpr hne
  rw [← hr] at hpos
  exact_mod_cast hpos

/-- Rational-distance sets are stable under the similarities `z ↦ a * z + b` whose ratio `a` has
rational modulus. This is the group action along which one normalises. -/
theorem IsRatDist.image_affine {u : Set ℂ} (h : IsRatDist u) {a b : ℂ}
    (ha : ‖a‖ ∈ ratField) : IsRatDist ((fun z => a * z + b) '' u) := by
  rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩ -
  have hd : dist (a * z + b) (a * w + b) = ‖a‖ * dist z w := by
    rw [Complex.dist_eq, Complex.dist_eq, show a * z + b - (a * w + b) = a * (z - w) by ring,
      norm_mul]
  rw [hd]
  exact mul_mem ha (h.dist_mem_ratField hz hw)

/- ### Normalisation: moving two points of the set to `0` and `1` -/

/-- A dense subset of `ℂ` has two distinct points. -/
theorem exists_ne_of_dense {u : Set ℂ} (hu : Dense u) : ∃ p ∈ u, ∃ q ∈ u, p ≠ q := by
  obtain ⟨p, hp1, hp2⟩ := Metric.dense_iff.mp hu 0 1 one_pos
  obtain ⟨q, hq1, hq2⟩ := Metric.dense_iff.mp hu 3 1 one_pos
  refine ⟨p, hp2, q, hq2, ?_⟩
  rintro rfl
  rw [Metric.mem_ball] at hp1 hq1
  have h03 : dist (0 : ℂ) 3 = 3 := by
    rw [Complex.dist_eq]
    norm_num
  have := dist_triangle (0 : ℂ) p 3
  rw [h03, dist_comm (0 : ℂ) p] at this
  linarith

/-- **Normalisation.** From any two distinct points of a rational-distance set one gets an affine
map (a rational similarity) that is injective, preserves density, preserves the rational-distance
property, and moves the two points to `0` and `1`. -/
theorem IsRatDist.exists_normalizing_map {u : Set ℂ} (h : IsRatDist u) {p q : ℂ}
    (hp : p ∈ u) (hq : q ∈ u) (hpq : p ≠ q) :
    ∃ f : ℂ → ℂ, Function.Injective f ∧ (∀ s : Set ℂ, Dense s → Dense (f '' s)) ∧
      IsRatDist (f '' u) ∧ (0 : ℂ) ∈ f '' u ∧ (1 : ℂ) ∈ f '' u := by
  have hqp : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  set a : ℂ := (q - p)⁻¹ with ha_def
  have ha : a ≠ 0 := inv_ne_zero hqp
  set b : ℂ := -(p * a) with hb_def
  set e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b) with he_def
  have hcoe : ⇑e = fun z => a * z + b := rfl
  refine ⟨fun z => a * z + b, ?_, ?_, ?_, ⟨p, hp, ?_⟩, ⟨q, hq, ?_⟩⟩
  · rw [← hcoe]; exact e.injective
  · intro s hs
    rw [← hcoe]
    exact e.surjective.denseRange.dense_image e.continuous hs
  · refine h.image_affine ?_
    have hna : ‖a‖ = (dist q p)⁻¹ := by rw [ha_def, norm_inv, Complex.dist_eq]
    rw [hna]
    exact inv_mem (h.dist_mem_ratField hq hp)
  · show a * p + b = 0
    rw [hb_def]; ring
  · show a * q + b = 1
    rw [hb_def, ha_def]
    field_simp
    ring

/- ### Coordinates of a normalised rational-distance set -/

/-- Subtracting the two circle equations centred at `0` and at `1` pins the real part of every
point of a normalised rational-distance set down to a rational number. -/
theorem IsRatDist.re_mem_ratField {u : Set ℂ} (h : IsRatDist u) (h0 : (0 : ℂ) ∈ u)
    (h1 : (1 : ℂ) ∈ u) {p : ℂ} (hp : p ∈ u) : p.re ∈ ratField := by
  have hA : dist p 0 ∈ ratField := h.dist_mem_ratField hp h0
  have hB : dist p 1 ∈ ratField := h.dist_mem_ratField hp h1
  have eA : dist p 0 ^ 2 = p.re ^ 2 + p.im ^ 2 := by
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
    simp
  have eB : dist p 1 ^ 2 = (p.re - 1) ^ 2 + p.im ^ 2 := by
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
    simp
  have key : p.re = (dist p 0 ^ 2 - dist p 1 ^ 2 + 1) / 2 := by rw [eA, eB]; ring
  rw [key]
  exact div_mem (add_mem (sub_mem (pow_mem hA 2) (pow_mem hB 2)) (one_mem ratField))
    (ofNat_mem ratField 2)

/-- The imaginary part of a point of a normalised rational-distance set need not be rational,
but its square is. -/
theorem IsRatDist.im_sq_mem_ratField {u : Set ℂ} (h : IsRatDist u) (h0 : (0 : ℂ) ∈ u)
    (h1 : (1 : ℂ) ∈ u) {p : ℂ} (hp : p ∈ u) : p.im ^ 2 ∈ ratField := by
  have hA : dist p 0 ∈ ratField := h.dist_mem_ratField hp h0
  have eA : p.im ^ 2 = dist p 0 ^ 2 - p.re ^ 2 := by
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
    simp
  rw [eA]
  exact sub_mem (pow_mem hA 2) (pow_mem (h.re_mem_ratField h0 h1 hp) 2)

/-- The key rigidity step: in a normalised rational-distance set the *product* of any two
imaginary parts is rational. Consequently all imaginary parts lie on a single line `ℚ · y`. -/
theorem IsRatDist.im_mul_im_mem_ratField {u : Set ℂ} (h : IsRatDist u) (h0 : (0 : ℂ) ∈ u)
    (h1 : (1 : ℂ) ∈ u) {p q : ℂ} (hp : p ∈ u) (hq : q ∈ u) : p.im * q.im ∈ ratField := by
  have hd : dist p q ∈ ratField := h.dist_mem_ratField hp hq
  have e : dist p q ^ 2 = (p.re - q.re) ^ 2 + (p.im - q.im) ^ 2 := by
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]
  have key : p.im * q.im =
      ((p.re - q.re) ^ 2 + p.im ^ 2 + q.im ^ 2 - dist p q ^ 2) / 2 := by rw [e]; ring
  rw [key]
  exact div_mem (sub_mem (add_mem (add_mem
    (pow_mem (sub_mem (h.re_mem_ratField h0 h1 hp) (h.re_mem_ratField h0 h1 hq)) 2)
    (h.im_sq_mem_ratField h0 h1 hp)) (h.im_sq_mem_ratField h0 h1 hq)) (pow_mem hd 2))
    (ofNat_mem ratField 2)

/- ### The quadratic slice `ℚ ⊕ ℚ·(y·i)` -/

/-- The point of `ℂ` whose coordinates in the `ℝ`-basis `(1, y * I)` are the rationals `p.1`,
`p.2`. -/
noncomputable def coord (y : ℝ) (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ) * y⟩

@[simp] theorem coord_re (y : ℝ) (p : ℚ × ℚ) : (coord y p).re = (p.1 : ℝ) := rfl

@[simp] theorem coord_im (y : ℝ) (p : ℚ × ℚ) : (coord y p).im = (p.2 : ℝ) * y := rfl

/-- `RatSlice y` is the `ℚ`-affine plane `ℚ ⊕ ℚ·(y·i) ⊆ ℂ`. -/
noncomputable def RatSlice (y : ℝ) : Set ℂ := Set.range (coord y)

theorem mem_ratSlice_iff {y : ℝ} {z : ℂ} :
    z ∈ RatSlice y ↔ z.re ∈ ratField ∧ ∃ c : ℚ, z.im = (c : ℝ) * y := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨⟨p.1, rfl⟩, p.2, rfl⟩
  · rintro ⟨⟨a, ha⟩, c, hc⟩
    exact ⟨(a, c), Complex.ext ha hc.symm⟩

/-- **Construction interface.** The analytic condition "all pairwise distances are rational"
becomes a purely arithmetic one on a set of rational coordinate pairs: the quadratic form
`(a₁ - a₂) ^ 2 + d * (c₁ - c₂) ^ 2` has to be a square in `ℚ`. This is the direction a solver
building a dense example would use. -/
theorem isRatDist_coord_image {y : ℝ} {d : ℚ} (hy : y ^ 2 = (d : ℝ)) {S : Set (ℚ × ℚ)}
    (hS : ∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, r ^ 2 = (p.1 - q.1) ^ 2 + d * (p.2 - q.2) ^ 2) :
    IsRatDist (coord y '' S) := by
  rintro x ⟨p, hp, rfl⟩ z ⟨q, hq, rfl⟩ -
  obtain ⟨r, hr⟩ := hS p hp q hq
  have hr' : ((r : ℝ)) ^ 2 = ((p.1 : ℝ) - (q.1 : ℝ)) ^ 2
      + (d : ℝ) * ((p.2 : ℝ) - (q.2 : ℝ)) ^ 2 := by exact_mod_cast congrArg (Rat.cast (K := ℝ)) hr
  have hsq : dist (coord y p) (coord y q) ^ 2 = (|(r : ℝ)|) ^ 2 := by
    rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity), sq_abs, hr', ← hy]
    simp only [coord_re, coord_im]
    ring
  have habs := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rw [abs_of_nonneg dist_nonneg, abs_abs] at habs
  exact ⟨|r|, by rw [habs]; push_cast; ring⟩

/-- **Structure theorem.** A rational-distance set containing `0` and `1` is contained in a
single `ℚ`-affine plane `ℚ ⊕ ℚ·(y·i)` whose parameter satisfies `y ^ 2 ∈ ℚ`; equivalently, it
lives inside a fixed imaginary quadratic field, except in the degenerate collinear case `y = 0`
(the branch taken when every point of `u` is real), where `RatSlice 0` is just `ℚ ⊆ ℝ`. -/
theorem IsRatDist.exists_subset_ratSlice {u : Set ℂ} (h : IsRatDist u) (h0 : (0 : ℂ) ∈ u)
    (h1 : (1 : ℂ) ∈ u) : ∃ y : ℝ, y ^ 2 ∈ ratField ∧ u ⊆ RatSlice y := by
  by_cases hex : ∃ p ∈ u, p.im ≠ 0
  · obtain ⟨p₀, hp₀, hne⟩ := hex
    refine ⟨p₀.im, h.im_sq_mem_ratField h0 h1 hp₀, fun z hz => ?_⟩
    rw [mem_ratSlice_iff]
    refine ⟨h.re_mem_ratField h0 h1 hz, ?_⟩
    have hm : z.im * p₀.im ∈ ratField := h.im_mul_im_mem_ratField h0 h1 hz hp₀
    have hs : p₀.im ^ 2 ∈ ratField := h.im_sq_mem_ratField h0 h1 hp₀
    obtain ⟨c, hc⟩ := mem_ratField_iff.mp (div_mem hm hs)
    refine ⟨c, ?_⟩
    rw [hc]
    field_simp
  · push_neg at hex
    refine ⟨0, by simp, fun z hz => ?_⟩
    rw [mem_ratSlice_iff]
    exact ⟨h.re_mem_ratField h0 h1 hz, 0, by simp [hex z hz]⟩

/-- **Corollary, with no normalisation hypothesis.** Every rational-distance set in the plane is
countable. So any witness of the target is countable — a positive answer must be a countable
dense set; nothing of positive measure or of second category can be a rational-distance set. -/
theorem IsRatDist.countable {u : Set ℂ} (h : IsRatDist u) : u.Countable := by
  by_cases hex : ∃ p ∈ u, ∃ q ∈ u, p ≠ q
  · obtain ⟨p, hp, q, hq, hpq⟩ := hex
    obtain ⟨f, hinj, -, hfr, hf0, hf1⟩ := h.exists_normalizing_map hp hq hpq
    obtain ⟨y, -, hsub⟩ := hfr.exists_subset_ratSlice hf0 hf1
    have hc : (f '' u).Countable := Set.Countable.mono hsub (Set.countable_range _)
    exact Set.Countable.mono (Set.subset_preimage_image f u) (hc.preimage hinj)
  · push_neg at hex
    exact Set.Subsingleton.countable fun x hx y hy => hex x hx y hy

/-- A set of reals (points with vanishing imaginary part) is never dense in `ℂ`. Used to rule out
the degenerate collinear case `y = 0` of the structure theorem. -/
theorem not_dense_of_forall_im_eq_zero {u : Set ℂ} (h : ∀ z ∈ u, z.im = 0) : ¬ Dense u := by
  intro hu
  obtain ⟨z, hz1, hz2⟩ := Metric.dense_iff.mp hu Complex.I 1 one_pos
  rw [Metric.mem_ball, Complex.dist_eq] at hz1
  have hle : |(z - Complex.I).im| ≤ ‖z - Complex.I‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, Complex.I_im, h z hz2] at hle
  norm_num at hle
  linarith

/- ### The headline reduction -/

/-- **Main reduction.** A dense rational-distance set in the plane exists if and only if there is
a positive rational `d` and a set `S` of rational coordinate pairs, dense in the plane under
`coord y` (`y ^ 2 = d`), such that the quadratic form `(a₁ - a₂) ^ 2 + d * (c₁ - c₂) ^ 2` is a
square in `ℚ` on every pair of points of `S`. The right-hand side mentions no distances, no
normalisation and no irrational numbers apart from the single scalar `y`. -/
theorem exists_dense_isRatDist_iff :
    (∃ u : Set ℂ, Dense u ∧ IsRatDist u) ↔
      ∃ (d : ℚ) (y : ℝ) (S : Set (ℚ × ℚ)), 0 < d ∧ y ^ 2 = (d : ℝ) ∧
        (∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, r ^ 2 = (p.1 - q.1) ^ 2 + d * (p.2 - q.2) ^ 2) ∧
        Dense (coord y '' S) := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := exists_ne_of_dense hu
    obtain ⟨f, -, hdens, hfr, hf0, hf1⟩ := h.exists_normalizing_map hp hq hpq
    have hvd : Dense (f '' u) := hdens u hu
    obtain ⟨y, hy2, hsub⟩ := hfr.exists_subset_ratSlice hf0 hf1
    have hyne : y ≠ 0 := by
      rintro rfl
      refine not_dense_of_forall_im_eq_zero (fun z hz => ?_) hvd
      obtain ⟨-, c, hc⟩ := mem_ratSlice_iff.mp (hsub hz)
      simpa using hc
    obtain ⟨d, hd⟩ := mem_ratField_iff.mp hy2
    have hdpos : 0 < d := by
      have hpos : (0 : ℝ) < (d : ℝ) := by rw [hd]; exact pow_two_pos_of_ne_zero hyne
      exact_mod_cast hpos
    refine ⟨d, y, coord y ⁻¹' (f '' u), hdpos, hd.symm, ?_, ?_⟩
    · intro a ha b hb
      obtain ⟨r, hr⟩ := mem_ratField_iff.mp (hfr.dist_mem_ratField ha hb)
      refine ⟨r, ?_⟩
      have hsq : ((r : ℝ)) ^ 2 = ((a.1 : ℝ) - (b.1 : ℝ)) ^ 2
          + (d : ℝ) * ((a.2 : ℝ) - (b.2 : ℝ)) ^ 2 := by
        rw [hr, Complex.dist_eq_re_im, Real.sq_sqrt (by positivity), hd]
        simp only [coord_re, coord_im]
        ring
      exact_mod_cast hsq
    · rw [Set.image_preimage_eq_of_subset hsub]
      exact hvd
  · rintro ⟨d, y, S, -, hy, hS, hdense⟩
    exact ⟨coord y '' S, hdense, isRatDist_coord_image hy hS⟩

/- ### Removing the scalar `y` from the density condition -/

/-- The homeomorphism of `ℂ` that scales the imaginary axis by `y ≠ 0`. It carries the Gaussian
rationals `coord 1 '' S` onto `coord y '' S`, so density of the latter does not depend on `y`. -/
noncomputable def imScale (y : ℝ) (hy : y ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := ⟨z.re, z.im * y⟩
  invFun z := ⟨z.re, z.im / y⟩
  left_inv z := by apply Complex.ext <;> simp [hy]
  right_inv z := by apply Complex.ext <;> simp [hy]
  continuous_toFun := by
    have h : (fun z : ℂ => (⟨z.re, z.im * y⟩ : ℂ)) =
        fun z : ℂ => ((z.re : ℝ) : ℂ) + ((z.im * y : ℝ) : ℂ) * Complex.I := by
      funext z; apply Complex.ext <;> simp
    rw [h]; fun_prop
  continuous_invFun := by
    have h : (fun z : ℂ => (⟨z.re, z.im / y⟩ : ℂ)) =
        fun z : ℂ => ((z.re : ℝ) : ℂ) + ((z.im / y : ℝ) : ℂ) * Complex.I := by
      funext z; apply Complex.ext <;> simp
    rw [h]; fun_prop

@[simp] theorem imScale_apply (y : ℝ) (hy : y ≠ 0) (z : ℂ) :
    imScale y hy z = ⟨z.re, z.im * y⟩ := rfl

/-- Density of the embedded family does not depend on the scalar `y`: it is exactly density of
`S ⊆ ℚ × ℚ` inside the plane. -/
theorem dense_coord_image_iff {y : ℝ} (hy : y ≠ 0) (S : Set (ℚ × ℚ)) :
    Dense (coord y '' S) ↔ Dense (coord 1 '' S) := by
  have himg : (imScale y hy) '' (coord 1 '' S) = coord y '' S := by
    rw [Set.image_image]
    exact Set.image_congr fun p _ => by apply Complex.ext <;> simp [coord]
  rw [← himg]
  exact (imScale y hy).isDenseEmbedding.dense_image

/-- **Main reduction, fully arithmetic form.** A dense rational-distance subset of the plane
exists if and only if there are a positive rational `d` and a set `S` of pairs of rationals,
dense in the plane, such that the binary quadratic form `(a₁ - a₂) ^ 2 + d * (c₁ - c₂) ^ 2` takes
square values on every pair of points of `S`. No distances, no normalisation, and no irrational
numbers occur on the right-hand side. -/
theorem exists_dense_isRatDist_iff_rat :
    (∃ u : Set ℂ, Dense u ∧ IsRatDist u) ↔
      ∃ (d : ℚ) (S : Set (ℚ × ℚ)), 0 < d ∧
        (∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, r ^ 2 = (p.1 - q.1) ^ 2 + d * (p.2 - q.2) ^ 2) ∧
        Dense (coord 1 '' S) := by
  rw [exists_dense_isRatDist_iff]
  constructor
  · rintro ⟨d, y, S, hd, hy, hS, hdense⟩
    have hyne : y ≠ 0 := by
      rintro rfl
      have h0 : (d : ℝ) = 0 := by rw [← hy]; ring
      have hd0 : d = 0 := by exact_mod_cast h0
      exact absurd hd0 (ne_of_gt hd)
    exact ⟨d, S, hd, hS, (dense_coord_image_iff hyne S).mp hdense⟩
  · rintro ⟨d, S, hd, hS, hdense⟩
    have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hsne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd')
    exact ⟨d, Real.sqrt (d : ℝ), S, hd, Real.sq_sqrt hd'.le, hS,
      (dense_coord_image_iff hsne S).mpr hdense⟩

/- ### Non-vacuity checks -/

/-- The containment produced by `IsRatDist.exists_subset_ratSlice` is *not* by itself a
contradiction: `RatSlice 1` (the Gaussian rationals) is dense in `ℂ`. So the structure theorem
genuinely leaves the arithmetic problem open, as it must. -/
theorem dense_ratSlice_one : Dense (RatSlice 1) := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨a, ha⟩ := exists_rat_near x.re (half_pos hr)
  obtain ⟨c, hc⟩ := exists_rat_near x.im (half_pos hr)
  refine ⟨coord 1 (a, c), ?_, ⟨(a, c), rfl⟩⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  have hle : ‖coord 1 (a, c) - x‖ ≤ |(coord 1 (a, c) - x).re| + |(coord 1 (a, c) - x).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  simp only [Complex.sub_re, Complex.sub_im, coord_re, coord_im, mul_one] at hle
  rw [abs_sub_comm] at ha hc
  linarith

/-- The normalised hypotheses `IsRatDist u`, `0 ∈ u`, `1 ∈ u` are satisfied by an infinite set,
so none of the lemmas above is vacuous. (The witness is the rational line, built through the
construction interface `isRatDist_coord_image`.) -/
theorem exists_infinite_normalized_isRatDist :
    ∃ u : Set ℂ, u.Infinite ∧ IsRatDist u ∧ (0 : ℂ) ∈ u ∧ (1 : ℂ) ∈ u := by
  refine ⟨coord 0 '' Set.univ, ?_, ?_, ⟨(0, 0), Set.mem_univ _, ?_⟩, ⟨(1, 0), Set.mem_univ _, ?_⟩⟩
  · refine Set.infinite_of_injective_forall_mem (f := fun a : ℚ => coord 0 (a, 0)) ?_ ?_
    · intro a b hab
      have := congrArg Complex.re hab
      simpa using this
    · exact fun a => ⟨(a, 0), Set.mem_univ _, rfl⟩
  · refine isRatDist_coord_image (d := 0) (by norm_num) ?_
    intro p _ q _
    exact ⟨|p.1 - q.1|, by rw [sq_abs]; ring⟩
  · apply Complex.ext <;> simp [coord]
  · apply Complex.ext <;> simp [coord]

/- ### Worked use sites against the reward statement -/

/-- **Use site 1.** The reduction, stated with the reward theorem's own right-hand side. -/
theorem erdos_212_iff_diophantine :
    (∃ u : Set ℂ, Dense u ∧ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast) ↔
      ∃ (d : ℚ) (S : Set (ℚ × ℚ)), 0 < d ∧
        (∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, r ^ 2 = (p.1 - q.1) ^ 2 + d * (p.2 - q.2) ^ 2) ∧
        Dense (coord 1 '' S) :=
  exists_dense_isRatDist_iff_rat

/-- **Use site 2.** The positive side of the reduction, in the form that closes the pinned reward
statement. Under the pinned `google.answer = always_true` setting the answer slot of
`Erdos212.erdos_212` elaborates to `True`, so the pinned statement is literally the biconditional
produced here: a solver who builds the arithmetic family closes the target outright. -/
theorem erdos_212_true_iff_of_dense_rational_family
    (H : ∃ (d : ℚ) (S : Set (ℚ × ℚ)), 0 < d ∧
      (∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, r ^ 2 = (p.1 - q.1) ^ 2 + d * (p.2 - q.2) ^ 2) ∧
      Dense (coord 1 '' S)) :
    True ↔ ∃ u : Set ℂ, Dense u ∧ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast :=
  ⟨fun _ => erdos_212_iff_diophantine.mpr H, fun _ => trivial⟩

/-- **Use site 3.** The negative side of the reduction: refuting the Diophantine family refutes
the geometric existential outright, with no geometry left. Note that under the pinned
`google.answer = always_true` setting the answer slot of `Erdos212.erdos_212` elaborates to
`True`, so the pinned statement reads `True ↔ ∃ u, …`; this lemma therefore does *not* prove the
pinned statement — a negative-answer solver must first replace the answer slot by `False`, after
which `¬ ∃ …` closes it. -/
theorem erdos_212_of_no_dense_rational_family
    (H : ∀ (d : ℚ) (S : Set (ℚ × ℚ)), 0 < d →
      (∀ p ∈ S, ∀ q ∈ S, ∃ r : ℚ, r ^ 2 = (p.1 - q.1) ^ 2 + d * (p.2 - q.2) ^ 2) →
      ¬ Dense (coord 1 '' S)) :
    ¬ ∃ u : Set ℂ, Dense u ∧ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast := by
  rintro hcon
  obtain ⟨d, S, hd, hS, hdense⟩ := erdos_212_iff_diophantine.mp hcon
  exact H d S hd hS hdense

/-- **Use site 4.** The countability corollary, phrased directly on the reward theorem's
pairwise predicate. -/
theorem countable_of_erdos_212_predicate {u : Set ℂ}
    (h : u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast) : u.Countable :=
  IsRatDist.countable h

end Contribution.Erdos212RationalDistance
