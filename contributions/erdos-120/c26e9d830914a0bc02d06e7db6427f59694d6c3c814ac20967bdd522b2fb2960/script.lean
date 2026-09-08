import Mathlib
import FormalConjectures.ErdosProblems.«120»

/-!
# Erdős Problem 120: the finite (Steinhaus) case proved, and a normal form for the open case

Target: `Erdos120.erdos_120` — for every infinite `A ⊆ ℝ`, must there be a measurable `E ⊆ ℝ`
of positive measure containing no affine copy `a * A + b` (`a ≠ 0`) of `A`?  This is the Erdős
similarity problem, and it is open.

## The obstacle

The pool file states two theorems and proves neither.  Its companion
`Erdos120.erdos_120.variants.finite_set`, tagged `@[category research solved]`, records the
classical fact (Steinhaus 1920) that the answer is *no* for finite `A`, and the pool file leaves
that statement unproved, closing it with the placeholder tactic.

Mathlib does contain the Steinhaus theorem of [St20], in difference-set form:
`MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos` states `E - E ∈ 𝓝 0` for measurable `E`
of positive Haar measure, and it applies verbatim to `volume` on `ℝ`.  That form settles the
*two-point* case of the companion, since realising the single difference `a * (p - q)` inside
`E - E` places an affine copy of `{p, q}` inside `E`.  Its conclusion constrains one difference
only: it asserts nothing about a configuration of three or more points and fixes no ratio `a`.
The step that the pinned Mathlib does not supply is the passage from a Lebesgue density point to
a union bound over the one-parameter family of affine images of a finite set.  Mathlib has the
density input in ratio-of-measures form (`Besicovitch.ae_tendsto_measure_inter_div`), but
`exact?` closes neither the complement-measure form
`exists_mem_measure_compl_inter_closedBall_le` nor the union bound
`exists_affine_copy_subset_of_finite` below, nor the normalisation
`erdos120For_iff_exists_witness_subset_Icc`.

On the open side, `Erdos120.Erdos120For` quantifies over *all* infinite `A ⊆ ℝ` and over all
measurable `E`, so a solver starts with no normalisation whatsoever: no bound on `A`, no
accumulation point, no bound on the witness set `E`, and no use of the affine freedom that the
problem itself supplies.  Two normalisations are proved below, each as an *equivalence* rather
than a one-way reduction, so that nothing is lost by adopting them: `A` may be taken to be the
range of a strictly decreasing null sequence normalised by `x₀ = 1`, and the witness `E` may be
taken inside `Set.Icc 0 1`.

## What is proved here

* `exists_mem_measure_compl_inter_closedBall_le`: a quantitative Lebesgue density point.  For
  measurable `E` of positive measure and `ε > 0` there are `x ∈ E` and `r₀ > 0` with
  `volume (Eᶜ ∩ closedBall x r) ≤ ENNReal.ofReal (ε * (2 * r))` for all `0 < r < r₀`.
* `exists_affine_copy_subset_of_finite`: **Steinhaus' theorem**, in a form quantified over the
  ratio.  If `E` is measurable with `0 < volume E`, `A` is finite and `η > 0`, then there are
  `a` and `b` with `0 < a < η` and `(fun y => a * y + b) '' A ⊆ E`; so the admissible ratios
  accumulate at `0`, and no finiteness hypothesis on `volume E` is needed (`volume E = ⊤` is
  allowed).
* `not_erdos120For_of_finite`: the pool companion `Erdos120.erdos_120.variants.finite_set`,
  proved outright: `A.Finite → ¬ Erdos120For A`.  (`exact?` does close this statement — with the
  pool's own `Erdos120.erdos_120.variants.finite_set`, which the pool file leaves unproved, so
  that closing term depends on the placeholder constant an incomplete proof emits.  The proof
  given here does not use it: the kernel dependency check on every declaration below returns
  exactly `[propext, Classical.choice, Quot.sound]`.)
* `erdos120For_mono`, `erdos120For_image_affine`, `erdos120For_image_affine_iff`,
  `erdos120For_of_not_bddAbove`, `erdos120For_of_not_bddBelow`: the structural API of
  `Erdos120For` — it is monotone under `⊆`, invariant under the affine group, and it holds
  outright, with the explicit witness `Set.Icc 0 1`, for every set unbounded above or below.
* `bddAbove_and_bddBelow_of_image_subset_Icc`: an affine copy of `A` inside `Set.Icc 0 1` bounds
  `A` on both sides.
* `erdos120For_iff_exists_witness_subset_Icc`: **first normalisation.**  `Erdos120For A` is
  *equivalent* to the existence of a witness `E ⊆ Set.Icc 0 1`; so the witness may always be
  taken bounded, of finite measure, and in a fixed interval.
* `exists_affine_image_accumulating_at_zero`: every infinite bounded `A ⊆ ℝ` has an affine image
  that accumulates at `0` from the right, i.e. there are `a ≠ 0` and `b` with points of
  `a * A + b` in every interval `(0, ε)`.
* `forall_infinite_iff_forall_strictAnti_tendsto_zero`: **second normalisation.**  The
  right-hand side of `Erdos120.erdos_120` is *equivalent* to its restriction to the sets
  `Set.range f` for `f` strictly decreasing with `f 0 = 1`, `f n > 0` and `f n → 0`.
* `forall_infinite_iff_forall_normalised`: the two normalisations combined into one equivalence.
  It is a direct composition of the two preceding equivalences, recorded as the single statement
  a later solver would quote.
* `forall_infinite_iff_forall_erdos120For_iff_infinite` and `use_site_erdos_120_answer_true`:
  worked use sites against the target statement.  The second is a one-step corollary of
  `forall_infinite_iff_forall_normalised`, kept only as the handoff in the exact shape of
  `Erdos120.erdos_120`; it is not independent content.

A later solver can use declaration `Contribution.Erdos120Steinhaus.not_erdos120For_of_finite` to
discharge or simplify obligation `Erdos120.erdos_120.variants.finite_set` (the statement
`A.Finite → ¬ Erdos120For A`, which the pool file leaves unproved) in target
`Erdos120.erdos_120`.  A later solver can use declaration
`Contribution.Erdos120Steinhaus.forall_infinite_iff_forall_normalised` to discharge or simplify
obligation `∀ A : Set ℝ, A.Infinite → Erdos120For A`, the right-hand side of
`Erdos120.erdos_120`, in target `Erdos120.erdos_120`, by replacing it with the same statement for
the ranges of strictly decreasing null sequences normalised by `f 0 = 1` and with the witness
set constrained to lie inside `Set.Icc 0 1`.

*References:*
- [erdosproblems.com/120](https://www.erdosproblems.com/120)
- [St20](http://matwbn.icm.edu.pl/ksiazki/fm/fm1/fm1111.pdf) H. Steinhaus, *Sur les distances des
  points dans les ensembles de mesure positive*, Fund. Math. 1 (1920), 93-104.
-/

open Set MeasureTheory Metric Filter Topology Erdos120

namespace Contribution.Erdos120Steinhaus

/-- A quantitative Lebesgue density point of a measurable set $E$ of positive measure: a point
$x \in E$ such that all small closed balls around $x$ miss $E$ in measure at most
$\varepsilon$ times their length. -/
theorem exists_mem_measure_compl_inter_closedBall_le {E : Set ℝ} (hE : MeasurableSet E)
    (hpos : 0 < volume E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ E, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      volume (Eᶜ ∩ closedBall x r) ≤ ENNReal.ofReal (ε * (2 * r)) := by
  set ε₁ : ℝ := min ε (1 / 2) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε (by norm_num)
  have hε₁' : ε₁ ≤ 1 / 2 := min_le_right _ _
  have hε₁'' : ε₁ ≤ ε := min_le_left _ _
  have hne : volume.restrict E ≠ 0 := by
    intro h
    rw [← Measure.restrict_apply_univ E] at hpos
    rw [h] at hpos
    simp at hpos
  haveI : (ae (volume.restrict E)).NeBot := ae_neBot.2 hne
  obtain ⟨x, hxlim, hxE⟩ :=
    ((Besicovitch.ae_tendsto_measure_inter_div volume E).and (ae_restrict_mem hE)).exists
  refine ⟨x, hxE, ?_⟩
  have hc : (ENNReal.ofReal (1 - ε₁)) < 1 := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    linarith
  have hev := hxlim.eventually_const_lt hc
  rw [(nhdsGT_basis (0 : ℝ)).eventually_iff] at hev
  obtain ⟨r₀, hr₀, hmain⟩ := hev
  refine ⟨r₀, hr₀, fun r hr hrr => ?_⟩
  have hkey := hmain (mem_Ioo.2 ⟨hr, hrr⟩)
  have hV : volume (closedBall x r) = ENNReal.ofReal (2 * r) := Real.volume_closedBall x r
  have hVne : volume (closedBall x r) ≠ 0 := by
    rw [hV]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  have hVtop : volume (closedBall x r) ≠ ⊤ := by rw [hV]; exact ENNReal.ofReal_ne_top
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hVne) (Or.inl hVtop)] at hkey
  have hsplit := measure_inter_add_diff (μ := volume) (closedBall x r) hE
  have hdiff : closedBall x r \ E = Eᶜ ∩ closedBall x r := by
    rw [Set.diff_eq, Set.inter_comm]
  rw [hdiff, Set.inter_comm (closedBall x r) E] at hsplit
  have hstep : ENNReal.ofReal (1 - ε₁) * volume (closedBall x r)
      + volume (Eᶜ ∩ closedBall x r) ≤ volume (closedBall x r) := by
    calc ENNReal.ofReal (1 - ε₁) * volume (closedBall x r) + volume (Eᶜ ∩ closedBall x r)
        ≤ volume (E ∩ closedBall x r) + volume (Eᶜ ∩ closedBall x r) := add_le_add hkey.le le_rfl
      _ = volume (closedBall x r) := hsplit
  have hle := ENNReal.le_sub_of_add_le_left
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVtop) hstep
  refine hle.trans ?_
  rw [hV, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_sub _ (mul_nonneg (by linarith) (by linarith))]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

/-- **Steinhaus' theorem** (the case of Erdős problem 120 settled in [St20]), in a form
quantified over the ratio: a measurable set $E$ of positive measure contains an affine copy
$a A + b$ of every finite set $A$, with a ratio $a$ that may be prescribed positive and smaller
than any given $\eta > 0$. -/
theorem exists_affine_copy_subset_of_finite {E : Set ℝ} (hE : MeasurableSet E)
    (hpos : 0 < volume E) {A : Set ℝ} (hA : A.Finite) {η : ℝ} (hη : 0 < η) :
    ∃ a b : ℝ, 0 < a ∧ a < η ∧ (fun y => a * y + b) '' A ⊆ E := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨η / 2, 0, by linarith, by linarith, by simp⟩
  have hFne : hA.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  set F : Finset ℝ := hA.toFinset with hF
  set a0 : ℝ := F.min' hFne with ha0
  set G : Finset ℝ := F.erase a0 with hG
  have hmem : ∀ t ∈ G, a0 < t := by
    intro t ht
    rcases Finset.mem_erase.1 ht with ⟨hne, htF⟩
    exact lt_of_le_of_ne (F.min'_le t htF) (Ne.symm hne)
  rcases G.eq_empty_or_nonempty with hGe | hGne
  · obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    refine ⟨η / 2, x - η / 2 * a0, by linarith, by linarith, ?_⟩
    rintro y ⟨t, htA, rfl⟩
    show η / 2 * t + (x - η / 2 * a0) ∈ E
    have ht : t = a0 := by
      by_contra h
      have hmemG : t ∈ G := Finset.mem_erase.2 ⟨h, hA.mem_toFinset.2 htA⟩
      rw [hGe] at hmemG
      exact absurd hmemG (Finset.notMem_empty t)
    have hval : η / 2 * t + (x - η / 2 * a0) = x := by rw [ht]; ring
    rw [hval]
    exact hx
  set m : ℝ := G.min' hGne - a0 with hm
  set M : ℝ := G.max' hGne - a0 with hM
  have hmpos : 0 < m := by
    have h := hmem _ (G.min'_mem hGne)
    rw [hm]; linarith
  have hmM : m ≤ M := by
    have h := G.min'_le (G.max' hGne) (G.max'_mem hGne)
    rw [hm, hM]; linarith
  have hMpos : 0 < M := lt_of_lt_of_le hmpos hmM
  have hkpos : 0 < G.card := Finset.card_pos.2 hGne
  have hkR : (0 : ℝ) < (G.card : ℝ) := by exact_mod_cast hkpos
  set ε : ℝ := m / (4 * G.card * M) with hε
  have hεpos : 0 < ε := by
    rw [hε]
    exact div_pos hmpos (by positivity)
  obtain ⟨x, hxE, r₀, hr₀, hdens⟩ := exists_mem_measure_compl_inter_closedBall_le hE hpos hεpos
  -- the pullback formula for the affine maps `c ↦ x + c * s` used below
  have hvolpre : ∀ s : ℝ, s ≠ 0 → ∀ S : Set ℝ,
      volume ((fun c => x + c * s) ⁻¹' S) = ENNReal.ofReal |s⁻¹| * volume S := by
    intro s hs S
    have h : (fun c : ℝ => x + c * s) ⁻¹' S
        = (fun c : ℝ => c * s) ⁻¹' ((fun y : ℝ => x + y) ⁻¹' S) := rfl
    rw [h, Real.volume_preimage_mul_right hs, measure_preimage_add]
  set δ : ℝ := min (r₀ / (2 * M)) (η / 2) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (div_pos hr₀ (by linarith)) (by linarith)
  have hδη : δ ≤ η / 2 := by rw [hδ]; exact min_le_right _ _
  have hδM : δ * M ≤ r₀ / 2 := by
    have h1 : δ ≤ r₀ / (2 * M) := by rw [hδ]; exact min_le_left _ _
    calc δ * M ≤ r₀ / (2 * M) * M := by nlinarith
      _ = r₀ / 2 := by field_simp
  have hdM : volume (Eᶜ ∩ closedBall x (δ * M)) ≤ ENNReal.ofReal (ε * (2 * (δ * M))) := by
    refine hdens (δ * M) (by positivity) ?_
    linarith
  set Bad : ℝ → Set ℝ := fun t => Ioc 0 δ ∩ (fun c => x + c * (t - a0)) ⁻¹' Eᶜ with hBad
  have hbadle : ∀ t ∈ G, volume (Bad t) ≤ ENNReal.ofReal (δ / (2 * G.card)) := by
    intro t ht
    have hst : 0 < t - a0 := sub_pos.2 (hmem t ht)
    have hstM : t - a0 ≤ M := by
      have h := G.le_max' t ht
      rw [hM]; linarith
    have hmst : m ≤ t - a0 := by
      have h := G.min'_le t ht
      rw [hm]; linarith
    have hsub : Bad t ⊆ (fun c => x + c * (t - a0)) ⁻¹' (Eᶜ ∩ closedBall x (δ * M)) := by
      rintro c ⟨⟨hc0, hcδ⟩, hcE⟩
      refine ⟨hcE, ?_⟩
      simp only [mem_closedBall, Real.dist_eq]
      have hxx : x + c * (t - a0) - x = c * (t - a0) := by ring
      rw [hxx, abs_of_nonneg (by positivity)]
      exact mul_le_mul hcδ hstM hst.le hδpos.le
    calc volume (Bad t)
        ≤ volume ((fun c => x + c * (t - a0)) ⁻¹' (Eᶜ ∩ closedBall x (δ * M))) := measure_mono hsub
      _ = ENNReal.ofReal |(t - a0)⁻¹| * volume (Eᶜ ∩ closedBall x (δ * M)) :=
          hvolpre _ hst.ne' _
      _ ≤ ENNReal.ofReal |(t - a0)⁻¹| * ENNReal.ofReal (ε * (2 * (δ * M))) :=
          mul_le_mul le_rfl hdM (zero_le _) (zero_le _)
      _ = ENNReal.ofReal (|(t - a0)⁻¹| * (ε * (2 * (δ * M)))) :=
          (ENNReal.ofReal_mul (abs_nonneg _)).symm
      _ ≤ ENNReal.ofReal (δ / (2 * G.card)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [abs_of_nonneg (by positivity)]
          have h1 : (t - a0)⁻¹ ≤ m⁻¹ := inv_anti₀ hmpos hmst
          have h2 : (0 : ℝ) ≤ ε * (2 * (δ * M)) := by positivity
          calc (t - a0)⁻¹ * (ε * (2 * (δ * M)))
              ≤ m⁻¹ * (ε * (2 * (δ * M))) := mul_le_mul_of_nonneg_right h1 h2
            _ = δ / (2 * G.card) := by rw [hε]; field_simp; ring
  have hcover : volume (⋃ t ∈ G, Bad t) ≤ ENNReal.ofReal (δ / 2) := by
    calc volume (⋃ t ∈ G, Bad t) ≤ ∑ t ∈ G, volume (Bad t) := measure_biUnion_finset_le G Bad
      _ ≤ ∑ _t ∈ G, ENNReal.ofReal (δ / (2 * G.card)) := Finset.sum_le_sum hbadle
      _ = (G.card : ENNReal) * ENNReal.ofReal (δ / (2 * G.card)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (δ / 2) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  have hlt : volume (⋃ t ∈ G, Bad t) < volume (Ioc 0 δ) := by
    rw [Real.volume_Ioc, sub_zero]
    exact lt_of_le_of_lt hcover ((ENNReal.ofReal_lt_ofReal_iff hδpos).2 (by linarith))
  have hnotsub : ¬ (Ioc 0 δ ⊆ ⋃ t ∈ G, Bad t) := fun h => absurd (measure_mono h) (not_le.2 hlt)
  obtain ⟨c, hc, hcnot⟩ := not_subset.1 hnotsub
  refine ⟨c, x - c * a0, hc.1, by linarith [hc.2], ?_⟩
  rintro y ⟨t, htA, rfl⟩
  show c * t + (x - c * a0) ∈ E
  have hval : c * t + (x - c * a0) = x + c * (t - a0) := by ring
  rw [hval]
  by_cases ht : t = a0
  · have hxx : x + c * (t - a0) = x := by rw [ht]; ring
    rw [hxx]
    exact hxE
  · have htG : t ∈ G := Finset.mem_erase.2 ⟨ht, hA.mem_toFinset.2 htA⟩
    by_contra hnot
    refine hcnot (Set.mem_iUnion₂.2 ⟨t, htG, ?_⟩)
    simp only [hBad]
    exact ⟨hc, hnot⟩

/-- The companion `Erdos120.erdos_120.variants.finite_set` of the pool file, proved outright:
Erdős 120 fails for every finite set, by Steinhaus' theorem [St20].  The pool file leaves the
same statement unproved; the proof here is complete. -/
theorem not_erdos120For_of_finite {A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A := by
  rintro ⟨E, hE, hpos, hno⟩
  obtain ⟨a, b, ha, -, hsub⟩ := exists_affine_copy_subset_of_finite hE hpos h one_pos
  exact hno a b ha.ne' hsub

/-- `Erdos120For` is monotone: a positive measure set avoiding all affine copies of `A` also
avoids all affine copies of any superset of `A`. -/
theorem erdos120For_mono {A B : Set ℝ} (hAB : A ⊆ B) (h : Erdos120For A) : Erdos120For B := by
  obtain ⟨E, hE, hpos, hno⟩ := h
  exact ⟨E, hE, hpos, fun a b ha hsub => hno a b ha ((Set.image_mono hAB).trans hsub)⟩

/-- `Erdos120For` is invariant under the affine group: it passes from `A` to `p * A + q`. -/
theorem erdos120For_image_affine {A : Set ℝ} {p q : ℝ} (hp : p ≠ 0) (h : Erdos120For A) :
    Erdos120For ((fun y => p * y + q) '' A) := by
  obtain ⟨E, hE, hpos, hno⟩ := h
  refine ⟨E, hE, hpos, fun a b ha hsub => ?_⟩
  have key : (fun x : ℝ => a * x + b) '' ((fun y : ℝ => p * y + q) '' A)
      = (fun x : ℝ => (a * p) * x + (a * q + b)) '' A := by
    rw [Set.image_image]
    exact Set.image_congr fun y _ => by ring
  rw [key] at hsub
  exact hno (a * p) (a * q + b) (mul_ne_zero ha hp) hsub

/-- Affine invariance of `Erdos120For`, as an equivalence: the property only depends on the
affine equivalence class of `A`. -/
theorem erdos120For_image_affine_iff {A : Set ℝ} {p q : ℝ} (hp : p ≠ 0) :
    Erdos120For ((fun y => p * y + q) '' A) ↔ Erdos120For A := by
  refine ⟨fun h => ?_, erdos120For_image_affine hp⟩
  have h2 := erdos120For_image_affine (A := (fun y => p * y + q) '' A) (p := p⁻¹)
    (q := -(p⁻¹ * q)) (inv_ne_zero hp) h
  have key : (fun y : ℝ => p⁻¹ * y + -(p⁻¹ * q)) '' ((fun y : ℝ => p * y + q) '' A) = A := by
    rw [Set.image_image]
    have hid : (fun y : ℝ => p⁻¹ * (p * y + q) + -(p⁻¹ * q)) = fun y : ℝ => y := by
      funext y
      field_simp
      ring
    rw [hid, Set.image_id']
  rwa [key] at h2

/-- **First normalisation: the witness may be taken inside `Set.Icc 0 1`.**  `Erdos120For A`
asks for *some* measurable set of positive measure containing no affine copy of `A`; this
equivalence shows that such a set can always be found inside the unit interval, hence bounded
and of finite measure.  The forward direction localises a witness to an integer interval, where
some piece must have positive measure, and then translates it to `Set.Icc 0 1`. -/
theorem erdos120For_iff_exists_witness_subset_Icc {A : Set ℝ} :
    Erdos120For A ↔ ∃ E : Set ℝ, E ⊆ Icc 0 1 ∧ MeasurableSet E ∧ 0 < volume E ∧
      ∀ a b : ℝ, a ≠ 0 → ¬ (fun x => a * x + b) '' A ⊆ E := by
  constructor
  · rintro ⟨E, hE, hpos, hno⟩
    have hcover : E ⊆ ⋃ n : ℤ, E ∩ Icc (n : ℝ) ((n : ℝ) + 1) := by
      intro y hy
      exact Set.mem_iUnion.2 ⟨⌊y⌋, hy, Int.floor_le y, (Int.lt_floor_add_one y).le⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, 0 < volume (E ∩ Icc (n : ℝ) ((n : ℝ) + 1)) := by
      by_contra hcon
      push_neg at hcon
      have hnull : volume (⋃ n : ℤ, E ∩ Icc (n : ℝ) ((n : ℝ) + 1)) = 0 :=
        measure_iUnion_null fun n => le_antisymm (hcon n) (zero_le _)
      exact hpos.ne' (le_antisymm ((measure_mono hcover).trans hnull.le) (zero_le _))
    refine ⟨(fun y : ℝ => y + (n : ℝ)) ⁻¹' (E ∩ Icc (n : ℝ) ((n : ℝ) + 1)), ?_, ?_, ?_, ?_⟩
    · intro y hy
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc] at hy
      exact ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩
    · exact (hE.inter measurableSet_Icc).preimage (measurable_add_const _)
    · rwa [measure_preimage_add_right]
    · intro a b ha hsub
      refine hno a (b + (n : ℝ)) ha ?_
      rintro _ ⟨y, hy, rfl⟩
      have hmem : a * y + b ∈ (fun z : ℝ => z + (n : ℝ)) ⁻¹' (E ∩ Icc (n : ℝ) ((n : ℝ) + 1)) :=
        hsub ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Set.mem_inter_iff] at hmem
      show a * y + (b + (n : ℝ)) ∈ E
      have heq : a * y + (b + (n : ℝ)) = a * y + b + (n : ℝ) := by ring
      rw [heq]
      exact hmem.1
  · rintro ⟨E, -, hE, hpos, hno⟩
    exact ⟨E, hE, hpos, hno⟩

/-- If an affine copy of `A` with nonzero ratio fits inside `Set.Icc 0 1`, then `A` is bounded
above and below. -/
theorem bddAbove_and_bddBelow_of_image_subset_Icc {A : Set ℝ} {a b : ℝ} (ha : a ≠ 0)
    (h : (fun x => a * x + b) '' A ⊆ Icc 0 1) : BddAbove A ∧ BddBelow A := by
  have key : ∀ y ∈ A, |y| ≤ (1 + |b|) / |a| := by
    intro y hy
    have hmem : a * y + b ∈ Icc (0 : ℝ) 1 := h ⟨y, hy, rfl⟩
    have h1 : |a * y + b| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hmem.1, hmem.2], hmem.2⟩
    have h3 : |a * y| ≤ |a * y + b| + |b| := by
      calc |a * y| = |(a * y + b) + -b| := by ring_nf
        _ ≤ |a * y + b| + |-b| := abs_add_le _ _
        _ = |a * y + b| + |b| := by rw [abs_neg]
    rw [le_div_iff₀ (abs_pos.2 ha)]
    calc |y| * |a| = |a * y| := by rw [← abs_mul, mul_comm]
      _ ≤ |a * y + b| + |b| := h3
      _ ≤ 1 + |b| := by linarith
  refine ⟨⟨(1 + |b|) / |a|, fun y hy => (le_abs_self y).trans (key y hy)⟩,
    ⟨-((1 + |b|) / |a|), fun y hy => ?_⟩⟩
  have := key y hy
  have hy' := neg_abs_le y
  linarith

/-- Erdős 120 holds, with the explicit witness `Set.Icc 0 1`, for every set that is unbounded
above: a bounded set contains no affine copy of an unbounded one. -/
theorem erdos120For_of_not_bddAbove {A : Set ℝ} (hA : ¬ BddAbove A) : Erdos120For A := by
  refine ⟨Icc 0 1, measurableSet_Icc, ?_, fun a b ha hsub => ?_⟩
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.2 (by norm_num)
  · exact hA (bddAbove_and_bddBelow_of_image_subset_Icc ha hsub).1

/-- Erdős 120 holds, with the explicit witness `Set.Icc 0 1`, for every set that is unbounded
below. -/
theorem erdos120For_of_not_bddBelow {A : Set ℝ} (hA : ¬ BddBelow A) : Erdos120For A := by
  refine ⟨Icc 0 1, measurableSet_Icc, ?_, fun a b ha hsub => ?_⟩
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.2 (by norm_num)
  · exact hA (bddAbove_and_bddBelow_of_image_subset_Icc ha hsub).2

/-- Every infinite bounded set of reals has an affine image that accumulates at $0$ from the
right: there are $a \neq 0$ and $b$ such that $aA+b$ meets every interval $(0,\varepsilon)$.
The accumulation point is produced by `Set.Infinite.exists_accPt_of_subset_isCompact`; the two
cases below record that an accumulation point may be approached from either side, and the
reflection `a = -1` handles the left-hand case. -/
theorem exists_affine_image_accumulating_at_zero {A : Set ℝ} (hA : A.Infinite)
    (hub : BddAbove A) (hlb : BddBelow A) :
    ∃ a b : ℝ, a ≠ 0 ∧ ∀ ε : ℝ, 0 < ε → ∃ y ∈ A, 0 < a * y + b ∧ a * y + b < ε := by
  obtain ⟨u, hu⟩ := hub
  obtain ⟨l, hl⟩ := hlb
  have hsub : A ⊆ Icc l u := fun y hy => ⟨hl hy, hu hy⟩
  obtain ⟨p, -, hp⟩ := hA.exists_accPt_of_subset_isCompact isCompact_Icc hsub
  rw [accPt_iff_nhds] at hp
  have hacc : ∀ ε : ℝ, 0 < ε → ∃ y ∈ A, y ≠ p ∧ |y - p| < ε := by
    intro ε hε
    obtain ⟨y, hy, hyne⟩ := hp (ball p ε) (ball_mem_nhds p hε)
    exact ⟨y, hy.2, hyne, by simpa [Real.dist_eq] using hy.1⟩
  by_cases hright : ∀ ε : ℝ, 0 < ε → ∃ y ∈ A, p < y ∧ y < p + ε
  · refine ⟨1, -p, one_ne_zero, fun ε hε => ?_⟩
    obtain ⟨y, hy, h1, h2⟩ := hright ε hε
    exact ⟨y, hy, by linarith, by linarith⟩
  · push_neg at hright
    obtain ⟨ε₀, hε₀, hno⟩ := hright
    refine ⟨-1, p, by norm_num, fun ε hε => ?_⟩
    obtain ⟨y, hy, hyne, habs⟩ := hacc (min ε ε₀) (lt_min hε hε₀)
    have h1 : |y - p| < ε := lt_of_lt_of_le habs (min_le_left _ _)
    have h2 : |y - p| < ε₀ := lt_of_lt_of_le habs (min_le_right _ _)
    have hylt : y < p := by
      rcases lt_or_gt_of_ne hyne with h | h
      · exact h
      · exact absurd (abs_lt.1 h2).2 (by linarith [hno y hy h])
    refine ⟨y, hy, by linarith, ?_⟩
    have := (abs_lt.1 h1).1
    linarith

/-- **Second normalisation: the set may be taken to be a normalised null sequence.**  The
right-hand side of `Erdos120.erdos_120` is equivalent to its restriction to the ranges of the
strictly decreasing null sequences with $x_0 = 1$, i.e. to the sets $\{x_0, x_1, \dots\}$ with
$1 = x_0 > x_1 > \cdots > 0$ and $x_n \to 0$.  The strictly decreasing sequence inside an
accumulating affine image is extracted with Mathlib's
`IsGLB.exists_seq_strictAnti_tendsto_of_notMem`. -/
theorem forall_infinite_iff_forall_strictAnti_tendsto_zero :
    (∀ A : Set ℝ, A.Infinite → Erdos120For A) ↔
      ∀ f : ℕ → ℝ, StrictAnti f → f 0 = 1 → (∀ n, 0 < f n) → Tendsto f atTop (𝓝 0) →
        Erdos120For (Set.range f) := by
  refine ⟨fun h f hf _ _ _ => h _ (Set.infinite_range_of_injective hf.injective), fun h A hA => ?_⟩
  by_cases hub : BddAbove A
  · by_cases hlb : BddBelow A
    · obtain ⟨a, b, ha, hacc⟩ := exists_affine_image_accumulating_at_zero hA hub hlb
      have hacc' : ∀ ε : ℝ, 0 < ε → ∃ z ∈ (fun y => a * y + b) '' A, 0 < z ∧ z < ε := by
        intro ε hε
        obtain ⟨y, hy, h1, h2⟩ := hacc ε hε
        exact ⟨a * y + b, ⟨y, hy, rfl⟩, h1, h2⟩
      have htne : ((fun y => a * y + b) '' A ∩ Ioi 0).Nonempty := by
        obtain ⟨z, hzB, hz0, -⟩ := hacc' 1 one_pos
        exact ⟨z, hzB, hz0⟩
      have hglb : IsGLB ((fun y => a * y + b) '' A ∩ Ioi 0) 0 := by
        constructor
        · rintro z ⟨-, hz⟩
          exact le_of_lt hz
        · intro c hc
          by_contra hlt
          push_neg at hlt
          obtain ⟨z, hzB, hz0, hz1⟩ := hacc' c hlt
          exact absurd (hc ⟨hzB, hz0⟩) (not_le.2 hz1)
      have hnotmem : (0 : ℝ) ∉ (fun y => a * y + b) '' A ∩ Ioi 0 :=
        fun hx => lt_irrefl (0 : ℝ) hx.2
      obtain ⟨f, hmono, hfpos, htend, hmemt⟩ :=
        hglb.exists_seq_strictAnti_tendsto_of_notMem hnotmem htne
      have hmem : ∀ n, f n ∈ (fun y => a * y + b) '' A := fun n => (hmemt n).1
      have hc : (0 : ℝ) < (f 0)⁻¹ := inv_pos.2 (hfpos 0)
      have hnorm : Erdos120For (Set.range fun n => (f 0)⁻¹ * f n + 0) := by
        refine h _ (fun i j hij => ?_) (by simp [inv_mul_cancel₀ (hfpos 0).ne'])
          (fun n => by simpa using mul_pos hc (hfpos n)) ?_
        · have h3 : f j < f i := hmono hij
          have h4 : (f 0)⁻¹ * f j < (f 0)⁻¹ * f i := mul_lt_mul_of_pos_left h3 hc
          simpa using h4
        · have h2 := htend.const_mul ((f 0)⁻¹)
          simpa using h2
      have himg : (fun y : ℝ => (f 0)⁻¹ * y + 0) '' Set.range f
          = Set.range fun n => (f 0)⁻¹ * f n + 0 := (Set.range_comp _ _).symm
      have hrf : Erdos120For (Set.range f) :=
        (erdos120For_image_affine_iff (A := Set.range f) (p := (f 0)⁻¹) (q := 0)
          hc.ne').1 (himg ▸ hnorm)
      have hrange : Set.range f ⊆ (fun y => a * y + b) '' A := by
        rintro _ ⟨n, rfl⟩
        exact hmem n
      exact (erdos120For_image_affine_iff (A := A) (p := a) (q := b) ha).1
        (erdos120For_mono hrange hrf)
    · exact erdos120For_of_not_bddBelow hlb
  · exact erdos120For_of_not_bddAbove hub

/-- **The normal form.**  Both normalisations at once: the right-hand side of
`Erdos120.erdos_120` is *equivalent* to the statement that for every strictly decreasing null
sequence `f` with `f 0 = 1` there is a positive-measure measurable `E ⊆ Set.Icc 0 1` containing
no affine copy of `Set.range f`.  Being an equivalence, this loses nothing: a solver may assume
the normalisation and still be proving the target. -/
theorem forall_infinite_iff_forall_normalised :
    (∀ A : Set ℝ, A.Infinite → Erdos120For A) ↔
      ∀ f : ℕ → ℝ, StrictAnti f → f 0 = 1 → (∀ n, 0 < f n) → Tendsto f atTop (𝓝 0) →
        ∃ E : Set ℝ, E ⊆ Icc 0 1 ∧ MeasurableSet E ∧ 0 < volume E ∧
          ∀ a b : ℝ, a ≠ 0 → ¬ (fun x => a * x + b) '' Set.range f ⊆ E := by
  constructor
  · intro h f h1 h2 h3 h4
    exact erdos120For_iff_exists_witness_subset_Icc.1
      (forall_infinite_iff_forall_strictAnti_tendsto_zero.1 h f h1 h2 h3 h4)
  · intro h
    exact forall_infinite_iff_forall_strictAnti_tendsto_zero.2 fun f h1 h2 h3 h4 =>
      erdos120For_iff_exists_witness_subset_Icc.2 (h f h1 h2 h3 h4)

/-- **Use site (sharp form).**  A positive answer to `Erdos120.erdos_120` is equivalent to the
statement that `Erdos120For` characterises infinitude: no strengthening of the hypothesis
`A.Infinite` in the target is possible, because `Erdos120For A` already fails for every finite
`A`. -/
theorem forall_infinite_iff_forall_erdos120For_iff_infinite :
    (∀ A : Set ℝ, A.Infinite → Erdos120For A) ↔ ∀ A : Set ℝ, Erdos120For A ↔ A.Infinite := by
  refine ⟨fun h A => ⟨fun hA => ?_, h A⟩, fun h A hA => (h A).2 hA⟩
  by_contra hfin
  exact not_erdos120For_of_finite (Set.not_infinite.1 hfin) hA

/-- **Use site (target statement).**  This is `Erdos120.erdos_120` with its unknown answer
instantiated to `True`: proving the normal form `forall_infinite_iff_forall_normalised` for
normalised strictly decreasing null sequences, with the witness constrained to `Set.Icc 0 1`,
settles the target affirmatively.  It is a one-step corollary of that equivalence, recorded
here only because it is the handoff in the exact shape of the target statement. -/
theorem use_site_erdos_120_answer_true
    (h : ∀ f : ℕ → ℝ, StrictAnti f → f 0 = 1 → (∀ n, 0 < f n) → Tendsto f atTop (𝓝 0) →
      ∃ E : Set ℝ, E ⊆ Icc 0 1 ∧ MeasurableSet E ∧ 0 < volume E ∧
        ∀ a b : ℝ, a ≠ 0 → ¬ (fun x => a * x + b) '' Set.range f ⊆ E) :
    True ↔ ∀ A : Set ℝ, A.Infinite → Erdos120For A :=
  iff_of_true trivial (forall_infinite_iff_forall_normalised.2 h)

end Contribution.Erdos120Steinhaus
