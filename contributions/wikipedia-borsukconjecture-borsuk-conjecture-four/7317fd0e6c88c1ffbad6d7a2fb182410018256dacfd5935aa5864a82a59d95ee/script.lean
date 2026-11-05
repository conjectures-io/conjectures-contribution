import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A five-sector cover for diameter-normalized sets whose projection onto a
coordinate two-plane has small diameter. The enclosing ball couples the
horizontal and vertical radii, yielding the sufficient condition 2 R D < 1. -/
namespace Contribution.BorsukFiveSectors
open Real
abbrev E := EuclideanSpace ℝ (Fin 4)
noncomputable def a (x : E) : ℂ := ⟨x 0,x 1⟩
noncomputable def b (x : E) : ℂ := ⟨x 2,x 3⟩
def sector (j : Fin 5) (θ : ℝ) : Prop :=
  -π + (j.val:ℝ)*(2*π/5) ≤ θ ∧ θ ≤ -π + ((j.val:ℝ)+1)*(2*π/5)

theorem sectors_cover (z : ℂ) : ∃ j : Fin 5, sector j z.arg := by
  have h := z.arg_mem_Ioc
  obtain ⟨hl,hu⟩ := h
  by_cases h0 : z.arg ≤ -3*π/5
  · refine ⟨0,?_⟩; norm_num [sector]; constructor <;> linarith
  by_cases h1 : z.arg ≤ -π/5
  · refine ⟨1,?_⟩; norm_num [sector]; constructor <;> linarith
  by_cases h2 : z.arg ≤ π/5
  · refine ⟨2,?_⟩; norm_num [sector]; constructor <;> linarith
  by_cases h3 : z.arg ≤ 3*π/5
  · refine ⟨3,?_⟩; norm_num [sector]; constructor <;> linarith
  refine ⟨4,?_⟩; norm_num [sector]; constructor <;> linarith

theorem cos72 : cos (2*π/5)=(sqrt 5-1)/4 := by
  rw [show 2*π/5=2*(π/5) by ring,cos_two_mul,cos_pi_div_five]
  nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]

theorem polar_sq (z w : ℂ) : ‖z-w‖^2 = ‖z‖^2+‖w‖^2-2*‖z‖*‖w‖*cos (z.arg-w.arg) := by
  calc
    ‖z-w‖^2 = ‖z‖^2+‖w‖^2-2*(z.re*w.re+z.im*w.im) := by
      rw [Complex.sq_norm (z-w),Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
      nlinarith only [Complex.sq_norm_sub_sq_re z,Complex.sq_norm_sub_sq_re w]
    _ = _ := by
      rw [cos_sub,←Complex.norm_mul_cos_arg z,←Complex.norm_mul_cos_arg w,
        ←Complex.norm_mul_sin_arg z,←Complex.norm_mul_sin_arg w]; ring

private theorem split_sq (x y : E) : dist x y^2=‖a x-a y‖^2+‖b x-b y‖^2 := by
  rw [EuclideanSpace.dist_sq_eq,Complex.sq_norm,Complex.sq_norm]
  simp [Fin.sum_univ_succ, Real.dist_eq, sq_abs, a, b, Complex.normSq_apply]
  ring

/-- For large total perpendicular reach p+q, the positive cosine of a sector
offsets both radial losses. -/
private theorem product_estimate (R p q u v : ℝ)
    (hR : 0 ≤ R) (hq : 0 ≤ q) (hpr : p ≤ R) (hqr : q ≤ R)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hup : R^2-p^2 ≤ u^2) (hvq : R^2-q^2 ≤ v^2)
    (hbig : 6*R ≤ 5*(p+q)) : 4*(R-p)*(R-q) ≤ u*v := by
  have h0 : (R+p)*(R+q) ≥ 16*(R-p)*(R-q) := by
    have hf := mul_nonneg (sub_nonneg.mpr hbig)
      (show 0 ≤ 10*R-3*(p+q) by linarith)
    nlinarith only [hf, sq_nonneg (p-q)]
  have h1 := mul_le_mul_of_nonneg_right h0 (mul_nonneg (sub_nonneg.mpr hpr) (sub_nonneg.mpr hqr))
  apply (sq_le_sq₀ (by positivity : 0 ≤ 4*(R-p)*(R-q)) (mul_nonneg hu hv)).mp
  calc
    (4*(R-p)*(R-q))^2 ≤ ((R+p)*(R+q))*((R-p)*(R-q)) := by nlinarith only [h1]
    _ = (R^2-p^2)*(R^2-q^2) := by ring
    _ ≤ (u*v)^2 := by
      rw [mul_pow]
      exact mul_le_mul hup hvq (by linarith [(sq_le_sq₀ hq hR).2 hqr]) (sq_nonneg _)

theorem coupled_radial (R p q u v d D h : ℝ)
    (hR : 0 ≤ R) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpr : p ≤ R) (hqr : q ≤ R)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ d)
    (hup : u^2 = R^2-p^2) (hvq : v^2 = R^2-q^2)
    (hdp : d ≤ p+q) (hdD : d ≤ D)
    (hh : h ≤ u^2+v^2-u*v/2) :
    h+d^2 ≤ max (12/5*R^2) (2*R*D) := by
  by_cases hsmall : 5*(p+q) ≤ 6*R
  · apply le_trans _ (le_max_left _ _)
    let P := max p (R/5)
    let Q := 6*R/5-P
    have hp' : p ≤ P := le_max_left _ _
    have hP : P ≤ R := max_le hpr (by linarith)
    have hQ : Q ≤ R := by dsimp [Q]; linarith only [le_max_right p (R/5)]
    have hq' : q ≤ Q := by
      have h : P ≤ 6*R/5-q := max_le (by linarith only [hsmall]) (by linarith only [hqr])
      dsimp [Q]; linarith only [h]
    have hP0 := hp.trans hp'
    have hQ0 := hq.trans hq'
    have hsum : P+Q = 6*R/5 := by dsimp [Q]; ring
    have hbound := product_estimate R P Q u v hR hQ0 hP hQ hu hv
      (by linarith only [(sq_le_sq₀ hp hP0).2 hp',hup])
      (by linarith only [(sq_le_sq₀ hq hQ0).2 hq',hvq]) (by rw [hsum]; linarith)
    have hpq : d^2 ≤ (p+q)^2 := (sq_le_sq₀ hd (by positivity)).2 hdp
    have hpq' := mul_le_mul hp' hq' hq hP0
    nlinarith only [hbound,hpq,hpq',hh,hup,hvq,congrArg (fun t:ℝ => R*t) hsum]
  · have hbig := product_estimate R p q u v hR hq hpr hqr hu hv hup.ge hvq.ge (not_le.mp hsmall).le
    have hfactor : h ≤ 2*R*(p+q)-(p+q)^2 := by
      nlinarith only [hh,hup,hvq,hbig]
    by_cases hdR : d ≤ R
    · apply le_trans _ (le_max_left _ _)
      have hd2 := (sq_le_sq₀ hd hR).2 hdR
      nlinarith only [hd2,hfactor,sq_nonneg (p+q-R),sq_nonneg R]
    · apply le_trans _ (le_max_right _ _)
      have hm := mul_nonneg (sub_nonneg.mpr hdp)
        (show 0 ≤ p+q+d-2*R by linarith [not_le.mp hdR])
      nlinarith only [hfactor,hm,mul_le_mul_of_nonneg_left hdD hR]

private theorem sector_horizontal (z w : ℂ) (j : Fin 5)
    (hz : sector j z.arg) (hw : sector j w.arg) :
    ‖z-w‖^2 ≤ ‖z‖^2+‖w‖^2-‖z‖*‖w‖/2 := by
  obtain ⟨hz0,hz1⟩ := hz
  obtain ⟨hw0,hw1⟩ := hw
  have ha : |z.arg-w.arg| ≤ 2*π/5 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    (by linarith [Real.pi_pos] : 2*π/5 ≤ π) ha
  rw [Real.cos_abs,cos72] at hc
  have hquarter : 1/4 ≤ cos (z.arg-w.arg) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5),Real.sqrt_nonneg (5:ℝ)]
  rw [polar_sq]
  nlinarith only [mul_nonneg (mul_nonneg (norm_nonneg z) (norm_nonneg w)) (sub_nonneg.mpr hquarter)]

/-- No support assumptions: a radius bound for the whole body and a diameter
bound for an orthogonal planar projection suffice. -/
theorem sector_cover_of_projected_diameter (K : Set E) (R D : ℝ)
    (hR : 0 ≤ R) (hball : ∀ x ∈ K, ‖a x‖^2+‖b x‖^2 ≤ R^2)
    (hproj : ∀ x ∈ K, ∀ y ∈ K, ‖b x-b y‖ ≤ D)
    (hrad : 12/5*R^2 < 1) (hbudget : 2*R*D < 1) :
    ∃ T : Fin 5 → Set E, (∀ j, T j ⊆ K) ∧ (K ⊆ ⋃ j,T j) ∧ ∀ j, Metric.ediam (T j)<1 := by
  let T : Fin 5 → Set E := fun j => {x | x∈K ∧ sector j (a x).arg}
  refine ⟨T,fun _ _ h => h.1,?_,?_⟩
  · intro x hx; obtain ⟨i,hi⟩ := sectors_cover (a x)
    exact Set.mem_iUnion.mpr ⟨i,hx,hi⟩
  let U := max (12/5*R^2) (2*R*D)
  have hU : 0≤U := le_trans (by positivity) (le_max_left _ _)
  have hU' : U<1 := max_lt hrad hbudget
  intro j
  apply lt_of_le_of_lt (b := ENNReal.ofReal (sqrt U))
  · apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    let reach (z:E) := sqrt (R^2-‖a z‖^2)
    have prop (z : E) (hz : z∈K) :
        ‖b z‖ ≤ reach z ∧ reach z ≤ R ∧ ‖a z‖^2 = R^2-(reach z)^2 := by
      have hgap : 0 ≤ R^2-‖a z‖^2 := by linarith [hball z hz,sq_nonneg ‖b z‖]
      have hsq : (reach z)^2 = R^2-‖a z‖^2 := Real.sq_sqrt hgap
      refine ⟨(sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp ?_,
        (sq_le_sq₀ (sqrt_nonneg _) hR).mp ?_, by linarith only [hsq]⟩
      · linarith only [hsq,hball z hz]
      · linarith only [hsq,sq_nonneg ‖a z‖]
    have px := prop x hx.1
    have py := prop y hy.1
    have hd : ‖b x-b y‖ ≤ reach x+reach y :=
      (norm_sub_le _ _).trans (add_le_add px.1 py.1)
    have h := coupled_radial R (reach x) (reach y) ‖a x‖ ‖a y‖ ‖b x-b y‖ D (‖a x-a y‖^2)
      hR (sqrt_nonneg _) (sqrt_nonneg _) px.2.1 py.2.1 (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) px.2.2 py.2.2 hd (hproj x hx.1 y hy.1)
      (sector_horizontal _ _ j hx.2 hy.2)
    apply (sq_le_sq₀ dist_nonneg (sqrt_nonneg _)).mp
    rw [split_sq,Real.sq_sqrt hU]
    exact h
  · rw [← ENNReal.ofReal_one]
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1)).2
    apply (sq_lt_sq₀ (sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [Real.sq_sqrt hU]; linarith only [hU']

theorem sector_cover_below_three_sixteenths (K : Set E) (center : ℂ) (s : ℝ)
    (hs : 0≤s) (hs' : s<3/16)
    (hball : ∀ x ∈ K, ‖a x‖^2+‖b x‖^2 ≤ 1/3)
    (hproj : ∀ x ∈ K, ‖b x-center‖^2 ≤ s) :
    ∃ T : Fin 5 → Set E, (∀ j, T j ⊆ K) ∧ (K ⊆ ⋃ j,T j) ∧ ∀ j, Metric.ediam (T j)<1 := by
  let R := sqrt (1/3 : ℝ)
  have hR : R^2 = 1/3 := Real.sq_sqrt (by norm_num)
  apply sector_cover_of_projected_diameter K R (2*sqrt s) (sqrt_nonneg _)
  · rwa [hR]
  · intro x hx y hy
    have h (z:E) (hz : z∈K) : ‖b z-center‖ ≤ sqrt s := by
      apply (sq_le_sq₀ (norm_nonneg _) (sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hs]; exact hproj z hz
    calc
      ‖b x-b y‖ = ‖(b x-center)-(b y-center)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
      _ ≤ 2*sqrt s := by linarith only [h x hx,h y hy]
  · rw [hR]; norm_num
  · have hR0 : 0≤R := sqrt_nonneg _
    apply (sq_lt_sq₀ (by positivity) (by norm_num : (0:ℝ) ≤ 1)).mp
    simp only [mul_pow,Real.sq_sqrt hs,hR]
    linarith only [hs']

/-- A normalized Borsuk special case with a strict extended-diameter conclusion.
The center of the projected disk can be chosen independently of the outer ball. -/
theorem five_cover_of_small_planar_projection (K : Set E) (unit : Metric.ediam K = 1)
    (ball : ∀ x ∈ K, ‖x‖^2 ≤ 1/3) (center : ℂ) (s : ℝ) (hs : 0 ≤ s) (hs' : s < 3/16)
    (proj : ∀ x ∈ K, ‖b x - center‖^2 ≤ s) :
    ∃ T : Fin 5 → Set E, (∀ j, T j ⊆ K) ∧ K ⊆ ⋃ j,T j ∧
      ∀ j, Metric.ediam (T j) < Metric.ediam K := by
  rw [unit]
  apply sector_cover_below_three_sixteenths K center s hs hs' _ proj
  intro x hx
  have hsplit : ‖x‖^2 = ‖a x‖^2 + ‖b x‖^2 := by
    simpa only [dist_zero_right, show a 0 = 0 from rfl, show b 0 = 0 from rfl, sub_zero] using split_sq x 0
  rw [←hsplit]
  exact ball x hx

end Contribution.BorsukFiveSectors
