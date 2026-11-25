import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Gauss's Circle Problem: Known Bounds and Jacobi's Exact Formula

Self-contained Lean 4 proofs of the two `[research solved]` theorems in
`FormalConjectures/Wikipedia/GaussCircleProblem.lean`:
1. `error_le`: Gauss's classical error bound `|N r - π * r ^ 2| ≤ 2 * √2 * π * r` for all large `r`
   (`r ≥ 1`), proved by covering/packing unit squares of Lebesgue measure `1` centered at the
   lattice points `(m, n) ∈ ℤ × ℤ`.
2. `exact_form_floor`: Jacobi's exact floor formula
   `N r = 1 + 4 * ∑' i, (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)` for `0 ≤ r`,
   proved from the divisor-sum representation `r₂(k) = 4 ∑_{d ∣ k} χ₄(d)` via coprime
   multiplicativity in `ℤ[i]` and explicit prime-power evaluations.
-/

namespace Contribution.GaussCircleProblem

open Filter
open scoped Real ENNReal

/--
Number of integer lattice points `(m, n) : ℤ × ℤ` in the closed ball of radius `r` centered at `0`.
Matches `GaussCircleProblem.N` definitionally.
-/
noncomputable abbrev N (r : ℝ) : ℕ :=
  { (m, n) : ℤ × ℤ | !₂[(m : ℝ), (n : ℝ)] ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r }.ncard

/--
Error term `E r = N r - π * r ^ 2`.
Matches `GaussCircleProblem.E` definitionally.
-/
noncomputable abbrev E (r : ℝ) : ℝ := N r - π * r ^ 2

/-! ### Shared Finite Lattice Representation for `N r` -/

private noncomputable def latticeFinset (M : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M).filter
    (fun p => p.1 ^ 2 + p.2 ^ 2 ≤ (M : ℤ))

private lemma abs_le_of_sq_le_natCast {x : ℤ} {M : ℕ} (h : x ^ 2 ≤ (M : ℤ)) :
    -(M : ℤ) ≤ x ∧ x ≤ (M : ℤ) := by
  have hM : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  constructor
  · by_contra hlt
    have h1 : x ≤ -(M : ℤ) - 1 := by omega
    nlinarith only [h, h1, hM]
  · by_contra hlt
    have h1 : (M : ℤ) + 1 ≤ x := by omega
    nlinarith only [h, h1, hM]

private lemma mem_latticeFinset_iff {M : ℕ} {p : ℤ × ℤ} :
    p ∈ latticeFinset M ↔ p.1 ^ 2 + p.2 ^ 2 ≤ (M : ℤ) := by
  unfold latticeFinset
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨fun h => h.2, fun h => ⟨⟨?_, ?_⟩, h⟩⟩
  · exact abs_le_of_sq_le_natCast (le_trans (le_add_of_nonneg_right (sq_nonneg p.2)) h)
  · exact abs_le_of_sq_le_natCast (le_trans (le_add_of_nonneg_left (sq_nonneg p.1)) h)

private lemma mem_closedBall_lattice_iff {r : ℝ} (hr : 0 ≤ r) (p : ℤ × ℤ) :
    !₂[(p.1 : ℝ), (p.2 : ℝ)] ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ↔
      p ∈ latticeFinset ⌊r ^ 2⌋₊ := by
  rw [EuclideanSpace.closedBall_zero_eq r hr, Set.mem_ofPred_eq, Fin.sum_univ_two,
    mem_latticeFinset_iff]
  have h0 : (!₂[(p.1 : ℝ), (p.2 : ℝ)] : EuclideanSpace ℝ (Fin 2)) 0 = p.1 := rfl
  have h1 : (!₂[(p.1 : ℝ), (p.2 : ℝ)] : EuclideanSpace ℝ (Fin 2)) 1 = p.2 := rfl
  rw [h0, h1]
  have hnonneg : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  constructor
  · intro hle
    have hnat : ((p.1 ^ 2 + p.2 ^ 2).toNat : ℝ) ≤ r ^ 2 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg]
      exact_mod_cast hle
    have hfl : (p.1 ^ 2 + p.2 ^ 2).toNat ≤ ⌊r ^ 2⌋₊ := (Nat.le_floor_iff (sq_nonneg r)).mpr hnat
    rwa [← Int.ofNat_le, Int.toNat_of_nonneg hnonneg] at hfl
  · intro hle
    have hto : (p.1 ^ 2 + p.2 ^ 2).toNat ≤ ⌊r ^ 2⌋₊ := by
      rwa [← Int.ofNat_le, Int.toNat_of_nonneg hnonneg]
    have hreal : ((p.1 ^ 2 + p.2 ^ 2).toNat : ℝ) ≤ r ^ 2 := (Nat.le_floor_iff (sq_nonneg r)).mp hto
    have hcast : ((p.1 ^ 2 + p.2 ^ 2 : ℤ) : ℝ) = ((p.1 ^ 2 + p.2 ^ 2).toNat : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg]
    push_cast at hcast
    linarith only [hreal, hcast]

private lemma N_eq_card_latticeFinset {r : ℝ} (hr : 0 ≤ r) :
    N r = (latticeFinset ⌊r ^ 2⌋₊).card := by
  unfold N
  have hset :
      { (m, n) : ℤ × ℤ |
          !₂[(m : ℝ), (n : ℝ)] ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r } =
        (latticeFinset ⌊r ^ 2⌋₊ : Set (ℤ × ℤ)) := by
    ext ⟨m, n⟩
    exact mem_closedBall_lattice_iff hr (m, n)
  rw [hset, Set.ncard_coe_finset]

/-! ### Part 1: Gauss's Error Bound `|E r| ≤ 2 * √2 * π * r` -/

section ErrorBound

open MeasureTheory

private def unitSquareBox (m n : ℤ) : Set (Fin 2 → ℝ) :=
  Set.pi Set.univ fun i =>
    if i = 0 then Set.Ico ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2)
    else Set.Ico ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2)

private def unitSquare (m n : ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  { x | (x : EuclideanSpace ℝ (Fin 2)) 0 ∈ Set.Ico ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) ∧
        (x : EuclideanSpace ℝ (Fin 2)) 1 ∈ Set.Ico ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) }

private lemma unitSquare_eq_preimage (m n : ℤ) :
    unitSquare m n = (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm ⁻¹' unitSquareBox m n := by
  ext x
  simp only [unitSquare, unitSquareBox, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi,
    Fin.forall_fin_two]
  rfl

private lemma measurableSet_unitSquareBox (m n : ℤ) : MeasurableSet (unitSquareBox m n) := by
  unfold unitSquareBox
  refine MeasurableSet.univ_pi fun i => ?_
  fin_cases i <;> simp [measurableSet_Ico]

private lemma measurableSet_unitSquare (m n : ℤ) : MeasurableSet (unitSquare m n) := by
  rw [unitSquare_eq_preimage]
  exact (measurableSet_unitSquareBox m n).preimage
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurable

private lemma volume_unitSquare (m n : ℤ) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))) (unitSquare m n) = 1 := by
  rw [unitSquare_eq_preimage]
  rw [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).measure_preimage
    (measurableSet_unitSquareBox m n).nullMeasurableSet]
  unfold unitSquareBox
  rw [MeasureTheory.volume_pi_pi, Fin.prod_univ_two]
  simp [Real.volume_Ico]
  norm_num

private lemma unitSquare_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (ℤ × ℤ)) fun p => unitSquare p.1 p.2 := by
  rintro ⟨m₁, n₁⟩ _ ⟨m₂, n₂⟩ _ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hm₁, hn₁⟩ ⟨hm₂, hn₂⟩
  dsimp only at hm₁ hn₁ hm₂ hn₂
  have hm : m₁ = m₂ := by
    have h1 : (m₁ : ℤ) < m₂ + 1 := by
      exact_mod_cast (by linarith [hm₁.1, hm₂.2] : (m₁ : ℝ) < (m₂ : ℝ) + 1)
    have h2 : (m₂ : ℤ) < m₁ + 1 := by
      exact_mod_cast (by linarith [hm₂.1, hm₁.2] : (m₂ : ℝ) < (m₁ : ℝ) + 1)
    omega
  have hn : n₁ = n₂ := by
    have h1 : (n₁ : ℤ) < n₂ + 1 := by
      exact_mod_cast (by linarith [hn₁.1, hn₂.2] : (n₁ : ℝ) < (n₂ : ℝ) + 1)
    have h2 : (n₂ : ℤ) < n₁ + 1 := by
      exact_mod_cast (by linarith [hn₂.1, hn₁.2] : (n₂ : ℝ) < (n₁ : ℝ) + 1)
    omega
  exact hne (Prod.ext hm hn)

private lemma dist_unitSquare_le {m n : ℤ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ unitSquare m n) :
    dist x !₂[(m : ℝ), (n : ℝ)] ≤ √2 / 2 := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have hx0 : |x 0 - m| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
  have hx1 : |x 1 - n| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  have hd0 : dist (x 0) ((!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 ≤ 1 / 4 := by
    rw [Real.dist_eq]
    change |x 0 - m| ^ 2 ≤ 1 / 4
    nlinarith [hx0, abs_nonneg (x 0 - m)]
  have hd1 : dist (x 1) ((!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2 ≤ 1 / 4 := by
    rw [Real.dist_eq]
    change |x 1 - n| ^ 2 ≤ 1 / 4
    nlinarith [hx1, abs_nonneg (x 1 - n)]
  have hsum : dist (x 0) ((!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
      dist (x 1) ((!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2 ≤ 1 / 2 := by
    linarith
  calc
    √(dist (x 0) ((!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
        dist (x 1) ((!₂[(m : ℝ), (n : ℝ)] : EuclideanSpace ℝ (Fin 2)) 1) ^ 2)
        ≤ √(1 / 2 : ℝ) := Real.sqrt_le_sqrt hsum
    _ = √2 / 2 := by
        rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
        have hsqrt2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
        field_simp
        nlinarith [hsqrt2]

private lemma error_le_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    |E r| ≤ 2 * √2 * π * r := by
  have hr0 : 0 ≤ r := by linarith
  have hsqrt2_lt : √2 / 2 ≤ 1 := by
    have : √2 ≤ 2 := by
      have hsq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    linarith
  have hr_sub_nonneg : 0 ≤ r - √2 / 2 := by linarith
  have hr_add_nonneg : 0 ≤ r + √2 / 2 := by
    have : 0 ≤ √2 := Real.sqrt_nonneg 2
    linarith
  let L := latticeFinset ⌊r ^ 2⌋₊
  let U : Set (EuclideanSpace ℝ (Fin 2)) := ⋃ p ∈ L, unitSquare p.1 p.2
  have hvolU : (volume : Measure (EuclideanSpace ℝ (Fin 2))) U = (N r : ℝ≥0∞) := by
    unfold U
    rw [measure_biUnion_finset (unitSquare_pairwiseDisjoint.subset (Set.subset_univ _))
      (fun p _ => measurableSet_unitSquare p.1 p.2)]
    simp_rw [volume_unitSquare]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, N_eq_card_latticeFinset hr0]
  have hsub_inner : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (r - √2 / 2) ⊆ U := by
    intro x hx
    let m : ℤ := ⌊x 0 + 1 / 2⌋
    let n : ℤ := ⌊x 1 + 1 / 2⌋
    have hx0 : x 0 ∈ Set.Ico ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2) := by
      refine ⟨?_, ?_⟩
      · linarith [Int.floor_le (x 0 + 1 / 2)]
      · linarith [Int.lt_floor_add_one (x 0 + 1 / 2)]
    have hx1 : x 1 ∈ Set.Ico ((n : ℝ) - 1 / 2) ((n : ℝ) + 1 / 2) := by
      refine ⟨?_, ?_⟩
      · linarith [Int.floor_le (x 1 + 1 / 2)]
      · linarith [Int.lt_floor_add_one (x 1 + 1 / 2)]
    have hxsq : x ∈ unitSquare m n := ⟨hx0, hx1⟩
    have hdist : dist !₂[(m : ℝ), (n : ℝ)] (0 : EuclideanSpace ℝ (Fin 2)) ≤ r := by
      calc
        dist !₂[(m : ℝ), (n : ℝ)] (0 : EuclideanSpace ℝ (Fin 2))
            ≤ dist !₂[(m : ℝ), (n : ℝ)] x + dist x 0 := dist_triangle _ _ _
        _ = dist x !₂[(m : ℝ), (n : ℝ)] + dist x 0 := by rw [dist_comm]
        _ ≤ √2 / 2 + (r - √2 / 2) := add_le_add (dist_unitSquare_le hxsq) (Metric.mem_closedBall.mp hx)
        _ = r := by ring
    have hpL : (m, n) ∈ L :=
      (mem_closedBall_lattice_iff hr0 (m, n)).mp (Metric.mem_closedBall.mpr hdist)
    exact Set.mem_biUnion hpL hxsq
  have hsub_outer : U ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (r + √2 / 2) := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨⟨m, n⟩, hpL, hxsq⟩ := hx
    have hdistp : dist !₂[(m : ℝ), (n : ℝ)] (0 : EuclideanSpace ℝ (Fin 2)) ≤ r :=
      Metric.mem_closedBall.mp ((mem_closedBall_lattice_iff hr0 (m, n)).mpr hpL)
    have hdistx : dist x (0 : EuclideanSpace ℝ (Fin 2)) ≤ r + √2 / 2 := by
      calc
        dist x (0 : EuclideanSpace ℝ (Fin 2))
            ≤ dist x !₂[(m : ℝ), (n : ℝ)] + dist !₂[(m : ℝ), (n : ℝ)] 0 := dist_triangle _ _ _
        _ ≤ √2 / 2 + r := add_le_add (dist_unitSquare_le hxsq) hdistp
        _ = r + √2 / 2 := by ring
    exact Metric.mem_closedBall.mpr hdistx
  have hvol_inner : ENNReal.ofReal (π * (r - √2 / 2) ^ 2) ≤ (N r : ℝ≥0∞) := by
    rw [← hvolU]
    calc
      ENNReal.ofReal (π * (r - √2 / 2) ^ 2)
          = ENNReal.ofReal (r - √2 / 2) ^ 2 * ENNReal.ofReal π := by
            rw [← ENNReal.ofReal_pow hr_sub_nonneg, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
      _ = (volume : Measure (EuclideanSpace ℝ (Fin 2)))
            (Metric.closedBall 0 (r - √2 / 2)) := by
            rw [EuclideanSpace.volume_closedBall_fin_two]
      _ ≤ volume U := measure_mono hsub_inner
  have hvol_outer : (N r : ℝ≥0∞) ≤ ENNReal.ofReal (π * (r + √2 / 2) ^ 2) := by
    rw [← hvolU]
    calc
      volume U ≤ (volume : Measure (EuclideanSpace ℝ (Fin 2)))
            (Metric.closedBall 0 (r + √2 / 2)) := measure_mono hsub_outer
      _ = ENNReal.ofReal (r + √2 / 2) ^ 2 * ENNReal.ofReal π := by
            rw [EuclideanSpace.volume_closedBall_fin_two]
      _ = ENNReal.ofReal (π * (r + √2 / 2) ^ 2) := by
            rw [← ENNReal.ofReal_pow hr_add_nonneg, ← ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
  have hpi_nonneg : 0 ≤ π := Real.pi_pos.le
  have hlo : π * (r - √2 / 2) ^ 2 ≤ N r := by
    have h := (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg (N r))).mp
      (by simpa [ENNReal.ofReal_natCast] using hvol_inner)
    exact h
  have hhi : (N r : ℝ) ≤ π * (r + √2 / 2) ^ 2 := by
    have h' : ENNReal.ofReal (N r : ℝ) ≤ ENNReal.ofReal (π * (r + √2 / 2) ^ 2) := by
      simpa [ENNReal.ofReal_natCast] using hvol_outer
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hpi_nonneg (sq_nonneg _))).mp h'
  have hsqrt2_ge1 : 1 ≤ √2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  have haux : √2 * r + 1 / 2 ≤ 2 * √2 * r := by
    nlinarith [hsqrt2_ge1, hr]
  have hpi_aux : π * (√2 * r + 1 / 2) ≤ 2 * √2 * π * r := by
    nlinarith [hpi_nonneg, haux]
  have hdiff_hi : (N r : ℝ) - π * r ^ 2 ≤ 2 * √2 * π * r := by
    have hsq : π * (r + √2 / 2) ^ 2 - π * r ^ 2 = π * (√2 * r + 1 / 2) := by
      have : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc
        π * (r + √2 / 2) ^ 2 - π * r ^ 2 = π * (√2 * r + √2 ^ 2 / 4) := by ring
        _ = π * (√2 * r + 1 / 2) := by rw [this]; norm_num
    linarith [hhi, hsq, hpi_aux]
  have hdiff_lo : -(2 * √2 * π * r) ≤ (N r : ℝ) - π * r ^ 2 := by
    have hsq : π * r ^ 2 - π * (r - √2 / 2) ^ 2 = π * (√2 * r - 1 / 2) := by
      have : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      calc
        π * r ^ 2 - π * (r - √2 / 2) ^ 2 = π * (√2 * r - √2 ^ 2 / 4) := by ring
        _ = π * (√2 * r - 1 / 2) := by rw [this]; norm_num
    have hpi_aux' : π * (√2 * r - 1 / 2) ≤ π * (√2 * r + 1 / 2) := by
      nlinarith [hpi_nonneg]
    linarith [hlo, hsq, hpi_aux', hpi_aux]
  exact abs_le.mpr ⟨hdiff_lo, hdiff_hi⟩

end ErrorBound

/--
Gauss proved that `|E r| ≤ 2 * √2 * π * r` for sufficiently large `r`.
Matches `GaussCircleProblem.error_le` definitionally.
-/
theorem error_le : ∀ᶠ r in atTop, |E r| ≤ 2 * √2 * π * r :=
  Filter.eventually_atTop.mpr ⟨1, fun _ hr => error_le_of_one_le hr⟩

/-! ### Part 2: Jacobi's Two-Squares Theorem and `exact_form_floor` -/

section JacobiFormula

private abbrev GI := GaussianInt

private def χ4 (d : ℕ) : ℤ :=
  if d % 2 = 0 then 0 else if d % 4 = 1 then 1 else -1

private lemma χ4_mul (a b : ℕ) : χ4 (a * b) = χ4 a * χ4 b := by
  unfold χ4
  by_cases ha2 : a % 2 = 0 <;> by_cases hb2 : b % 2 = 0
  · have h : (a * b) % 2 = 0 := by rw [Nat.mul_mod, ha2, zero_mul, Nat.zero_mod]
    simp [ha2, hb2, h]
  · have h : (a * b) % 2 = 0 := by rw [Nat.mul_mod, ha2, zero_mul, Nat.zero_mod]
    simp [ha2, hb2, h]
  · have h : (a * b) % 2 = 0 := by rw [Nat.mul_mod, hb2, mul_zero, Nat.zero_mod]
    simp [ha2, hb2, h]
  · have ha1 : a % 2 = 1 := by omega
    have hb1 : b % 2 = 1 := by omega
    have h2 : (a * b) % 2 ≠ 0 := by rw [Nat.mul_mod, ha1, hb1]; decide
    have ha4 : a % 4 = 1 ∨ a % 4 = 3 := by omega
    have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by omega
    rcases ha4 with ha1' | ha3 <;> rcases hb4 with hb1' | hb3
    · have hab : (a * b) % 4 = 1 := by rw [Nat.mul_mod, ha1', hb1']
      simp [ha2, hb2, h2, ha1', hb1', hab]
    · have hab : (a * b) % 4 = 3 := by rw [Nat.mul_mod, ha1', hb3]
      simp [ha2, hb2, h2, ha1', hb3, hab]
    · have hab : (a * b) % 4 = 3 := by rw [Nat.mul_mod, ha3, hb1']
      simp [ha2, hb2, h2, ha3, hb1', hab]
    · have hab : (a * b) % 4 = 1 := by rw [Nat.mul_mod, ha3, hb3]
      simp [ha2, hb2, h2, ha3, hb3, hab]

private def q1Finset (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 k ×ˢ Finset.Iic k).filter (fun p => p.1 ^ 2 + p.2 ^ 2 = k)

private def a2 (k : ℕ) : ℕ := (q1Finset k).card

private lemma mem_q1Finset_iff {k : ℕ} {p : ℕ × ℕ} :
    p ∈ q1Finset k ↔ 1 ≤ p.1 ∧ p.1 ^ 2 + p.2 ^ 2 = k := by
  unfold q1Finset
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Iic]
  refine ⟨fun h => ⟨h.1.1.1, h.2⟩, fun ⟨h1, h2⟩ => ⟨⟨⟨h1, ?_⟩, ?_⟩, h2⟩⟩
  · calc p.1 ≤ p.1 * p.1 := Nat.le_mul_self p.1
      _ = p.1 ^ 2 := by ring
      _ ≤ k := h2 ▸ Nat.le_add_right _ _
  · calc p.2 ≤ p.2 * p.2 := Nat.le_mul_self p.2
      _ = p.2 ^ 2 := by ring
      _ ≤ k := h2 ▸ Nat.le_add_left _ _

private noncomputable def r2Finset (k : ℕ) : Finset (ℤ × ℤ) :=
  (latticeFinset k).filter (fun p => p.1 ^ 2 + p.2 ^ 2 = (k : ℤ))

private lemma mem_r2Finset_iff {k : ℕ} {p : ℤ × ℤ} :
    p ∈ r2Finset k ↔ p.1 ^ 2 + p.2 ^ 2 = (k : ℤ) := by
  unfold r2Finset
  rw [Finset.mem_filter, mem_latticeFinset_iff]
  exact ⟨fun h => h.2, fun h => ⟨le_of_eq h, h⟩⟩

private lemma r2Finset_zero : (r2Finset 0).card = 1 := by
  have heq : r2Finset 0 = {(0, 0)} := by
    ext ⟨m, n⟩
    rw [mem_r2Finset_iff, Finset.mem_singleton, Prod.ext_iff]
    constructor
    · intro h
      norm_num at h
      exact ⟨by nlinarith only [h], by nlinarith only [h]⟩
    · rintro ⟨rfl, rfl⟩
      norm_num
  rw [heq, Finset.card_singleton]

private def rotQuad (j : Fin 4) (u v : ℕ) : ℤ × ℤ :=
  match j with
  | ⟨0, _⟩ => ((u : ℤ), (v : ℤ))
  | ⟨1, _⟩ => (-(v : ℤ), (u : ℤ))
  | ⟨2, _⟩ => (-(u : ℤ), -(v : ℤ))
  | ⟨3, _⟩ => ((v : ℤ), -(u : ℤ))

private lemma r2_eq_four_mul_a2 {k : ℕ} (hk : 1 ≤ k) :
    (r2Finset k).card = 4 * a2 k := by
  unfold a2
  rw [show 4 = (Finset.univ : Finset (Fin 4)).card by simp, ← Finset.card_product]
  symm
  refine Finset.card_bij (fun x _ => rotQuad x.1 x.2.1 x.2.2) ?_ ?_ ?_
  · rintro ⟨j, ⟨u, v⟩⟩ hx
    rw [Finset.mem_product, mem_q1Finset_iff] at hx
    rw [mem_r2Finset_iff]
    rcases hx with ⟨_, _, hsum⟩
    have hsumZ : (u : ℤ) ^ 2 + (v : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hsum
    dsimp only
    fin_cases j <;> simp [rotQuad] <;> linarith only [hsumZ]
  · rintro ⟨j₁, ⟨u₁, v₁⟩⟩ hx₁ ⟨j₂, ⟨u₂, v₂⟩⟩ hx₂ heq
    rw [Finset.mem_product, mem_q1Finset_iff] at hx₁ hx₂
    have hu1 : 1 ≤ (u₁ : ℤ) := by exact_mod_cast hx₁.2.1
    have hu2 : 1 ≤ (u₂ : ℤ) := by exact_mod_cast hx₂.2.1
    clear hx₁ hx₂
    dsimp only at heq
    fin_cases j₁ <;> fin_cases j₂ <;> simp only [rotQuad, Prod.mk.injEq] at heq <;>
      first
      | exact (by omega)
      | (have hu_eq : u₁ = u₂ := by omega
         have hv_eq : v₁ = v₂ := by omega
         subst hu_eq hv_eq; rfl)
  · rintro ⟨m, n⟩ hy
    rw [mem_r2Finset_iff] at hy
    have hne : m ≠ 0 ∨ n ≠ 0 := by
      by_contra h0
      rw [not_or] at h0
      rcases h0 with ⟨h1, h2⟩
      have hm0 : m = 0 := not_not.mp h1
      have hn0 : n = 0 := not_not.mp h2
      subst hm0 hn0
      norm_num at hy
      omega
    by_cases h1 : 0 < m ∧ 0 ≤ n
    · refine ⟨(⟨0, by decide⟩, (m.natAbs, n.natAbs)), ?_, ?_⟩
      · rw [Finset.mem_product, mem_q1Finset_iff]
        refine ⟨Finset.mem_univ _, by dsimp only; omega, ?_⟩
        dsimp only; zify; rw [abs_of_pos h1.1, abs_of_nonneg h1.2]; exact_mod_cast hy
      · simp [rotQuad, abs_of_pos h1.1, abs_of_nonneg h1.2]
    · by_cases h2 : m ≤ 0 ∧ 0 < n
      · refine ⟨(⟨1, by decide⟩, (n.natAbs, m.natAbs)), ?_, ?_⟩
        · rw [Finset.mem_product, mem_q1Finset_iff]
          refine ⟨Finset.mem_univ _, by dsimp only; omega, ?_⟩
          dsimp only; zify; rw [abs_of_pos h2.2, abs_of_nonpos h2.1]; linarith only [hy]
        · simp [rotQuad, abs_of_pos h2.2, abs_of_nonpos h2.1]
      · by_cases h3 : m < 0 ∧ n ≤ 0
        · refine ⟨(⟨2, by decide⟩, (m.natAbs, n.natAbs)), ?_, ?_⟩
          · rw [Finset.mem_product, mem_q1Finset_iff]
            refine ⟨Finset.mem_univ _, by dsimp only; omega, ?_⟩
            dsimp only; zify; rw [abs_of_neg h3.1, abs_of_nonpos h3.2]; linarith only [hy]
          · simp [rotQuad, abs_of_neg h3.1, abs_of_nonpos h3.2]
        · have h4 : 0 ≤ m ∧ n < 0 := by omega
          refine ⟨(⟨3, by decide⟩, (n.natAbs, m.natAbs)), ?_, ?_⟩
          · rw [Finset.mem_product, mem_q1Finset_iff]
            refine ⟨Finset.mem_univ _, by dsimp only; omega, ?_⟩
            dsimp only; zify; rw [abs_of_neg h4.2, abs_of_nonneg h4.1]; linarith only [hy]
          · simp [rotQuad, abs_of_neg h4.2, abs_of_nonneg h4.1]

private lemma q1_pair_eq_of_associated {x y : GI} (hx : 0 < x.re ∧ 0 ≤ x.im)
    (hy : 0 < y.re ∧ 0 ≤ y.im) (hass : Associated x y) : x = y := by
  obtain ⟨u, hu⟩ := hass
  have hnorm1 : (u : GI).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (d := -1) (by decide) (u : GI)).mpr u.isUnit
  have hu2 : (u : GI).re ^ 2 + (u : GI).im ^ 2 = 1 := by
    simpa [Zsqrtd.norm_def, sq] using hnorm1
  have hcases : (u : GI) = 1 ∨ (u : GI) = -1 ∨ (u : GI) = ⟨0, 1⟩ ∨ (u : GI) = ⟨0, -1⟩ := by
    have hre1 : (u : GI).re = 0 ∨ (u : GI).re = 1 ∨ (u : GI).re = -1 := by
      have : (u : GI).re ^ 2 ≤ 1 := by nlinarith [sq_nonneg (u : GI).im]
      rcases le_or_gt (u : GI).re 1 with h1 | h1
      · rcases le_or_gt (-1) (u : GI).re with h2 | h2
        · omega
        · nlinarith only [h2, this]
      · nlinarith only [h1, this]
    rcases hre1 with hr | hr | hr
    · have him : (u : GI).im = 1 ∨ (u : GI).im = -1 := by
        rw [hr] at hu2; norm_num at hu2; exact hu2
      rcases him with hi | hi
      · right; right; left; ext <;> simp [hr, hi]
      · right; right; right; ext <;> simp [hr, hi]
    · have him : (u : GI).im = 0 := by rw [hr] at hu2; nlinarith
      left; ext <;> simp [hr, him]
    · have him : (u : GI).im = 0 := by rw [hr] at hu2; nlinarith
      right; left; ext <;> simp [hr, him]
  rcases hcases with h1 | h2 | h3 | h4
  · rw [h1, mul_one] at hu; exact hu
  · rw [h2, mul_neg_one] at hu
    have : y.re = -x.re := by rw [← hu]; rfl
    omega
  · rw [h3] at hu
    have hre : y.re = -x.im := by
      calc y.re = (x * ⟨0, 1⟩).re := by rw [hu]
        _ = -x.im := by simp [Zsqrtd.re_mul]
    omega
  · rw [h4] at hu
    have him : y.im = -x.re := by
      calc y.im = (x * ⟨0, -1⟩).im := by rw [hu]
        _ = -x.re := by simp [Zsqrtd.im_mul]
    omega

private def unitPowGI : Fin 4 → GI
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => ⟨0, 1⟩
  | ⟨2, _⟩ => -1
  | ⟨3, _⟩ => ⟨0, -1⟩

private lemma isUnit_unitPowGI (j : Fin 4) : IsUnit (unitPowGI j) := by
  rw [← Zsqrtd.norm_eq_one_iff' (d := -1) (by decide)]
  fin_cases j <;> simp [unitPowGI, Zsqrtd.norm_def]

private def q1Normalize (z : GI) : GI :=
  if 0 < z.re ∧ 0 ≤ z.im then z
  else if 0 < z.im ∧ z.re ≤ 0 then ⟨z.im, -z.re⟩
  else if z.re < 0 ∧ z.im ≤ 0 then -z
  else ⟨-z.im, z.re⟩

private lemma q1Normalize_spec {z : GI} (hz : z ≠ 0) :
    (0 < (q1Normalize z).re ∧ 0 ≤ (q1Normalize z).im) ∧
    (q1Normalize z).norm = z.norm ∧
    Associated (q1Normalize z) z := by
  have hnz : z.re ≠ 0 ∨ z.im ≠ 0 := by
    by_contra h0
    apply hz
    ext <;> tauto
  unfold q1Normalize
  split_ifs with h1 h2 h3
  · exact ⟨h1, rfl, Associated.refl z⟩
  · refine ⟨⟨h2.1, by dsimp only; omega⟩, ?_,
        ⟨(isUnit_unitPowGI ⟨1, by decide⟩).unit, ?_⟩⟩
    · simp only [Zsqrtd.norm_def]; ring
    · ext <;> simp [unitPowGI, Zsqrtd.re_mul, Zsqrtd.im_mul]
  · refine ⟨⟨by simp only [Zsqrtd.re_neg]; omega, by simp only [Zsqrtd.im_neg]; omega⟩, ?_,
        ⟨(isUnit_unitPowGI ⟨2, by decide⟩).unit, ?_⟩⟩
    · simp only [Zsqrtd.norm_def, Zsqrtd.re_neg, Zsqrtd.im_neg]; ring
    · ext <;> simp [unitPowGI]
  · have him : z.im < 0 := by omega
    have hre : 0 ≤ z.re := by omega
    refine ⟨⟨by dsimp only; omega, hre⟩, ?_,
        ⟨(isUnit_unitPowGI ⟨3, by decide⟩).unit, ?_⟩⟩
    · simp only [Zsqrtd.norm_def]; ring
    · ext <;> simp [unitPowGI, Zsqrtd.re_mul, Zsqrtd.im_mul]

private lemma associated_q1Normalize {z : GI} (hz : z ≠ 0) :
    Associated (q1Normalize z) z := (q1Normalize_spec hz).2.2

private lemma q1Normalize_eq_of_associated {x y : GI} (hx : x ≠ 0) (hy : y ≠ 0)
    (hass : Associated x y) : q1Normalize x = q1Normalize y := by
  have hx' := q1Normalize_spec hx
  have hy' := q1Normalize_spec hy
  exact q1_pair_eq_of_associated hx'.1 hy'.1 ((hx'.2.2.trans hass).trans hy'.2.2.symm)

private lemma q1Normalize_eq_self {z : GI} (hz : 0 < z.re ∧ 0 ≤ z.im) :
    q1Normalize z = z := by
  unfold q1Normalize
  rw [if_pos hz]

private lemma gi_dvd_natCast_iff {m k : ℤ} :
    (m : GI) ∣ (k : GI) ↔ m ∣ k := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.re, ?_⟩
    have hre := congr_arg Zsqrtd.re hw
    simpa [Zsqrtd.re_mul] using hre
  · rintro ⟨c, rfl⟩
    exact ⟨(c : GI), by push_cast; rfl⟩

private lemma gi_mul_q1Normalize_inj {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n)
    {x₁ y₁ x₂ y₂ : GI}
    (hx₁q : 0 < x₁.re ∧ 0 ≤ x₁.im) (hy₁q : 0 < y₁.re ∧ 0 ≤ y₁.im)
    (hx₂q : 0 < x₂.re ∧ 0 ≤ x₂.im) (hy₂q : 0 < y₂.re ∧ 0 ≤ y₂.im)
    (hx₁n : x₁.norm = m) (hy₁n : y₁.norm = n) (hx₂n : x₂.norm = m) (hy₂n : y₂.norm = n)
    (heq : q1Normalize (x₁ * y₁) = q1Normalize (x₂ * y₂)) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hx1_ne : x₁ ≠ 0 := by intro h; rw [h, Zsqrtd.norm_zero] at hx₁n; omega
  have hy1_ne : y₁ ≠ 0 := by intro h; rw [h, Zsqrtd.norm_zero] at hy₁n; omega
  have hx2_ne : x₂ ≠ 0 := by intro h; rw [h, Zsqrtd.norm_zero] at hx₂n; omega
  have hy2_ne : y₂ ≠ 0 := by intro h; rw [h, Zsqrtd.norm_zero] at hy₂n; omega
  have hmul_ass : Associated (x₁ * y₁) (x₂ * y₂) := by
    have ha := associated_q1Normalize (mul_ne_zero hx1_ne hy1_ne)
    have hb := associated_q1Normalize (mul_ne_zero hx2_ne hy2_ne)
    exact ha.symm.trans (heq ▸ hb)
  have hdvd_prod : x₂ ∣ x₁ * y₁ := (dvd_mul_right x₂ y₂).trans hmul_ass.symm.dvd
  have hxm : x₂ ∣ (m : GI) := ⟨star x₂, by
    rw [← Zsqrtd.norm_eq_mul_conj x₂, hx₂n]; push_cast; rfl⟩
  let s := Nat.gcdA m n
  let t := Nat.gcdB m n
  have hbez : (s : GI) * (m : GI) + (t : GI) * (n : GI) = 1 := by
    have hnat : (Nat.gcd m n : ℤ) = (m : ℤ) * s + (n : ℤ) * t := Nat.gcd_eq_gcd_ab m n
    rw [hcop] at hnat
    exact_mod_cast (by linear_combination -hnat : s * (m : ℤ) + t * (n : ℤ) = 1)
  have hyn : y₁ * star y₁ = (n : GI) := by
    rw [← Zsqrtd.norm_eq_mul_conj, hy₁n]; push_cast; rfl
  have hx_dvd : x₂ ∣ x₁ := by
    have hexpr : x₁ = (s : GI) * x₁ * (m : GI) + (t : GI) * (x₁ * y₁) * star y₁ := by
      calc x₁ = x₁ * 1 := (mul_one x₁).symm
        _ = x₁ * ((s : GI) * (m : GI) + (t : GI) * (n : GI)) := by rw [hbez]
        _ = x₁ * ((s : GI) * (m : GI) + (t : GI) * (y₁ * star y₁)) := by rw [hyn]
        _ = (s : GI) * x₁ * (m : GI) + (t : GI) * (x₁ * y₁) * star y₁ := by ring
    rw [hexpr]
    exact dvd_add (dvd_mul_of_dvd_right hxm ((s : GI) * x₁))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdvd_prod (t : GI)) (star y₁))
  obtain ⟨w, hw⟩ := hx_dvd
  have hw_norm : w.norm = 1 := by
    have hnrm := congr_arg Zsqrtd.norm hw
    rw [Zsqrtd.norm_mul, hx₁n, hx₂n] at hnrm
    have hmpos : (0 : ℤ) < m := by omega
    nlinarith only [hnrm, hmpos]
  have hwu : IsUnit w := (Zsqrtd.norm_eq_one_iff' (d := -1) (by decide) w).mp hw_norm
  have hxeq : x₁ = x₂ :=
    (q1_pair_eq_of_associated hx₂q hx₁q ⟨hwu.unit, by simpa using hw.symm⟩).symm
  subst hxeq
  obtain ⟨u, hu⟩ := hmul_ass
  have huy : x₁ * (y₁ * (u : GI)) = x₁ * y₂ := by linear_combination hu
  have hyass : Associated y₁ y₂ := ⟨u, mul_left_cancel₀ hx1_ne huy⟩
  exact ⟨rfl, q1_pair_eq_of_associated hy₁q hy₂q hyass⟩

private lemma a2_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    a2 (m * n) = a2 m * a2 n := by
  unfold a2
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij
    (fun xy _ => let z := q1Normalize (⟨xy.1.1, xy.1.2⟩ * ⟨xy.2.1, xy.2.2⟩);
      (z.re.natAbs, z.im.natAbs)) ?_ ?_ ?_
  · rintro ⟨⟨u₁, v₁⟩, ⟨u₂, v₂⟩⟩ hxy
    rw [Finset.mem_product, mem_q1Finset_iff, mem_q1Finset_iff] at hxy
    dsimp only at hxy
    rcases hxy with ⟨⟨hu1, hs1⟩, ⟨hu2, hs2⟩⟩
    let x : GI := ⟨u₁, v₁⟩
    let y : GI := ⟨u₂, v₂⟩
    have hx_ne : x ≠ 0 := by
      intro h; have hre := congr_arg Zsqrtd.re h
      dsimp only [x] at hre; simp only [Zsqrtd.re_zero] at hre; omega
    have hy_ne : y ≠ 0 := by
      intro h; have hre := congr_arg Zsqrtd.re h
      dsimp only [y] at hre; simp only [Zsqrtd.re_zero] at hre; omega
    have hspec := q1Normalize_spec (mul_ne_zero hx_ne hy_ne)
    rw [mem_q1Finset_iff]
    dsimp only
    refine ⟨Int.natAbs_pos.mpr hspec.1.1.ne', ?_⟩
    have hnorm : (q1Normalize (x * y)).norm = (m : ℤ) * n := by
      rw [hspec.2.1, Zsqrtd.norm_mul]
      have hxnorm : x.norm = (m : ℤ) := by simp only [x, Zsqrtd.norm_def]; zify at hs1; linarith only [hs1]
      have hynorm : y.norm = (n : ℤ) := by simp only [y, Zsqrtd.norm_def]; zify at hs2; linarith only [hs2]
      rw [hxnorm, hynorm]
    zify
    rw [abs_of_pos hspec.1.1, abs_of_nonneg hspec.1.2]
    have : (q1Normalize (x * y)).re ^ 2 + (q1Normalize (x * y)).im ^ 2 = (q1Normalize (x * y)).norm := by
      simp [Zsqrtd.norm_def, sq]
    rw [this, hnorm]
  · rintro ⟨⟨u₁, v₁⟩, ⟨u₂, v₂⟩⟩ h₁ ⟨⟨u₃, v₃⟩, ⟨u₄, v₄⟩⟩ h₂ heq
    rw [Finset.mem_product, mem_q1Finset_iff, mem_q1Finset_iff] at h₁ h₂
    dsimp only at h₁ h₂
    rcases h₁ with ⟨⟨hu1, hs1⟩, ⟨hu2, hs2⟩⟩
    rcases h₂ with ⟨⟨hu3, hs3⟩, ⟨hu4, hs4⟩⟩
    let x₁ : GI := ⟨u₁, v₁⟩; let y₁ : GI := ⟨u₂, v₂⟩
    let x₂ : GI := ⟨u₃, v₃⟩; let y₂ : GI := ⟨u₄, v₄⟩
    have hx₁_ne : x₁ ≠ 0 := by
      intro h; have hre := congr_arg Zsqrtd.re h
      dsimp only [x₁] at hre; simp only [Zsqrtd.re_zero] at hre; omega
    have hy₁_ne : y₁ ≠ 0 := by
      intro h; have hre := congr_arg Zsqrtd.re h
      dsimp only [y₁] at hre; simp only [Zsqrtd.re_zero] at hre; omega
    have hx₂_ne : x₂ ≠ 0 := by
      intro h; have hre := congr_arg Zsqrtd.re h
      dsimp only [x₂] at hre; simp only [Zsqrtd.re_zero] at hre; omega
    have hy₂_ne : y₂ ≠ 0 := by
      intro h; have hre := congr_arg Zsqrtd.re h
      dsimp only [y₂] at hre; simp only [Zsqrtd.re_zero] at hre; omega
    have h1s := q1Normalize_spec (mul_ne_zero hx₁_ne hy₁_ne)
    have h2s := q1Normalize_spec (mul_ne_zero hx₂_ne hy₂_ne)
    dsimp only at heq
    simp only [Prod.mk.injEq] at heq
    have hnorm_eq : q1Normalize (x₁ * y₁) = q1Normalize (x₂ * y₂) := by
      ext
      · zify at heq; rw [← abs_of_pos h1s.1.1, ← abs_of_pos h2s.1.1]; exact_mod_cast heq.1
      · zify at heq; rw [← abs_of_nonneg h1s.1.2, ← abs_of_nonneg h2s.1.2]; exact_mod_cast heq.2
    have hpair := gi_mul_q1Normalize_inj hm hn hcop
      ⟨by simp [x₁]; omega, by simp [x₁]⟩ ⟨by simp [y₁]; omega, by simp [y₁]⟩
      ⟨by simp [x₂]; omega, by simp [x₂]⟩ ⟨by simp [y₂]; omega, by simp [y₂]⟩
      (by simp only [x₁, Zsqrtd.norm_def]; zify at hs1; linarith only [hs1])
      (by simp only [y₁, Zsqrtd.norm_def]; zify at hs2; linarith only [hs2])
      (by simp only [x₂, Zsqrtd.norm_def]; zify at hs3; linarith only [hs3])
      (by simp only [y₂, Zsqrtd.norm_def]; zify at hs4; linarith only [hs4])
      hnorm_eq
    have hx_re : u₁ = u₃ := by
      have hre := congr_arg Zsqrtd.re hpair.1
      dsimp only [x₁, x₂] at hre
      exact Int.ofNat.inj hre
    have hx_im : v₁ = v₃ := by
      have him := congr_arg Zsqrtd.im hpair.1
      dsimp only [x₁, x₂] at him
      exact Int.ofNat.inj him
    have hy_re : u₂ = u₄ := by
      have hre := congr_arg Zsqrtd.re hpair.2
      dsimp only [y₁, y₂] at hre
      exact Int.ofNat.inj hre
    have hy_im : v₂ = v₄ := by
      have him := congr_arg Zsqrtd.im hpair.2
      dsimp only [y₁, y₂] at him
      exact Int.ofNat.inj him
    simp [hx_re, hx_im, hy_re, hy_im]
  · rintro ⟨a, b⟩ hab
    rw [mem_q1Finset_iff] at hab
    dsimp only at hab
    let z : GI := ⟨a, b⟩
    have hz_norm : z.norm = (m : ℤ) * n := by
      simp only [z, Zsqrtd.norm_def]; zify at hab; linarith only [hab.2]
    let g := EuclideanDomain.gcd z (m : GI)
    let x := q1Normalize g
    have hg_ne : g ≠ 0 := by
      intro h0
      have hd : g ∣ (m : GI) := EuclideanDomain.gcd_dvd_right z (m : GI)
      rw [h0, zero_dvd_iff] at hd
      have hre := congr_arg Zsqrtd.re hd
      simp only [Zsqrtd.re_natCast, Zsqrtd.re_zero] at hre
      omega
    have hxg : Associated x g := associated_q1Normalize hg_ne
    have hxm : x ∣ (m : GI) := hxg.dvd.trans (EuclideanDomain.gcd_dvd_right z (m : GI))
    have hxz : x ∣ z := hxg.dvd.trans (EuclideanDomain.gcd_dvd_left z (m : GI))
    have hxnorm_dvd_m : x.norm ∣ (m : ℤ) := by
      have hd1 : x.norm ∣ (m : ℤ) ^ 2 := by
        obtain ⟨c, hc⟩ := hxm
        refine ⟨c.norm, ?_⟩
        have hnrm := congr_arg Zsqrtd.norm hc
        rw [Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at hnrm
        linarith only [hnrm]
      have hd2 : x.norm ∣ (m : ℤ) * n := by
        obtain ⟨c, hc⟩ := hxz
        refine ⟨c.norm, ?_⟩
        have hnrm := congr_arg Zsqrtd.norm hc
        rw [Zsqrtd.norm_mul, hz_norm] at hnrm
        exact hnrm
      have hnonneg : 0 ≤ x.norm := Zsqrtd.norm_nonneg (by decide) x
      have hx_eq : ((x.norm.natAbs : ℕ) : ℤ) = x.norm := Int.natAbs_of_nonneg hnonneg
      rw [← hx_eq] at hd1 hd2
      have hd1n : x.norm.natAbs ∣ m * m := Int.natCast_dvd_natCast.mp (by simpa [sq] using hd1)
      have hd2n : x.norm.natAbs ∣ m * n := Int.natCast_dvd_natCast.mp (by simpa using hd2)
      have hd_gcd : x.norm.natAbs ∣ Nat.gcd (m * m) (m * n) := Nat.dvd_gcd hd1n hd2n
      rw [Nat.gcd_mul_left, hcop, mul_one] at hd_gcd
      rw [← hx_eq]
      exact Int.natCast_dvd_natCast.mpr hd_gcd
    have hm_dvd_xnorm : (m : ℤ) ∣ x.norm := by
      have hbez : g = z * EuclideanDomain.gcdA z (m : GI) + (m : GI) * EuclideanDomain.gcdB z (m : GI) :=
        EuclideanDomain.gcd_eq_gcd_ab z (m : GI)
      let A := EuclideanDomain.gcdA z (m : GI)
      let B := EuclideanDomain.gcdB z (m : GI)
      have hgi : (m : GI) ∣ (g.norm : GI) := by
        rw [Zsqrtd.norm_eq_mul_conj]
        have hzz : z * star z = (m : GI) * (n : GI) := by
          rw [← Zsqrtd.norm_eq_mul_conj, hz_norm]; push_cast; rfl
        have hsm : star (m : GI) = (m : GI) := by ext <;> simp
        have hcalc : g * star g = (m : GI) *
            ((A * star A) * (n : GI) + (z * A) * star B + B * star (z * A) + (m : GI) * (B * star B)) := by
          calc g * star g
              = (z * A + (m : GI) * B) * star (z * A + (m : GI) * B) := by rw [hbez]
            _ = (A * star A) * (z * star z) + (m : GI) * ((z * A) * star B + B * star (z * A) +
                (m : GI) * (B * star B)) := by simp only [star_add, star_mul, hsm]; ring
            _ = _ := by rw [hzz]; ring
        exact ⟨_, hcalc⟩
      have hm_g : (m : ℤ) ∣ g.norm := gi_dvd_natCast_iff.mp hgi
      rwa [(q1Normalize_spec hg_ne).2.1]
    have hxnorm_eq : x.norm = (m : ℤ) := by
      have hnonneg : 0 ≤ x.norm := Zsqrtd.norm_nonneg (by decide) x
      exact Int.dvd_antisymm hnonneg (by omega) hxnorm_dvd_m hm_dvd_xnorm
    obtain ⟨y₀, hy₀⟩ := hxz
    have hy₀_ne : y₀ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hy₀
      have hrm := congr_arg Zsqrtd.norm hy₀
      rw [hz_norm, Zsqrtd.norm_zero] at hrm
      have : (m : ℤ) * n = 0 := hrm
      nlinarith only [this, hm, hn]
    let y := q1Normalize y₀
    have hynorm_eq : y.norm = (n : ℤ) := by
      have hnrm := congr_arg Zsqrtd.norm hy₀
      rw [Zsqrtd.norm_mul, hxnorm_eq, hz_norm] at hnrm
      rw [(q1Normalize_spec hy₀_ne).2.1]
      have hmpos : (0 : ℤ) < m := by omega
      nlinarith only [hnrm, hmpos]
    have hxspec := q1Normalize_spec hg_ne
    have hyspec := q1Normalize_spec hy₀_ne
    have hxre : 0 < x.re ∧ 0 ≤ x.im := hxspec.1
    have hyre : 0 < y.re ∧ 0 ≤ y.im := hyspec.1
    refine ⟨((x.re.natAbs, x.im.natAbs), (y.re.natAbs, y.im.natAbs)), ?_, ?_⟩
    · rw [Finset.mem_product, mem_q1Finset_iff, mem_q1Finset_iff]
      have hxnat : x.re.natAbs ^ 2 + x.im.natAbs ^ 2 = m := by
        zify
        rw [abs_of_pos hxre.1, abs_of_nonneg hxre.2]
        have : x.re ^ 2 + x.im ^ 2 = x.norm := by simp [Zsqrtd.norm_def, sq]
        linarith only [this, hxnorm_eq]
      have hynat : y.re.natAbs ^ 2 + y.im.natAbs ^ 2 = n := by
        zify
        rw [abs_of_pos hyre.1, abs_of_nonneg hyre.2]
        have : y.re ^ 2 + y.im ^ 2 = y.norm := by simp [Zsqrtd.norm_def, sq]
        linarith only [this, hynorm_eq]
      dsimp only
      exact ⟨⟨Int.natAbs_pos.mpr hxre.1.ne', hxnat⟩, ⟨Int.natAbs_pos.mpr hyre.1.ne', hynat⟩⟩
    · have hass : Associated (⟨(x.re.natAbs : ℤ), (x.im.natAbs : ℤ)⟩ *
          ⟨(y.re.natAbs : ℤ), (y.im.natAbs : ℤ)⟩) z := by
        have hx' : (⟨(x.re.natAbs : ℤ), (x.im.natAbs : ℤ)⟩ : GI) = x := by
          ext <;> simp [abs_of_pos hxre.1, abs_of_nonneg hxre.2]
        have hy' : (⟨(y.re.natAbs : ℤ), (y.im.natAbs : ℤ)⟩ : GI) = y := by
          ext <;> simp [abs_of_pos hyre.1, abs_of_nonneg hyre.2]
        rw [hx', hy']
        exact (Associated.mul_left x hyspec.2.2).trans ⟨1, by simpa using hy₀.symm⟩
      have hz_ne : z ≠ 0 := by
        intro h; have hre := congr_arg Zsqrtd.re h
        dsimp only [z] at hre; simp only [Zsqrtd.re_zero] at hre; omega
      have hmul_ne : (⟨(x.re.natAbs : ℤ), (x.im.natAbs : ℤ)⟩ : GI) *
          ⟨(y.re.natAbs : ℤ), (y.im.natAbs : ℤ)⟩ ≠ 0 := by
        intro h0
        have hnrm_eq : z.norm = 0 := by
          have := Zsqrtd.norm_eq_of_associated (d := -1) (by decide) hass
          rw [h0, Zsqrtd.norm_zero] at this
          exact this.symm
        exact hz_ne ((Zsqrtd.norm_eq_zero_iff (d := -1) (by decide) z).mp hnrm_eq)
      have hnormz : q1Normalize (⟨(x.re.natAbs : ℤ), (x.im.natAbs : ℤ)⟩ *
          ⟨(y.re.natAbs : ℤ), (y.im.natAbs : ℤ)⟩) = z := by
        rw [q1Normalize_eq_of_associated hmul_ne hz_ne hass]
        exact q1Normalize_eq_self ⟨by simp [z]; omega, by simp [z]⟩
      dsimp only
      rw [hnormz]
      simp [z]

private lemma a2_one : a2 1 = 1 := by
  have hq : q1Finset 1 = {(1, 0)} := by
    ext ⟨u, v⟩
    rw [mem_q1Finset_iff, Finset.mem_singleton, Prod.ext_iff]
    dsimp only
    constructor
    · rintro ⟨hu, hs⟩
      have hu1 : u ≤ 1 := by
        by_contra hlt
        have : 2 ≤ u := by omega
        have : 4 ≤ u ^ 2 := by nlinarith
        omega
      have hv0 : v = 0 := by
        by_contra hne
        have : 1 ≤ v := by omega
        have : 1 ≤ u ^ 2 := by nlinarith
        have : 1 ≤ v ^ 2 := by nlinarith
        omega
      omega
    · rintro ⟨rfl, rfl⟩
      norm_num
  unfold a2
  rw [hq, Finset.card_singleton]

private lemma even_of_four_dvd_sq_add_sq {u v : ℕ} (h4 : 4 ∣ u ^ 2 + v ^ 2) :
    u % 2 = 0 ∧ v % 2 = 0 := by
  have hmod4 : ((u % 4) ^ 2 + (v % 4) ^ 2) % 4 = 0 := by
    have h0 := Nat.dvd_iff_mod_eq_zero.mp h4
    rwa [Nat.add_mod, Nat.pow_mod u 2 4, Nat.pow_mod v 2 4, ← Nat.add_mod] at h0
  have hu4 : u % 4 < 4 := Nat.mod_lt u (by decide)
  have hv4 : v % 4 < 4 := Nat.mod_lt v (by decide)
  interval_cases hu : u % 4 <;> interval_cases hv : v % 4 <;> simp at hmod4 <;> omega

private lemma gi_norm_pow (z : GI) : ∀ k : ℕ, (z ^ k).norm = z.norm ^ k
  | 0 => by simp
  | k + 1 => by rw [pow_succ, Zsqrtd.norm_mul, gi_norm_pow z k, pow_succ]

private lemma a2_two_pow : ∀ e : ℕ, (a2 (2 ^ e) : ℤ) = ∑ d ∈ (2 ^ e).divisors, χ4 d
  | 0 => by simp [a2_one, χ4]
  | 1 => by
    have ha : a2 2 = 1 := by
      have hq : q1Finset 2 = {(1, 1)} := by
        ext ⟨u, v⟩
        rw [mem_q1Finset_iff, Finset.mem_singleton, Prod.ext_iff]
        dsimp only
        constructor
        · rintro ⟨hu, hs⟩
          have hu2 : u ≤ 1 := by
            by_contra hlt
            have : 2 ≤ u := by omega
            have : 4 ≤ u ^ 2 := by nlinarith
            omega
          have hv2 : v ≤ 1 := by
            by_contra hlt
            have : 2 ≤ v := by omega
            have : 4 ≤ v ^ 2 := by nlinarith
            omega
          have : u = 1 := by omega
          subst this
          have hvs : v ^ 2 = 1 := by omega
          have : v = 1 := by
            by_contra hv0
            have : v = 0 := by omega
            subst this; norm_num at hs
          exact ⟨rfl, this⟩
        · rintro ⟨rfl, rfl⟩
          norm_num
      unfold a2; rw [hq, Finset.card_singleton]
    have hdiv : (2 : ℕ).divisors = {1, 2} := Nat.Prime.divisors Nat.prime_two
    rw [pow_one, ha, hdiv, Finset.sum_pair (by decide)]
    simp [χ4]
  | e + 2 => by
    have ih := a2_two_pow e
    have ha_step : a2 (2 ^ (e + 2)) = a2 (2 ^ e) := by
      unfold a2
      refine Finset.card_bij (fun p _ => (p.1 / 2, p.2 / 2)) ?_ ?_ ?_
      · rintro ⟨u, v⟩ hp
        rw [mem_q1Finset_iff] at hp ⊢
        rcases hp with ⟨hu, hs⟩
        have h4 : 4 ∣ u ^ 2 + v ^ 2 := by
          rw [hs, show 2 ^ (e + 2) = 4 * 2 ^ e by ring]
          exact dvd_mul_right _ _
        have heven := even_of_four_dvd_sq_add_sq h4
        dsimp only
        refine ⟨by omega, ?_⟩
        have hmul : 4 * ((u / 2) ^ 2 + (v / 2) ^ 2) = 4 * 2 ^ e := by
          calc 4 * ((u / 2) ^ 2 + (v / 2) ^ 2) = (2 * (u / 2)) ^ 2 + (2 * (v / 2)) ^ 2 := by ring
            _ = u ^ 2 + v ^ 2 := by rw [show 2 * (u / 2) = u by omega, show 2 * (v / 2) = v by omega]
            _ = 2 ^ (e + 2) := hs
            _ = 4 * 2 ^ e := by ring
        omega
      · rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
        rw [mem_q1Finset_iff] at h₁ h₂
        have h4₁ : 4 ∣ u₁ ^ 2 + v₁ ^ 2 := by rw [h₁.2, show 2 ^ (e + 2) = 4 * 2 ^ e by ring]; exact dvd_mul_right _ _
        have h4₂ : 4 ∣ u₂ ^ 2 + v₂ ^ 2 := by rw [h₂.2, show 2 ^ (e + 2) = 4 * 2 ^ e by ring]; exact dvd_mul_right _ _
        have heven1 := even_of_four_dvd_sq_add_sq h4₁
        have heven2 := even_of_four_dvd_sq_add_sq h4₂
        dsimp only at heq
        simp only [Prod.mk.injEq] at heq
        ext <;> omega
      · rintro ⟨u', v'⟩ h'
        rw [mem_q1Finset_iff] at h'
        refine ⟨(2 * u', 2 * v'), mem_q1Finset_iff.mpr ⟨by omega, by
          calc (2 * u') ^ 2 + (2 * v') ^ 2 = 4 * (u' ^ 2 + v' ^ 2) := by ring
            _ = 4 * 2 ^ e := by rw [h'.2]
            _ = 2 ^ (e + 2) := by ring⟩, by simp⟩
    have hsum_step : ∑ d ∈ (2 ^ (e + 2)).divisors, χ4 d = 1 := by
      rw [Nat.sum_divisors_prime_pow Nat.prime_two]
      have : ∀ j ∈ Finset.range (e + 3), χ4 (2 ^ j) = if j = 0 then 1 else 0 := by
        intro j _
        cases j with
        | zero => simp [χ4]
        | succ m =>
          have h2 : 2 ^ (m + 1) % 2 = 0 := by rw [Nat.pow_succ']; simp
          simp [χ4, h2]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      simp
    have hsum_e : ∑ d ∈ (2 ^ e).divisors, χ4 d = 1 := by
      rw [Nat.sum_divisors_prime_pow Nat.prime_two]
      have : ∀ j ∈ Finset.range (e + 1), χ4 (2 ^ j) = if j = 0 then 1 else 0 := by
        intro j _
        cases j with
        | zero => simp [χ4]
        | succ m =>
          have h2 : 2 ^ (m + 1) % 2 = 0 := by rw [Nat.pow_succ']; simp
          simp [χ4, h2]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
      simp
    omega

private lemma a2_mod_four_eq_three {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∀ e : ℕ, (a2 (p ^ e) : ℤ) = ∑ d ∈ (p ^ e).divisors, χ4 d := by
  intro e
  have hsum : ∀ k : ℕ, ∑ d ∈ (p ^ k).divisors, χ4 d = if Even k then 1 else 0 := by
    intro k
    rw [Nat.sum_divisors_prime_pow hp]
    induction k with
    | zero => simp [χ4]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hodd : p ^ (k + 1) % 2 ≠ 0 := by
        have : p % 2 = 1 := by omega
        rw [Nat.pow_mod, this, Nat.one_pow]; decide
      have hmod4 : p ^ (k + 1) % 4 = if Even (k + 1) then 1 else 3 := by
        rw [Nat.pow_mod, hp4]
        rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · have hnot : ¬ Even (m + m + 1) := by
            rw [show m + m + 1 = 2 * m + 1 by omega]; exact Nat.not_even_two_mul_add_one m
          rw [if_neg hnot, show m + m + 1 = 2 * m + 1 by omega, pow_succ, pow_mul,
            show (3 ^ 2 : ℕ) = 9 by decide, Nat.mul_mod, Nat.pow_mod 9 m 4,
            show (9 : ℕ) % 4 = 1 by decide, Nat.one_pow]
        · have hev : Even (2 * m + 1 + 1) := ⟨m + 1, by omega⟩
          rw [if_pos hev, show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul,
            show (3 ^ 2 : ℕ) = 9 by decide, Nat.pow_mod 9 (m + 1) 4,
            show (9 : ℕ) % 4 = 1 by decide, Nat.one_pow]
      rcases Nat.even_or_odd k with hk_even | hk_odd
      · have hnot : ¬ Even (k + 1) := by simp [Nat.even_add_one, hk_even]
        simp only [if_pos hk_even, if_neg hnot]
        unfold χ4
        simp [hodd, hmod4, hnot]
      · have hev : Even (k + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr hk_odd
        have hnot : ¬ Even k := Nat.not_even_iff_odd.mpr hk_odd
        simp only [if_neg hnot, if_pos hev]
        unfold χ4
        simp [hodd, hmod4, hev]
  rw [hsum]
  induction e using Nat.twoStepInduction with
  | zero => simp [a2_one]
  | one =>
    have ha : a2 p = 0 := by
      unfold a2
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ hp_mem
      rw [mem_q1Finset_iff] at hp_mem
      dsimp only at hp_mem
      have hmod : ((u % 4) ^ 2 + (v % 4) ^ 2) % 4 = 3 := by
        have h0 : (u ^ 2 + v ^ 2) % 4 = 3 := by rw [hp_mem.2, hp4]
        rwa [Nat.add_mod, Nat.pow_mod u 2 4, Nat.pow_mod v 2 4, ← Nat.add_mod] at h0
      have : u % 4 < 4 := Nat.mod_lt _ (by decide)
      have : v % 4 < 4 := Nat.mod_lt _ (by decide)
      interval_cases hu : u % 4 <;> interval_cases hv : v % 4 <;> simp at hmod
    simp [ha]
  | more e ih _ =>
    have ha_step : a2 (p ^ (e + 2)) = a2 (p ^ e) := by
      unfold a2
      have : Fact p.Prime := ⟨hp⟩
      have dvd_both : ∀ u v : ℕ, u ^ 2 + v ^ 2 = p ^ (e + 2) → p ∣ u ∧ p ∣ v := by
        intro u v hs
        have hdvd : p ∣ u ^ 2 + v ^ 2 := hs ▸ dvd_pow_self p (by omega)
        have hv_dvd : p ∣ v := by
          rw [← ZMod.natCast_eq_zero_iff]
          by_contra hv0
          have hsq : IsSquare (-1 : ZMod p) := by
            refine ⟨(u : ZMod p) / (v : ZMod p), ?_⟩
            have hz : (u : ZMod p) ^ 2 + (v : ZMod p) ^ 2 = 0 := by
              have := (ZMod.natCast_eq_zero_iff (u ^ 2 + v ^ 2) p).mpr hdvd
              simpa using this
            field_simp [hv0]
            linear_combination -hz
          exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4
        have hu_dvd : p ∣ u := by
          rw [← ZMod.natCast_eq_zero_iff]
          have hvz := (ZMod.natCast_eq_zero_iff v p).mpr hv_dvd
          have hz : (u : ZMod p) ^ 2 + (v : ZMod p) ^ 2 = 0 := by
            have := (ZMod.natCast_eq_zero_iff (u ^ 2 + v ^ 2) p).mpr hdvd
            simpa using this
          rw [hvz, zero_pow (by decide), add_zero] at hz
          simpa [sq] using hz
        exact ⟨hu_dvd, hv_dvd⟩
      refine Finset.card_bij (fun q _ => (q.1 / p, q.2 / p)) ?_ ?_ ?_
      · rintro ⟨u, v⟩ hq
        rw [mem_q1Finset_iff] at hq ⊢
        dsimp only at hq ⊢
        obtain ⟨hu_dvd, hv_dvd⟩ := dvd_both u v hq.2
        have hu' : 1 ≤ u / p := Nat.div_pos (Nat.le_of_dvd hq.1 hu_dvd) hp.pos
        refine ⟨hu', ?_⟩
        obtain ⟨u', rfl⟩ := hu_dvd
        obtain ⟨v', rfl⟩ := hv_dvd
        rw [Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
        have hmul : p ^ 2 * (u' ^ 2 + v' ^ 2) = p ^ 2 * p ^ e := by
          calc p ^ 2 * (u' ^ 2 + v' ^ 2) = (p * u') ^ 2 + (p * v') ^ 2 := by ring
            _ = p ^ (e + 2) := hq.2
            _ = p ^ 2 * p ^ e := by ring
        exact mul_left_cancel₀ (pow_ne_zero 2 hp.ne_zero) hmul
      · rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ heq
        rw [mem_q1Finset_iff] at h₁ h₂
        dsimp only at h₁ h₂
        obtain ⟨hu1, hv1⟩ := dvd_both u₁ v₁ h₁.2
        obtain ⟨hu2, hv2⟩ := dvd_both u₂ v₂ h₂.2
        dsimp only at heq
        simp only [Prod.mk.injEq] at heq
        ext
        · calc u₁ = p * (u₁ / p) := (Nat.mul_div_cancel' hu1).symm
            _ = p * (u₂ / p) := by rw [heq.1]
            _ = u₂ := Nat.mul_div_cancel' hu2
        · calc v₁ = p * (v₁ / p) := (Nat.mul_div_cancel' hv1).symm
            _ = p * (v₂ / p) := by rw [heq.2]
            _ = v₂ := Nat.mul_div_cancel' hv2
      · rintro ⟨u', v'⟩ h'
        rw [mem_q1Finset_iff] at h'
        dsimp only at h'
        refine ⟨(p * u', p * v'), mem_q1Finset_iff.mpr ⟨Nat.mul_pos hp.pos h'.1, by
          calc (p * u') ^ 2 + (p * v') ^ 2 = p ^ 2 * (u' ^ 2 + v' ^ 2) := by ring
            _ = p ^ 2 * p ^ e := by rw [h'.2]
            _ = p ^ (e + 2) := by ring⟩, ?_⟩
        simp [Nat.mul_div_cancel_left _ hp.pos]
    simp only [ha_step, ih, Nat.even_add]
    norm_num

private lemma a2_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∀ e : ℕ, (a2 (p ^ e) : ℤ) = ∑ d ∈ (p ^ e).divisors, χ4 d := by
  intro e
  have hsum : ∑ d ∈ (p ^ e).divisors, χ4 d = (e : ℤ) + 1 := by
    rw [Nat.sum_divisors_prime_pow hp]
    have hterm : ∀ j ∈ Finset.range (e + 1), χ4 (p ^ j) = 1 := by
      intro j _
      have hp2 : p % 2 = 1 := by omega
      have h2 : p ^ j % 2 ≠ 0 := by rw [Nat.pow_mod, hp2, Nat.one_pow]; decide
      have h4 : p ^ j % 4 = 1 := by rw [Nat.pow_mod, hp4, Nat.one_pow]
      simp [χ4, h2, h4]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    norm_cast
  rw [hsum]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u₀, v₀, huv⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  let piZ : GI := ⟨u₀, v₀⟩
  have hπ_norm : piZ.norm = p := by
    simp only [piZ, Zsqrtd.norm_def]
    linear_combination (by exact_mod_cast huv : (u₀ : ℤ) ^ 2 + (v₀ : ℤ) ^ 2 = p)
  have hπ_irred : Irreducible piZ := by
    refine ⟨fun hu => ?_, fun a b hab => ?_⟩
    · rw [← Zsqrtd.norm_eq_one_iff' (d := -1) (by decide), hπ_norm] at hu
      have hp1 : p = 1 := by omega
      exact hp.ne_one hp1
    · have hn := congr_arg Zsqrtd.norm hab
      rw [Zsqrtd.norm_mul, hπ_norm] at hn
      have ha0 : 0 ≤ a.norm := Zsqrtd.norm_nonneg (by decide) a
      have hb0 : 0 ≤ b.norm := Zsqrtd.norm_nonneg (by decide) b
      have hnat : a.norm.natAbs * b.norm.natAbs = p := by
        zify
        rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
        exact hn.symm
      rcases (Nat.dvd_prime hp).mp ⟨b.norm.natAbs, hnat.symm⟩ with h1 | hp_eq
      · left; exact (Zsqrtd.norm_eq_one_iff).mp h1
      · right
        have hb1 : b.norm.natAbs = 1 := by
          rw [hp_eq] at hnat
          exact mul_left_cancel₀ hp.ne_zero (hnat.trans (mul_one p).symm)
        exact (Zsqrtd.norm_eq_one_iff).mp hb1
  have hπ_prime : Prime piZ := _root_.irreducible_iff_prime.mp hπ_irred
  have hπ_conj_not_dvd : ¬ piZ ∣ star piZ := by
    rintro ⟨w, hw⟩
    have hn : p = p * w.norm := by
      have := congr_arg Zsqrtd.norm hw
      simpa [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hπ_norm, mul_comm] using this
    have hw1 : w.norm = 1 := by nlinarith only [hn, hp.pos]
    have hre1 : w.re = 0 ∨ w.re = 1 ∨ w.re = -1 := by
      have : w.re ^ 2 + w.im ^ 2 = 1 := by simpa [Zsqrtd.norm_def, sq] using hw1
      have : w.re ^ 2 ≤ 1 := by nlinarith [sq_nonneg w.im]
      rcases le_or_gt w.re 1 with h1 | h1
      · rcases le_or_gt (-1) w.re with h2 | h2
        · omega
        · nlinarith only [h2, this]
      · nlinarith only [h1, this]
    have hw_norm2 : w.re ^ 2 + w.im ^ 2 = 1 := by simpa [Zsqrtd.norm_def, sq] using hw1
    have hcomp_re := congr_arg Zsqrtd.re hw
    have hcomp_im := congr_arg Zsqrtd.im hw
    simp only [piZ, Zsqrtd.star_mk, Zsqrtd.re_mul, Zsqrtd.im_mul] at hcomp_re hcomp_im
    rcases hre1 with hr | hr | hr
    · have him : w.im = 1 ∨ w.im = -1 := by
        rw [hr] at hw_norm2
        have : (w.im - 1) * (w.im + 1) = 0 := by linear_combination hw_norm2
        rcases mul_eq_zero.mp this with h | h <;> omega
      rcases him with hi | hi
      · simp [hr, hi] at hcomp_re
        have hu0 : u₀ = 0 := by omega
        have hv0 : v₀ = 0 := by omega
        rw [hu0, hv0] at huv
        norm_num at huv
        exact hp.ne_zero huv.symm
      · simp [hr, hi] at hcomp_re
        have huv_eq : u₀ = v₀ := by omega
        rw [huv_eq] at huv
        have h2p : 2 ∣ p := ⟨v₀ ^ 2, by rw [← huv]; ring⟩
        have h2eq : 2 = p := (Nat.dvd_prime hp).mp h2p |>.resolve_left (by decide)
        omega
    · have him : w.im = 0 := by rw [hr] at hw_norm2; nlinarith
      simp [hr, him] at hcomp_im
      have hv0 : v₀ = 0 := by omega
      rw [hv0] at huv
      have hsq : u₀ * u₀ = p := by nlinarith only [huv]
      rcases (Nat.dvd_prime hp).mp ⟨u₀, hsq.symm⟩ with h1 | hself
      · rw [h1] at hsq; exact hp.ne_one (by omega)
      · rw [hself] at hsq
        have hgt : p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
        omega
    · have him : w.im = 0 := by rw [hr] at hw_norm2; nlinarith
      simp [hr, him] at hcomp_re
      have hu0 : u₀ = 0 := by omega
      rw [hu0] at huv
      have hsq : v₀ * v₀ = p := by nlinarith only [huv]
      rcases (Nat.dvd_prime hp).mp ⟨v₀, hsq.symm⟩ with h1 | hself
      · rw [h1] at hsq; exact hp.ne_one (by omega)
      · rw [hself] at hsq
        have hgt : p < p * p := lt_mul_of_one_lt_right hp.pos hp.one_lt
        omega
  have hfactor : ∀ (k : ℕ) (z : GI), z.norm = (p : ℤ) ^ k →
      ∃ j ≤ k, Associated z (piZ ^ j * (star piZ) ^ (k - j)) := by
    intro k
    induction k with
    | zero =>
      intro z hz
      refine ⟨0, le_rfl, ?_⟩
      simp only [pow_zero, mul_one, tsub_zero]
      have hu : IsUnit z := (Zsqrtd.norm_eq_one_iff' (d := -1) (by decide) z).mp (by simpa using hz)
      exact ⟨hu.unit⁻¹, by simp⟩
    | succ k ih =>
      intro z hz
      have hp_dvd : piZ ∣ z * star z := by
        refine ⟨star piZ * (p : GI) ^ k, ?_⟩
        rw [← Zsqrtd.norm_eq_mul_conj z, hz]
        push_cast
        have hmul : piZ * star piZ = (p : GI) := by
          rw [← Zsqrtd.norm_eq_mul_conj piZ, hπ_norm]; push_cast; rfl
        rw [pow_succ', ← hmul]
        ring
      rcases hπ_prime.dvd_or_dvd hp_dvd with hd | hd
      · obtain ⟨w, rfl⟩ := hd
        have hw_norm : w.norm = (p : ℤ) ^ k := by
          rw [Zsqrtd.norm_mul, hπ_norm, pow_succ'] at hz
          have hppos : (0 : ℤ) < p := by omega
          nlinarith only [hz, hppos]
        obtain ⟨j, hjk, hw_ass⟩ := ih w hw_norm
        refine ⟨j + 1, by omega, ?_⟩
        rw [show k + 1 - (j + 1) = k - j by omega, pow_succ', mul_assoc]
        exact Associated.mul_left piZ hw_ass
      · have hstar_dvd : star piZ ∣ z := by
          obtain ⟨w, hw⟩ := hd
          refine ⟨star w, ?_⟩
          have := congr_arg star hw
          simpa [star_mul, star_star, mul_comm] using this
        obtain ⟨w, rfl⟩ := hstar_dvd
        have hw_norm : w.norm = (p : ℤ) ^ k := by
          rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hπ_norm, pow_succ'] at hz
          have hppos : (0 : ℤ) < p := by omega
          nlinarith only [hz, hppos]
        obtain ⟨j, hjk, hw_ass⟩ := ih w hw_norm
        refine ⟨j, by omega, ?_⟩
        have hstep : star piZ ^ (k + 1 - j) = star piZ * star piZ ^ (k - j) := by
          rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ']
        rw [hstep, show piZ ^ j * (star piZ * star piZ ^ (k - j)) =
          star piZ * (piZ ^ j * star piZ ^ (k - j)) by ring]
        exact Associated.mul_left (star piZ) hw_ass
  have ha_eq : a2 (p ^ e) = e + 1 := by
    unfold a2
    rw [← Finset.card_range (e + 1)]
    symm
    refine Finset.card_bij
      (fun j _ => let z := q1Normalize (piZ ^ j * star piZ ^ (e - j)); (z.re.natAbs, z.im.natAbs)) ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_range] at hj
      have hjle : j ≤ e := by omega
      have hne : piZ ^ j * star piZ ^ (e - j) ≠ 0 := by
        apply mul_ne_zero <;> exact pow_ne_zero _ (fun h0 => by
          have := congr_arg Zsqrtd.norm h0
          first | (rw [Zsqrtd.norm_zero, hπ_norm] at this; omega) |
                  (rw [Zsqrtd.norm_zero, Zsqrtd.norm_conj, hπ_norm] at this; omega))
      have hs := q1Normalize_spec hne
      rw [mem_q1Finset_iff]
      dsimp only
      refine ⟨Int.natAbs_pos.mpr hs.1.1.ne', ?_⟩
      have hnorm : (q1Normalize (piZ ^ j * star piZ ^ (e - j))).norm = (p : ℤ) ^ e := by
        rw [hs.2.1, Zsqrtd.norm_mul, gi_norm_pow, gi_norm_pow, Zsqrtd.norm_conj, hπ_norm,
          ← pow_add, show j + (e - j) = e by omega]
      zify
      rw [abs_of_pos hs.1.1, abs_of_nonneg hs.1.2]
      have : (q1Normalize (piZ ^ j * star piZ ^ (e - j))).re ^ 2 +
          (q1Normalize (piZ ^ j * star piZ ^ (e - j))).im ^ 2 =
          (q1Normalize (piZ ^ j * star piZ ^ (e - j))).norm := by
        simp [Zsqrtd.norm_def, sq]
      rw [this, hnorm]
    · intro j₁ hj₁ j₂ hj₂ heq
      rw [Finset.mem_range] at hj₁ hj₂
      have hne : ∀ j : ℕ, piZ ^ j * star piZ ^ (e - j) ≠ 0 := fun j =>
        mul_ne_zero (pow_ne_zero _ (fun h0 => by
          have hnrm := congr_arg Zsqrtd.norm h0
          rw [Zsqrtd.norm_zero, hπ_norm] at hnrm
          exact hp.ne_zero (by exact_mod_cast hnrm)))
          (pow_ne_zero _ (fun h0 => by
            have hnrm := congr_arg Zsqrtd.norm h0
            rw [Zsqrtd.norm_zero, Zsqrtd.norm_conj, hπ_norm] at hnrm
            exact hp.ne_zero (by exact_mod_cast hnrm)))
      have hs1 := q1Normalize_spec (hne j₁)
      have hs2 := q1Normalize_spec (hne j₂)
      dsimp only at heq
      simp only [Prod.mk.injEq] at heq
      have hnorm_eq : q1Normalize (piZ ^ j₁ * star piZ ^ (e - j₁)) =
          q1Normalize (piZ ^ j₂ * star piZ ^ (e - j₂)) := by
        ext
        · zify at heq; rw [← abs_of_pos hs1.1.1, ← abs_of_pos hs2.1.1]; exact_mod_cast heq.1
        · zify at heq; rw [← abs_of_nonneg hs1.1.2, ← abs_of_nonneg hs2.1.2]; exact_mod_cast heq.2
      have hass : Associated (piZ ^ j₁ * star piZ ^ (e - j₁)) (piZ ^ j₂ * star piZ ^ (e - j₂)) :=
        hs1.2.2.symm.trans (hnorm_eq ▸ hs2.2.2)
      by_contra hne_j
      have kill_lt : ∀ a b : ℕ, a < b → b ≤ e →
          Associated (piZ ^ a * star piZ ^ (e - a)) (piZ ^ b * star piZ ^ (e - b)) → False := by
        intro a b hab hbe hab_ass
        obtain ⟨u, hu⟩ := hab_ass
        have hae : star piZ ^ (e - a) = star piZ ^ (e - b) * star piZ ^ (b - a) := by
          rw [← pow_add, show (e - b) + (b - a) = e - a by omega]
        have hba : piZ ^ b = piZ ^ a * piZ ^ (b - a) := by
          rw [← pow_add, show a + (b - a) = b by omega]
        have hfact : (piZ ^ a * star piZ ^ (e - b)) * (star piZ ^ (b - a) * (u : GI)) =
            (piZ ^ a * star piZ ^ (e - b)) * piZ ^ (b - a) := by
          calc (piZ ^ a * star piZ ^ (e - b)) * (star piZ ^ (b - a) * (u : GI))
              = (piZ ^ a * star piZ ^ (e - a)) * (u : GI) := by rw [hae]; ring
            _ = piZ ^ b * star piZ ^ (e - b) := hu
            _ = (piZ ^ a * star piZ ^ (e - b)) * piZ ^ (b - a) := by rw [hba]; ring
        have hcommon_ne : piZ ^ a * star piZ ^ (e - b) ≠ 0 := by
          apply mul_ne_zero <;> exact pow_ne_zero _ (fun h0 => by
            have := congr_arg Zsqrtd.norm h0
            first | (rw [Zsqrtd.norm_zero, hπ_norm] at this; omega) |
                    (rw [Zsqrtd.norm_zero, Zsqrtd.norm_conj, hπ_norm] at this; omega))
        have hpow_eq := mul_left_cancel₀ hcommon_ne hfact
        have hdvd_pow : piZ ∣ star piZ ^ (b - a) := by
          have h1 : piZ ∣ piZ ^ (b - a) := dvd_pow_self piZ (by omega)
          have h2 : star piZ ^ (b - a) = piZ ^ (b - a) * ((u⁻¹ : GIˣ) : GI) := by
            rw [← hpow_eq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
          rw [h2]
          exact dvd_mul_of_dvd_left h1 _
        exact hπ_conj_not_dvd (hπ_prime.dvd_of_dvd_pow hdvd_pow)
      rcases lt_trichotomy j₁ j₂ with hlt | heqj | hgt
      · exact kill_lt j₁ j₂ hlt (by omega) hass
      · exact hne_j heqj
      · exact kill_lt j₂ j₁ hgt (by omega) hass.symm
    · rintro ⟨a, b⟩ hab
      rw [mem_q1Finset_iff] at hab
      dsimp only at hab
      let z : GI := ⟨a, b⟩
      have hz_norm : z.norm = (p : ℤ) ^ e := by
        simp only [z, Zsqrtd.norm_def]
        linear_combination (by exact_mod_cast hab.2 : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) ^ e)
      obtain ⟨j, hje, hass⟩ := hfactor e z hz_norm
      have hz_ne : z ≠ 0 := by
        intro h; have hre := congr_arg Zsqrtd.re h
        dsimp only [z] at hre; simp only [Zsqrtd.re_zero] at hre; omega
      have hpow_ne : piZ ^ j * star piZ ^ (e - j) ≠ 0 := by
        apply mul_ne_zero <;> exact pow_ne_zero _ (fun h0 => by
          have := congr_arg Zsqrtd.norm h0
          first | (rw [Zsqrtd.norm_zero, hπ_norm] at this; omega) |
                  (rw [Zsqrtd.norm_zero, Zsqrtd.norm_conj, hπ_norm] at this; omega))
      refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
      have hnormz : q1Normalize (piZ ^ j * star piZ ^ (e - j)) = z := by
        rw [q1Normalize_eq_of_associated hpow_ne hz_ne hass.symm]
        exact q1Normalize_eq_self ⟨by simp [z]; omega, by simp [z]⟩
      dsimp only
      rw [hnormz]
      simp [z]
  exact_mod_cast ha_eq

private lemma sum_divisors_χ4_mul {m n : ℕ} (hcop : m.Coprime n) :
    ∑ d ∈ (m * n).divisors, χ4 d =
      (∑ d₁ ∈ m.divisors, χ4 d₁) * ∑ d₂ ∈ n.divisors, χ4 d₂ := by
  rw [Finset.sum_mul_sum]
  symm
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun ab _ => ab.1 * ab.2) ?_ ?_ ?_ (fun ab _ => (χ4_mul ab.1 ab.2).symm)
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hab
    rw [Nat.mem_divisors]
    exact ⟨mul_dvd_mul hab.1.1 hab.2.1, mul_ne_zero hab.1.2 hab.2.2⟩
  · rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at h₁ h₂
    have ha1_cop : a₁.Coprime b₂ := hcop.coprime_dvd_left h₁.1.1 |>.coprime_dvd_right h₂.2.1
    have ha2_cop : a₂.Coprime b₁ := hcop.coprime_dvd_left h₂.1.1 |>.coprime_dvd_right h₁.2.1
    have ha12 : a₁ ∣ a₂ := ha1_cop.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a₁ b₁)
    have ha21 : a₂ ∣ a₁ := ha2_cop.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right a₂ b₂)
    have ha : a₁ = a₂ := Nat.dvd_antisymm ha12 ha21
    have ha0 : a₁ ≠ 0 := Nat.pos_of_ne_zero (fun h0 => h₁.1.2 (zero_dvd_iff.mp (h0 ▸ h₁.1.1))) |>.ne'
    have hb : b₁ = b₂ := mul_left_cancel₀ ha0 (ha ▸ heq)
    exact Prod.ext ha hb
  · rintro d hd
    rw [Nat.mem_divisors] at hd
    rcases hd with ⟨hdvd, hmn0⟩
    have hm0 : m ≠ 0 := left_ne_zero_of_mul hmn0
    let a := d.gcd m
    let b := d / a
    have ha_dvd_d : a ∣ d := Nat.gcd_dvd_left d m
    have ha_dvd_m : a ∣ m := Nat.gcd_dvd_right d m
    have ha_pos : 0 < a := Nat.gcd_pos_of_pos_right d (Nat.pos_of_ne_zero hm0)
    have hcop_ba : b.Coprime (m / a) := Nat.coprime_div_gcd_div_gcd ha_pos
    have hprod_dvd : a * b ∣ a * (m / a * n) := by
      rw [Nat.mul_div_cancel' ha_dvd_d, ← mul_assoc, Nat.mul_div_cancel' ha_dvd_m]
      exact hdvd
    have hb_dvd_prod : b ∣ (m / a) * n := Nat.dvd_of_mul_dvd_mul_left ha_pos hprod_dvd
    have hb_dvd_n : b ∣ n := hcop_ba.dvd_of_dvd_mul_left hb_dvd_prod
    refine ⟨(a, b), ?_, Nat.mul_div_cancel' ha_dvd_d⟩
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
    exact ⟨⟨ha_dvd_m, hm0⟩, ⟨hb_dvd_n, right_ne_zero_of_mul hmn0⟩⟩

private lemma a2_eq_sum_χ4 : ∀ {k : ℕ}, 1 ≤ k → (a2 k : ℤ) = ∑ d ∈ k.divisors, χ4 d := by
  intro k hk
  induction k using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simpa using a2_two_pow 0
  | prime_pow p e hp _ =>
    rcases hp.eq_two_or_odd with rfl | hp_odd
    · exact a2_two_pow e
    · have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases hmod4 with h1 | h3
      · exact a2_mod_four_eq_one hp h1 e
      · exact a2_mod_four_eq_three hp h3 e
  | coprime a b ha hb hcop iha ihb =>
    rw [a2_mul_of_coprime (by omega) (by omega) hcop, sum_divisors_χ4_mul hcop]
    push_cast
    rw [iha (by omega), ihb (by omega)]

private lemma card_Icc_filter_dvd (M d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 M).filter (d ∣ ·)).card = M / d := by
  rw [← Finset.card_range (M / d)]
  symm
  refine Finset.card_bij (fun t _ => d * (t + 1)) ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_range] at ht
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hmul : d * (t + 1) ≤ M := by
      calc d * (t + 1) = (t + 1) * d := Nat.mul_comm _ _
        _ ≤ M := Nat.mul_le_of_le_div d (t + 1) M (by omega)
    exact ⟨⟨by nlinarith only [hd], hmul⟩, dvd_mul_right d (t + 1)⟩
  · intro t₁ _ t₂ _ heq
    have : t₁ + 1 = t₂ + 1 := mul_left_cancel₀ (by omega) heq
    omega
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    have hq_pos : 1 ≤ k / d := Nat.div_pos (Nat.le_of_dvd hk.1.1 hk.2) (by omega)
    have hq_le : k / d ≤ M / d := Nat.div_le_div_right hk.1.2
    refine ⟨k / d - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel hq_pos]
    exact Nat.mul_div_cancel' hk.2

private lemma floor_div_nat_eq_nat_div {r : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    ⌊r ^ 2 / (d : ℝ)⌋ = ((⌊r ^ 2⌋₊ / d : ℕ) : ℤ) := by
  rw [Int.floor_eq_iff]
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  let M := ⌊r ^ 2⌋₊
  have hM_le : (M : ℝ) ≤ r ^ 2 := Nat.floor_le (sq_nonneg r)
  have hlt_M : r ^ 2 < (M : ℝ) + 1 := Nat.lt_floor_add_one (r ^ 2)
  have hnat1 : (M / d) * d ≤ M := Nat.div_mul_le_self M d
  have hnat2 : M + 1 ≤ (M / d + 1) * d := by
    have hdm : d * (M / d) + M % d = M := Nat.div_add_mod M d
    have hlt : M % d < d := Nat.mod_lt M hd
    nlinarith only [hdm, hlt]
  have hr1 : ((M / d : ℕ) : ℝ) * d ≤ r ^ 2 := by
    have : ((M / d : ℕ) : ℝ) * d ≤ M := by exact_mod_cast hnat1
    linarith only [this, hM_le]
  have hr2 : r ^ 2 < (((M / d : ℕ) : ℝ) + 1) * d := by
    have : (M : ℝ) + 1 ≤ (((M / d : ℕ) : ℝ) + 1) * d := by exact_mod_cast hnat2
    linarith only [this, hlt_M]
  constructor
  · exact (le_div_iff₀ hd_pos).mpr (by exact_mod_cast hr1)
  · exact (div_lt_iff₀ hd_pos).mpr (by exact_mod_cast hr2)

end JacobiFormula

/--
The exact number of integer lattice points in the closed disk of radius `r ≥ 0` is given by
`N r = 1 + 4 * ∑' i, (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋)`.
Matches `GaussCircleProblem.exact_form_floor` definitionally.
-/
theorem exact_form_floor (r : ℝ) (hr : 0 ≤ r) :
    (N r : ℤ) = 1 + 4 * ∑' (i : ℕ), (⌊r ^ 2 / (4 * i + 1)⌋ - ⌊r ^ 2 / (4 * i + 3)⌋) := by
  let M := ⌊r ^ 2⌋₊
  have hN : (N r : ℤ) = 1 + 4 * ∑ k ∈ Finset.Icc 1 M, (a2 k : ℤ) := by
    rw [N_eq_card_latticeFinset hr]
    have hsplit : latticeFinset M = (Finset.Icc 0 M).biUnion r2Finset := by
      ext p
      rw [Finset.mem_biUnion, mem_latticeFinset_iff]
      constructor
      · intro hp
        have hnn : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
        refine ⟨(p.1 ^ 2 + p.2 ^ 2).toNat, Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩,
          mem_r2Finset_iff.mpr ?_⟩
        · rw [← Int.ofNat_le, Int.toNat_of_nonneg hnn]; exact hp
        · exact (Int.toNat_of_nonneg hnn).symm
      · rintro ⟨k, hk, hp⟩
        rw [mem_r2Finset_iff] at hp
        rw [Finset.mem_Icc] at hk
        rw [hp]
        exact_mod_cast hk.2
    have hdisj : Set.PairwiseDisjoint (Finset.Icc 0 M : Set ℕ) r2Finset := by
      intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp₁ hp₂
      rw [mem_r2Finset_iff] at hp₁ hp₂
      have : (k₁ : ℤ) = k₂ := hp₁.symm.trans hp₂
      exact hne (by exact_mod_cast this)
    rw [hsplit, Finset.card_biUnion hdisj]
    have hIcc : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
      ext x; rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert (by simp), r2Finset_zero]
    have h4mul : ∑ k ∈ Finset.Icc 1 M, (r2Finset k).card =
        ∑ k ∈ Finset.Icc 1 M, 4 * a2 k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      exact r2_eq_four_mul_a2 (Finset.mem_Icc.mp hk).1
    rw [h4mul, ← Finset.mul_sum]
    push_cast
    rfl
  have hsum_a2 : ∑ k ∈ Finset.Icc 1 M, (a2 k : ℤ) =
      ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℤ) * χ4 d := by
    have h1 : ∑ k ∈ Finset.Icc 1 M, (a2 k : ℤ) =
        ∑ k ∈ Finset.Icc 1 M, ∑ d ∈ k.divisors, χ4 d := by
      refine Finset.sum_congr rfl fun k hk => ?_
      exact a2_eq_sum_χ4 (Finset.mem_Icc.mp hk).1
    rw [h1]
    have hfiber : ∀ k ∈ Finset.Icc 1 M,
        ∑ d ∈ k.divisors, χ4 d =
          ∑ d ∈ Finset.Icc 1 M, if d ∣ k then χ4 d else 0 := by
      intro k hk
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_le : k ≤ M := (Finset.mem_Icc.mp hk).2
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_dvd_iff] at hdvd; omega),
          (Nat.le_of_dvd (by omega) hdvd).trans hk_le⟩, hdvd⟩
      · rintro ⟨⟨_, _⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [Finset.sum_congr rfl hfiber, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      card_Icc_filter_dvd M d (Finset.mem_Icc.mp hd).1]
  let f : ℕ → ℤ := fun i => ⌊r ^ 2 / (4 * (i : ℝ) + 1)⌋ - ⌊r ^ 2 / (4 * (i : ℝ) + 3)⌋
  have htsum_eq : ∑' i : ℕ, f i = ∑ i ∈ Finset.range (M + 1), f i := by
    refine tsum_eq_sum fun i hi => ?_
    rw [Finset.mem_range, not_lt] at hi
    have h1 : M < 4 * i + 1 := by omega
    have h3 : M < 4 * i + 3 := by omega
    have hzero : ∀ d : ℕ, M < d → ⌊r ^ 2 / (d : ℝ)⌋ = 0 := by
      intro d hd
      rw [Int.floor_eq_iff]
      have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
      have hlt_M : r ^ 2 < (M : ℝ) + 1 := Nat.lt_floor_add_one (r ^ 2)
      have hMd : (M : ℝ) + 1 ≤ d := by exact_mod_cast hd
      push_cast
      rw [zero_add]
      exact ⟨div_nonneg (sq_nonneg r) hdpos.le, (div_lt_one hdpos).mpr (lt_of_lt_of_le hlt_M hMd)⟩
    have hf1 := hzero (4 * i + 1) h1
    have hf3 := hzero (4 * i + 3) h3
    push_cast at hf1 hf3
    simp only [f, hf1, hf3, sub_self]
  have hsum_range : ∑ i ∈ Finset.range (M + 1), f i =
      ∑ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℤ) * χ4 d := by
    have hrewrite : ∀ i : ℕ, f i =
        (if 4 * i + 1 ≤ M then ((M / (4 * i + 1) : ℕ) : ℤ) else 0) -
        (if 4 * i + 3 ≤ M then ((M / (4 * i + 3) : ℕ) : ℤ) else 0) := by
      intro i
      dsimp only [f]
      have hf1 : ⌊r ^ 2 / (4 * (i : ℝ) + 1)⌋ =
          if 4 * i + 1 ≤ M then ((M / (4 * i + 1) : ℕ) : ℤ) else 0 := by
        split_ifs with h
        · have := floor_div_nat_eq_nat_div (r := r) (d := 4 * i + 1) (by omega)
          push_cast at this; exact this
        · rw [Int.floor_eq_iff]
          have hdpos : (0 : ℝ) < 4 * (i : ℝ) + 1 := by positivity
          have hlt_M : r ^ 2 < (M : ℝ) + 1 := Nat.lt_floor_add_one (r ^ 2)
          have hMd : (M : ℝ) + 1 ≤ 4 * (i : ℝ) + 1 := by exact_mod_cast (by omega : M + 1 ≤ 4 * i + 1)
          push_cast
          rw [zero_add]
          exact ⟨div_nonneg (sq_nonneg r) hdpos.le,
            (div_lt_one hdpos).mpr (lt_of_lt_of_le hlt_M hMd)⟩
      have hf3 : ⌊r ^ 2 / (4 * (i : ℝ) + 3)⌋ =
          if 4 * i + 3 ≤ M then ((M / (4 * i + 3) : ℕ) : ℤ) else 0 := by
        split_ifs with h
        · have := floor_div_nat_eq_nat_div (r := r) (d := 4 * i + 3) (by omega)
          push_cast at this; exact this
        · rw [Int.floor_eq_iff]
          have hdpos : (0 : ℝ) < 4 * (i : ℝ) + 3 := by positivity
          have hlt_M : r ^ 2 < (M : ℝ) + 1 := Nat.lt_floor_add_one (r ^ 2)
          have hMd : (M : ℝ) + 1 ≤ 4 * (i : ℝ) + 3 := by exact_mod_cast (by omega : M + 1 ≤ 4 * i + 3)
          push_cast
          rw [zero_add]
          exact ⟨div_nonneg (sq_nonneg r) hdpos.le,
            (div_lt_one hdpos).mpr (lt_of_lt_of_le hlt_M hMd)⟩
      rw [hf1, hf3]
    rw [Finset.sum_congr rfl (fun i _ => hrewrite i), Finset.sum_sub_distrib]
    have hsum1 : ∑ i ∈ Finset.range (M + 1),
          (if 4 * i + 1 ≤ M then ((M / (4 * i + 1) : ℕ) : ℤ) else 0) =
        ∑ d ∈ (Finset.Icc 1 M).filter (· % 4 = 1), ((M / d : ℕ) : ℤ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i _ => 4 * i + 1) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hi.2⟩, by omega⟩
      · intro i₁ _ i₂ _ h; omega
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        refine ⟨d / 4, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
    have hsum3 : ∑ i ∈ Finset.range (M + 1),
          (if 4 * i + 3 ≤ M then ((M / (4 * i + 3) : ℕ) : ℤ) else 0) =
        ∑ d ∈ (Finset.Icc 1 M).filter (· % 4 = 3), ((M / d : ℕ) : ℤ) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i _ => 4 * i + 3) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro i hi
        rw [Finset.mem_filter, Finset.mem_range] at hi
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hi.2⟩, by omega⟩
      · intro i₁ _ i₂ _ h; omega
      · intro d hd
        rw [Finset.mem_filter, Finset.mem_Icc] at hd
        refine ⟨d / 4, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
    rw [hsum1, hsum3]
    have hpart : ∀ d ∈ Finset.Icc 1 M, ((M / d : ℕ) : ℤ) * χ4 d =
        (if d % 4 = 1 then ((M / d : ℕ) : ℤ) else 0) -
        (if d % 4 = 3 then ((M / d : ℕ) : ℤ) else 0) := by
      intro d _
      unfold χ4
      have : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
      rcases this with h | h | h | h
      · have h2 : d % 2 = 0 := by omega
        simp [h, h2]
      · have h2 : d % 2 ≠ 0 := by omega
        simp [h, h2]
      · have h2 : d % 2 = 0 := by omega
        simp [h, h2]
      · have h2 : d % 2 ≠ 0 := by omega
        simp [h, h2]
    rw [Finset.sum_congr rfl hpart, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  rw [hN, hsum_a2, ← hsum_range, ← htsum_eq]

end Contribution.GaussCircleProblem
