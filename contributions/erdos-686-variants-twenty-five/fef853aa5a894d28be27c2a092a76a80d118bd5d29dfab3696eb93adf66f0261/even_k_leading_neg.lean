import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Universal Even-k Remainder Leading-Coefficient Sign Theorem (`lc(R_r) < 0` for ALL `r ≥ 1`)

Proves unconditionally for **all** integers `r ≥ 1` (`k = 2 * r`) that for the unique monic
polynomial `Q_r ∈ ℚ[X]` (or `ℝ[X]`) of degree `r` truncating the Puiseux square-root expansion
of `P_{2r}(X) = ∏_{j=1}^r (X^2 - (2j - 1)^2)` up to `(P_{2r} - Q_r^2).coeff k = 0` for all
`k > degR r := 2 * ((r - 1) / 2)`, the remainder `R_r := P_{2r} - Q_r^2` satisfies
`R_r.natDegree = degR r` and **`R_r.leadingCoeff < 0`**.
-/

namespace Contribution.Erdos686EvenKLeadingNegTwentyFive

open scoped Real

/-! ## 1. Polynomial Setup, Existence, and Uniqueness -/

/-- Exact remainder degree bound: `r - 2` when `r ≥ 2` is even, `r - 1` when `r ≥ 1` is odd. -/
def degR (r : ℕ) : ℕ := 2 * ((r - 1) / 2)

lemma degR_lt {r : ℕ} (hr : 1 ≤ r) : degR r < r := by
  dsimp [degR]; omega

lemma degR_add_eq {r : ℕ} (hr : 1 ≤ r) : degR r + 2 * (r / 2 + 1) = 2 * r := by
  dsimp [degR]; omega

/-- Symmetric even polynomial `P_{2r}(X) = ∏_{j=1}^r (X^2 - (2j - 1)^2)` over `ℚ`. -/
noncomputable def P_even_poly (r : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.Icc 1 r, (Polynomial.X ^ 2 - Polynomial.C (((2 * j - 1 : ℕ) : ℚ) ^ 2))

noncomputable def P_even_poly_real (r : ℕ) : Polynomial ℝ :=
  (P_even_poly r).map (algebraMap ℚ ℝ)

private lemma xsq_sub_c_monic (c : ℚ) :
    (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).Monic := by
  refine (Polynomial.monic_X_pow 2).sub_of_left ?_
  by_cases hc : c = 0
  · simp [hc]
    decide
  · simp [Polynomial.degree_C hc]

private lemma xsq_sub_c_natDegree (c : ℚ) :
    (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).natDegree = 2 := by
  have hd : (Polynomial.C c : Polynomial ℚ).natDegree < (Polynomial.X ^ 2 : Polynomial ℚ).natDegree := by
    simp
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hd, Polynomial.natDegree_X_pow]

private lemma xsq_sub_c_odd_coeff (c : ℚ) {k : ℕ} (hk : Odd k) :
    (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℚ).coeff k = 0 := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  have hk2 : k ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hk
  have hk0 : k ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd 0) hk
  simp [hk2, hk0]

lemma P_even_poly_monic (r : ℕ) : (P_even_poly r).Monic := by
  dsimp [P_even_poly]
  exact Polynomial.monic_prod_of_monic _ _ fun j _ => xsq_sub_c_monic _

lemma P_even_poly_natDegree (r : ℕ) : (P_even_poly r).natDegree = 2 * r := by
  induction r with
  | zero => simp [P_even_poly]
  | succ r ih =>
    have hsplit : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : r + 1 ∉ Finset.Icc 1 r := by simp
    have hstep : P_even_poly (r + 1) =
        (Polynomial.X ^ 2 - Polynomial.C (((2 * (r + 1) - 1 : ℕ) : ℚ) ^ 2)) * P_even_poly r := by
      dsimp [P_even_poly]
      rw [hsplit, Finset.prod_insert hnot]
    rw [hstep, Polynomial.natDegree_mul (xsq_sub_c_monic _).ne_zero (P_even_poly_monic r).ne_zero,
      xsq_sub_c_natDegree, ih]
    ring

lemma P_even_poly_odd_coeff (r : ℕ) : ∀ {k : ℕ}, Odd k → (P_even_poly r).coeff k = 0 := by
  induction r with
  | zero =>
    intro k hk
    simp only [P_even_poly, Finset.Icc_eq_empty_of_lt (by decide : 0 < 1), Finset.prod_empty,
      Polynomial.coeff_one]
    have hk0 : k ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd 0) hk
    simp [hk0]
  | succ r ih =>
    have hsplit : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : r + 1 ∉ Finset.Icc 1 r := by simp
    have hstep : P_even_poly (r + 1) =
        (Polynomial.X ^ 2 - Polynomial.C (((2 * (r + 1) - 1 : ℕ) : ℚ) ^ 2)) * P_even_poly r := by
      dsimp [P_even_poly]
      rw [hsplit, Finset.prod_insert hnot]
    intro k hk
    rw [hstep, Polynomial.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    have hpar : Odd ab.1 ∨ Odd ab.2 := by
      by_contra h
      push Not at h
      have hev1 : Even ab.1 := Nat.not_odd_iff_even.mp h.1
      have hev2 : Even ab.2 := Nat.not_odd_iff_even.mp h.2
      exact (Nat.not_odd_iff_even.mpr (hab ▸ hev1.add hev2)) hk
    rcases hpar with h1 | h2
    · rw [xsq_sub_c_odd_coeff _ h1, zero_mul]
    · rw [ih h2, mul_zero]

lemma P_even_poly_real_monic (r : ℕ) : (P_even_poly_real r).Monic :=
  (P_even_poly_monic r).map (algebraMap ℚ ℝ)

lemma P_even_poly_real_natDegree (r : ℕ) : (P_even_poly_real r).natDegree = 2 * r := by
  rw [P_even_poly_real, (P_even_poly_monic r).natDegree_map, P_even_poly_natDegree]

lemma P_even_poly_real_coeff_odd {r k : ℕ} (hk : Odd k) :
    (P_even_poly_real r).coeff k = 0 := by
  simp [P_even_poly_real, P_even_poly_odd_coeff r hk]

/-- Inductive coefficients `qCoeff r t` of the square-root truncation polynomial `Q_r`. -/
noncomputable def qCoeff (r : ℕ) : ℕ → ℚ
  | 0 => 1
  | t + 1 => ((P_even_poly r).coeff (2 * r - 2 * (t + 1)) -
      ∑ j : Finset.Icc 1 t, qCoeff r j.1 * qCoeff r (t + 1 - j.1)) / 2
termination_by t => t
decreasing_by
  all_goals
    have hj := j.2
    rw [Finset.mem_Icc] at hj
    omega

private lemma qCoeff_zero (r : ℕ) : qCoeff r 0 = 1 := by simp [qCoeff]

private lemma qCoeff_succ (r t : ℕ) :
    qCoeff r (t + 1) = ((P_even_poly r).coeff (2 * r - 2 * (t + 1)) -
      ∑ j ∈ Finset.Icc 1 t, qCoeff r j * qCoeff r (t + 1 - j)) / 2 := by
  rw [qCoeff]
  congr 2
  exact (Finset.sum_coe_sort (Finset.Icc 1 t) (fun j => qCoeff r j * qCoeff r (t + 1 - j)))

/-- Explicit monic polynomial square-root truncation `Q_r ∈ ℚ[X]` of degree `r`. -/
noncomputable def Q_even_poly (r : ℕ) : Polynomial ℚ :=
  ∑ t ∈ Finset.range (r / 2 + 1), Polynomial.C (qCoeff r t) * Polynomial.X ^ (r - 2 * t)

private lemma Q_even_poly_coeff_of_ge {r k : ℕ} (hk : r ≤ k) :
    (Q_even_poly r).coeff k = if k = r then 1 else 0 := by
  dsimp [Q_even_poly]
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rcases eq_or_lt_of_le hk with rfl | hgt
  · have hmem : 0 ∈ Finset.range (r / 2 + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single 0]
    · simp [qCoeff_zero]
    · intro b hb hb0
      rw [Finset.mem_range] at hb
      have hne : r ≠ r - 2 * b := by omega
      simp [hne]
    · intro hnot; exact absurd hmem hnot
  · rw [if_neg hgt.ne']
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : k ≠ r - 2 * b := by omega
    simp [hne]

lemma Q_even_poly_natDegree (r : ℕ) : (Q_even_poly r).natDegree = r := by
  refine le_antisymm ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [Q_even_poly_coeff_of_ge hk.le, if_neg hk.ne']
  · exact Polynomial.le_natDegree_of_ne_zero
      (by rw [Q_even_poly_coeff_of_ge le_rfl, if_pos rfl]; exact one_ne_zero)

lemma Q_even_poly_monic (r : ℕ) : (Q_even_poly r).Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, Q_even_poly_natDegree,
    Q_even_poly_coeff_of_ge le_rfl, if_pos rfl]

private lemma Q_even_poly_sq_coeff (r : ℕ) {t : ℕ} (ht : t ≤ r / 2) :
    ((Q_even_poly r) ^ 2).coeff (2 * r - 2 * t) =
      ∑ j ∈ Finset.range (t + 1), qCoeff r j * qCoeff r (t - j) := by
  rw [sq, Polynomial.coeff_mul]
  have hQ_coeff (k : ℕ) :
      (Q_even_poly r).coeff k =
        ∑ s ∈ Finset.range (r / 2 + 1), if k = r - 2 * s then qCoeff r s else 0 := by
    dsimp [Q_even_poly]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
  have hsum_anti :
      ∑ ab ∈ Finset.antidiagonal (2 * r - 2 * t),
        (Q_even_poly r).coeff ab.1 * (Q_even_poly r).coeff ab.2 =
      ∑ j ∈ Finset.range (t + 1),
        (Q_even_poly r).coeff (r - 2 * j) * (Q_even_poly r).coeff (r - 2 * (t - j)) := by
    refine Finset.sum_bij_ne_zero (fun ab _ _ => (r - ab.1) / 2) ?hi ?hinj ?hsurj ?heq
    · intro ab hab hne
      rw [Finset.mem_antidiagonal] at hab
      have hle1 : ab.1 ≤ r := by
        by_contra hgt
        have hzero : (Q_even_poly r).coeff ab.1 = 0 := by
          rw [Q_even_poly_coeff_of_ge (by omega), if_neg (by omega)]
        exact hne (by simp [hzero])
      have hle2 : ab.2 ≤ r := by
        by_contra hgt
        have hzero : (Q_even_poly r).coeff ab.2 = 0 := by
          rw [Q_even_poly_coeff_of_ge (by omega), if_neg (by omega)]
        exact hne (by simp [hzero])
      rw [Finset.mem_range]
      omega
    · intro ab₁ hab₁ hne₁ ab₂ hab₂ hne₂ heq
      rw [Finset.mem_antidiagonal] at hab₁ hab₂
      have hpar1 : 2 ∣ r - ab₁.1 := by
        by_contra hodd
        rw [hQ_coeff ab₁.1] at hne₁
        have hz : ∑ s ∈ Finset.range (r / 2 + 1), (if ab₁.1 = r - 2 * s then qCoeff r s else 0) = 0 := by
          refine Finset.sum_eq_zero fun s hs => ?_
          rw [if_neg]
          intro he
          apply hodd
          have hs_le : 2 * s ≤ r := by rw [Finset.mem_range] at hs; omega
          omega
        exact hne₁ (by simp [hz])
      have hpar2 : 2 ∣ r - ab₂.1 := by
        by_contra hodd
        rw [hQ_coeff ab₂.1] at hne₂
        have hz : ∑ s ∈ Finset.range (r / 2 + 1), (if ab₂.1 = r - 2 * s then qCoeff r s else 0) = 0 := by
          refine Finset.sum_eq_zero fun s hs => ?_
          rw [if_neg]
          intro he
          apply hodd
          have hs_le : 2 * s ≤ r := by rw [Finset.mem_range] at hs; omega
          omega
        exact hne₂ (by simp [hz])
      have hle1 : ab₁.1 ≤ r := by
        by_contra hgt
        have hzero : (Q_even_poly r).coeff ab₁.1 = 0 := by
          rw [Q_even_poly_coeff_of_ge (by omega), if_neg (by omega)]
        exact hne₁ (by simp [hzero])
      have hle2 : ab₂.1 ≤ r := by
        by_contra hgt
        have hzero : (Q_even_poly r).coeff ab₂.1 = 0 := by
          rw [Q_even_poly_coeff_of_ge (by omega), if_neg (by omega)]
        exact hne₂ (by simp [hzero])
      ext <;> omega
    · intro j hj hne
      rw [Finset.mem_range] at hj
      refine ⟨(r - 2 * j, r - 2 * (t - j)), Finset.mem_antidiagonal.mpr (by omega), hne, ?_⟩
      omega
    · intro ab hab hne
      rw [Finset.mem_antidiagonal] at hab
      have hpar1 : 2 ∣ r - ab.1 := by
        by_contra hodd
        rw [hQ_coeff ab.1] at hne
        have hz : ∑ s ∈ Finset.range (r / 2 + 1), (if ab.1 = r - 2 * s then qCoeff r s else 0) = 0 := by
          refine Finset.sum_eq_zero fun s hs => ?_
          rw [if_neg]
          intro he
          apply hodd
          have hs_le : 2 * s ≤ r := by rw [Finset.mem_range] at hs; omega
          omega
        exact hne (by simp [hz])
      have hle1 : ab.1 ≤ r := by
        by_contra hgt
        have hzero : (Q_even_poly r).coeff ab.1 = 0 := by
          rw [Q_even_poly_coeff_of_ge (by omega), if_neg (by omega)]
        exact hne (by simp [hzero])
      have hle2 : ab.2 ≤ r := by
        by_contra hgt
        have hzero : (Q_even_poly r).coeff ab.2 = 0 := by
          rw [Q_even_poly_coeff_of_ge (by omega), if_neg (by omega)]
        exact hne (by simp [hzero])
      congr 1 <;> congr 1 <;> omega
  rw [hsum_anti]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hc (s : ℕ) (hs : s ≤ r / 2) : (Q_even_poly r).coeff (r - 2 * s) = qCoeff r s := by
    rw [hQ_coeff, Finset.sum_eq_single s]
    · simp
    · intro b hb hne
      rw [if_neg]
      rw [Finset.mem_range] at hb
      omega
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  rw [hc j (by omega), hc (t - j) (by omega)]

private lemma Q_even_poly_coeff_odd_par {r k : ℕ} (hk : Odd (2 * r - k)) (_hkle : k ≤ 2 * r) :
    ((Q_even_poly r) ^ 2).coeff k = 0 := by
  rw [sq, Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  have hQ_odd_diff (x : ℕ) (hx : ¬ 2 ∣ r - x ∨ r < x) : (Q_even_poly r).coeff x = 0 := by
    rcases hx with hnd | hgt
    · dsimp [Q_even_poly]
      rw [Polynomial.finsetSum_coeff]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      rw [Finset.mem_range] at hs
      intro he
      apply hnd
      omega
    · rw [Q_even_poly_coeff_of_ge hgt.le, if_neg hgt.ne']
  have hdisj : (¬ 2 ∣ r - ab.1 ∨ r < ab.1) ∨ (¬ 2 ∣ r - ab.2 ∨ r < ab.2) := by
    by_contra hnone
    push Not at hnone
    rcases hnone with ⟨⟨h1, hl1⟩, ⟨h2, hl2⟩⟩
    obtain ⟨a1, ha1⟩ := h1
    obtain ⟨a2, ha2⟩ := h2
    have hk_even : Even k := by
      have : k = 2 * (r - a1 - a2) := by omega
      exact ⟨r - a1 - a2, by omega⟩
    have h2rk_even : Even (2 * r - k) := by
      obtain ⟨c, hc⟩ := hk_even
      exact ⟨r - c, by omega⟩
    exact (Nat.not_odd_iff_even.mpr h2rk_even) hk
  rcases hdisj with h1 | h2
  · rw [hQ_odd_diff ab.1 h1, zero_mul]
  · rw [hQ_odd_diff ab.2 h2, mul_zero]

theorem P_sub_Q_sq_coeff_zero_of_gt {r : ℕ} (hr : 1 ≤ r) :
    ∀ k : ℕ, degR r < k → (P_even_poly r - (Q_even_poly r) ^ 2).coeff k = 0 := by
  intro k hk
  rw [Polynomial.coeff_sub, sub_eq_zero]
  by_cases hgt : 2 * r < k
  · have hP0 : (P_even_poly r).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [P_even_poly_natDegree]; exact hgt)
    have hQ0 : ((Q_even_poly r) ^ 2).coeff k = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      calc ((Q_even_poly r) ^ 2).natDegree ≤ (Q_even_poly r).natDegree + (Q_even_poly r).natDegree := by
            rw [sq]; exact Polynomial.natDegree_mul_le
        _ = 2 * r := by rw [Q_even_poly_natDegree]; ring
        _ < k := hgt
    rw [hP0, hQ0]
  · have hkle : k ≤ 2 * r := by omega
    by_cases hodd : Odd k
    · have h2rk_odd : Odd (2 * r - k) := by
        obtain ⟨c, hc⟩ := hodd
        exact ⟨r - 1 - c, by omega⟩
      rw [P_even_poly_odd_coeff r hodd, Q_even_poly_coeff_odd_par h2rk_odd hkle]
    · have hev : Even k := Nat.not_odd_iff_even.mp hodd
      obtain ⟨u, hu⟩ := hev
      set t := r - u
      have ht_le : t ≤ r / 2 := by
        have hdeg := degR_add_eq hr
        omega
      have hk_eq : k = 2 * r - 2 * t := by omega
      rw [hk_eq, Q_even_poly_sq_coeff r ht_le]
      rcases t with _ | s
      · simp only [Nat.mul_zero, Nat.sub_zero, Nat.zero_add, Finset.sum_range_one]
        rw [qCoeff_zero, mul_one, ← P_even_poly_natDegree r]
        exact (P_even_poly_monic r).leadingCoeff
      · have hsum_split :
            ∑ j ∈ Finset.range (s + 2), qCoeff r j * qCoeff r (s + 1 - j) =
              qCoeff r 0 * qCoeff r (s + 1) +
              (∑ j ∈ Finset.Icc 1 s, qCoeff r j * qCoeff r (s + 1 - j)) +
              qCoeff r (s + 1) * qCoeff r 0 := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ']
          simp only [Nat.sub_self, Nat.sub_zero]
          have hIcc : ∑ j ∈ Finset.range s, qCoeff r (j + 1) * qCoeff r (s + 1 - (j + 1)) =
              ∑ j ∈ Finset.Icc 1 s, qCoeff r j * qCoeff r (s + 1 - j) := by
            refine Finset.sum_nbij (· + 1)
              (fun j hj => by rw [Finset.mem_range] at hj; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
              (fun a _ b _ h => by dsimp only at h; omega)
              (fun y hy => by
                rw [Finset.mem_coe, Finset.mem_Icc] at hy
                exact ⟨y - 1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩)
              (fun _ _ => rfl)
          rw [hIcc]
          ring
        rw [hsum_split, qCoeff_succ, qCoeff_zero]
        ring

theorem exists_unique_square_root_truncation {r : ℕ} (hr : 1 ≤ r) :
    ∃! Q : Polynomial ℝ,
      Q.Monic ∧ Q.natDegree = r ∧
      ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q ^ 2).coeff k = 0 := by
  set Q0 : Polynomial ℝ := (Q_even_poly r).map (algebraMap ℚ ℝ)
  have hQ0_monic : Q0.Monic := (Q_even_poly_monic r).map _
  have hQ0_deg : Q0.natDegree = r := by
    dsimp only [Q0]
    rw [(Q_even_poly_monic r).natDegree_map, Q_even_poly_natDegree]
  have hQ0_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q0 ^ 2).coeff k = 0 := by
    intro k hk
    have hq := P_sub_Q_sq_coeff_zero_of_gt hr k hk
    have hmap : P_even_poly_real r - Q0 ^ 2 =
        (P_even_poly r - (Q_even_poly r) ^ 2).map (algebraMap ℚ ℝ) := by
      simp [P_even_poly_real, Q0, Polynomial.map_sub, Polynomial.map_pow]
    rw [hmap, Polynomial.coeff_map, hq, map_zero]
  refine ⟨Q0, ⟨hQ0_monic, hQ0_deg, hQ0_zero⟩, ?_⟩
  · rintro Q₁ ⟨hQ1_monic, hQ1_deg, hQ1_zero⟩
    by_contra hne
    have hdiff_ne : Q₁ - Q0 ≠ 0 := sub_ne_zero.mpr hne
    have hsum_deg : (Q₁ + Q0).natDegree = r := by
      have hlc : (Q₁ + Q0).coeff r = 2 := by
        rw [Polynomial.coeff_add]
        have hc1 : Q₁.coeff r = 1 := by rw [← hQ1_deg]; exact hQ1_monic.leadingCoeff
        have hc0 : Q0.coeff r = 1 := by rw [← hQ0_deg]; exact hQ0_monic.leadingCoeff
        rw [hc1, hc0]
        norm_num
      refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero (by rw [hlc]; norm_num))
      exact (Polynomial.natDegree_add_le Q₁ Q0).trans (by rw [hQ1_deg, hQ0_deg, max_self])
    have hsum_ne : Q₁ + Q0 ≠ 0 := by
      intro hz
      rw [hz, Polynomial.natDegree_zero] at hsum_deg
      omega
    set N := ((Q₁ - Q0) * (Q₁ + Q0)).natDegree
    have hprod_deg : N = (Q₁ - Q0).natDegree + r := by
      dsimp only [N]
      rw [Polynomial.natDegree_mul hdiff_ne hsum_ne, hsum_deg]
    have hprod_ne : (Q₁ - Q0) * (Q₁ + Q0) ≠ 0 := mul_ne_zero hdiff_ne hsum_ne
    have hprod_lt : degR r < N := by
      rw [hprod_deg]
      have := degR_lt hr
      omega
    have hprod_coeff_nz : ((Q₁ - Q0) * (Q₁ + Q0)).coeff N ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hprod_ne
    have hdiff_sq : (Q₁ - Q0) * (Q₁ + Q0) = (P_even_poly_real r - Q0 ^ 2) - (P_even_poly_real r - Q₁ ^ 2) := by
      ring
    have hcoeff0 : ((Q₁ - Q0) * (Q₁ + Q0)).coeff N = 0 := by
      rw [hdiff_sq, Polynomial.coeff_sub, hQ0_zero N hprod_lt, hQ1_zero N hprod_lt, sub_zero]
    exact hprod_coeff_nz hcoeff0

/-! ## 2. Upper Half-Plane Square Root `uhpSqrt` and `F_uhp` -/

noncomputable def uhpSqrt (w : ℂ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi / 4)) * (-Complex.I * w) ^ ((1 : ℂ) / 2)

private lemma cpow_half_polar {ζ : ℂ} (hζ : ζ ≠ 0) :
    ζ ^ ((1 : ℂ) / 2) = (Real.sqrt ‖ζ‖ : ℂ) * Complex.exp (Complex.I * (ζ.arg / 2)) := by
  rw [Complex.cpow_def_of_ne_zero hζ]
  have hlog : Complex.log ζ * ((1 : ℂ) / 2) =
      (Real.log ‖ζ‖ / 2 : ℝ) + Complex.I * (ζ.arg / 2 : ℝ) := by
    apply Complex.ext
    · simp [Complex.log_re]
      ring
    · simp [Complex.log_im]
      ring
  rw [hlog, Complex.exp_add]
  have hreal : Complex.exp ((Real.log ‖ζ‖ / 2 : ℝ) : ℂ) = (Real.sqrt ‖ζ‖ : ℂ) := by
    rw [← Complex.ofReal_exp, Real.sqrt_eq_rpow]
    have hnorm : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    rw [Real.rpow_def_of_pos hnorm]
    congr 2
    ring
  rw [hreal]
  push_cast
  rfl

lemma uhpSqrt_sq (w : ℂ) : uhpSqrt w ^ 2 = w := by
  by_cases hw : w = 0
  · subst hw
    simp [uhpSqrt]
  · have hni : -Complex.I * w ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw
    dsimp [uhpSqrt]
    rw [mul_pow]
    have hexp : Complex.exp (Complex.I * (Real.pi / 4)) ^ 2 = Complex.I := by
      rw [← Complex.exp_nat_mul]
      have harg : (2 : ℕ) * (Complex.I * ((Real.pi : ℂ) / 4)) = ((Real.pi : ℂ) / 2) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.exp_pi_div_two_mul_I]
    have hcp : ((-Complex.I * w) ^ ((1 : ℂ) / 2)) ^ 2 = -Complex.I * w := by
      rw [Complex.cpow_def_of_ne_zero hni, ← Complex.exp_nat_mul]
      have harg : (2 : ℕ) * (Complex.log (-Complex.I * w) * ((1 : ℂ) / 2)) =
          Complex.log (-Complex.I * w) := by
        push_cast; ring
      rw [harg, Complex.exp_log hni]
    rw [hexp, hcp]
    calc Complex.I * (-Complex.I * w) = -(Complex.I * Complex.I) * w := by ring
      _ = -(-1) * w := by rw [Complex.I_mul_I]
      _ = w := by ring

lemma uhpSqrt_continuousOn : ContinuousOn uhpSqrt {w : ℂ | 0 ≤ w.im} := by
  intro w hw
  have hre : 0 ≤ (-Complex.I * w).re := by
    simpa [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] using hw
  have hc1 : ContinuousAt (fun z : ℂ => z ^ ((1 : ℂ) / 2)) (-Complex.I * w) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl hre) (by norm_num)
  have hc2 : ContinuousAt (fun z : ℂ => (-Complex.I * z) ^ ((1 : ℂ) / 2)) w :=
    hc1.comp ((continuous_const.mul continuous_id).continuousAt)
  exact (continuousAt_const.mul hc2).continuousWithinAt

lemma uhpSqrt_differentiableOn : DifferentiableOn ℂ uhpSqrt {w : ℂ | 0 < w.im} := by
  intro w hw
  have hslit : -Complex.I * w ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] using hw
  have hd : DifferentiableAt ℂ uhpSqrt w := by
    unfold uhpSqrt
    exact (((differentiableAt_id).const_mul (-Complex.I)).cpow_const hslit).const_mul _
  exact hd.differentiableWithinAt

lemma uhpSqrt_ofReal_nonneg {t : ℝ} (ht : 0 ≤ t) :
    uhpSqrt (t : ℂ) = (Real.sqrt t : ℂ) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp [uhpSqrt]
  · have hni : -Complex.I * (t : ℂ) ≠ 0 := by
      exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht_pos.ne')
    dsimp [uhpSqrt]
    rw [cpow_half_polar hni]
    have hnorm : ‖-Complex.I * (t : ℂ)‖ = t := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg ht]
    have harg : (-Complex.I * (t : ℂ)).arg = -(Real.pi / 2) := by
      rw [Complex.arg_eq_neg_pi_div_two_iff]
      constructor
      · simp
      · simp [ht_pos]
    rw [hnorm, harg]
    have hexp : Complex.exp (Complex.I * (Real.pi / 4)) *
        Complex.exp (Complex.I * ((-(Real.pi / 2) : ℝ) / 2)) = 1 := by
      rw [← Complex.exp_add]
      have h0 : Complex.I * ((Real.pi : ℂ) / 4) + Complex.I * (↑(-(Real.pi / 2)) / 2) = 0 := by
        push_cast; ring
      rw [h0, Complex.exp_zero]
    rw [show Complex.exp (Complex.I * (Real.pi / 4)) *
          ((Real.sqrt t : ℂ) * Complex.exp (Complex.I * (↑(-(Real.pi / 2)) / 2))) =
        (Real.sqrt t : ℂ) * (Complex.exp (Complex.I * (Real.pi / 4)) *
          Complex.exp (Complex.I * (↑(-(Real.pi / 2)) / 2))) by ring, hexp, mul_one]

lemma uhpSqrt_ofReal_nonpos {t : ℝ} (ht : t ≤ 0) :
    uhpSqrt (t : ℂ) = Complex.I * (Real.sqrt (-t) : ℂ) := by
  rcases eq_or_lt_of_le ht with rfl | ht_neg
  · simp [uhpSqrt]
  · have hni : -Complex.I * (t : ℂ) ≠ 0 := by
      exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht_neg.ne)
    dsimp [uhpSqrt]
    rw [cpow_half_polar hni]
    have hnorm : ‖-Complex.I * (t : ℂ)‖ = -t := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonpos ht]
    have harg : (-Complex.I * (t : ℂ)).arg = Real.pi / 2 := by
      rw [Complex.arg_eq_pi_div_two_iff]
      constructor
      · simp
      · simp [ht_neg]
    rw [hnorm, harg]
    have hexp : Complex.exp (Complex.I * (Real.pi / 4)) *
        Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) / 2)) = Complex.I := by
      rw [← Complex.exp_add]
      have harg2 : Complex.I * ((Real.pi : ℂ) / 4) + Complex.I * (↑(Real.pi / 2) / 2) =
          ((Real.pi : ℂ) / 2) * Complex.I := by
        push_cast; ring
      rw [harg2, Complex.exp_pi_div_two_mul_I]
    rw [show Complex.exp (Complex.I * (Real.pi / 4)) *
          ((Real.sqrt (-t) : ℂ) * Complex.exp (Complex.I * (↑(Real.pi / 2) / 2))) =
        (Complex.exp (Complex.I * (Real.pi / 4)) *
          Complex.exp (Complex.I * (↑(Real.pi / 2) / 2))) * (Real.sqrt (-t) : ℂ) by ring, hexp]

private lemma uhpSqrt_first_quadrant {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (uhpSqrt w).re ∧ 0 ≤ (uhpSqrt w).im := by
  by_cases hw0 : w = 0
  · subst hw0; simp [uhpSqrt]
  · have hni : -Complex.I * w ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hw0
    dsimp [uhpSqrt]
    rw [cpow_half_polar hni]
    have hre : 0 ≤ (-Complex.I * w).re := by
      simpa [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] using hw
    have harg : |(-Complex.I * w).arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre
    have hlo : 0 ≤ Real.pi / 4 + (-Complex.I * w).arg / 2 := by
      linarith [abs_le.mp harg]
    have hhi : Real.pi / 4 + (-Complex.I * w).arg / 2 ≤ Real.pi / 2 := by
      linarith [abs_le.mp harg]
    set θ := Real.pi / 4 + (-Complex.I * w).arg / 2
    have hid : Complex.exp (Complex.I * (Real.pi / 4)) *
          ((Real.sqrt ‖-Complex.I * w‖ : ℂ) * Complex.exp (Complex.I * ((-Complex.I * w).arg / 2))) =
        (Real.sqrt ‖-Complex.I * w‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      have hexp : Complex.exp (Complex.I * (Real.pi / 4)) *
            Complex.exp (Complex.I * ((-Complex.I * w).arg / 2)) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        dsimp [θ]
        push_cast
        ring
      rw [show Complex.exp (Complex.I * (Real.pi / 4)) *
            ((Real.sqrt ‖-Complex.I * w‖ : ℂ) * Complex.exp (Complex.I * ((-Complex.I * w).arg / 2))) =
          (Real.sqrt ‖-Complex.I * w‖ : ℂ) * (Complex.exp (Complex.I * (Real.pi / 4)) *
            Complex.exp (Complex.I * ((-Complex.I * w).arg / 2))) by ring, hexp]
    rw [hid, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhi⟩
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hlo, by linarith [Real.pi_pos]⟩
    have hsq : 0 ≤ Real.sqrt ‖-Complex.I * w‖ := Real.sqrt_nonneg _
    simp only [mul_add, ← mul_assoc, ← Complex.ofReal_mul, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
    exact ⟨mul_nonneg hsq hcos, mul_nonneg hsq hsin⟩

lemma uhpSqrt_ne_zero {w : ℂ} (hw : w ≠ 0) : uhpSqrt w ≠ 0 := by
  intro hz
  have h := uhpSqrt_sq w
  rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
  exact hw h.symm

lemma uhpSqrt_div_sub_one_norm_le {z : ℂ} {c : ℝ} (hz : 0 ≤ z.im) (hz0 : z ≠ 0) :
    ‖uhpSqrt (z - (c : ℂ)) / uhpSqrt z - 1‖ ≤ |c| / ‖z‖ := by
  set a := uhpSqrt (z - (c : ℂ))
  set b := uhpSqrt z
  set q := a / b
  have hb0 : b ≠ 0 := uhpSqrt_ne_zero hz0
  have ha_q := uhpSqrt_first_quadrant (show 0 ≤ (z - (c : ℂ)).im by simp [hz])
  have hb_q := uhpSqrt_first_quadrant hz
  have hq_re : 0 ≤ q.re := by
    dsimp [q]
    rw [Complex.div_re]
    exact add_nonneg
      (div_nonneg (mul_nonneg ha_q.1 hb_q.1) (Complex.normSq_nonneg b))
      (div_nonneg (mul_nonneg ha_q.2 hb_q.2) (Complex.normSq_nonneg b))
  have hqp1_norm : 1 ≤ ‖q + 1‖ := by
    have hre1 : 1 ≤ (q + 1).re := by simp [hq_re]
    calc (1 : ℝ) ≤ |(q + 1).re| := by rw [abs_of_nonneg (by linarith)]; exact hre1
      _ ≤ ‖q + 1‖ := Complex.abs_re_le_norm (q + 1)
  have hdiff_sq : (q - 1) * (q + 1) = -(c : ℂ) / z := by
    have h1 : q ^ 2 = (z - (c : ℂ)) / z := by
      dsimp [q, a, b]
      rw [div_pow, uhpSqrt_sq, uhpSqrt_sq]
    calc (q - 1) * (q + 1) = q ^ 2 - 1 := by ring
      _ = (z - (c : ℂ)) / z - 1 := by rw [h1]
      _ = -(c : ℂ) / z := by field_simp [hz0]; ring
  have hnorm_prod : ‖q - 1‖ * ‖q + 1‖ = |c| / ‖z‖ := by
    rw [← norm_mul, hdiff_sq, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hqp1_pos : 0 < ‖q + 1‖ := by linarith
  calc ‖q - 1‖ = (‖q - 1‖ * ‖q + 1‖) / ‖q + 1‖ := by
        rw [mul_div_cancel_right₀ _ hqp1_pos.ne']
    _ = (|c| / ‖z‖) / ‖q + 1‖ := by rw [hnorm_prod]
    _ ≤ |c| / ‖z‖ := div_le_self (by positivity) hqp1_norm

/-- Uniform arithmetic-progression indexing of the `2 * r` roots `-(2r-1), -(2r-3), ..., +(2r-1)`. -/
noncomputable def rootPt (r k : ℕ) : ℝ := 2 * (k : ℝ) - (2 * (r : ℝ) - 1)

noncomputable def F_uhp (r : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.range (2 * r), uhpSqrt (z - (rootPt r k : ℂ))

noncomputable def P_even_real (r : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (2 * r), (x - rootPt r k)

private lemma prod_range_two_r_pair {R : Type*} [CommMonoid R] (r : ℕ) (f : ℕ → R) :
    ∏ k ∈ Finset.range (2 * r), f k =
      ∏ j ∈ Finset.Icc 1 r, (f (r - j) * f (r - 1 + j)) := by
  have hsplit : Finset.range (2 * r) = Finset.range r ∪ Finset.Ico r (2 * r) := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range r) (Finset.Ico r (2 * r)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hL : ∏ k ∈ Finset.range r, f k = ∏ j ∈ Finset.Icc 1 r, f (r - j) := by
    refine Finset.prod_nbij (fun k => r - k)
      (fun k hk => by rw [Finset.mem_range] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun k₁ hk₁ k₂ hk₂ heq => by
        rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
        dsimp only at heq
        omega)
      (fun j hj => by
        rw [Finset.mem_coe, Finset.mem_Icc] at hj
        exact ⟨r - j, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp only; omega⟩)
      (fun k hk => by
        rw [Finset.mem_range] at hk
        congr 1
        omega)
  have hR : ∏ k ∈ Finset.Ico r (2 * r), f k = ∏ j ∈ Finset.Icc 1 r, f (r - 1 + j) := by
    refine Finset.prod_nbij (fun k => k - r + 1)
      (fun k hk => by rw [Finset.mem_Ico] at hk; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun k₁ hk₁ k₂ hk₂ heq => by
        rw [Finset.mem_coe, Finset.mem_Ico] at hk₁ hk₂
        dsimp only at heq
        omega)
      (fun j hj => by
        rw [Finset.mem_coe, Finset.mem_Icc] at hj
        exact ⟨r - 1 + j, Finset.mem_coe.mpr (Finset.mem_Ico.mpr (by omega)), by dsimp only; omega⟩)
      (fun k hk => by
        rw [Finset.mem_Ico] at hk
        congr 1
        omega)
  rw [hL, hR, Finset.prod_mul_distrib]

private lemma rootPt_pair (r j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ r) :
    rootPt r (r - j) = -((2 * j - 1 : ℕ) : ℝ) ∧
      rootPt r (r - 1 + j) = ((2 * j - 1 : ℕ) : ℝ) := by
  dsimp [rootPt]
  have hrj : j ≤ r := hj2
  have h2j : 1 ≤ 2 * j := by omega
  have h1r : 1 ≤ r := le_trans hj1 hj2
  rw [Nat.cast_sub hrj, Nat.cast_add, Nat.cast_sub h1r, Nat.cast_sub h2j]
  constructor <;> push_cast <;> ring

lemma F_uhp_sq (r : ℕ) (z : ℂ) :
    F_uhp r z ^ 2 = Polynomial.aeval z (P_even_poly_real r) := by
  dsimp [F_uhp]
  rw [← Finset.prod_pow]
  have hsq : ∀ k ∈ Finset.range (2 * r),
      uhpSqrt (z - (rootPt r k : ℂ)) ^ 2 = z - (rootPt r k : ℂ) :=
    fun k _ => uhpSqrt_sq _
  rw [Finset.prod_congr rfl hsq, prod_range_two_r_pair]
  have hpair : ∏ j ∈ Finset.Icc 1 r,
        ((z - (rootPt r (r - j) : ℂ)) * (z - (rootPt r (r - 1 + j) : ℂ))) =
      ∏ j ∈ Finset.Icc 1 r, (z ^ 2 - (((2 * j - 1 : ℕ) : ℂ) ^ 2)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    obtain ⟨hL, hR⟩ := rootPt_pair r j hj.1 hj.2
    rw [hL, hR]
    push_cast
    ring
  rw [hpair]
  have haeval : Polynomial.aeval z (P_even_poly_real r) =
      ∏ j ∈ Finset.Icc 1 r, (z ^ 2 - (((2 * j - 1 : ℕ) : ℂ) ^ 2)) := by
    dsimp [P_even_poly_real, P_even_poly]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.eval₂_finsetProd]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_natCast]
  exact haeval.symm

lemma P_even_real_eq_aeval (r : ℕ) (x : ℝ) :
    P_even_real r x = Polynomial.aeval x (P_even_poly_real r) := by
  dsimp [P_even_real]
  rw [prod_range_two_r_pair]
  have hpair : ∏ j ∈ Finset.Icc 1 r, ((x - rootPt r (r - j)) * (x - rootPt r (r - 1 + j))) =
      ∏ j ∈ Finset.Icc 1 r, (x ^ 2 - ((2 * j - 1 : ℕ) : ℝ) ^ 2) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    obtain ⟨hL, hR⟩ := rootPt_pair r j hj.1 hj.2
    rw [hL, hR]
    ring
  rw [hpair]
  dsimp [P_even_poly_real, P_even_poly]
  rw [Polynomial.eval_map, Polynomial.eval₂_finsetProd]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_natCast]

lemma F_uhp_continuousOn (r : ℕ) : ContinuousOn (F_uhp r) {w : ℂ | 0 ≤ w.im} := by
  unfold F_uhp
  refine continuousOn_finsetProd _ fun k _ => ?_
  refine uhpSqrt_continuousOn.comp (continuousOn_id.sub continuousOn_const) ?_
  intro z hz
  simpa using hz

lemma F_uhp_differentiableOn (r : ℕ) : DifferentiableOn ℂ (F_uhp r) {w : ℂ | 0 < w.im} := by
  unfold F_uhp
  have hprod : DifferentiableOn ℂ
      (∏ k ∈ Finset.range (2 * r), fun w : ℂ => uhpSqrt (w - (rootPt r k : ℂ)))
      {w : ℂ | 0 < w.im} := by
    refine DifferentiableOn.finsetProd fun k _ => ?_
    refine uhpSqrt_differentiableOn.comp (differentiableOn_id.sub (differentiableOn_const _)) ?_
    intro z hz
    simpa using hz
  have hfun : (∏ k ∈ Finset.range (2 * r), fun w : ℂ => uhpSqrt (w - (rootPt r k : ℂ))) =
      fun z => ∏ k ∈ Finset.range (2 * r), uhpSqrt (z - (rootPt r k : ℂ)) := by
    ext z
    simp [Finset.prod_apply]
  rw [← hfun]
  exact hprod

lemma uhpSqrt_neg_conj_real {x : ℝ} (hx : x ≠ 0) :
    uhpSqrt ((-x : ℝ) : ℂ) = Complex.I * star (uhpSqrt (x : ℂ)) := by
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · have hx_nonpos : x ≤ 0 := hx_neg.le
    have hnx_nonneg : 0 ≤ -x := neg_nonneg.mpr hx_nonpos
    rw [uhpSqrt_ofReal_nonneg hnx_nonneg, uhpSqrt_ofReal_nonpos hx_nonpos]
    simp only [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    calc (Real.sqrt (-x) : ℂ) = -(Complex.I * Complex.I) * (Real.sqrt (-x) : ℂ) := by
            rw [Complex.I_mul_I]; ring
      _ = Complex.I * (-Complex.I * (Real.sqrt (-x) : ℂ)) := by ring
  · have hx_nonneg : 0 ≤ x := hx_pos.le
    have hnx_nonpos : -x ≤ 0 := neg_nonpos.mpr hx_nonneg
    rw [uhpSqrt_ofReal_nonpos hnx_nonpos, uhpSqrt_ofReal_nonneg hx_nonneg]
    simp [Complex.conj_ofReal]

private lemma sqrt_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, Real.sqrt (f i) = Real.sqrt (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ← Real.sqrt_mul (hf a (Finset.mem_insert_self a s))]

lemma F_uhp_ofReal_outside {r : ℕ} {x : ℝ} (hx : (2 * (r : ℝ) - 1) ≤ |x|) :
    (F_uhp r (x : ℂ)).im = 0 := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp [F_uhp]
  · rcases le_abs.mp hx with hxpos | hxneg
    · have hprod : F_uhp r (x : ℂ) =
          ((∏ k ∈ Finset.range (2 * r), Real.sqrt (x - rootPt r k) : ℝ) : ℂ) := by
        dsimp [F_uhp]
        push_cast
        refine Finset.prod_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        have hsub : 0 ≤ x - rootPt r k := by
          dsimp [rootPt]
          have hkr : (k : ℝ) ≤ ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k ≤ 2 * r - 1)
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)] at hkr
          push_cast at hkr
          linarith
        rw [← Complex.ofReal_sub, uhpSqrt_ofReal_nonneg hsub]
      rw [hprod, Complex.ofReal_im]
    · have hr_neg : x ≤ -(2 * (r : ℝ) - 1) := by linarith
      have hprod : F_uhp r (x : ℂ) =
          Complex.I ^ (2 * r) *
            ((∏ k ∈ Finset.range (2 * r), Real.sqrt (rootPt r k - x) : ℝ) : ℂ) := by
        dsimp [F_uhp]
        have hfac : ∀ k ∈ Finset.range (2 * r),
            uhpSqrt ((x : ℂ) - (rootPt r k : ℂ)) =
              Complex.I * (Real.sqrt (rootPt r k - x) : ℂ) := by
          intro k hk
          rw [Finset.mem_range] at hk
          have hsub : x - rootPt r k ≤ 0 := by
            dsimp [rootPt]
            have : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith
          rw [← Complex.ofReal_sub, uhpSqrt_ofReal_nonpos hsub, neg_sub]
        rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range]
        push_cast
        rfl
      have hI2r : Complex.I ^ (2 * r) = (((-1 : ℝ) ^ r : ℝ) : ℂ) := by
        rw [pow_mul, Complex.I_sq]
        push_cast
        rfl
      rw [hprod, hI2r, ← Complex.ofReal_mul, Complex.ofReal_im]

lemma F_uhp_ofReal_subinterval {r m : ℕ} (hm : m + 1 < 2 * r) {x : ℝ}
    (hx1 : rootPt r m ≤ x) (hx2 : x ≤ rootPt r (m + 1)) :
    F_uhp r (x : ℂ) = Complex.I ^ (2 * r - 1 - m) * (Real.sqrt |P_even_real r x| : ℂ) := by
  dsimp [F_uhp]
  have hsplit : Finset.range (2 * r) = Finset.range (m + 1) ∪ Finset.Ico (m + 1) (2 * r) := by
    ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range (m + 1)) (Finset.Ico (m + 1) (2 * r)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_range, Finset.mem_Ico] at hk1 hk2
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hL : ∏ k ∈ Finset.range (m + 1), uhpSqrt ((x : ℂ) - (rootPt r k : ℂ)) =
      ((∏ k ∈ Finset.range (m + 1), Real.sqrt |x - rootPt r k| : ℝ) : ℂ) := by
    push_cast
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hnonneg : 0 ≤ x - rootPt r k := by
      have hk_le : rootPt r k ≤ rootPt r m := by
        dsimp [rootPt]
        have : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : k ≤ m)
        linarith
      linarith
    rw [← Complex.ofReal_sub, uhpSqrt_ofReal_nonneg hnonneg, abs_of_nonneg hnonneg]
  have hR : ∏ k ∈ Finset.Ico (m + 1) (2 * r), uhpSqrt ((x : ℂ) - (rootPt r k : ℂ)) =
      Complex.I ^ (2 * r - 1 - m) *
        ((∏ k ∈ Finset.Ico (m + 1) (2 * r), Real.sqrt |x - rootPt r k| : ℝ) : ℂ) := by
    have hfac : ∀ k ∈ Finset.Ico (m + 1) (2 * r),
        uhpSqrt ((x : ℂ) - (rootPt r k : ℂ)) =
          Complex.I * (Real.sqrt |x - rootPt r k| : ℂ) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hnonpos : x - rootPt r k ≤ 0 := by
        have hk_ge : rootPt r (m + 1) ≤ rootPt r k := by
          dsimp [rootPt]
          have : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          linarith
        linarith
      rw [← Complex.ofReal_sub, uhpSqrt_ofReal_nonpos hnonpos, abs_of_nonpos hnonpos]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
      Nat.card_Ico, show 2 * r - (m + 1) = 2 * r - 1 - m by omega]
    push_cast
    rfl
  rw [hL, hR]
  have hmul : (∏ k ∈ Finset.range (m + 1), Real.sqrt |x - rootPt r k|) *
      (∏ k ∈ Finset.Ico (m + 1) (2 * r), Real.sqrt |x - rootPt r k|) =
      Real.sqrt |P_even_real r x| := by
    rw [← Finset.prod_union hdisj, ← hsplit,
      sqrt_finset_prod _ _ (fun _ _ => abs_nonneg _), P_even_real, Finset.abs_prod]
  calc ((∏ k ∈ Finset.range (m + 1), Real.sqrt |x - rootPt r k| : ℝ) : ℂ) *
        (Complex.I ^ (2 * r - 1 - m) *
          ((∏ k ∈ Finset.Ico (m + 1) (2 * r), Real.sqrt |x - rootPt r k| : ℝ) : ℂ))
      = Complex.I ^ (2 * r - 1 - m) *
          (((∏ k ∈ Finset.range (m + 1), Real.sqrt |x - rootPt r k|) *
            (∏ k ∈ Finset.Ico (m + 1) (2 * r), Real.sqrt |x - rootPt r k|) : ℝ) : ℂ) := by
        push_cast; ring
    _ = Complex.I ^ (2 * r - 1 - m) * (Real.sqrt |P_even_real r x| : ℂ) := by rw [hmul]

/-! ## 3. Cauchy–Goursat Contour Identity and `O(‖z‖⁻²)` Remainder Asymptotics -/

noncomputable def w_fn (r : ℕ) (z : ℂ) : ℂ := if Even r then z else 1

private lemma w_fn_ofReal (r : ℕ) (x : ℝ) :
    w_fn r (x : ℂ) = ((if Even r then x else 1 : ℝ) : ℂ) := by
  by_cases h : Even r <;> simp [w_fn, h]

private lemma w_fn_continuous (r : ℕ) : Continuous (fun z : ℂ => w_fn r z) := by
  by_cases h : Even r
  · have : (fun z : ℂ => w_fn r z) = id := by ext z; simp [w_fn, h]
    rw [this]
    exact continuous_id
  · have : (fun z : ℂ => w_fn r z) = fun _ => 1 := by ext z; simp [w_fn, h]
    rw [this]
    exact continuous_const

noncomputable def upperRect3 (f : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x in (-R)..R, f ((x : ℂ) + (R : ℂ) * Complex.I)) -
    Complex.I * (∫ y in (0 : ℝ)..R, f ((R : ℂ) + (y : ℂ) * Complex.I)) +
    Complex.I * (∫ y in (0 : ℝ)..R, f ((-R : ℂ) + (y : ℂ) * Complex.I))

private lemma upperRect3_add {f g : ℂ → ℂ} {R : ℝ}
    (hf_top : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (R : ℂ) * Complex.I)) MeasureTheory.volume (-R) R)
    (hg_top : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (R : ℂ) * Complex.I)) MeasureTheory.volume (-R) R)
    (hf_r : IntervalIntegrable (fun y : ℝ => f ((R : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 R)
    (hg_r : IntervalIntegrable (fun y : ℝ => g ((R : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 R)
    (hf_l : IntervalIntegrable (fun y : ℝ => f ((-R : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 R)
    (hg_l : IntervalIntegrable (fun y : ℝ => g ((-R : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 R) :
    upperRect3 (fun z => f z + g z) R = upperRect3 f R + upperRect3 g R := by
  dsimp [upperRect3]
  rw [intervalIntegral.integral_add hf_top hg_top,
    intervalIntegral.integral_add hf_r hg_r,
    intervalIntegral.integral_add hf_l hg_l]
  ring

private lemma upperRect3_const_mul {c : ℂ} {f : ℂ → ℂ} {R : ℝ} :
    upperRect3 (fun z => c * f z) R = c * upperRect3 f R := by
  dsimp [upperRect3]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

private lemma hasDerivAt_ofReal_mul_I (b : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -Complex.I * ((t : ℂ) + b)) (-Complex.I) x := by
  have hc : HasDerivAt (fun w : ℂ => -Complex.I * (w + b)) (-Complex.I * 1) (x : ℂ) :=
    ((hasDerivAt_id (x : ℂ)).add_const b).const_mul (-Complex.I)
  simpa only [mul_one] using hc.comp_ofReal

private lemma hasDerivAt_const_add_ofReal_mul_I (a : ℂ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => -Complex.I * (a + (t : ℂ) * Complex.I)) 1 y := by
  have hc : HasDerivAt (fun w : ℂ => -Complex.I * (a + w * Complex.I))
      (-Complex.I * (1 * Complex.I)) (y : ℂ) :=
    (((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add a).const_mul (-Complex.I)
  simpa only [one_mul, neg_mul, Complex.I_mul_I, neg_neg] using hc.comp_ofReal

lemma upperRect3_inv_z {R : ℝ} (hR : 0 < R) :
    upperRect3 (fun z => 1 / z) R = -(Real.pi : ℂ) * Complex.I := by
  dsimp [upperRect3]
  have htop_slit : ∀ x : ℝ, -Complex.I * ((x : ℂ) + (R : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro x
    rw [Complex.mem_slitPlane_iff]
    left
    have hre : (-Complex.I * ((x : ℂ) + (R : ℂ) * Complex.I)).re = R := by
      simp [mul_add, Complex.mul_re, Complex.I_re, Complex.I_im]
    linarith
  have htop_deriv : ∀ x ∈ Set.uIcc (-R) R,
      HasDerivAt (fun t : ℝ => Complex.log (-Complex.I * ((t : ℂ) + (R : ℂ) * Complex.I)))
        (1 / ((x : ℂ) + (R : ℂ) * Complex.I)) x := by
    intro x _
    have hlog := (hasDerivAt_ofReal_mul_I ((R : ℂ) * Complex.I) x).clog_real (htop_slit x)
    have hne : (x : ℂ) + (R : ℂ) * Complex.I ≠ 0 := by
      intro h0
      have him : ((x : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
      rw [h0, Complex.zero_im] at him
      linarith
    convert hlog using 1
    field_simp [hne, Complex.I_ne_zero]
  have htop_cont : Continuous (fun x : ℝ => (1 : ℂ) / ((x : ℂ) + (R : ℂ) * Complex.I)) := by
    refine continuous_const.div (Complex.continuous_ofReal.add continuous_const) fun x => ?_
    intro h0
    have him : ((x : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
    rw [h0, Complex.zero_im] at him
    linarith
  have htop_int : ∫ x in (-R)..R, (1 : ℂ) / ((x : ℂ) + (R : ℂ) * Complex.I) =
      Complex.log (-Complex.I * ((R : ℂ) + (R : ℂ) * Complex.I)) -
        Complex.log (-Complex.I * ((-R : ℂ) + (R : ℂ) * Complex.I)) := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt htop_deriv
      (htop_cont.intervalIntegrable (-R) R)
  have hr_slit : ∀ y : ℝ, -Complex.I * ((R : ℂ) + (y : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    right
    have him : (-Complex.I * ((R : ℂ) + (y : ℂ) * Complex.I)).im = -R := by
      simp [mul_add, Complex.mul_im, Complex.I_re, Complex.I_im]
    linarith
  have hr_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => Complex.log (-Complex.I * ((R : ℂ) + (t : ℂ) * Complex.I)))
        (Complex.I / ((R : ℂ) + (y : ℂ) * Complex.I)) y := by
    intro y _
    have hlog := (hasDerivAt_const_add_ofReal_mul_I (R : ℂ) y).clog_real (hr_slit y)
    have hne : (R : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro h0
      have hre : ((R : ℂ) + (y : ℂ) * Complex.I).re = R := by simp
      rw [h0, Complex.zero_re] at hre
      linarith
    convert hlog using 1
    field_simp [hne, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  have hr_cont : Continuous (fun y : ℝ => Complex.I / ((R : ℂ) + (y : ℂ) * Complex.I)) := by
    refine continuous_const.div (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y => ?_
    intro h0
    have hre : ((R : ℂ) + (y : ℂ) * Complex.I).re = R := by simp
    rw [h0, Complex.zero_re] at hre
    linarith
  have hr_int : Complex.I * ∫ y in (0 : ℝ)..R, (1 : ℂ) / ((R : ℂ) + (y : ℂ) * Complex.I) =
      Complex.log (-Complex.I * ((R : ℂ) + (R : ℂ) * Complex.I)) -
        Complex.log (-Complex.I * ((R : ℂ) + (0 : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [mul_one_div]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hr_deriv (hr_cont.intervalIntegrable 0 R)
  have hl_slit : ∀ y : ℝ, -Complex.I * ((-R : ℂ) + (y : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    intro y
    rw [Complex.mem_slitPlane_iff]
    right
    have him : (-Complex.I * ((-R : ℂ) + (y : ℂ) * Complex.I)).im = R := by
      simp [mul_add, Complex.mul_im, Complex.I_re, Complex.I_im]
    linarith
  have hl_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => Complex.log (-Complex.I * ((-R : ℂ) + (t : ℂ) * Complex.I)))
        (Complex.I / ((-R : ℂ) + (y : ℂ) * Complex.I)) y := by
    intro y _
    have hlog := (hasDerivAt_const_add_ofReal_mul_I (-R : ℂ) y).clog_real (hl_slit y)
    have hne : (-R : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
      intro h0
      have hre : ((-R : ℂ) + (y : ℂ) * Complex.I).re = -R := by simp
      rw [h0, Complex.zero_re] at hre
      linarith
    convert hlog using 1
    field_simp [hne, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  have hl_cont : Continuous (fun y : ℝ => Complex.I / ((-R : ℂ) + (y : ℂ) * Complex.I)) := by
    refine continuous_const.div (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y => ?_
    intro h0
    have hre : ((-R : ℂ) + (y : ℂ) * Complex.I).re = -R := by simp
    rw [h0, Complex.zero_re] at hre
    linarith
  have hl_int : Complex.I * ∫ y in (0 : ℝ)..R, (1 : ℂ) / ((-R : ℂ) + (y : ℂ) * Complex.I) =
      Complex.log (-Complex.I * ((-R : ℂ) + (R : ℂ) * Complex.I)) -
        Complex.log (-Complex.I * ((-R : ℂ) + (0 : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [mul_one_div]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hl_deriv (hl_cont.intervalIntegrable 0 R)
  rw [htop_int, hr_int, hl_int]
  have hz0_r : (R : ℂ) + (0 : ℂ) * Complex.I = (R : ℂ) := by ring
  have hz0_l : (-R : ℂ) + (0 : ℂ) * Complex.I = -(R : ℂ) := by ring
  have hml : -Complex.I * (-(R : ℂ)) = Complex.I * (R : ℂ) := by ring
  have hcancel :
      (Complex.log (-Complex.I * ((R : ℂ) + (R : ℂ) * Complex.I)) -
          Complex.log (-Complex.I * ((-R : ℂ) + (R : ℂ) * Complex.I))) -
        (Complex.log (-Complex.I * ((R : ℂ) + (R : ℂ) * Complex.I)) -
          Complex.log (-Complex.I * ((R : ℂ) + (0 : ℂ) * Complex.I))) +
        (Complex.log (-Complex.I * ((-R : ℂ) + (R : ℂ) * Complex.I)) -
          Complex.log (-Complex.I * ((-R : ℂ) + (0 : ℂ) * Complex.I))) =
      Complex.log (-Complex.I * (R : ℂ)) - Complex.log (Complex.I * (R : ℂ)) := by
    rw [hz0_r, hz0_l, hml]
    ring
  rw [hcancel]
  have hnorm1 : ‖-Complex.I * (R : ℂ)‖ = R := by
    simp [Complex.norm_I, Complex.norm_real, abs_of_pos hR]
  have hnorm2 : ‖Complex.I * (R : ℂ)‖ = R := by
    simp [Complex.norm_I, Complex.norm_real, abs_of_pos hR]
  have harg1 : (-Complex.I * (R : ℂ)).arg = -(Real.pi / 2) := by
    rw [Complex.arg_eq_neg_pi_div_two_iff]
    simp [hR]
  have harg2 : (Complex.I * (R : ℂ)).arg = Real.pi / 2 := by
    rw [Complex.arg_eq_pi_div_two_iff]
    simp [hR]
  apply Complex.ext
  · rw [Complex.sub_re, Complex.log_re, Complex.log_re, hnorm1, hnorm2, sub_self]
    simp
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im, harg1, harg2]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, neg_zero]
    ring

private lemma norm_aeval_le_of_natDegree_le (p : Polynomial ℝ) {m : ℕ} (hm : p.natDegree ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 1 ≤ ‖z‖ → ‖Polynomial.aeval z p‖ ≤ C * ‖z‖ ^ m := by
  refine ⟨∑ i ∈ Finset.range (m + 1), |p.coeff i|,
    Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro z hz
  have hdeg : p.natDegree < m + 1 := Nat.lt_succ_of_le hm
  rw [Polynomial.aeval_eq_sum_range' hdeg]
  calc ‖∑ i ∈ Finset.range (m + 1), p.coeff i • z ^ i‖
      ≤ ∑ i ∈ Finset.range (m + 1), ‖p.coeff i • z ^ i‖ :=
        norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (m + 1), |p.coeff i| * ‖z‖ ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, norm_pow]
    _ ≤ ∑ i ∈ Finset.range (m + 1), |p.coeff i| * ‖z‖ ^ m := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [Finset.mem_range] at hi
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by omega)) (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (m + 1), |p.coeff i|) * ‖z‖ ^ m := by
        rw [← Finset.sum_mul]

private lemma prod_sub_one_norm_le {u : ℕ → ℂ} {η : ℝ} (hη0 : 0 ≤ η) :
    ∀ m : ℕ, (∀ k < m, ‖u k - 1‖ ≤ η) →
      ‖(∏ k ∈ Finset.range m, u k) - 1‖ ≤ (1 + η) ^ m - 1
  | 0, _ => by simp
  | m + 1, hu => by
    have ihm := prod_sub_one_norm_le hη0 m (fun k hk => hu k (Nat.lt_succ_of_lt hk))
    have hum := hu m (Nat.lt_succ_self m)
    have hsplit : (∏ k ∈ Finset.range (m + 1), u k) - 1 =
        (∏ k ∈ Finset.range m, u k) * (u m - 1) + ((∏ k ∈ Finset.range m, u k) - 1) := by
      rw [Finset.prod_range_succ]; ring
    have hprod_bound : ‖∏ k ∈ Finset.range m, u k‖ ≤ (1 + η) ^ m := by
      have h1 : ‖∏ k ∈ Finset.range m, u k‖ ≤ ‖(∏ k ∈ Finset.range m, u k) - 1‖ + ‖(1 : ℂ)‖ :=
        norm_le_norm_sub_add _ 1
      rw [norm_one] at h1
      linarith
    rw [hsplit]
    calc ‖(∏ k ∈ Finset.range m, u k) * (u m - 1) + ((∏ k ∈ Finset.range m, u k) - 1)‖
        ≤ ‖(∏ k ∈ Finset.range m, u k) * (u m - 1)‖ + ‖(∏ k ∈ Finset.range m, u k) - 1‖ :=
          norm_add_le _ _
      _ = ‖∏ k ∈ Finset.range m, u k‖ * ‖u m - 1‖ + ‖(∏ k ∈ Finset.range m, u k) - 1‖ := by
          rw [norm_mul]
      _ ≤ (1 + η) ^ m * η + ((1 + η) ^ m - 1) := by
          gcongr
      _ = (1 + η) ^ (m + 1) - 1 := by ring

private lemma one_add_pow_sub_one_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∀ m : ℕ, (1 + η) ^ m - 1 ≤ (m : ℝ) * (2 : ℝ) ^ m * η
  | 0 => by simp
  | m + 1 => by
    have ih := one_add_pow_sub_one_le hη0 hη1 m
    have hm1 : (1 + η) ^ m ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have hexp : (1 + η) ^ (m + 1) - 1 = (1 + η) * ((1 + η) ^ m - 1) + η := by ring
    rw [hexp]
    have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ m := by positivity
    calc (1 + η) * ((1 + η) ^ m - 1) + η
        ≤ 2 * ((m : ℝ) * (2 : ℝ) ^ m * η) + (2 : ℝ) ^ (m + 1) * η := by
          have h1 : (1 + η) * ((1 + η) ^ m - 1) ≤ 2 * ((m : ℝ) * (2 : ℝ) ^ m * η) := by
            have hnn : 0 ≤ (1 + η) ^ m - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
            nlinarith
          have h2 : η ≤ (2 : ℝ) ^ (m + 1) * η := by
            have : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) := one_le_pow₀ (by norm_num)
            nlinarith
          linarith
      _ = (((m + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (m + 1) * η := by push_cast; ring

private lemma F_uhp_sub_pow_bound (r : ℕ) :
    ∃ C_F : ℝ, 0 ≤ C_F ∧ ∀ z : ℂ, 0 ≤ z.im → (2 * (r : ℝ) + 1) ≤ ‖z‖ →
      ‖F_uhp r z - z ^ r‖ ≤ C_F * ‖z‖ ^ r / ‖z‖ := by
  set C_F : ℝ := (2 * (r : ℝ)) * (2 : ℝ) ^ (2 * r) * (2 * (r : ℝ))
  refine ⟨C_F, by positivity, ?_⟩
  intro z hz hnorm
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; linarith [show (0 : ℝ) ≤ (r : ℝ) by positivity]
  have hzn_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hb0 : uhpSqrt z ≠ 0 := uhpSqrt_ne_zero hz0
  have hF_fac : F_uhp r z = z ^ r * ∏ k ∈ Finset.range (2 * r),
      (uhpSqrt (z - (rootPt r k : ℂ)) / uhpSqrt z) := by
    have hpow : uhpSqrt z ^ (2 * r) = z ^ r := by
      rw [pow_mul, uhpSqrt_sq]
    have hprod : ∏ k ∈ Finset.range (2 * r),
        (uhpSqrt (z - (rootPt r k : ℂ)) / uhpSqrt z) =
        F_uhp r z / uhpSqrt z ^ (2 * r) := by
      simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
        ← inv_pow]
      rfl
    rw [hprod, hpow, mul_div_cancel₀ _ (pow_ne_zero r hz0)]
  set η : ℝ := (2 * (r : ℝ)) / ‖z‖
  have hη0 : 0 ≤ η := by positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one hzn_pos]
    linarith
  have hu : ∀ k < 2 * r, ‖uhpSqrt (z - (rootPt r k : ℂ)) / uhpSqrt z - 1‖ ≤ η := by
    intro k hk
    have hle := uhpSqrt_div_sub_one_norm_le (c := rootPt r k) hz hz0
    refine hle.trans (div_le_div_of_nonneg_right ?_ hzn_pos.le)
    dsimp [rootPt]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2r_pos : 1 ≤ 2 * r := by omega
    have hk_nat : k ≤ 2 * r - 1 := by omega
    have hk_lt : (k : ℝ) ≤ ((2 * r - 1 : ℕ) : ℝ) := by exact_mod_cast hk_nat
    rw [Nat.cast_sub h2r_pos, Nat.cast_mul] at hk_lt
    push_cast at hk_lt
    rw [abs_le]
    constructor <;> linarith
  have hprod_sub : ‖(∏ k ∈ Finset.range (2 * r),
        (uhpSqrt (z - (rootPt r k : ℂ)) / uhpSqrt z)) - 1‖ ≤ C_F / ‖z‖ := by
    have h1 := prod_sub_one_norm_le hη0 (2 * r) hu
    have h2 := one_add_pow_sub_one_le hη0 hη1 (2 * r)
    refine h1.trans (h2.trans_eq ?_)
    dsimp [C_F, η]
    push_cast
    ring
  rw [show F_uhp r z - z ^ r = z ^ r * ((∏ k ∈ Finset.range (2 * r),
      (uhpSqrt (z - (rootPt r k : ℂ)) / uhpSqrt z)) - 1) by rw [hF_fac]; ring]
  rw [norm_mul, norm_pow]
  calc ‖z‖ ^ r * ‖(∏ k ∈ Finset.range (2 * r),
        (uhpSqrt (z - (rootPt r k : ℂ)) / uhpSqrt z)) - 1‖
      ≤ ‖z‖ ^ r * (C_F / ‖z‖) := by gcongr
    _ = C_F * ‖z‖ ^ r / ‖z‖ := by ring

private lemma two_mul_z_mul_w_fn_mul_z_pow {r : ℕ} (hr : 1 ≤ r) (z : ℂ) :
    2 * z * w_fn r z * z ^ (degR r) = 2 * z ^ r := by
  by_cases he : Even r
  · have h2r : 2 ≤ r := by
      rcases he with ⟨s, hs⟩
      omega
    have hdeg : degR r = r - 2 := by
      dsimp [degR]
      rcases he with ⟨s, hs⟩
      omega
    simp only [w_fn, he, ↓reduceIte, hdeg]
    calc 2 * z * z * z ^ (r - 2) = 2 * (z ^ 2 * z ^ (r - 2)) := by ring
      _ = 2 * z ^ (2 + (r - 2)) := by rw [← pow_add]
      _ = 2 * z ^ r := by rw [show 2 + (r - 2) = r by omega]
  · have hdeg : degR r = r - 1 := by
      dsimp [degR]
      obtain ⟨s, hs⟩ := Nat.not_even_iff_odd.mp he
      omega
    simp only [w_fn, he, ↓reduceIte, hdeg, mul_one]
    calc 2 * z * z ^ (r - 1) = 2 * (z ^ 1 * z ^ (r - 1)) := by simp [mul_assoc]
      _ = 2 * z ^ (1 + (r - 1)) := by rw [← pow_add]
      _ = 2 * z ^ r := by rw [show 1 + (r - 1) = r by omega]

lemma remainder_asymptotic_O_inv_sq {r : ℕ} (hr : 1 ≤ r) {Q : Polynomial ℝ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = r)
    (hQ_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q ^ 2).coeff k = 0) :
    ∃ R0 : ℝ, max 1 (2 * (r : ℝ) + 1) ≤ R0 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, 0 ≤ z.im → R0 ≤ ‖z‖ →
        ‖w_fn r z * (F_uhp r z - Polynomial.aeval z Q) -
            ((((P_even_poly_real r - Q ^ 2).coeff (degR r) / 2 : ℝ) : ℂ) / z)‖ ≤
          C / ‖z‖ ^ 2 := by
  set R_poly : Polynomial ℝ := P_even_poly_real r - Q ^ 2
  set d : ℕ := degR r
  set a : ℝ := R_poly.coeff d
  set R_tail : Polynomial ℝ := R_poly - Polynomial.C a * Polynomial.X ^ d
  set Q_tail : Polynomial ℝ := Q - Polynomial.X ^ r
  have hQ_tail_deg : Q_tail.natDegree ≤ r - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    dsimp [Q_tail]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    by_cases hkr : k = r
    · subst hkr
      have hlc : Q.coeff Q.natDegree = 1 := hQ_monic.leadingCoeff
      rw [hQ_deg] at hlc
      simp [hlc]
    · have hlt : Q.natDegree < k := by rw [hQ_deg]; omega
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, hkr]
  obtain ⟨C_Q, hCQ0, hCQ⟩ := norm_aeval_le_of_natDegree_le Q_tail hQ_tail_deg
  have hQ_aeval_bound : ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖Polynomial.aeval z Q - z ^ r‖ ≤ C_Q * ‖z‖ ^ (r - 1) := by
    intro z hz
    have hsub : Polynomial.aeval z Q - z ^ r = Polynomial.aeval z Q_tail := by
      dsimp [Q_tail]; simp
    rw [hsub]
    exact hCQ z hz
  have hR_tail_bound : ∃ C_Rt : ℝ, 0 ≤ C_Rt ∧ ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖2 * z * w_fn r z * Polynomial.aeval z R_tail‖ ≤ C_Rt * ‖z‖ ^ (r - 1) := by
    by_cases hd0 : d = 0
    · refine ⟨0, le_rfl, fun z _ => ?_⟩
      have hzero : R_tail = 0 := by
        ext k
        dsimp [R_tail]
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, hd0]
        by_cases hk0 : k = 0
        · subst hk0; simp [a, d, hd0]
        · simp [hk0, hQ_zero k (by omega)]
      simp [hzero]
    · have hRt_deg : R_tail.natDegree ≤ d - 1 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro k hk
        dsimp [R_tail]
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow]
        by_cases hkd : k = d
        · subst hkd; simp [a]
        · have hk_gt : d < k := by omega
          simp [hkd, hQ_zero k hk_gt]
      obtain ⟨C_Rt0, hCRt0, hCRt⟩ := norm_aeval_le_of_natDegree_le R_tail hRt_deg
      refine ⟨2 * C_Rt0, by positivity, fun z hz => ?_⟩
      have hw_norm : ‖2 * z * w_fn r z‖ = 2 * ‖z‖ ^ (1 + if Even r then 1 else 0) := by
        by_cases he : Even r <;> simp [w_fn, he, pow_two, mul_assoc]
      rw [norm_mul, hw_norm]
      have hpow_eq : (1 + if Even r then 1 else 0) + (d - 1) = r - 1 := by
        dsimp [d, degR] at hd0 ⊢
        by_cases he : Even r
        · have ⟨s, hs⟩ := he
          simp [he]
          omega
        · have ⟨s, hs⟩ := Nat.not_even_iff_odd.mp he
          simp [he]
          omega
      calc 2 * ‖z‖ ^ (1 + if Even r then 1 else 0) * ‖Polynomial.aeval z R_tail‖
          ≤ 2 * ‖z‖ ^ (1 + if Even r then 1 else 0) * (C_Rt0 * ‖z‖ ^ (d - 1)) := by
            gcongr
            exact hCRt z hz
        _ = (2 * C_Rt0) * (‖z‖ ^ (1 + if Even r then 1 else 0) * ‖z‖ ^ (d - 1)) := by ring
        _ = (2 * C_Rt0) * ‖z‖ ^ (r - 1) := by rw [← pow_add, hpow_eq]
  obtain ⟨C_Rt, hCRt0, hCRt⟩ := hR_tail_bound
  obtain ⟨C_F, hCF0, hCF⟩ := F_uhp_sub_pow_bound r
  set R0 : ℝ := max (max 1 (2 * (r : ℝ) + 1)) (4 * (C_F + C_Q) + 1)
  have hR0_ge : max 1 (2 * (r : ℝ) + 1) ≤ R0 := le_max_left _ _
  set C : ℝ := (C_Rt + |a| * (C_F + C_Q)) / 2
  refine ⟨R0, hR0_ge, C, by positivity, ?_⟩
  intro z hz hnorm
  have h1z : 1 ≤ ‖z‖ := le_trans (le_trans (le_max_left _ _) hR0_ge) hnorm
  have h2rz : 2 * (r : ℝ) + 1 ≤ ‖z‖ := le_trans (le_trans (le_max_right _ _) hR0_ge) hnorm
  have hz_pos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp hz_pos.ne'
  have hFz : ‖F_uhp r z - z ^ r‖ ≤ C_F * ‖z‖ ^ (r - 1) := by
    calc ‖F_uhp r z - z ^ r‖ ≤ C_F * ‖z‖ ^ r / ‖z‖ := hCF z hz h2rz
      _ = C_F * (‖z‖ ^ (r - 1) * ‖z‖) / ‖z‖ := by
          rw [← pow_succ, show r - 1 + 1 = r by omega]
      _ = C_F * ‖z‖ ^ (r - 1) := by
          field_simp [hz_pos.ne']
  have hQz : ‖Polynomial.aeval z Q - z ^ r‖ ≤ C_Q * ‖z‖ ^ (r - 1) := hQ_aeval_bound z h1z
  have hCFQ : 4 * (C_F + C_Q) ≤ ‖z‖ := by
    have : 4 * (C_F + C_Q) + 1 ≤ R0 := le_max_right _ _
    linarith
  have hsum_small : ‖F_uhp r z - z ^ r‖ + ‖Polynomial.aeval z Q - z ^ r‖ ≤ (1 / 2 : ℝ) * ‖z‖ ^ r := by
    have hpow : ‖z‖ ^ r = ‖z‖ ^ (r - 1) * ‖z‖ := by
      rw [← pow_succ, show r - 1 + 1 = r by omega]
    calc ‖F_uhp r z - z ^ r‖ + ‖Polynomial.aeval z Q - z ^ r‖
        ≤ (C_F + C_Q) * ‖z‖ ^ (r - 1) := by linarith
      _ ≤ ((1 / 4 : ℝ) * ‖z‖) * ‖z‖ ^ (r - 1) := by
          gcongr
          linarith
      _ = (1 / 4 : ℝ) * ‖z‖ ^ r := by rw [hpow]; ring
      _ ≤ (1 / 2 : ℝ) * ‖z‖ ^ r := by nlinarith [show (0 : ℝ) ≤ ‖z‖ ^ r by positivity]
  have hden_ge : ‖z‖ ^ r ≤ ‖F_uhp r z + Polynomial.aeval z Q‖ := by
    have htri : ‖2 * z ^ r‖ - ‖(F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r)‖ ≤
        ‖2 * z ^ r + ((F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r))‖ := by
      have hsub := norm_sub_le (F_uhp r z + Polynomial.aeval z Q)
        ((F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r))
      have heq : (F_uhp r z + Polynomial.aeval z Q) -
          ((F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r)) = 2 * z ^ r := by ring
      rw [heq] at hsub
      have hadd_eq : 2 * z ^ r + ((F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r)) =
          F_uhp r z + Polynomial.aeval z Q := by ring
      rw [hadd_eq]
      linarith
    have h2 : ‖2 * z ^ r‖ = 2 * ‖z‖ ^ r := by simp [norm_pow]
    have hadd_eq2 : 2 * z ^ r + ((F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r)) =
        F_uhp r z + Polynomial.aeval z Q := by ring
    rw [hadd_eq2, h2] at htri
    have h3 : ‖(F_uhp r z - z ^ r) + (Polynomial.aeval z Q - z ^ r)‖ ≤
        ‖F_uhp r z - z ^ r‖ + ‖Polynomial.aeval z Q - z ^ r‖ := norm_add_le _ _
    linarith [show (0 : ℝ) ≤ ‖z‖ ^ r by positivity]
  have hden0 : F_uhp r z + Polynomial.aeval z Q ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hden_ge
    have : 0 < ‖z‖ ^ r := pow_pos hz_pos r
    linarith
  have hid :
      2 * z * (F_uhp r z + Polynomial.aeval z Q) *
          (w_fn r z * (F_uhp r z - Polynomial.aeval z Q) - (((a / 2 : ℝ) : ℂ) / z)) =
        2 * z * w_fn r z * Polynomial.aeval z R_tail - (a : ℂ) * (F_uhp r z - z ^ r) -
          (a : ℂ) * (Polynomial.aeval z Q - z ^ r) := by
    have hdiff_sq : (F_uhp r z + Polynomial.aeval z Q) * (F_uhp r z - Polynomial.aeval z Q) =
        Polynomial.aeval z R_poly := by
      rw [show (F_uhp r z + Polynomial.aeval z Q) * (F_uhp r z - Polynomial.aeval z Q) =
          F_uhp r z ^ 2 - Polynomial.aeval z Q ^ 2 by ring,
        F_uhp_sq]
      dsimp [R_poly]
      simp [map_sub, map_pow]
    have hRsplit : Polynomial.aeval z R_poly = (a : ℂ) * z ^ d + Polynomial.aeval z R_tail := by
      dsimp [R_tail]
      simp [map_sub, map_mul, map_pow]
    calc 2 * z * (F_uhp r z + Polynomial.aeval z Q) *
            (w_fn r z * (F_uhp r z - Polynomial.aeval z Q) - (((a / 2 : ℝ) : ℂ) / z))
        = 2 * z * w_fn r z * ((F_uhp r z + Polynomial.aeval z Q) *
            (F_uhp r z - Polynomial.aeval z Q)) -
            (a : ℂ) * (F_uhp r z + Polynomial.aeval z Q) := by
          push_cast; field_simp [hz0]
      _ = 2 * z * w_fn r z * ((a : ℂ) * z ^ d + Polynomial.aeval z R_tail) -
            (a : ℂ) * (F_uhp r z + Polynomial.aeval z Q) := by rw [hdiff_sq, hRsplit]
      _ = (a : ℂ) * (2 * z * w_fn r z * z ^ d) + 2 * z * w_fn r z * Polynomial.aeval z R_tail -
            (a : ℂ) * (F_uhp r z + Polynomial.aeval z Q) := by ring
      _ = (a : ℂ) * (2 * z ^ r) + 2 * z * w_fn r z * Polynomial.aeval z R_tail -
            (a : ℂ) * (F_uhp r z + Polynomial.aeval z Q) := by
          rw [two_mul_z_mul_w_fn_mul_z_pow hr]
      _ = 2 * z * w_fn r z * Polynomial.aeval z R_tail - (a : ℂ) * (F_uhp r z - z ^ r) -
            (a : ℂ) * (Polynomial.aeval z Q - z ^ r) := by ring
  have hnum :
      ‖2 * z * (F_uhp r z + Polynomial.aeval z Q) *
          (w_fn r z * (F_uhp r z - Polynomial.aeval z Q) - (((a / 2 : ℝ) : ℂ) / z))‖ ≤
        (C_Rt + |a| * (C_F + C_Q)) * ‖z‖ ^ (r - 1) := by
    rw [hid]
    calc ‖2 * z * w_fn r z * Polynomial.aeval z R_tail - (a : ℂ) * (F_uhp r z - z ^ r) -
          (a : ℂ) * (Polynomial.aeval z Q - z ^ r)‖
        ≤ ‖2 * z * w_fn r z * Polynomial.aeval z R_tail‖ +
            ‖(a : ℂ) * (F_uhp r z - z ^ r)‖ + ‖(a : ℂ) * (Polynomial.aeval z Q - z ^ r)‖ := by
          have h1 := norm_sub_le (2 * z * w_fn r z * Polynomial.aeval z R_tail -
              (a : ℂ) * (F_uhp r z - z ^ r)) ((a : ℂ) * (Polynomial.aeval z Q - z ^ r))
          have h2 := norm_sub_le (2 * z * w_fn r z * Polynomial.aeval z R_tail)
              ((a : ℂ) * (F_uhp r z - z ^ r))
          linarith
      _ ≤ C_Rt * ‖z‖ ^ (r - 1) + |a| * (C_F * ‖z‖ ^ (r - 1)) + |a| * (C_Q * ‖z‖ ^ (r - 1)) := by
          have hwa := hCRt z h1z
          rw [norm_mul (a : ℂ), norm_mul (a : ℂ), Complex.norm_real, Real.norm_eq_abs]
          gcongr
      _ = (C_Rt + |a| * (C_F + C_Q)) * ‖z‖ ^ (r - 1) := by ring
  have hden_prod : 2 * ‖z‖ ^ (r + 1) ≤ ‖2 * z * (F_uhp r z + Polynomial.aeval z Q)‖ := by
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, pow_succ', ← mul_assoc]
    gcongr
  have h2z_pos : 0 < 2 * ‖z‖ ^ (r + 1) := by positivity
  have hden0' : 2 * z * (F_uhp r z + Polynomial.aeval z Q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hz0) hden0
  have hden_norm_pos : 0 < ‖2 * z * (F_uhp r z + Polynomial.aeval z Q)‖ :=
    norm_pos_iff.mpr hden0'
  rw [← mul_div_cancel_left₀
      ‖w_fn r z * (F_uhp r z - Polynomial.aeval z Q) - (((a / 2 : ℝ) : ℂ) / z)‖
      hden_norm_pos.ne', ← norm_mul]
  calc ‖2 * z * (F_uhp r z + Polynomial.aeval z Q) *
            (w_fn r z * (F_uhp r z - Polynomial.aeval z Q) - (((a / 2 : ℝ) : ℂ) / z))‖ /
          ‖2 * z * (F_uhp r z + Polynomial.aeval z Q)‖
      ≤ ((C_Rt + |a| * (C_F + C_Q)) * ‖z‖ ^ (r - 1)) / (2 * ‖z‖ ^ (r + 1)) :=
        div_le_div₀ (by positivity) hnum h2z_pos hden_prod
    _ = C / ‖z‖ ^ 2 := by
        dsimp [C]
        rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
        field_simp [hz_pos.ne']

lemma contour_identity_im {r : ℕ} (hr : 1 ≤ r) {Q : Polynomial ℝ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = r)
    (hQ_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q ^ 2).coeff k = 0) :
    -(Real.pi * ((P_even_poly_real r - Q ^ 2).coeff (degR r)) / 2) =
      ∫ x in (-(2 * (r : ℝ) - 1))..(2 * (r : ℝ) - 1),
        (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im := by
  set a : ℝ := (P_even_poly_real r - Q ^ 2).coeff (degR r)
  set g : ℂ → ℂ := fun z => w_fn r z * (F_uhp r z - Polynomial.aeval z Q)
  set err : ℂ → ℂ := fun z => g z - (((a / 2 : ℝ) : ℂ) / z)
  obtain ⟨R0, hR0_ge, C, hC0, hO2⟩ := remainder_asymptotic_O_inv_sq hr hQ_monic hQ_deg hQ_zero
  have h1_le_R0 : 1 ≤ R0 := le_trans (le_max_left _ _) hR0_ge
  have h2r_le_R0 : 2 * (r : ℝ) + 1 ≤ R0 := le_trans (le_max_right _ _) hR0_ge
  have hQ_sum : (fun z : ℂ => Polynomial.aeval z Q) =
      fun z => ∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i • z ^ i := by
    ext z
    exact Polynomial.aeval_eq_sum_range z
  have hg_cont : ContinuousOn g {w : ℂ | 0 ≤ w.im} := by
    have hQ_cont : Continuous (fun z : ℂ => Polynomial.aeval z Q) := by
      rw [hQ_sum]
      exact continuous_finsetSum _ fun i _ => (continuous_id.pow i).const_smul (Q.coeff i)
    exact (w_fn_continuous r).continuousOn.mul ((F_uhp_continuousOn r).sub hQ_cont.continuousOn)
  have hg_diff : DifferentiableOn ℂ g {w : ℂ | 0 < w.im} := by
    have hw_diff : Differentiable ℂ (fun z : ℂ => w_fn r z) := by
      by_cases he : Even r
      · have : (fun z : ℂ => w_fn r z) = id := by ext z; simp [w_fn, he]
        rw [this]
        exact differentiable_id
      · have : (fun z : ℂ => w_fn r z) = fun _ => 1 := by ext z; simp [w_fn, he]
        rw [this]
        exact differentiable_const (1 : ℂ)
    have hQ_diff : Differentiable ℂ (fun z : ℂ => Polynomial.aeval z Q) := by
      rw [hQ_sum]
      exact Differentiable.fun_sum fun i _ => ((differentiable_id.pow i).const_smul (Q.coeff i))
    exact hw_diff.differentiableOn.mul ((F_uhp_differentiableOn r).sub hQ_diff.differentiableOn)
  have hR_step : ∀ {R : ℝ}, R0 ≤ R →
      |(∫ x in (-(2 * (r : ℝ) - 1))..(2 * (r : ℝ) - 1),
          (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im) + Real.pi * a / 2| ≤ 4 * C / R := by
    intro R hR
    have hR_pos : 0 < R := by linarith
    have hR2 : 2 * (r : ℝ) - 1 ≤ R := by linarith
    have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn g
      (-R : ℂ) ((R : ℂ) + (R : ℂ) * Complex.I)
      (hg_cont.mono (by
        intro w hw
        rcases hw with ⟨_, hw_im⟩
        change 0 ≤ w.im
        have him : w.im ∈ Set.uIcc 0 R := by
          simpa [Complex.neg_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
            Complex.I_re, Complex.I_im] using hw_im
        rw [Set.uIcc_of_le hR_pos.le] at him
        exact him.1))
      (hg_diff.mono (by
        intro w hw
        rcases hw with ⟨_, hw_im⟩
        change 0 < w.im
        have him : w.im ∈ Set.Ioo (min 0 R) (max 0 R) := by
          simpa [Complex.neg_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
            Complex.I_re, Complex.I_im] using hw_im
        rw [min_eq_left hR_pos.le] at him
        exact him.1))
    have hrect_sim :
        (∫ x in (-R)..R, g (x : ℂ)) = upperRect3 g R := by
      have hbot_eq : ∫ x in (-R : ℂ).re..((R : ℂ) + (R : ℂ) * Complex.I).re,
          g ((x : ℂ) + ((-R : ℂ).im : ℂ) * Complex.I) = ∫ x in (-R)..R, g (x : ℂ) := by
        simp
      have htop_eq : ∫ x in (-R : ℂ).re..((R : ℂ) + (R : ℂ) * Complex.I).re,
          g ((x : ℂ) + (((R : ℂ) + (R : ℂ) * Complex.I).im : ℂ) * Complex.I) =
          ∫ x in (-R)..R, g ((x : ℂ) + (R : ℂ) * Complex.I) := by
        simp
      have hright_eq : ∫ y in (-R : ℂ).im..((R : ℂ) + (R : ℂ) * Complex.I).im,
          g ((((R : ℂ) + (R : ℂ) * Complex.I).re : ℂ) + (y : ℂ) * Complex.I) =
          ∫ y in (0 : ℝ)..R, g ((R : ℂ) + (y : ℂ) * Complex.I) := by
        simp
      have hleft_eq : ∫ y in (-R : ℂ).im..((R : ℂ) + (R : ℂ) * Complex.I).im,
          g (((-R : ℂ).re : ℂ) + (y : ℂ) * Complex.I) =
          ∫ y in (0 : ℝ)..R, g ((-R : ℂ) + (y : ℂ) * Complex.I) := by
        simp
      rw [smul_eq_mul, smul_eq_mul, hbot_eq, htop_eq, hright_eq, hleft_eq] at hrect
      dsimp [upperRect3]
      exact sub_eq_zero.mp (by rw [← hrect]; ring)
    have hnorm_top : ∀ x : ℝ, R ≤ ‖(x : ℂ) + (R : ℂ) * Complex.I‖ := by
      intro x
      calc R = |((x : ℂ) + (R : ℂ) * Complex.I).im| := by simp [abs_of_pos hR_pos]
        _ ≤ ‖(x : ℂ) + (R : ℂ) * Complex.I‖ := Complex.abs_im_le_norm _
    have hnorm_right : ∀ y : ℝ, R ≤ ‖(R : ℂ) + (y : ℂ) * Complex.I‖ := by
      intro y
      calc R = |((R : ℂ) + (y : ℂ) * Complex.I).re| := by simp [abs_of_pos hR_pos]
        _ ≤ ‖(R : ℂ) + (y : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _
    have hnorm_left : ∀ y : ℝ, R ≤ ‖(-R : ℂ) + (y : ℂ) * Complex.I‖ := by
      intro y
      calc R = |((-R : ℂ) + (y : ℂ) * Complex.I).re| := by simp [abs_of_pos hR_pos]
        _ ≤ ‖(-R : ℂ) + (y : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _
    have him_top : ∀ x : ℝ, 0 ≤ ((x : ℂ) + (R : ℂ) * Complex.I).im := fun x => by simp [hR_pos.le]
    have him_rl : ∀ y ∈ Set.Icc (0 : ℝ) R, 0 ≤ y := fun _ hy => hy.1
    have hinv_cont_top : Continuous (fun x : ℝ => ((a / 2 : ℝ) : ℂ) * (1 / ((x : ℂ) + (R : ℂ) * Complex.I))) := by
      refine continuous_const.mul (continuous_const.div (Complex.continuous_ofReal.add continuous_const) fun x => ?_)
      intro h0
      have him : ((x : ℂ) + (R : ℂ) * Complex.I).im = R := by simp
      rw [h0, Complex.zero_im] at him
      linarith
    have hinv_cont_right : Continuous (fun y : ℝ => ((a / 2 : ℝ) : ℂ) * (1 / ((R : ℂ) + (y : ℂ) * Complex.I))) := by
      refine continuous_const.mul (continuous_const.div (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y => ?_)
      intro h0
      have hre : ((R : ℂ) + (y : ℂ) * Complex.I).re = R := by simp
      rw [h0, Complex.zero_re] at hre
      linarith
    have hinv_cont_left : Continuous (fun y : ℝ => ((a / 2 : ℝ) : ℂ) * (1 / ((-R : ℂ) + (y : ℂ) * Complex.I))) := by
      refine continuous_const.mul (continuous_const.div (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y => ?_)
      intro h0
      have hre : ((-R : ℂ) + (y : ℂ) * Complex.I).re = -R := by simp
      rw [h0, Complex.zero_re] at hre
      linarith
    have hg_cont_top : ContinuousOn (fun x : ℝ => g ((x : ℂ) + (R : ℂ) * Complex.I)) (Set.uIcc (-R) R) :=
      hg_cont.comp (Complex.continuous_ofReal.add continuous_const).continuousOn (fun x _ => by simp [hR_pos.le])
    have hg_cont_right : ContinuousOn (fun y : ℝ => g ((R : ℂ) + (y : ℂ) * Complex.I)) (Set.uIcc 0 R) :=
      hg_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
        (fun y hy => by rw [Set.uIcc_of_le hR_pos.le] at hy; simp [hy.1])
    have hg_cont_left : ContinuousOn (fun y : ℝ => g ((-R : ℂ) + (y : ℂ) * Complex.I)) (Set.uIcc 0 R) :=
      hg_cont.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
        (fun y hy => by rw [Set.uIcc_of_le hR_pos.le] at hy; simp [hy.1])
    have herr_top_int : IntervalIntegrable
        (fun x : ℝ => err ((x : ℂ) + (R : ℂ) * Complex.I)) MeasureTheory.volume (-R) R := by
      simpa only [err, mul_one_div] using
        (hg_cont_top.intervalIntegrable (μ := MeasureTheory.volume)).sub
          (hinv_cont_top.intervalIntegrable (-R) R)
    have herr_right_int : IntervalIntegrable
        (fun y : ℝ => err ((R : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 R := by
      simpa only [err, mul_one_div] using
        (hg_cont_right.intervalIntegrable (μ := MeasureTheory.volume)).sub
          (hinv_cont_right.intervalIntegrable 0 R)
    have herr_left_int : IntervalIntegrable
        (fun y : ℝ => err ((-R : ℂ) + (y : ℂ) * Complex.I)) MeasureTheory.volume 0 R := by
      simpa only [err, mul_one_div] using
        (hg_cont_left.intervalIntegrable (μ := MeasureTheory.volume)).sub
          (hinv_cont_left.intervalIntegrable 0 R)
    have hg_split : g = fun z => ((a / 2 : ℝ) : ℂ) * (1 / z) + err z := by
      ext z; dsimp [err]; rw [mul_one_div]; ring
    have hu_split : upperRect3 g R =
        ((a / 2 : ℝ) : ℂ) * upperRect3 (fun z => 1 / z) R + upperRect3 err R := by
      calc upperRect3 g R
          = upperRect3 (fun z => ((a / 2 : ℝ) : ℂ) * (1 / z) + err z) R := by
              rw [hg_split]
        _ = upperRect3 (fun z => ((a / 2 : ℝ) : ℂ) * (1 / z)) R + upperRect3 err R :=
            upperRect3_add
              (hinv_cont_top.intervalIntegrable (-R) R) herr_top_int
              (hinv_cont_right.intervalIntegrable 0 R) herr_right_int
              (hinv_cont_left.intervalIntegrable 0 R) herr_left_int
        _ = ((a / 2 : ℝ) : ℂ) * upperRect3 (fun z => 1 / z) R + upperRect3 err R := by
            rw [upperRect3_const_mul]
    rw [upperRect3_inv_z hR_pos] at hu_split
    have herr_bound : ‖upperRect3 err R‖ ≤ 4 * C / R := by
      have hbt : ‖∫ x in (-R)..R, err ((x : ℂ) + (R : ℂ) * Complex.I)‖ ≤ (C / R ^ 2) * |R - (-R)| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
        have h1 := hO2 ((x : ℂ) + (R : ℂ) * Complex.I) (him_top x) (le_trans hR (hnorm_top x))
        exact h1.trans (div_le_div_of_nonneg_left hC0 (pow_pos hR_pos 2)
          (pow_le_pow_left₀ hR_pos.le (hnorm_top x) 2))
      have hbr : ‖∫ y in (0 : ℝ)..R, err ((R : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (C / R ^ 2) * |R - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le hR_pos.le] at hy
        have h1 := hO2 ((R : ℂ) + (y : ℂ) * Complex.I) (by simp [hy.1.le]) (le_trans hR (hnorm_right y))
        exact h1.trans (div_le_div_of_nonneg_left hC0 (pow_pos hR_pos 2)
          (pow_le_pow_left₀ hR_pos.le (hnorm_right y) 2))
      have hbl : ‖∫ y in (0 : ℝ)..R, err ((-R : ℂ) + (y : ℂ) * Complex.I)‖ ≤ (C / R ^ 2) * |R - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        rw [Set.uIoc_of_le hR_pos.le] at hy
        have h1 := hO2 ((-R : ℂ) + (y : ℂ) * Complex.I) (by simp [hy.1.le]) (le_trans hR (hnorm_left y))
        exact h1.trans (div_le_div_of_nonneg_left hC0 (pow_pos hR_pos 2)
          (pow_le_pow_left₀ hR_pos.le (hnorm_left y) 2))
      have h2R : |R - (-R)| = 2 * R := by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
      have h1R : |R - 0| = R := by rw [sub_zero, abs_of_pos hR_pos]
      rw [h2R] at hbt
      rw [h1R] at hbr hbl
      dsimp [upperRect3]
      calc ‖(∫ x in (-R)..R, err ((x : ℂ) + (R : ℂ) * Complex.I)) -
              Complex.I * (∫ y in (0 : ℝ)..R, err ((R : ℂ) + (y : ℂ) * Complex.I)) +
              Complex.I * (∫ y in (0 : ℝ)..R, err ((-R : ℂ) + (y : ℂ) * Complex.I))‖
          ≤ ‖∫ x in (-R)..R, err ((x : ℂ) + (R : ℂ) * Complex.I)‖ +
              ‖Complex.I * (∫ y in (0 : ℝ)..R, err ((R : ℂ) + (y : ℂ) * Complex.I))‖ +
              ‖Complex.I * (∫ y in (0 : ℝ)..R, err ((-R : ℂ) + (y : ℂ) * Complex.I))‖ := by
            have h1 := norm_add_le
              ((∫ x in (-R)..R, err ((x : ℂ) + (R : ℂ) * Complex.I)) -
                Complex.I * (∫ y in (0 : ℝ)..R, err ((R : ℂ) + (y : ℂ) * Complex.I)))
              (Complex.I * (∫ y in (0 : ℝ)..R, err ((-R : ℂ) + (y : ℂ) * Complex.I)))
            have h2 := norm_sub_le (∫ x in (-R)..R, err ((x : ℂ) + (R : ℂ) * Complex.I))
              (Complex.I * (∫ y in (0 : ℝ)..R, err ((R : ℂ) + (y : ℂ) * Complex.I)))
            linarith
        _ = ‖∫ x in (-R)..R, err ((x : ℂ) + (R : ℂ) * Complex.I)‖ +
              ‖∫ y in (0 : ℝ)..R, err ((R : ℂ) + (y : ℂ) * Complex.I)‖ +
              ‖∫ y in (0 : ℝ)..R, err ((-R : ℂ) + (y : ℂ) * Complex.I)‖ := by
            simp [Complex.norm_I]
        _ ≤ C / R ^ 2 * (2 * R) + C / R ^ 2 * R + C / R ^ 2 * R := by linarith
        _ = 4 * C / R := by field_simp [hR_pos.ne']; ring
    have hg_bot_cont : Continuous (fun x : ℝ => g (x : ℂ)) :=
      hg_cont.comp_continuous Complex.continuous_ofReal (fun x => by simp)
    have hbot_im : (∫ x in (-R)..R, g (x : ℂ)).im =
        ∫ x in (-R)..R, (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im := by
      have him := Complex.imCLM.intervalIntegral_comp_comm
        (hg_bot_cont.intervalIntegrable (μ := MeasureTheory.volume) (-R) R)
      change ∫ x in (-R)..R, (g (x : ℂ)).im = (∫ x in (-R)..R, g (x : ℂ)).im at him
      rw [← him]
      refine intervalIntegral.integral_congr fun x _ => ?_
      dsimp [g]
      rw [mul_sub]
      have hqreal : (w_fn r (x : ℂ) * Polynomial.aeval (x : ℂ) Q).im = 0 := by
        rw [w_fn_ofReal]
        have haeval : Polynomial.aeval (x : ℂ) Q = ((Polynomial.aeval x Q : ℝ) : ℂ) := by
          rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
          push_cast
          simp [Algebra.smul_def]
        rw [haeval, ← Complex.ofReal_mul, Complex.ofReal_im]
      rw [Complex.sub_im, hqreal, sub_zero]
    have hwf_cont : Continuous (fun x : ℝ => (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im) :=
      Complex.continuous_im.comp (((w_fn_continuous r).comp Complex.continuous_ofReal).mul
        ((F_uhp_continuousOn r).comp_continuous Complex.continuous_ofReal (fun x => by simp)))
    have hbot_split : ∫ x in (-R)..R, (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im =
        ∫ x in (-(2 * (r : ℝ) - 1))..(2 * (r : ℝ) - 1),
          (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hwf_cont.intervalIntegrable (μ := MeasureTheory.volume) (-R) (-(2 * (r : ℝ) - 1)))
        (hwf_cont.intervalIntegrable (μ := MeasureTheory.volume) (-(2 * (r : ℝ) - 1)) (2 * (r : ℝ) - 1))
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hwf_cont.intervalIntegrable (μ := MeasureTheory.volume) (-R) (2 * (r : ℝ) - 1))
        (hwf_cont.intervalIntegrable (μ := MeasureTheory.volume) (2 * (r : ℝ) - 1) R)
      have hleft0 : ∫ x in (-R)..(-(2 * (r : ℝ) - 1)),
          (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
          rw [Set.uIcc_of_le (by linarith)] at hx
          have hle : 2 * (r : ℝ) - 1 ≤ |x| := by
            rw [le_abs]; right; linarith [hx.2]
          rw [w_fn_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            F_uhp_ofReal_outside hle, mul_zero], intervalIntegral.integral_zero]
      have hright0 : ∫ x in (2 * (r : ℝ) - 1)..R,
          (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
          rw [Set.uIcc_of_le hR2] at hx
          have hle : 2 * (r : ℝ) - 1 ≤ |x| := by
            rw [le_abs]; left; exact hx.1
          rw [w_fn_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
            F_uhp_ofReal_outside hle, mul_zero], intervalIntegral.integral_zero]
      linarith
    have hdiff_im : (∫ x in (-R)..R, g (x : ℂ)).im + Real.pi * a / 2 = (upperRect3 err R).im := by
      rw [hrect_sim, hu_split]
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hbot_im, hbot_split] at hdiff_im
    rw [hdiff_im]
    exact (Complex.abs_im_le_norm (upperRect3 err R)).trans herr_bound
  set I_val : ℝ := ∫ x in (-(2 * (r : ℝ) - 1))..(2 * (r : ℝ) - 1),
      (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im
  have hzero : |I_val + Real.pi * a / 2| = 0 := by
    by_contra hne
    have hpos : 0 < |I_val + Real.pi * a / 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    set R : ℝ := max R0 (8 * C + 1) / |I_val + Real.pi * a / 2| + R0
    have hR0 : R0 ≤ R := by
      have : 0 ≤ max R0 (8 * C + 1) / |I_val + Real.pi * a / 2| := by
        have : 0 ≤ max R0 (8 * C + 1) := le_trans (by linarith) (le_max_left _ _)
        positivity
      linarith
    have h1 := hR_step hR0
    have hR_big : (8 * C + 1) / |I_val + Real.pi * a / 2| ≤ R := by
      have hmax : (8 * C + 1) / |I_val + Real.pi * a / 2| ≤
          max R0 (8 * C + 1) / |I_val + Real.pi * a / 2| :=
        div_le_div_of_nonneg_right (le_max_right _ _) hpos.le
      linarith
    have hR_pos : 0 < R := by linarith
    have h2 : 4 * C / R < |I_val + Real.pi * a / 2| := by
      rw [div_lt_iff₀ hR_pos]
      have h3 : (8 * C + 1) ≤ |I_val + Real.pi * a / 2| * R := by
        rwa [div_le_iff₀' hpos] at hR_big
      linarith
    linarith
  have heq0 : I_val + Real.pi * a / 2 = 0 := abs_eq_zero.mp hzero
  linarith

/-! ## 4. Symmetry, Shift-by-4 Inequality, Alternating Sum, and Main Sign Theorems -/

private lemma I_pow_even_im (k : ℕ) : (Complex.I ^ (2 * k)).im = 0 := by
  rw [pow_mul, Complex.I_sq]
  norm_cast

private lemma I_pow_odd_im (k : ℕ) : (Complex.I ^ (2 * k + 1)).im = (-1 : ℝ) ^ k := by
  have h : Complex.I ^ (2 * k + 1) = (((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.I := by
    calc Complex.I ^ (2 * k + 1) = (Complex.I ^ 2) ^ k * Complex.I := by
          rw [pow_succ, pow_mul]
      _ = ((-1 : ℂ) ^ k) * Complex.I := by rw [Complex.I_sq]
      _ = (((-1 : ℝ) ^ k : ℝ) : ℂ) * Complex.I := by push_cast; rfl
  rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, zero_mul, add_zero]

noncomputable def g_int (r : ℕ) (x : ℝ) : ℝ :=
  (w_fn r (x : ℂ) * F_uhp r (x : ℂ)).im

lemma g_int_continuous (r : ℕ) : Continuous (g_int r) :=
  Complex.continuous_im.comp (((w_fn_continuous r).comp Complex.continuous_ofReal).mul
    ((F_uhp_continuousOn r).comp_continuous Complex.continuous_ofReal (fun _ => by simp)))

private lemma rootPt_reflect (r k : ℕ) (hk : k < 2 * r) :
    rootPt r (2 * r - 1 - k) = -rootPt r k := by
  dsimp [rootPt]
  have hk1 : k ≤ 2 * r - 1 := by omega
  have h1r : 1 ≤ 2 * r := by omega
  rw [Nat.cast_sub hk1, Nat.cast_sub h1r]
  push_cast
  ring

private lemma F_uhp_eq_zero_at_rootPt {r k : ℕ} (hk : k < 2 * r) :
    F_uhp r (rootPt r k : ℂ) = 0 := by
  dsimp [F_uhp]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hk) ?_
  simp [uhpSqrt]

lemma g_int_neg (r : ℕ) (x : ℝ) : g_int r (-x) = g_int r x := by
  dsimp [g_int]
  by_cases hroot : ∃ k ∈ Finset.range (2 * r), x = rootPt r k
  · obtain ⟨k, hk, rfl⟩ := hroot
    rw [Finset.mem_range] at hk
    have href : ((-rootPt r k : ℝ) : ℂ) = (rootPt r (2 * r - 1 - k) : ℂ) := by
      rw [rootPt_reflect r k hk]
    rw [href, F_uhp_eq_zero_at_rootPt (by omega), F_uhp_eq_zero_at_rootPt hk, mul_zero, mul_zero]
  · push Not at hroot
    have hx_ne : ∀ k ∈ Finset.range (2 * r), x - rootPt r k ≠ 0 := by
      intro k hk h0
      exact hroot k hk (sub_eq_zero.mp h0)
    have hF_neg : F_uhp r ((-x : ℝ) : ℂ) =
        Complex.I ^ (2 * r) * star (F_uhp r (x : ℂ)) := by
      dsimp [F_uhp]
      have hreidx : ∏ j ∈ Finset.range (2 * r),
            uhpSqrt (((-x : ℝ) : ℂ) - (rootPt r j : ℂ)) =
          ∏ k ∈ Finset.range (2 * r),
            uhpSqrt (((-x : ℝ) : ℂ) - (rootPt r (2 * r - 1 - k) : ℂ)) := by
        refine Finset.prod_nbij (fun j => 2 * r - 1 - j)
          (fun j hj => by rw [Finset.mem_range] at hj ⊢; omega)
          (fun j₁ hj₁ j₂ hj₂ heq => by
            rw [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
            dsimp only at heq
            omega)
          (fun k hk => by
            rw [Finset.mem_coe, Finset.mem_range] at hk
            exact ⟨2 * r - 1 - k, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)),
              by dsimp only; omega⟩)
          (fun j hj => by
            rw [Finset.mem_range] at hj
            rw [show 2 * r - 1 - (2 * r - 1 - j) = j by omega])
      rw [hreidx]
      have hfac : ∀ k ∈ Finset.range (2 * r),
          uhpSqrt (((-x : ℝ) : ℂ) - (rootPt r (2 * r - 1 - k) : ℂ)) =
            Complex.I * star (uhpSqrt ((x : ℂ) - (rootPt r k : ℂ))) := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [rootPt_reflect r k hk]
        push_cast
        rw [show -(x : ℂ) - -(rootPt r k : ℂ) = -((x - rootPt r k : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_neg, uhpSqrt_neg_conj_real (hx_ne k (Finset.mem_range.mpr hk)),
          ← Complex.ofReal_sub]
      rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range]
      congr 1
      simp only [Complex.star_def, map_prod]
    have hI2r : Complex.I ^ (2 * r) = (((-1 : ℝ) ^ r : ℝ) : ℂ) := by
      rw [pow_mul, Complex.I_sq]
      push_cast
      rfl
    rw [hF_neg, hI2r]
    by_cases he : Even r
    · have hneg1 : ((-1 : ℝ) ^ r : ℝ) = 1 := he.neg_one_pow
      rw [hneg1, Complex.ofReal_one, one_mul, w_fn, if_pos he, w_fn, if_pos he]
      simp [Complex.mul_im]
    · have hodd : Odd r := Nat.not_even_iff_odd.mp he
      have hneg1 : ((-1 : ℝ) ^ r : ℝ) = -1 := hodd.neg_one_pow
      simp only [hneg1, Complex.ofReal_neg, Complex.ofReal_one, w_fn, if_neg he, one_mul]
      simp

lemma integral_g_int_symm {r : ℕ} (_hr : 1 ≤ r) :
    ∫ x in (-(2 * (r : ℝ) - 1))..(2 * (r : ℝ) - 1), g_int r x =
      2 * ∫ x in (0 : ℝ)..(2 * (r : ℝ) - 1), g_int r x := by
  have hc := g_int_continuous r
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (-(2 * (r : ℝ) - 1)) 0)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * (r : ℝ) - 1))
  have hcomp : ∫ x in (-(2 * (r : ℝ) - 1))..0, g_int r x =
      ∫ x in (0 : ℝ)..(2 * (r : ℝ) - 1), g_int r x := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 2 * (r : ℝ) - 1)
      (f := g_int r)
    rw [neg_zero] at h1
    rw [← h1]
    exact intervalIntegral.integral_congr fun x _ => g_int_neg r x
  linarith

lemma P_even_real_shift4_id {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    P_even_real r (x + 4) * (x - (2 * (r : ℝ) - 3)) * (x - (2 * (r : ℝ) - 1)) =
      P_even_real r x * (x + (2 * (r : ℝ) + 1)) * (x + (2 * (r : ℝ) + 3)) := by
  set N : ℕ := 2 * r - 2
  have h2r : 2 * r = N + 2 := by omega
  have hL : P_even_real r (x + 4) =
      (x + (2 * (r : ℝ) + 3)) * (x + (2 * (r : ℝ) + 1)) *
        ∏ k ∈ Finset.range N, (x - rootPt r k) := by
    dsimp [P_even_real]
    rw [h2r, Finset.prod_range_succ', Finset.prod_range_succ']
    have h0 : x + 4 - rootPt r 0 = x + (2 * (r : ℝ) + 3) := by
      dsimp [rootPt]; ring
    have h1 : x + 4 - rootPt r 1 = x + (2 * (r : ℝ) + 1) := by
      dsimp [rootPt]; ring
    have hshift : ∏ k ∈ Finset.range N, (x + 4 - rootPt r (k + 1 + 1)) =
        ∏ k ∈ Finset.range N, (x - rootPt r k) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      dsimp [rootPt]
      push_cast
      ring
    rw [h0, h1, hshift]
    ring
  have hR : P_even_real r x =
      (∏ k ∈ Finset.range N, (x - rootPt r k)) *
        (x - (2 * (r : ℝ) - 3)) * (x - (2 * (r : ℝ) - 1)) := by
    dsimp [P_even_real]
    rw [h2r, Finset.prod_range_succ, Finset.prod_range_succ]
    have hN : rootPt r N = 2 * (r : ℝ) - 3 := by
      dsimp [rootPt, N]
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * r), Nat.cast_mul]
      push_cast
      ring
    have hN1 : rootPt r (N + 1) = 2 * (r : ℝ) - 1 := by
      dsimp [rootPt, N]
      rw [Nat.cast_add, Nat.cast_sub (by omega : 2 ≤ 2 * r), Nat.cast_mul]
      push_cast
      ring
    rw [hN, hN1]
  rw [hL, hR]
  ring

lemma P_even_real_abs_le_shift4 {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * (r : ℝ) - 3) :
    |P_even_real r x| ≤ |P_even_real r (x + 4)| := by
  by_cases hx_eq : x = 2 * (r : ℝ) - 3
  · subst hx_eq
    have hzero : P_even_real r (2 * (r : ℝ) - 3) = 0 := by
      dsimp [P_even_real]
      refine Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 2 * r - 2 < 2 * r)) ?_
      dsimp [rootPt]
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * r), Nat.cast_mul]
      push_cast
      ring
    rw [hzero, abs_zero]
    exact abs_nonneg _
  · have hx_lt : x < 2 * (r : ℝ) - 3 := lt_of_le_of_ne hx1 hx_eq
    have hid := congrArg abs (P_even_real_shift4_id hr x)
    simp only [abs_mul] at hid
    have ha : 0 < |x - (2 * (r : ℝ) - 3)| := abs_pos.mpr (by linarith)
    have hb : 0 < |x - (2 * (r : ℝ) - 1)| := abs_pos.mpr (by linarith)
    have hden_pos : 0 < |x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)| := mul_pos ha hb
    have hfac1 : |x - (2 * (r : ℝ) - 3)| < |x + (2 * (r : ℝ) + 1)| := by
      rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith
    have hfac2 : |x - (2 * (r : ℝ) - 1)| < |x + (2 * (r : ℝ) + 3)| := by
      rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith
    have hprod_le :
        |P_even_real r x| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) ≤
          |P_even_real r x| * (|x + (2 * (r : ℝ) + 1)| * |x + (2 * (r : ℝ) + 3)|) := by
      have hmul : |x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)| ≤
          |x + (2 * (r : ℝ) + 1)| * |x + (2 * (r : ℝ) + 3)| :=
        mul_le_mul hfac1.le hfac2.le (abs_nonneg _) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left hmul (abs_nonneg _)
    have hid' :
        |P_even_real r (x + 4)| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) =
          |P_even_real r x| * (|x + (2 * (r : ℝ) + 1)| * |x + (2 * (r : ℝ) + 3)|) := by
      linarith
    have : |P_even_real r x| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) ≤
        |P_even_real r (x + 4)| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) := by
      linarith
    exact le_of_mul_le_mul_right this hden_pos

lemma P_even_real_abs_lt_shift4 {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 2 * (r : ℝ) - 3) (hne : P_even_real r x ≠ 0) :
    |P_even_real r x| < |P_even_real r (x + 4)| := by
  have hid := congrArg abs (P_even_real_shift4_id hr x)
  simp only [abs_mul] at hid
  have ha : 0 < |x - (2 * (r : ℝ) - 3)| := abs_pos.mpr (by linarith)
  have hb : 0 < |x - (2 * (r : ℝ) - 1)| := abs_pos.mpr (by linarith)
  have hden_pos : 0 < |x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)| := mul_pos ha hb
  have hfac1 : |x - (2 * (r : ℝ) - 3)| < |x + (2 * (r : ℝ) + 1)| := by
    rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith
  have hfac2 : |x - (2 * (r : ℝ) - 1)| < |x + (2 * (r : ℝ) + 3)| := by
    rw [abs_of_neg (by linarith), abs_of_pos (by linarith)]; linarith
  have hmul : |x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)| <
      |x + (2 * (r : ℝ) + 1)| * |x + (2 * (r : ℝ) + 3)| :=
    mul_lt_mul' hfac1.le hfac2 hb.le (abs_pos.mpr (by linarith))
  have hP_pos : 0 < |P_even_real r x| := abs_pos.mpr hne
  have hprod_lt :
      |P_even_real r x| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) <
        |P_even_real r x| * (|x + (2 * (r : ℝ) + 1)| * |x + (2 * (r : ℝ) + 3)|) :=
    mul_lt_mul_of_pos_left hmul hP_pos
  have hid' :
      |P_even_real r (x + 4)| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) =
        |P_even_real r x| * (|x + (2 * (r : ℝ) + 1)| * |x + (2 * (r : ℝ) + 3)|) := by
    linarith
  have : |P_even_real r x| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) <
      |P_even_real r (x + 4)| * (|x - (2 * (r : ℝ) - 3)| * |x - (2 * (r : ℝ) - 1)|) := by
    linarith
  exact lt_of_mul_lt_mul_right this hden_pos.le

private lemma P_even_real_ne_zero_even_nat (r n : ℕ) :
    P_even_real r ((2 * n : ℕ) : ℝ) ≠ 0 := by
  dsimp [P_even_real]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  dsimp [rootPt]
  intro h0
  push_cast at h0
  have hint : (((2 * (n : ℤ) : ℤ) : ℝ)) = (((2 * (k : ℤ) - (2 * (r : ℤ) - 1) : ℤ) : ℝ)) := by
    push_cast
    linarith
  have hz : 2 * (n : ℤ) = 2 * (k : ℤ) - (2 * (r : ℤ) - 1) := Int.cast_injective hint
  omega

private lemma P_even_real_ne_zero_half (r : ℕ) :
    P_even_real r (1 / 2 : ℝ) ≠ 0 := by
  dsimp [P_even_real]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
  dsimp [rootPt]
  intro h0
  have hint : (((1 : ℤ) : ℝ)) = (((4 * (k : ℤ) - 4 * (r : ℤ) + 2 : ℤ) : ℝ)) := by
    push_cast
    linarith
  have hz : (1 : ℤ) = 4 * (k : ℤ) - 4 * (r : ℤ) + 2 := Int.cast_injective hint
  omega

private lemma alt_sum_pos (A : ℕ → ℝ) :
    ∀ m : ℕ, 0 < A 0 → (∀ k < m, A k < A (k + 1)) →
      0 < ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - k) * A k
  | 0, h0, _ => by simp [h0]
  | 1, _, hinc => by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have hlt := hinc 0 (by decide)
    norm_num
    linarith
  | m + 2, h0, hinc => by
    have ih := alt_sum_pos A m h0 (fun k hk => hinc k (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hre : ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m + 2 - k) * A k =
        ∑ k ∈ Finset.range (m + 1), (-1 : ℝ) ^ (m - k) * A k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show m + 2 - k = (m - k) + 2 by omega, pow_add]
      norm_num
    have hlast : (-1 : ℝ) ^ (m + 2 - (m + 1)) = -1 := by
      rw [show m + 2 - (m + 1) = 1 by omega]; norm_num
    have htop : (-1 : ℝ) ^ (m + 2 - (m + 2)) = 1 := by
      rw [Nat.sub_self]; norm_num
    have hinc_top := hinc (m + 1) (by omega)
    rw [hre, hlast, htop]
    linarith

private lemma sum_range_two_mul_add_one_even_only (f : ℕ → ℝ) (hf : ∀ k : ℕ, Odd k → f k = 0) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (2 * n + 1), f j = ∑ q ∈ Finset.range (n + 1), f (2 * q)
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul_add_one_even_only f hf n,
      hf (2 * n + 1) ⟨n, rfl⟩, add_zero,
      Finset.sum_range_succ (fun q => f (2 * q)) (n + 1),
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring]

private lemma sum_range_two_mul_odd_only (f : ℕ → ℝ) (hf : ∀ k : ℕ, Even k → f k = 0) :
    ∀ n : ℕ, ∑ j ∈ Finset.range (2 * n), f j = ∑ q ∈ Finset.range n, f (2 * q + 1)
  | 0 => by simp
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul_odd_only f hf n,
      hf (2 * n) ⟨n, by ring⟩, add_zero,
      Finset.sum_range_succ (fun q => f (2 * q + 1)) n]

private lemma sqrt_P_continuous (r : ℕ) : Continuous (fun x : ℝ => Real.sqrt |P_even_real r x|) :=
  Real.continuous_sqrt.comp (continuous_abs.comp (continuous_finsetProd _ fun _ _ =>
    continuous_id.sub continuous_const))

private lemma g_int_on_subinterval {r m : ℕ} (hm : m + 1 < 2 * r) {x : ℝ}
    (hx1 : rootPt r m ≤ x) (hx2 : x ≤ rootPt r (m + 1)) :
    g_int r x =
      (if Even r then x else 1) * (Complex.I ^ (2 * r - 1 - m)).im *
        Real.sqrt |P_even_real r x| := by
  dsimp [g_int]
  rw [w_fn_ofReal, F_uhp_ofReal_subinterval hm hx1 hx2, ← mul_assoc]
  have hid : ((if Even r then x else 1 : ℝ) : ℂ) * Complex.I ^ (2 * r - 1 - m) *
        (Real.sqrt |P_even_real r x| : ℂ) =
      (((if Even r then x else 1 : ℝ) : ℂ) * Complex.I ^ (2 * r - 1 - m)) *
        (Real.sqrt |P_even_real r x| : ℂ) := rfl
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_zero]
  ring

lemma integral_g_int_pos {r : ℕ} (hr : 1 ≤ r) :
    0 < ∫ x in (0 : ℝ)..(2 * (r : ℝ) - 1), g_int r x := by
  have hgc := g_int_continuous r
  have hsc := sqrt_P_continuous r
  by_cases he : Even r
  · have ⟨s, hs⟩ := he
    have hs1 : 1 ≤ s := by omega
    have hr_eq : r = 2 * s := by omega
    have hsplit0 : ∫ x in (0 : ℝ)..(2 * (r : ℝ) - 1), g_int r x =
        (∫ x in (0 : ℝ)..1, g_int r x) + ∫ x in (1 : ℝ)..(2 * (r : ℝ) - 1), g_int r x :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hgc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
        (hgc.intervalIntegrable (μ := MeasureTheory.volume) 1 (2 * (r : ℝ) - 1))).symm
    have h01 : ∫ x in (0 : ℝ)..1, g_int r x = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
        rw [Set.uIcc_of_le zero_le_one] at hx
        have hlo : rootPt r (r - 1) ≤ x := by
          dsimp [rootPt]
          rw [Nat.cast_sub (by omega : 1 ≤ r)]
          push_cast
          linarith [hx.1]
        have hhi : x ≤ rootPt r ((r - 1) + 1) := by
          dsimp [rootPt]
          rw [Nat.sub_add_cancel hr]
          linarith [hx.2]
        rw [g_int_on_subinterval (by omega : (r - 1) + 1 < 2 * r) hlo hhi,
          show 2 * r - 1 - (r - 1) = 2 * s by omega, I_pow_even_im]
        simp, intervalIntegral.integral_zero]
    set M : ℕ := 2 * (s - 1) + 1
    have hM_eq : (1 : ℝ) + 2 * (M : ℝ) = 2 * (r : ℝ) - 1 := by
      dsimp [M]; rw [hr_eq]; push_cast; rw [Nat.cast_sub hs1]; ring
    have hadj : ∫ x in (1 : ℝ)..(2 * (r : ℝ) - 1), g_int r x =
        ∑ j ∈ Finset.range M,
          ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x := by
      have hs_int := intervalIntegral.sum_integral_adjacent_intervals
        (f := g_int r) (a := fun j : ℕ => (1 : ℝ) + 2 * (j : ℝ)) (n := M)
        (fun j _ => hgc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      rw [Nat.cast_zero, mul_zero, add_zero, hM_eq] at hs_int
      exact hs_int.symm
    have hodd0 : ∀ j : ℕ, Odd j →
        (if j < M then ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x else 0) =
          0 := by
      intro j hj
      split_ifs with hlt
      · obtain ⟨q, rfl⟩ := hj
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
          have hle : (1 + 2 * ((2 * q + 1 : ℕ) : ℝ)) ≤ 1 + 2 * ((2 * q + 1 + 1 : ℕ) : ℝ) := by
            push_cast; linarith
          rw [Set.uIcc_of_le hle] at hx
          push_cast at hx
          have hlo : rootPt r (r + (2 * q + 1)) ≤ x := by
            dsimp [rootPt]; push_cast; linarith [hx.1]
          have hhi : x ≤ rootPt r (r + (2 * q + 1) + 1) := by
            dsimp [rootPt]; push_cast; linarith [hx.2]
          rw [g_int_on_subinterval (by omega : (r + (2 * q + 1)) + 1 < 2 * r) hlo hhi,
            show 2 * r - 1 - (r + (2 * q + 1)) = 2 * (s - 1 - q) by omega, I_pow_even_im]
          simp, intervalIntegral.integral_zero]
      · rfl
    have hsum_filt :
        ∑ j ∈ Finset.range M,
            ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x =
          ∑ q ∈ Finset.range s,
            (if 2 * q < M then
              ∫ x in (1 + 2 * ((2 * q : ℕ) : ℝ))..(1 + 2 * ((2 * q + 1 : ℕ) : ℝ)), g_int r x
            else 0) := by
      have hite : ∑ j ∈ Finset.range M,
            ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x =
          ∑ j ∈ Finset.range M,
            (if j < M then
              ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x else 0) := by
        refine Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
      rw [hite]
      dsimp [M]
      rw [sum_range_two_mul_add_one_even_only _ hodd0 (s - 1),
        show (s - 1) + 1 = s by omega]
    set I_even : ℕ → ℝ := fun q =>
      ∫ x in (4 * (q : ℝ) + 1)..(4 * (q : ℝ) + 3), x * Real.sqrt |P_even_real r x|
    have hsum_I :
        ∑ q ∈ Finset.range s,
            (if 2 * q < M then
              ∫ x in (1 + 2 * ((2 * q : ℕ) : ℝ))..(1 + 2 * ((2 * q + 1 : ℕ) : ℝ)), g_int r x
            else 0) =
          ∑ q ∈ Finset.range s, (-1 : ℝ) ^ ((s - 1) - q) * I_even q := by
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [Finset.mem_range] at hq
      have hqM : 2 * q < M := by dsimp [M]; omega
      rw [if_pos hqM]
      have ha_eq : 1 + 2 * ((2 * q : ℕ) : ℝ) = 4 * (q : ℝ) + 1 := by push_cast; ring
      have hb_eq : 1 + 2 * ((2 * q + 1 : ℕ) : ℝ) = 4 * (q : ℝ) + 3 := by push_cast; ring
      rw [ha_eq, hb_eq]
      have hcongr :
          ∫ x in (4 * (q : ℝ) + 1)..(4 * (q : ℝ) + 3), g_int r x =
            ∫ x in (4 * (q : ℝ) + 1)..(4 * (q : ℝ) + 3),
              (-1 : ℝ) ^ ((s - 1) - q) * (x * Real.sqrt |P_even_real r x|) := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [Set.uIcc_of_le (by linarith)] at hx
        have hlo : rootPt r (r + 2 * q) ≤ x := by
          dsimp [rootPt]; rw [hr_eq]; push_cast; linarith [hx.1]
        have hhi : x ≤ rootPt r (r + 2 * q + 1) := by
          dsimp [rootPt]; rw [hr_eq]; push_cast; linarith [hx.2]
        rw [g_int_on_subinterval (by omega : (r + 2 * q) + 1 < 2 * r) hlo hhi, if_pos he,
          show 2 * r - 1 - (r + 2 * q) = 2 * ((s - 1) - q) + 1 by omega, I_pow_odd_im]
        ring
      rw [hcongr, intervalIntegral.integral_const_mul]
    have hI0_pos : 0 < I_even 0 := by
      dsimp [I_even]
      have hc : ContinuousOn (fun x : ℝ => x * Real.sqrt |P_even_real r x|)
          (Set.Icc (4 * ((0 : ℕ) : ℝ) + 1) (4 * ((0 : ℕ) : ℝ) + 3)) :=
        (continuous_id.mul hsc).continuousOn
      refine intervalIntegral.integral_pos (by norm_num) hc ?_ ?_
      · intro x hx
        rw [Set.mem_Ioc] at hx
        exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
      · refine ⟨2, ⟨by norm_num, by norm_num⟩, ?_⟩
        have hne := P_even_real_ne_zero_even_nat r 1
        simp only [Nat.mul_one] at hne
        exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (abs_pos.mpr hne))
    have hI_inc : ∀ q < s - 1, I_even q < I_even (q + 1) := by
      intro q hq
      dsimp [I_even]
      have hshift :
          ∫ x in (4 * ((q + 1 : ℕ) : ℝ) + 1)..(4 * ((q + 1 : ℕ) : ℝ) + 3),
              x * Real.sqrt |P_even_real r x| =
            ∫ x in (4 * (q : ℝ) + 1)..(4 * (q : ℝ) + 3),
              (x + 4) * Real.sqrt |P_even_real r (x + 4)| := by
        have hcomp := intervalIntegral.integral_comp_add_right
          (f := fun y : ℝ => y * Real.sqrt |P_even_real r y|) (a := 4 * (q : ℝ) + 1)
          (b := 4 * (q : ℝ) + 3) 4
        rw [hcomp]
        have ha : 4 * ((q + 1 : ℕ) : ℝ) + 1 = 4 * (q : ℝ) + 1 + 4 := by push_cast; ring
        have hb : 4 * ((q + 1 : ℕ) : ℝ) + 3 = 4 * (q : ℝ) + 3 + 4 := by push_cast; ring
        rw [ha, hb]
      rw [hshift]
      have h12 : (4 * (q : ℝ) + 1) < (4 * (q : ℝ) + 3) := by linarith
      have hcL : ContinuousOn (fun x : ℝ => x * Real.sqrt |P_even_real r x|)
          (Set.Icc (4 * (q : ℝ) + 1) (4 * (q : ℝ) + 3)) :=
        (continuous_id.mul hsc).continuousOn
      have hcR : ContinuousOn (fun x : ℝ => (x + 4) * Real.sqrt |P_even_real r (x + 4)|)
          (Set.Icc (4 * (q : ℝ) + 1) (4 * (q : ℝ) + 3)) :=
        ((continuous_id.add continuous_const).mul
          (hsc.comp (continuous_id.add continuous_const))).continuousOn
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h12 hcL hcR ?_ ?_
      · intro x hx
        rw [Set.mem_Ioc] at hx
        have hq_le : 4 * (q : ℝ) + 3 ≤ 2 * (r : ℝ) - 3 := by
          have : q + 2 ≤ s := by omega
          have h1 : (4 * ((q + 2 : ℕ) : ℝ) : ℝ) ≤ 4 * (s : ℝ) := by exact_mod_cast (by omega : 4 * (q + 2) ≤ 4 * s)
          rw [hr_eq]
          push_cast at h1 ⊢
          linarith
        have hP : Real.sqrt |P_even_real r x| ≤ Real.sqrt |P_even_real r (x + 4)| :=
          Real.sqrt_le_sqrt (P_even_real_abs_le_shift4 (by omega) (by linarith [hx.1]) (by linarith [hx.2]))
        exact mul_le_mul (by linarith) hP (Real.sqrt_nonneg _) (by linarith [hx.1])
      · refine ⟨4 * (q : ℝ) + 2, ⟨by linarith, by linarith⟩, ?_⟩
        have hne : P_even_real r (4 * (q : ℝ) + 2) ≠ 0 := by
          have h := P_even_real_ne_zero_even_nat r (2 * q + 1)
          rwa [show ((2 * (2 * q + 1) : ℕ) : ℝ) = 4 * (q : ℝ) + 2 by push_cast; ring] at h
        have hq_lt : 4 * (q : ℝ) + 2 < 2 * (r : ℝ) - 3 := by
          have : q + 2 ≤ s := by omega
          have h1 : (4 * ((q + 2 : ℕ) : ℝ) : ℝ) ≤ 4 * (s : ℝ) := by exact_mod_cast (by omega : 4 * (q + 2) ≤ 4 * s)
          rw [hr_eq]
          push_cast at h1 ⊢
          linarith
        have hP : Real.sqrt |P_even_real r (4 * (q : ℝ) + 2)| <
            Real.sqrt |P_even_real r ((4 * (q : ℝ) + 2) + 4)| :=
          Real.sqrt_lt_sqrt (abs_nonneg _)
            (P_even_real_abs_lt_shift4 (by omega) (by linarith) hq_lt hne)
        exact mul_lt_mul' (by linarith) hP (Real.sqrt_nonneg _) (by linarith)
    rw [hsplit0, h01, zero_add, hadj, hsum_filt, hsum_I]
    have hpos := alt_sum_pos I_even (s - 1) hI0_pos hI_inc
    rwa [show (s - 1) + 1 = s by omega] at hpos
  · obtain ⟨s, hs⟩ := Nat.not_even_iff_odd.mp he
    rcases s with _ | s
    · have hr1 : r = 1 := by omega
      subst hr1
      norm_num
      have hcongr : ∫ x in (0 : ℝ)..1, g_int 1 x =
          ∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real 1 x| := by
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [Set.uIcc_of_le zero_le_one] at hx
        have hlo : rootPt 1 0 ≤ x := by dsimp [rootPt]; norm_num; linarith [hx.1]
        have hhi : x ≤ rootPt 1 1 := by dsimp [rootPt]; norm_num; linarith [hx.2]
        rw [g_int_on_subinterval (by decide : 0 + 1 < 2 * 1) hlo hhi, if_neg he]
        norm_num
      rw [hcongr]
      refine intervalIntegral.integral_pos zero_lt_one (hsc.continuousOn)
        (fun _ _ => Real.sqrt_nonneg _) ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      exact Real.sqrt_pos.mpr (abs_pos.mpr (by simpa using P_even_real_ne_zero_even_nat 1 0))
    · set s1 := s + 1
      have hr_eq : r = 2 * s1 + 1 := by omega
      have hsplit0 : ∫ x in (0 : ℝ)..(2 * (r : ℝ) - 1), g_int r x =
          (∫ x in (0 : ℝ)..1, g_int r x) + ∫ x in (1 : ℝ)..(2 * (r : ℝ) - 1), g_int r x :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hgc.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
          (hgc.intervalIntegrable (μ := MeasureTheory.volume) 1 (2 * (r : ℝ) - 1))).symm
      set J : ℕ → ℝ := fun k =>
        if k = 0 then ∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real r x|
        else ∫ x in (4 * ((k - 1 : ℕ) : ℝ) + 3)..(4 * ((k - 1 : ℕ) : ℝ) + 5),
          Real.sqrt |P_even_real r x|
      have h01 : ∫ x in (0 : ℝ)..1, g_int r x = (-1 : ℝ) ^ s1 * J 0 := by
        have hJ0 : J 0 = ∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real r x| := by simp [J]
        rw [hJ0, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [Set.uIcc_of_le zero_le_one] at hx
        have hlo : rootPt r (r - 1) ≤ x := by
          dsimp [rootPt]; rw [Nat.cast_sub (by omega : 1 ≤ r)]; push_cast; linarith [hx.1]
        have hhi : x ≤ rootPt r ((r - 1) + 1) := by
          dsimp [rootPt]; rw [Nat.sub_add_cancel hr]; linarith [hx.2]
        rw [g_int_on_subinterval (by omega : (r - 1) + 1 < 2 * r) hlo hhi, if_neg he,
          show 2 * r - 1 - (r - 1) = 2 * s1 + 1 by omega, I_pow_odd_im]
        ring
      have hM_eq : (1 : ℝ) + 2 * ((2 * s1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
        rw [hr_eq]; push_cast; ring
      have hadj : ∫ x in (1 : ℝ)..(2 * (r : ℝ) - 1), g_int r x =
          ∑ j ∈ Finset.range (2 * s1),
            ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x := by
        have hs_int := intervalIntegral.sum_integral_adjacent_intervals
          (f := g_int r) (a := fun j : ℕ => (1 : ℝ) + 2 * (j : ℝ)) (n := 2 * s1)
          (fun j _ => hgc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
        rw [Nat.cast_zero, mul_zero, add_zero, hM_eq] at hs_int
        exact hs_int.symm
      have heven0 : ∀ j : ℕ, Even j →
          (if j < 2 * s1 then
            ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x else 0) = 0 := by
        intro j hj
        split_ifs with hlt
        · obtain ⟨q, rfl⟩ := hj
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => by
            have hle : 1 + 2 * ((q + q : ℕ) : ℝ) ≤ 1 + 2 * ((q + q + 1 : ℕ) : ℝ) := by
              push_cast; linarith
            rw [Set.uIcc_of_le hle] at hx
            push_cast at hx
            have hlo : rootPt r (r + (q + q)) ≤ x := by
              dsimp [rootPt]; push_cast; linarith [hx.1]
            have hhi : x ≤ rootPt r (r + (q + q) + 1) := by
              dsimp [rootPt]; push_cast; linarith [hx.2]
            rw [g_int_on_subinterval (by omega : (r + (q + q)) + 1 < 2 * r) hlo hhi, if_neg he,
              show 2 * r - 1 - (r + (q + q)) = 2 * (s1 - q) by omega, I_pow_even_im]
            simp, intervalIntegral.integral_zero]
        · rfl
      have hsum_filt :
          ∑ j ∈ Finset.range (2 * s1),
              ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x =
            ∑ q ∈ Finset.range s1,
              (if 2 * q + 1 < 2 * s1 then
                ∫ x in (1 + 2 * ((2 * q + 1 : ℕ) : ℝ))..(1 + 2 * ((2 * q + 2 : ℕ) : ℝ)),
                  g_int r x
              else 0) := by
        have hite : ∑ j ∈ Finset.range (2 * s1),
              ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x =
            ∑ j ∈ Finset.range (2 * s1),
              (if j < 2 * s1 then
                ∫ x in (1 + 2 * (j : ℝ))..(1 + 2 * ((j + 1 : ℕ) : ℝ)), g_int r x else 0) := by
          refine Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]
        rw [hite]
        exact sum_range_two_mul_odd_only _ heven0 s1
      have hsum_J :
          ∑ q ∈ Finset.range s1,
              (if 2 * q + 1 < 2 * s1 then
                ∫ x in (1 + 2 * ((2 * q + 1 : ℕ) : ℝ))..(1 + 2 * ((2 * q + 2 : ℕ) : ℝ)),
                  g_int r x
              else 0) =
            ∑ q ∈ Finset.range s1, (-1 : ℝ) ^ (s1 - (q + 1)) * J (q + 1) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [Finset.mem_range] at hq
        rw [if_pos (by omega : 2 * q + 1 < 2 * s1)]
        have ha_eq : 1 + 2 * ((2 * q + 1 : ℕ) : ℝ) = 4 * (q : ℝ) + 3 := by push_cast; ring
        have hb_eq : 1 + 2 * ((2 * q + 2 : ℕ) : ℝ) = 4 * (q : ℝ) + 5 := by push_cast; ring
        have hJq : J (q + 1) =
            ∫ x in (4 * (q : ℝ) + 3)..(4 * (q : ℝ) + 5), Real.sqrt |P_even_real r x| := by
          simp [J]
        rw [ha_eq, hb_eq, hJq, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr fun x hx => ?_
        rw [Set.uIcc_of_le (by linarith)] at hx
        have hlo : rootPt r (r + (2 * q + 1)) ≤ x := by
          dsimp [rootPt]; rw [hr_eq]; push_cast; linarith [hx.1]
        have hhi : x ≤ rootPt r (r + (2 * q + 1) + 1) := by
          dsimp [rootPt]; rw [hr_eq]; push_cast; linarith [hx.2]
        rw [g_int_on_subinterval (by omega : (r + (2 * q + 1)) + 1 < 2 * r) hlo hhi, if_neg he,
          show 2 * r - 1 - (r + (2 * q + 1)) = 2 * (s1 - (q + 1)) + 1 by omega, I_pow_odd_im]
        ring
      have hJ0_pos : 0 < J 0 := by
        simp only [J, ↓reduceIte]
        refine intervalIntegral.integral_pos zero_lt_one hsc.continuousOn
          (fun _ _ => Real.sqrt_nonneg _) ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
        exact Real.sqrt_pos.mpr (abs_pos.mpr (by simpa using P_even_real_ne_zero_even_nat r 0))
      have hJ_inc : ∀ k < s1, J k < J (k + 1) := by
        intro k hk
        rcases k with _ | k
        · have hs1_ge : (1 : ℝ) ≤ (s1 : ℝ) := by exact_mod_cast hk
          have hJ0_eq : J 0 = ∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real r x| := by
            simp only [J, ↓reduceIte]
          have hJ1_eq : J (0 + 1) = ∫ y in (3 : ℝ)..5, Real.sqrt |P_even_real r y| := by
            simp [J]
          rw [hJ0_eq, hJ1_eq]
          have hlt4 : (∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real r x|) <
              ∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real r (x + 4)| := by
            refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
              zero_lt_one hsc.continuousOn
              (hsc.comp (continuous_id.add continuous_const)).continuousOn ?_ ?_
            · intro x hx
              rw [Set.mem_Ioc] at hx
              exact Real.sqrt_le_sqrt
                (P_even_real_abs_le_shift4 (by omega) hx.1.le
                  (by rw [hr_eq]; push_cast; linarith [hx.2, hs1_ge]))
            · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
              exact Real.sqrt_lt_sqrt (abs_nonneg _)
                (P_even_real_abs_lt_shift4 (by omega) (by norm_num)
                  (by rw [hr_eq]; push_cast; linarith [hs1_ge]) (P_even_real_ne_zero_half r))
          have hcomp : ∫ x in (0 : ℝ)..1, Real.sqrt |P_even_real r (x + 4)| =
              ∫ y in (4 : ℝ)..5, Real.sqrt |P_even_real r y| := by
            have h := intervalIntegral.integral_comp_add_right
              (f := fun y : ℝ => Real.sqrt |P_even_real r y|) (a := (0 : ℝ)) (b := 1) 4
            norm_num at h
            exact h
          have hmono : ∫ y in (4 : ℝ)..5, Real.sqrt |P_even_real r y| ≤
              ∫ y in (3 : ℝ)..5, Real.sqrt |P_even_real r y| :=
            intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) le_rfl
              (MeasureTheory.ae_of_all _ fun _ => Real.sqrt_nonneg _)
              (hsc.intervalIntegrable (μ := MeasureTheory.volume) 3 5)
          linarith
        · have hk1 : J (k + 1) =
              ∫ x in (4 * (k : ℝ) + 3)..(4 * (k : ℝ) + 5), Real.sqrt |P_even_real r x| := by
            simp [J]
          have hk2 : J (k + 2) =
              ∫ x in (4 * ((k + 1 : ℕ) : ℝ) + 3)..(4 * ((k + 1 : ℕ) : ℝ) + 5),
                Real.sqrt |P_even_real r x| := by
            simp [J]
          rw [hk1, hk2]
          have hcomp :
              ∫ x in (4 * ((k + 1 : ℕ) : ℝ) + 3)..(4 * ((k + 1 : ℕ) : ℝ) + 5),
                  Real.sqrt |P_even_real r x| =
                ∫ x in (4 * (k : ℝ) + 3)..(4 * (k : ℝ) + 5),
                  Real.sqrt |P_even_real r (x + 4)| := by
            rw [intervalIntegral.integral_comp_add_right
              (f := fun y : ℝ => Real.sqrt |P_even_real r y|) (a := 4 * (k : ℝ) + 3)
              (b := 4 * (k : ℝ) + 5) 4]
            rw [show 4 * ((k + 1 : ℕ) : ℝ) + 3 = 4 * (k : ℝ) + 3 + 4 by push_cast; ring,
              show 4 * ((k + 1 : ℕ) : ℝ) + 5 = 4 * (k : ℝ) + 5 + 4 by push_cast; ring]
          rw [hcomp]
          refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
            (by linarith) hsc.continuousOn
            (hsc.comp (continuous_id.add continuous_const)).continuousOn ?_ ?_
          · intro x hx
            rw [Set.mem_Ioc] at hx
            have hk_le : 4 * (k : ℝ) + 5 ≤ 2 * (r : ℝ) - 3 := by
              have h1 : (4 * (k + 2 : ℕ) : ℝ) ≤ 4 * (s1 : ℝ) := by exact_mod_cast (by omega : 4 * (k + 2) ≤ 4 * s1)
              rw [hr_eq]; push_cast at h1 ⊢; linarith
            exact Real.sqrt_le_sqrt
              (P_even_real_abs_le_shift4 (by omega) (by linarith [hx.1]) (by linarith [hx.2]))
          · refine ⟨4 * (k : ℝ) + 4, ⟨by linarith, by linarith⟩, ?_⟩
            have hne : P_even_real r (4 * (k : ℝ) + 4) ≠ 0 := by
              have h := P_even_real_ne_zero_even_nat r (2 * k + 2)
              rwa [show ((2 * (2 * k + 2) : ℕ) : ℝ) = 4 * (k : ℝ) + 4 by push_cast; ring] at h
            have hk_lt : 4 * (k : ℝ) + 4 < 2 * (r : ℝ) - 3 := by
              have h1 : (4 * (k + 2 : ℕ) : ℝ) ≤ 4 * (s1 : ℝ) := by exact_mod_cast (by omega : 4 * (k + 2) ≤ 4 * s1)
              rw [hr_eq]; push_cast at h1 ⊢; linarith
            exact Real.sqrt_lt_sqrt (abs_nonneg _)
              (P_even_real_abs_lt_shift4 (by omega) (by linarith) hk_lt hne)
      rw [hsplit0, h01, hadj, hsum_filt, hsum_J]
      have hcomb :
          (-1 : ℝ) ^ s1 * J 0 + ∑ q ∈ Finset.range s1, (-1 : ℝ) ^ (s1 - (q + 1)) * J (q + 1) =
            ∑ k ∈ Finset.range (s1 + 1), (-1 : ℝ) ^ (s1 - k) * J k := by
        rw [Finset.sum_range_succ' (fun k => (-1 : ℝ) ^ (s1 - k) * J k) s1, Nat.sub_zero]
        ring
      rw [hcomb]
      exact alt_sum_pos J s1 hJ0_pos hJ_inc

/-- **Main Theorem (Real Coefficient Version):** For every integer `r ≥ 1` (`k = 2 * r`),
the remainder polynomial `R_r = P_{2r} - Q^2` has strictly negative coefficient at `degR r = 2 * ((r - 1) / 2)`. -/
theorem even_k_remainder_coeff_neg_real {r : ℕ} (hr : 1 ≤ r) {Q : Polynomial ℝ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = r)
    (hQ_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q ^ 2).coeff k = 0) :
    (P_even_poly_real r - Q ^ 2).coeff (degR r) < 0 := by
  have hid := contour_identity_im hr hQ_monic hQ_deg hQ_zero
  change _ = ∫ x in (-(2 * (r : ℝ) - 1))..(2 * (r : ℝ) - 1), g_int r x at hid
  rw [integral_g_int_symm hr] at hid
  have hpos := integral_g_int_pos hr
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith

theorem even_k_remainder_natDegree_eq_real {r : ℕ} (hr : 1 ≤ r) {Q : Polynomial ℝ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = r)
    (hQ_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q ^ 2).coeff k = 0) :
    (P_even_poly_real r - Q ^ 2).natDegree = degR r := by
  have hneg := even_k_remainder_coeff_neg_real hr hQ_monic hQ_deg hQ_zero
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hneg.ne)
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hQ_zero

theorem even_k_remainder_leadingCoeff_neg_real {r : ℕ} (hr : 1 ≤ r) {Q : Polynomial ℝ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = r)
    (hQ_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q ^ 2).coeff k = 0) :
    (P_even_poly_real r - Q ^ 2).leadingCoeff < 0 := by
  rw [Polynomial.leadingCoeff, even_k_remainder_natDegree_eq_real hr hQ_monic hQ_deg hQ_zero]
  exact even_k_remainder_coeff_neg_real hr hQ_monic hQ_deg hQ_zero

/-- **Main Theorem (Rational Spec Version):** For every integer `r ≥ 1` and any monic `Q : Polynomial ℚ`
of degree `r` annihilating `(P_{2r} - Q^2).coeff k` for all `k > degR r`,
`(P_{2r} - Q^2).natDegree = degR r` and `(P_{2r} - Q^2).leadingCoeff < 0`. -/
theorem even_k_remainder_leadingCoeff_neg_rat_of_spec {r : ℕ} (hr : 1 ≤ r) {Q : Polynomial ℚ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = r)
    (hQ_zero : ∀ k : ℕ, degR r < k → (P_even_poly r - Q ^ 2).coeff k = 0) :
    (P_even_poly r - Q ^ 2).natDegree = degR r ∧ (P_even_poly r - Q ^ 2).leadingCoeff < 0 := by
  set Q_R : Polynomial ℝ := Q.map (algebraMap ℚ ℝ)
  have hQ_R_monic : Q_R.Monic := hQ_monic.map _
  have hQ_R_deg : Q_R.natDegree = r := by
    rw [← hQ_deg]
    exact Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective Q
  have hmap : P_even_poly_real r - Q_R ^ 2 =
      (P_even_poly r - Q ^ 2).map (algebraMap ℚ ℝ) := by
    simp [P_even_poly_real, Q_R, Polynomial.map_sub, Polynomial.map_pow]
  have hQ_R_zero : ∀ k : ℕ, degR r < k → (P_even_poly_real r - Q_R ^ 2).coeff k = 0 := by
    intro k hk
    rw [hmap, Polynomial.coeff_map, hQ_zero k hk, map_zero]
  have hneg_R := even_k_remainder_coeff_neg_real hr hQ_R_monic hQ_R_deg hQ_R_zero
  rw [hmap, Polynomial.coeff_map] at hneg_R
  have hneg_Q : (P_even_poly r - Q ^ 2).coeff (degR r) < 0 := by
    have : (((P_even_poly r - Q ^ 2).coeff (degR r) : ℚ) : ℝ) < (0 : ℝ) := by
      simpa using hneg_R
    exact_mod_cast this
  have hdeg : (P_even_poly r - Q ^ 2).natDegree = degR r := by
    refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hneg_Q.ne)
    exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hQ_zero
  refine ⟨hdeg, ?_⟩
  rwa [Polynomial.leadingCoeff, hdeg]

theorem even_k_remainder_natDegree_eq_rat {r : ℕ} (hr : 1 ≤ r) :
    (P_even_poly r - (Q_even_poly r) ^ 2).natDegree = degR r :=
  (even_k_remainder_leadingCoeff_neg_rat_of_spec hr (Q_even_poly_monic r)
    (Q_even_poly_natDegree r) (P_sub_Q_sq_coeff_zero_of_gt hr)).1

/-- **Main Theorem (Canonical Explicit `Q_even_poly r` Over `ℚ`):** For every integer `r ≥ 1`,
`lc(P_{2r} - Q_r^2) < 0` in `ℚ`. -/
theorem even_k_remainder_leadingCoeff_neg_rat {r : ℕ} (hr : 1 ≤ r) :
    (P_even_poly r - (Q_even_poly r) ^ 2).leadingCoeff < 0 :=
  (even_k_remainder_leadingCoeff_neg_rat_of_spec hr (Q_even_poly_monic r)
    (Q_even_poly_natDegree r) (P_sub_Q_sq_coeff_zero_of_gt hr)).2

end Contribution.Erdos686EvenKLeadingNegTwentyFive
