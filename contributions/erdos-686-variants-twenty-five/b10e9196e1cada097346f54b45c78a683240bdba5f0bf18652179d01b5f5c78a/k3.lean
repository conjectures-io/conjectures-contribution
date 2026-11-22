import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Zify

/-!
# Erdős 686: unconditional length-3 exclusion for ratio 25

This is a fixed-length (`k = 3`) partial result, not the full unrestricted conjecture.
It gives a self-contained, 100% kernel-verified proof (no `sorry`, no `native_decide`,
only standard axioms `[propext, Classical.choice, Quot.sound]`) that no integers `m, n : ℕ`
satisfy `(m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3))`
or the equivalent rational-quotient equation for `Erdos686.erdos_686.variants.twenty_five`.

## Proof Architecture
1. `Reduction`: Thue–Mordell descent to `25 * y1^3 - x1^3 = d` (`d ∣ 15600`), local mod-`27`
   admissibility filter (`60 → 24` divisors), `decide +kernel` exclusion of `y1 ≤ 2000`, and an
   8-step pure-integer continued-fraction convergent chain covering `2001 ≤ y1 ≤ 10^73`.
2. Extra continued-fraction convergents `excl_conv_275` (`10^73 ≤ y1 ≤ 10^140`) and
   `excl_conv_511` (`10^140 ≤ y1 ≤ 10^276`) extend the convergent bound up to `y1 ≤ 10^276`.
3. `Pade`: First-principles Padé / hypergeometric approximants to `(1 - z)^(1/3)` evaluated at
   the 21st convergent `(a21, b21) = (700728535, 239645788)` of `25^(1/3)` (creative
   telescoping, non-vanishing Wronskian, Euler integral remainder, and elementary 3-adic clearing)
   unconditionally rule out all remaining solutions `y1 > 10^276`.
4. Top-level theorems in `Contribution.Erdos686ThreeTwentyFive`:
   `no_sol_twenty_five_three`, `no_sol_twenty_five_three_unrestricted`,
   `no_sol_twenty_five_three_Icc`, `no_ratio_twenty_five_three`, and
   `erdos_686_variants_twenty_five_k3_bridge`.
-/

namespace Contribution.Erdos686ThreeTwentyFive

namespace Reduction

/-! ## 1. Centered Cubic Reduction, Weierstrass Birational Map, and `ℤ[∛5]` Norm -/

/-- Natural/integer equivalence between the `k = 3` product equation and the centered cubic
`x^3 - x = 25 * (y^3 - y)` at `x = m + 2`, `y = n + 2`. -/
theorem k3_iff_cubic (m n : ℕ) :
    (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) ↔
      ((m : ℤ) + 2) ^ 3 - ((m : ℤ) + 2) = 25 * (((n : ℤ) + 2) ^ 3 - ((n : ℤ) + 2)) := by
  have hid (t : ℤ) : (t + 1) * (t + 2) * (t + 3) = (t + 2) ^ 3 - (t + 2) := by ring
  constructor
  · intro h
    have hz : ((m : ℤ) + 1) * ((m : ℤ) + 2) * ((m : ℤ) + 3) =
        25 * (((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3)) := by
      exact_mod_cast h
    rw [← hid (m : ℤ), ← hid (n : ℤ)]
    exact hz
  · intro h
    rw [← hid (m : ℤ), ← hid (n : ℤ)] at h
    exact_mod_cast h

/-- Rational equivalence `(x - 1)*x*(x + 1) = 25*(y - 1)*y*(y + 1) ↔ x^3 - x = 25*(y^3 - y)`. -/
theorem k3_rat_iff_cubic (x y : ℚ) :
    (x - 1) * x * (x + 1) = 25 * ((y - 1) * y * (y + 1)) ↔ x ^ 3 - x = 25 * (y ^ 3 - y) := by
  have h1 : (x - 1) * x * (x + 1) = x ^ 3 - x := by ring
  have h2 : (y - 1) * y * (y + 1) = y ^ 3 - y := by ring
  rw [h1, h2]

/-- The inflection line `x = 25 * y` intersects `C : x^3 - x = 25 * (y^3 - y)` over `ℚ`
only at `(0, 0)`. -/
theorem flex_line_trivial {x y : ℚ} (hc : x ^ 3 - x = 25 * (y ^ 3 - y)) (hflex : x = 25 * y) :
    y = 0 ∧ x = 0 := by
  subst hflex
  have h3 : 15600 * y ^ 3 = 0 := by linarith
  have hy3 : y ^ 3 = 0 := by linarith
  have hy : y = 0 := by
    by_contra h
    exact pow_ne_zero 3 h hy3
  subst hy
  exact ⟨rfl, by norm_num⟩

/-- **Exact Birational Equivalence (`C \ {x = 25y} ↔ E \ {Y = 0}`)** over `ℚ` between
`x^3 - x = 25*(y^3 - y)` and `Y^2 = X^3 - 1875*X + 391250`. -/
theorem weierstrass_birational :
    (∀ x y : ℚ, x ^ 3 - x = 25 * (y ^ 3 - y) → x ≠ 25 * y →
      let X := (625 * x - 25 * y) / (x - 25 * y)
      let Y := 15600 / (x - 25 * y)
      Y ≠ 0 ∧ Y ^ 2 = X ^ 3 - 1875 * X + 391250 ∧
        25 * (X - 1) / Y = x ∧ (X - 625) / Y = y) ∧
    (∀ X Y : ℚ, Y ≠ 0 → Y ^ 2 = X ^ 3 - 1875 * X + 391250 →
      let x := 25 * (X - 1) / Y
      let y := (X - 625) / Y
      x ^ 3 - x = 25 * (y ^ 3 - y) ∧ x ≠ 25 * y ∧
        (625 * x - 25 * y) / (x - 25 * y) = X ∧ 15600 / (x - 25 * y) = Y) := by
  constructor
  · intro x y hc hne
    have hden : x - 25 * y ≠ 0 := sub_ne_zero.mpr hne
    dsimp
    refine ⟨div_ne_zero (by norm_num) hden, ?_, ?_, ?_⟩
    · field_simp [hden]
      linear_combination -243360000 * hc
    · field_simp [hden]
      ring
    · field_simp [hden]
      ring
  · intro X Y hY hE
    dsimp
    have hx_sub : 25 * (X - 1) / Y - 25 * ((X - 625) / Y) = 15600 / Y := by
      field_simp [hY]
      ring
    have hne : 25 * (X - 1) / Y ≠ 25 * ((X - 625) / Y) := by
      intro h
      have : (15600 : ℚ) / Y = 0 := by rw [← hx_sub, h, sub_self]
      have : (15600 : ℚ) / Y ≠ 0 := div_ne_zero (by norm_num) hY
      exact this ‹_›
    refine ⟨?_, hne, ?_, ?_⟩
    · field_simp [hY]
      linear_combination -624 * hE
    · rw [hx_sub]
      field_simp [hY]
      ring
    · rw [hx_sub]
      field_simp [hY]

/-- **`ℤ[∛5]` Field-Norm Matrix Identity**: `25 * y1^3 - x1^3` equals the determinant of the
multiplication-by-`(y1 * ∛25 - x1)` endomorphism in the power basis `{1, ∛5, ∛25}`. -/
theorem cbrt5_norm_identity (x1 y1 : ℤ) :
    25 * y1 ^ 3 - x1 ^ 3 =
      Matrix.det !![(-x1), 5 * y1, 0;
                     0,   (-x1), 5 * y1;
                     y1,   0,   (-x1)] := by
  simp [Matrix.det_fin_three]
  ring

/-! ## 2. Thue–Mordell Descent and Divisor Reduction (`d ∣ 15600`) -/

private lemma cube_sub_mono {a b : ℤ} (ha : 1 ≤ a) (hab : a < b) :
    a ^ 3 - a < b ^ 3 - b := by
  have hdiff : b ^ 3 - b - (a ^ 3 - a) = (b - a) * (b ^ 2 + b * a + a ^ 2 - 1) := by ring
  have hpos : 0 < b ^ 2 + b * a + a ^ 2 - 1 := by nlinarith
  have hmul : 0 < (b - a) * (b ^ 2 + b * a + a ^ 2 - 1) := mul_pos (sub_pos.mpr hab) hpos
  linarith

/-- **Unconditional `k = 3` Thue–Mordell Reduction Theorem**. -/
theorem k3_thue_reduction {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3))) :
    let x := m + 2
    let y := n + 2
    let D := Nat.gcd x y
    let x1 := x / D
    let y1 := y / D
    let d : ℤ := 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3
    1 ≤ D ∧ x = D * x1 ∧ y = D * y1 ∧ Nat.Coprime x1 y1 ∧
    y1 < x1 ∧ x1 < 3 * y1 ∧
    0 < d ∧ 25 * (y1 : ℤ) - (x1 : ℤ) = d * (D : ℤ) ^ 2 ∧
    22 * (y1 : ℤ) < d * (D : ℤ) ^ 2 ∧ d * (D : ℤ) ^ 2 < 24 * (y1 : ℤ) ∧
    d.natAbs ∈ (15600 : ℕ).divisors ∧
    (-((15600 / d.natAbs : ℕ) : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2
      - 75 * d * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 2 * (D : ℤ) ^ 6 = 1) ∧
    Nat.Coprime y1 d.natAbs ∧ Nat.Coprime D (15600 / d.natAbs) ∧ Nat.Coprime D y1 := by
  intro x y D x1 y1 d
  have hy_ge2 : 2 ≤ y := by dsimp [y]; omega
  have hx_gt_y : y < x := by dsimp [x, y]; omega
  have hD_pos : 0 < D := Nat.gcd_pos_of_pos_right x (by omega : 0 < y)
  have hD_ge1 : 1 ≤ D := hD_pos
  have hDx : D * x1 = x := Nat.mul_div_cancel' (Nat.gcd_dvd_left x y)
  have hDy : D * y1 = y := Nat.mul_div_cancel' (Nat.gcd_dvd_right x y)
  have hcop : Nat.Coprime x1 y1 := Nat.coprime_div_gcd_div_gcd hD_pos
  have hy1_pos : 0 < y1 := by
    by_contra hy0
    have : y1 = 0 := Nat.le_zero.mp (Nat.not_lt.mp hy0)
    rw [this, mul_zero] at hDy
    omega
  have hy1_lt_x1 : y1 < x1 :=
    (Nat.mul_lt_mul_left hD_pos).mp (by rw [hDx, hDy]; exact hx_gt_y)
  have hcub : (x : ℤ) ^ 3 - (x : ℤ) = 25 * ((y : ℤ) ^ 3 - (y : ℤ)) :=
    (k3_iff_cubic m n).mp heq
  have hx_lt_3y : x < 3 * y := by
    by_contra hx3
    have hx_ge : 3 * (y : ℤ) ≤ (x : ℤ) := by exact_mod_cast (by omega : 3 * y ≤ x)
    have h1 : (25 : ℤ) * ((y : ℤ) ^ 3 - (y : ℤ)) < (3 * (y : ℤ)) ^ 3 - 3 * (y : ℤ) := by
      have hyz : (2 : ℤ) ≤ y := by exact_mod_cast hy_ge2
      have hdiff : (3 * (y : ℤ)) ^ 3 - 3 * (y : ℤ) - 25 * ((y : ℤ) ^ 3 - (y : ℤ)) =
          2 * (y : ℤ) ^ 3 + 22 * (y : ℤ) := by ring
      have hpos : 0 < 2 * (y : ℤ) ^ 3 + 22 * (y : ℤ) := by positivity
      linarith
    have h2 : (3 * (y : ℤ)) ^ 3 - 3 * (y : ℤ) ≤ (x : ℤ) ^ 3 - (x : ℤ) := by
      rcases eq_or_lt_of_le hx_ge with h_eq | h_lt
      · rw [← h_eq]
      · have hy3 : (1 : ℤ) ≤ 3 * (y : ℤ) := by omega
        exact le_of_lt (cube_sub_mono hy3 h_lt)
    linarith
  have hx1_lt_3y1 : x1 < 3 * y1 := by
    have hmul : D * x1 < D * (3 * y1) := by
      calc
        D * x1 = x := hDx
        _ < 3 * y := hx_lt_3y
        _ = 3 * (D * y1) := by rw [hDy]
        _ = D * (3 * y1) := by ring
    exact (Nat.mul_lt_mul_left hD_pos).mp hmul
  have hrel : 25 * (y1 : ℤ) - (x1 : ℤ) = d * (D : ℤ) ^ 2 := by
    have hxz : (x : ℤ) = (D : ℤ) * (x1 : ℤ) := by exact_mod_cast hDx.symm
    have hyz : (y : ℤ) = (D : ℤ) * (y1 : ℤ) := by exact_mod_cast hDy.symm
    rw [hxz, hyz] at hcub
    have hDz : (D : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfac : (D : ℤ) * (25 * (y1 : ℤ) - (x1 : ℤ) - d * (D : ℤ) ^ 2) = 0 := by
      dsimp [d]
      linarith
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact absurd h0 hDz
    · linarith
  have h22 : 22 * (y1 : ℤ) < d * (D : ℤ) ^ 2 := by
    have h3z : (x1 : ℤ) + 1 ≤ 3 * (y1 : ℤ) := by exact_mod_cast hx1_lt_3y1
    linarith
  have h24 : d * (D : ℤ) ^ 2 < 24 * (y1 : ℤ) := by
    have h1z : (y1 : ℤ) + 1 ≤ (x1 : ℤ) := by exact_mod_cast hy1_lt_x1
    linarith
  have hd_pos : 0 < d := by
    have hy1z : (1 : ℤ) ≤ y1 := by exact_mod_cast hy1_pos
    have hDz2 : 0 < (D : ℤ) ^ 2 := by positivity
    nlinarith
  have hd_dvd_y1 : d ∣ 15600 * (y1 : ℤ) ^ 3 := by
    refine ⟨(625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) * (D : ℤ) ^ 2 - 1, ?_⟩
    have hrel' := hrel
    dsimp [d] at hrel' ⊢
    calc
      15600 * (y1 : ℤ) ^ 3
          = (625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) *
              (25 * (y1 : ℤ) - (x1 : ℤ)) - (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) := by ring
      _ = (625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) *
              ((25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) * (D : ℤ) ^ 2) -
              (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) := by rw [hrel']
      _ = (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) *
              ((625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) * (D : ℤ) ^ 2 - 1) := by
          ring
  have hd_dvd_x1 : d ∣ 15600 * (x1 : ℤ) ^ 3 := by
    refine ⟨25 * (625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) * (D : ℤ) ^ 2 -
        15625, ?_⟩
    have hrel' := hrel
    dsimp [d] at hrel' ⊢
    calc
      15600 * (x1 : ℤ) ^ 3
          = 25 * (625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) *
              (25 * (y1 : ℤ) - (x1 : ℤ)) - 15625 * (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) := by ring
      _ = 25 * (625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) *
              ((25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) * (D : ℤ) ^ 2) -
              15625 * (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) := by rw [hrel']
      _ = (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) *
              (25 * (625 * (y1 : ℤ) ^ 2 + 25 * (x1 : ℤ) * (y1 : ℤ) + (x1 : ℤ) ^ 2) * (D : ℤ) ^ 2 -
                15625) := by ring
  have hd_dvd_15600 : d.natAbs ∣ 15600 := by
    have h1 : d.natAbs ∣ 15600 * x1 ^ 3 := by
      have hz := Int.natAbs_dvd_natAbs.mpr hd_dvd_x1
      simpa [Int.natAbs_mul, Int.natAbs_pow] using hz
    have h2 : d.natAbs ∣ 15600 * y1 ^ 3 := by
      have hz := Int.natAbs_dvd_natAbs.mpr hd_dvd_y1
      simpa [Int.natAbs_mul, Int.natAbs_pow] using hz
    have hg : d.natAbs ∣ Nat.gcd (15600 * x1 ^ 3) (15600 * y1 ^ 3) := Nat.dvd_gcd h1 h2
    rw [Nat.gcd_mul_left, (hcop.pow 3 3).gcd_eq_one, mul_one] at hg
    exact hg
  have hd_mem : d.natAbs ∈ (15600 : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨hd_dvd_15600, by norm_num⟩
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos)
  set B0 : ℕ := 15600 / d.natAbs
  have hB0_mul : d * (B0 : ℤ) = 15600 := by
    have hnat : d.natAbs * B0 = 15600 := Nat.mul_div_cancel' hd_dvd_15600
    have hz : (d.natAbs : ℤ) * (B0 : ℤ) = 15600 := by exact_mod_cast hnat
    rwa [hdz_eq] at hz
  have hnorm : -(B0 : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
      75 * d * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 2 * (D : ℤ) ^ 6 = 1 := by
    have hx1z : (x1 : ℤ) = 25 * (y1 : ℤ) - d * (D : ℤ) ^ 2 := by linarith
    have hmul : d * (-(B0 : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
        75 * d * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 2 * (D : ℤ) ^ 6) = d * 1 := by
      have hsub : 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 = d := rfl
      rw [hx1z] at hsub
      calc
        d * (-(B0 : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
            75 * d * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 2 * (D : ℤ) ^ 6)
            = -(d * (B0 : ℤ)) * (y1 : ℤ) ^ 3 + 1875 * d * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
                75 * d ^ 2 * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 3 * (D : ℤ) ^ 6 := by ring
        _ = -15600 * (y1 : ℤ) ^ 3 + 1875 * d * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
                75 * d ^ 2 * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 3 * (D : ℤ) ^ 6 := by rw [hB0_mul]
        _ = 25 * (y1 : ℤ) ^ 3 - (25 * (y1 : ℤ) - d * (D : ℤ) ^ 2) ^ 3 := by ring
        _ = d * 1 := by linarith
    exact mul_left_cancel₀ (ne_of_gt hd_pos) hmul
  have hcop_y1_d : Nat.Coprime y1 d.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg1 : ((Nat.gcd y1 d.natAbs : ℕ) : ℤ) ∣ 1 := by
      have hy_dvd : ((Nat.gcd y1 d.natAbs : ℕ) : ℤ) ∣ (y1 : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left y1 d.natAbs)
      have hd_dvd : ((Nat.gcd y1 d.natAbs : ℕ) : ℤ) ∣ d := by
        rw [← hdz_eq]
        exact Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right y1 d.natAbs)
      rw [← hnorm]
      have hid : -(B0 : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
          75 * d * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 2 * (D : ℤ) ^ 6 =
          (y1 : ℤ) * (-(B0 : ℤ) * (y1 : ℤ) ^ 2 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) -
            75 * d * (D : ℤ) ^ 4) + d * (d * (D : ℤ) ^ 6) := by ring
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_left hy_dvd _) (dvd_mul_of_dvd_left hd_dvd _)
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)
  have hcop_D_B0 : Nat.Coprime D B0 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg1 : ((Nat.gcd D B0 : ℕ) : ℤ) ∣ 1 := by
      have hD_dvd : ((Nat.gcd D B0 : ℕ) : ℤ) ∣ (D : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left D B0)
      have hB_dvd : ((Nat.gcd D B0 : ℕ) : ℤ) ∣ (B0 : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right D B0)
      rw [← hnorm]
      have hid : -(B0 : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
          75 * d * (D : ℤ) ^ 4 * (y1 : ℤ) + d ^ 2 * (D : ℤ) ^ 6 =
          (B0 : ℤ) * (-(y1 : ℤ) ^ 3) +
          (D : ℤ) * (1875 * (D : ℤ) * (y1 : ℤ) ^ 2 - 75 * d * (D : ℤ) ^ 3 * (y1 : ℤ) +
            d ^ 2 * (D : ℤ) ^ 5) := by ring
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_left hB_dvd _) (dvd_mul_of_dvd_left hD_dvd _)
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)
  have hcop_D_y1 : Nat.Coprime D y1 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hg1 : ((Nat.gcd D y1 : ℕ) : ℤ) ∣ 1 := by
      have hD_dvd : ((Nat.gcd D y1 : ℕ) : ℤ) ∣ (D : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left D y1)
      have hy_dvd : ((Nat.gcd D y1 : ℕ) : ℤ) ∣ (y1 : ℤ) :=
        Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right D y1)
      have hx1_dvd : ((Nat.gcd D y1 : ℕ) : ℤ) ∣ (x1 : ℤ) := by
        have hid : (x1 : ℤ) = 25 * (y1 : ℤ) - d * (D : ℤ) ^ 2 := by linarith
        rw [hid]
        exact dvd_sub (dvd_mul_of_dvd_right hy_dvd 25)
          (dvd_mul_of_dvd_right (dvd_pow hD_dvd (by norm_num)) d)
      have hx1_dvd_nat : Nat.gcd D y1 ∣ x1 := Int.natCast_dvd.mp hx1_dvd
      have hy1_dvd_nat : Nat.gcd D y1 ∣ y1 := Nat.gcd_dvd_right D y1
      have hcop_dvd : Nat.gcd D y1 ∣ Nat.gcd x1 y1 := Nat.dvd_gcd hx1_dvd_nat hy1_dvd_nat
      rw [hcop.gcd_eq_one] at hcop_dvd
      exact Int.natCast_dvd_natCast.mpr hcop_dvd
    exact Nat.dvd_one.mp (Int.natCast_dvd.mp hg1)
  exact ⟨hD_ge1, hDx.symm, hDy.symm, hcop, hy1_lt_x1, hx1_lt_3y1, hd_pos, hrel,
    h22, h24, hd_mem, hnorm, hcop_y1_d, hcop_D_B0, hcop_D_y1⟩

/-! ## 3. Local Congruence Obstructions (60 → 24 Surviving Divisors) -/

/-- Whenever `5 ∣ d.natAbs` in `d = 25 * y1^3 - x1^3`, automatically `25 ∣ d.natAbs`. -/
theorem five_dvd_d_implies_twentyfive_dvd {x1 y1 : ℕ}
    (h5 : 5 ∣ (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3).natAbs) :
    25 ∣ (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3).natAbs := by
  have h5z : (5 : ℤ) ∣ 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 :=
    Int.natCast_dvd.mpr h5
  have h5x3 : (5 : ℤ) ∣ (x1 : ℤ) ^ 3 := by
    have : (x1 : ℤ) ^ 3 = 25 * (y1 : ℤ) ^ 3 - (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3) := by ring
    rw [this]
    exact dvd_sub ⟨5 * (y1 : ℤ) ^ 3, by ring⟩ h5z
  have h5x : 5 ∣ x1 := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5)
    (by simpa [Int.natCast_pow] using Int.natCast_dvd.mp h5x3))
  rcases h5x with ⟨t, rfl⟩
  have h25z : (25 : ℤ) ∣ 25 * (y1 : ℤ) ^ 3 - ((5 * t : ℕ) : ℤ) ^ 3 := by
    refine ⟨(y1 : ℤ) ^ 3 - 5 * (t : ℤ) ^ 3, ?_⟩
    push_cast
    ring
  exact Int.natCast_dvd.mp h25z

/-- Modular polynomial evaluation for the divided norm equation modulo `M`. -/
def polyMod (B0 d M y1 D : ℕ) : ℤ :=
  let y1z : ℤ := (y1 : ℤ)
  let Dz : ℤ := (D : ℤ)
  let Mz : ℤ := (M : ℤ)
  let y2 := (y1z * y1z) % Mz
  let y3 := (y2 * y1z) % Mz
  let D2 := (Dz * Dz) % Mz
  let D4 := (D2 * D2) % Mz
  let D6 := (D4 * D2) % Mz
  ((-(B0 : ℤ) * y3 + 1875 * D2 * y2 - 75 * (d : ℤ) * D4 * y1z + (d : ℤ) ^ 2 * D6) - 1) % Mz

/-- Checks existence of locally coprime solutions `(y1, D)` modulo `M` for `d ∣ 15600`. -/
def checkMod (d M : ℕ) : Bool :=
  let B0 := 15600 / d
  (List.range M).any fun y1 =>
    (Nat.gcd y1 (Nat.gcd d M) == 1) &&
    (List.range M).any fun D =>
      (Nat.gcd D (Nat.gcd B0 M) == 1) &&
      (Nat.gcd D (Nat.gcd y1 M) == 1) &&
      (polyMod B0 d M y1 D == 0)

/-- Local congruence admissibility predicate modulo `[8, 9, 25, 13]` on positive divisors `d ∣ 15600`. -/
def LocallyAdmissible3 (d : ℕ) : Bool :=
  (0 < d) && (15600 % d == 0) && [8, 9, 25, 13].all (checkMod d)

private lemma gcd_mod_gcd_eq_one {a b M : ℕ} (hcop : Nat.Coprime a b) :
    Nat.gcd (a % M) (Nat.gcd b M) = 1 := by
  set g := Nat.gcd (a % M) (Nat.gcd b M)
  have h1 : g ∣ a % M := Nat.gcd_dvd_left _ _
  have h2 : g ∣ Nat.gcd b M := Nat.gcd_dvd_right _ _
  have hb : g ∣ b := dvd_trans h2 (Nat.gcd_dvd_left _ _)
  have hM : g ∣ M := dvd_trans h2 (Nat.gcd_dvd_right _ _)
  have ha : g ∣ a := by
    rw [← Nat.div_add_mod a M]
    exact dvd_add (dvd_mul_of_dvd_left hM _) h1
  have hab : g ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
  rw [hcop.gcd_eq_one] at hab
  exact Nat.dvd_one.mp hab

private lemma gcd_mod_both_gcd_eq_one {a b M : ℕ} (hcop : Nat.Coprime a b) :
    Nat.gcd (a % M) (Nat.gcd (b % M) M) = 1 := by
  set g := Nat.gcd (a % M) (Nat.gcd (b % M) M)
  have h1 : g ∣ a % M := Nat.gcd_dvd_left _ _
  have h2 : g ∣ Nat.gcd (b % M) M := Nat.gcd_dvd_right _ _
  have hbm : g ∣ b % M := dvd_trans h2 (Nat.gcd_dvd_left _ _)
  have hM : g ∣ M := dvd_trans h2 (Nat.gcd_dvd_right _ _)
  have ha : g ∣ a := by
    rw [← Nat.div_add_mod a M]
    exact dvd_add (dvd_mul_of_dvd_left hM _) h1
  have hb : g ∣ b := by
    rw [← Nat.div_add_mod b M]
    exact dvd_add (dvd_mul_of_dvd_left hM _) hbm
  have hab : g ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
  rw [hcop.gcd_eq_one] at hab
  exact Nat.dvd_one.mp hab

private lemma polyMod_eq_eval_mod (B0 d M y1 D : ℕ) :
    polyMod B0 d M (y1 % M) (D % M) =
      (-(B0 : ℤ) * (y1 : ℤ) ^ 3 + 1875 * (D : ℤ) ^ 2 * (y1 : ℤ) ^ 2 -
        75 * (d : ℤ) * (D : ℤ) ^ 4 * (y1 : ℤ) + (d : ℤ) ^ 2 * (D : ℤ) ^ 6 - 1) % (M : ℤ) := by
  dsimp [polyMod]
  have hy : ((y1 % M : ℕ) : ℤ) ≡ (y1 : ℤ) [ZMOD (M : ℤ)] := by
    change ((y1 : ℤ) % (M : ℤ)) % (M : ℤ) = (y1 : ℤ) % (M : ℤ)
    exact Int.emod_emod (y1 : ℤ) (M : ℤ)
  have hD : ((D % M : ℕ) : ℤ) ≡ (D : ℤ) [ZMOD (M : ℤ)] := by
    change ((D : ℤ) % (M : ℤ)) % (M : ℤ) = (D : ℤ) % (M : ℤ)
    exact Int.emod_emod (D : ℤ) (M : ℤ)
  have hy2 : (((y1 % M : ℕ) : ℤ) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ) ≡ (y1 : ℤ) ^ 2 [ZMOD (M : ℤ)] := by
    have hp := Int.ModEq.mul hy hy
    have hmod : (((y1 % M : ℕ) : ℤ) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ) ≡
        ((y1 % M : ℕ) : ℤ) * ((y1 % M : ℕ) : ℤ) [ZMOD (M : ℤ)] := Int.mod_modEq _ _
    simpa [sq] using hmod.trans hp
  have hy3 : (((((y1 % M : ℕ) : ℤ) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ)) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ) ≡
      (y1 : ℤ) ^ 3 [ZMOD (M : ℤ)] := by
    have hmul := Int.ModEq.mul hy2 hy
    have hmod : (((((y1 % M : ℕ) : ℤ) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ)) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ) ≡
        ((((y1 % M : ℕ) : ℤ) * ((y1 % M : ℕ) : ℤ)) % (M : ℤ)) * ((y1 % M : ℕ) : ℤ) [ZMOD (M : ℤ)] :=
      Int.mod_modEq _ _
    simpa [pow_succ] using hmod.trans hmul
  have hD2 : (((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ) ≡ (D : ℤ) ^ 2 [ZMOD (M : ℤ)] := by
    have hp := Int.ModEq.mul hD hD
    have hmod : (((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ) ≡
        ((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ) [ZMOD (M : ℤ)] := Int.mod_modEq _ _
    simpa [sq] using hmod.trans hp
  have hD4 : (((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ)) *
      ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ))) % (M : ℤ) ≡ (D : ℤ) ^ 4 [ZMOD (M : ℤ)] := by
    have hp := Int.ModEq.mul hD2 hD2
    have hmod : (((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ)) *
        ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ))) % (M : ℤ) ≡
        ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ)) *
        ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ)) [ZMOD (M : ℤ)] := Int.mod_modEq _ _
    have hp4 : (D : ℤ) ^ 2 * (D : ℤ) ^ 2 = (D : ℤ) ^ 4 := by ring
    rw [hp4] at hp
    exact hmod.trans hp
  have hD6 : (((((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ)) *
      ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ))) % (M : ℤ)) *
      ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ))) % (M : ℤ) ≡ (D : ℤ) ^ 6 [ZMOD (M : ℤ)] := by
    have hp := Int.ModEq.mul hD4 hD2
    have hmod := Int.mod_modEq ((((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ)) *
      ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ))) % (M : ℤ) *
      ((((D % M : ℕ) : ℤ) * ((D % M : ℕ) : ℤ)) % (M : ℤ))) (M : ℤ)
    have hp6 : (D : ℤ) ^ 4 * (D : ℤ) ^ 2 = (D : ℤ) ^ 6 := by ring
    rw [hp6] at hp
    exact hmod.trans hp
  have ht1 := Int.ModEq.mul_left (-(B0 : ℤ)) hy3
  have ht2 := Int.ModEq.mul_left (1875 : ℤ) (hD2.mul hy2)
  have ht3 := Int.ModEq.mul_left (75 * (d : ℤ)) (hD4.mul hy)
  have ht4 := Int.ModEq.mul_left ((d : ℤ) ^ 2) hD6
  have hfull := (((ht1.add ht2).sub ht3).add ht4).sub_right 1
  change _ % (M : ℤ) = _ % (M : ℤ)
  have hs := hfull.symm
  dsimp [Int.ModEq] at hs
  convert hs.symm using 1 <;> ring_nf

/-- Every solution to `k = 3` (`m ≥ n + 3`) produces `d.natAbs` passing `LocallyAdmissible3`. -/
theorem locallyAdmissible3_of_solution {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3))) :
    let x := m + 2
    let y := n + 2
    let D := Nat.gcd x y
    let d : ℤ := 25 * ((y / D : ℕ) : ℤ) ^ 3 - ((x / D : ℕ) : ℤ) ^ 3
    LocallyAdmissible3 d.natAbs = true := by
  intro x y D d
  rcases k3_thue_reduction hmn heq with
    ⟨_, _, _, _, _, _, hd_pos, _, _, _, hd_mem, hnorm, hcop_y1_d, hcop_D_B0, hcop_D_y1⟩
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos)
  have hd_dvd : d.natAbs ∣ 15600 := (Nat.mem_divisors.mp hd_mem).1
  have hd_pos_nat : 0 < d.natAbs := Int.natAbs_pos.mpr (ne_of_gt hd_pos)
  unfold LocallyAdmissible3
  have hd0 : decide (0 < d.natAbs) = true := decide_eq_true hd_pos_nat
  have h156 : (15600 % d.natAbs == 0) = true := beq_iff_eq.mpr (Nat.mod_eq_zero_of_dvd hd_dvd)
  have hall : ([8, 9, 25, 13].all (checkMod d.natAbs)) = true := by
    rw [List.all_eq_true]
    intro M hM
    have hM_pos : 0 < M := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
      rcases hM with rfl | rfl | rfl | rfl <;> omega
    dsimp [checkMod]
    rw [List.any_eq_true]
    refine ⟨(y / D) % M, List.mem_range.mpr (Nat.mod_lt _ hM_pos), ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨gcd_mod_gcd_eq_one hcop_y1_d, ?_⟩
    rw [List.any_eq_true]
    refine ⟨D % M, List.mem_range.mpr (Nat.mod_lt _ hM_pos), ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨gcd_mod_gcd_eq_one hcop_D_B0, gcd_mod_both_gcd_eq_one hcop_D_y1⟩, ?_⟩
    rw [polyMod_eq_eval_mod, hdz_eq]
    have hnorm0 : -((15600 / d.natAbs : ℕ) : ℤ) * ((y / D : ℕ) : ℤ) ^ 3 +
        1875 * (D : ℤ) ^ 2 * ((y / D : ℕ) : ℤ) ^ 2 -
        75 * d * (D : ℤ) ^ 4 * ((y / D : ℕ) : ℤ) + d ^ 2 * (D : ℤ) ^ 6 - 1 = 0 := by
      dsimp only [x, y, D, d] at hnorm ⊢
      linarith
    rw [hnorm0]
    norm_num
  rw [hd0, h156, hall]
  rfl

/-- **Exact 60 → 24 Kernel-Checked Divisor Filter**. -/
theorem locallyAdmissible3_filters_15600 :
    (Nat.divisors 15600).filter (fun d => LocallyAdmissible3 d = true) =
      {1, 2, 3, 6, 8, 16, 24, 25, 26, 48, 75, 78, 200, 208, 325,
       600, 624, 650, 975, 1950, 2600, 5200, 7800, 15600} := by
  decide +kernel

/-- Exact 24 surviving divisors of `15600`. -/
def surv24 : List ℕ :=
  [1, 2, 3, 6, 8, 16, 24, 25, 26, 48, 75, 78, 200, 208, 325,
   600, 624, 650, 975, 1950, 2600, 5200, 7800, 15600]

/-! ## 4. Universal Kernel-Checked Low-`y1` Exclusion (`1 ≤ y1 ≤ 2000`, All `D ≥ 1`) -/

def cbrtSearch13 (rhs : ℕ) : ℕ → ℕ → ℕ
  | lo, 0 => lo
  | lo, fuel + 1 =>
    let mid := lo + (1 <<< fuel)
    if mid * mid * mid ≤ rhs then cbrtSearch13 rhs mid fuel else cbrtSearch13 rhs lo fuel

def checkDown (rhs y1 : ℕ) : ℕ → Bool
  | 0 => true
  | x + 1 =>
    let xcur := x + 1
    if xcur ≤ y1 then true
    else if rhs ≤ xcur ^ 3 then false
    else
      let d := rhs - xcur ^ 3
      if 15600 < d then true
      else
        let okThis :=
          !(xcur < 3 * y1 && 25 * y1 > xcur && (25 * y1 - xcur) % d == 0 && surv24.elem d)
        okThis && checkDown rhs y1 x

def checkLowY1 (y1 : ℕ) : Bool :=
  let rhs := 25 * y1 ^ 3
  let x0 := cbrtSearch13 (rhs - 1) 0 13
  decide (x0 ^ 3 < rhs ∧ rhs ≤ (x0 + 1) ^ 3) && checkDown rhs y1 x0

def checkBlockY1 (start : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkLowY1 (start + k) && checkBlockY1 start k

def checkGridY1 (start blockSize : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => checkBlockY1 (start + b * blockSize) blockSize && checkGridY1 start blockSize b

theorem low_y1_1_to_2000_ok : checkGridY1 1 250 8 = true := by
  decide +kernel

private lemma checkDown_sound (rhs y1 : ℕ) :
    ∀ x : ℕ, checkDown rhs y1 x = true →
      ∀ x1 ≤ x, y1 < x1 → x1 ^ 3 < rhs → rhs - x1 ^ 3 ≤ 15600 →
      x1 < 3 * y1 → x1 < 25 * y1 → (25 * y1 - x1) % (rhs - x1 ^ 3) = 0 →
      (rhs - x1 ^ 3) ∈ surv24 → False
  | 0, _, x1, hx1, hy1, _, _, _, _, _, _ => by omega
  | x + 1, hchk, x1, hx1, hy1, hlt, hdle, h3y, h25y, hmod, hmem => by
    dsimp only [checkDown] at hchk
    by_cases hle_y : x + 1 ≤ y1
    · omega
    · rw [if_neg hle_y] at hchk
      by_cases hge_r : rhs ≤ (x + 1) ^ 3
      · rw [if_pos hge_r] at hchk
        exact absurd hchk Bool.false_ne_true
      · rw [if_neg hge_r] at hchk
        by_cases hgt_d : 15600 < rhs - (x + 1) ^ 3
        · have hx3 : x1 ^ 3 ≤ (x + 1) ^ 3 := Nat.pow_le_pow_left hx1 3
          omega
        · rw [if_neg hgt_d, Bool.and_eq_true, Bool.not_eq_true'] at hchk
          rcases Nat.eq_or_lt_of_le hx1 with h_eq | hlt_x
          · subst h_eq
            have hmem_elem : surv24.elem (rhs - (x + 1) ^ 3) = true := by simp [hmem]
            have hbad : (x + 1 < 3 * y1 && 25 * y1 > x + 1 &&
                (25 * y1 - (x + 1)) % (rhs - (x + 1) ^ 3) == 0 &&
                surv24.elem (rhs - (x + 1) ^ 3)) = true := by
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
              exact ⟨⟨⟨h3y, h25y⟩, hmod⟩, hmem_elem⟩
            rw [hchk.1] at hbad
            exact Bool.false_ne_true hbad
          · exact checkDown_sound rhs y1 x hchk.2 x1 (by omega) hy1 hlt hdle h3y h25y hmod hmem

private lemma checkBlockY1_sound (start k : ℕ) (h : checkBlockY1 start k = true) :
    ∀ j < k, checkLowY1 (start + j) = true := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    simp only [checkBlockY1, Bool.and_eq_true] at h
    intro j hj
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
    · exact h.1
    · exact ih h.2 j hlt

private lemma checkGridY1_sound (start blockSize b : ℕ)
    (h : checkGridY1 start blockSize b = true) :
    ∀ t < b * blockSize, checkLowY1 (start + t) = true := by
  induction b with
  | zero => intro t ht; simp at ht
  | succ b ih =>
    simp only [checkGridY1, Bool.and_eq_true] at h
    intro t ht
    rw [Nat.succ_mul] at ht
    by_cases hlt : t < b * blockSize
    · exact ih h.2 t hlt
    · have hsub : t - b * blockSize < blockSize := by omega
      have hcell := checkBlockY1_sound (start + b * blockSize) blockSize h.1 (t - b * blockSize) hsub
      have heq : start + b * blockSize + (t - b * blockSize) = start + t := by omega
      rwa [heq] at hcell

/-- **Universal Low-`y1` Exclusion (`y1 ≤ 2000`, All `D ≥ 1`)**:
No integers `m ≥ n + 3` solve `k = 3, N = 25` with `(n + 2) / gcd(m + 2, n + 2) ≤ 2000`. -/
theorem no_k3_solution_y1_le_2000 :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧ (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 2000 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, hy1_le, heq⟩
  set D := Nat.gcd (m + 2) (n + 2)
  set x1 := (m + 2) / D
  set y1 := (n + 2) / D
  set d : ℤ := 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3
  have hadm := locallyAdmissible3_of_solution hmn heq
  rcases k3_thue_reduction hmn heq with
    ⟨hD1, _, hDy, _, hy1_lt_x1, hx1_lt_3y1, hd_pos, hrel, _, _, hd_mem, _, _, _, _⟩
  have hd_pos' : 0 < d := by dsimp only [D, x1, y1, d] at hd_pos ⊢; exact hd_pos
  have hrel' : 25 * (y1 : ℤ) - (x1 : ℤ) = d * (D : ℤ) ^ 2 := by
    dsimp only [D, x1, y1, d] at hrel ⊢; exact hrel
  have hy1_pos : 1 ≤ y1 := by
    by_contra hy0
    have hy0' : y1 = 0 := Nat.le_zero.mp (Nat.not_lt.mp hy0)
    have hDy' : n + 2 = D * y1 := hDy
    rw [hy0', mul_zero] at hDy'
    omega
  have hlow := checkGridY1_sound 1 250 8 low_y1_1_to_2000_ok (y1 - 1) (by omega)
  have heq_y1 : 1 + (y1 - 1) = y1 := by omega
  rw [heq_y1] at hlow
  dsimp [checkLowY1] at hlow
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlow
  set x0 := cbrtSearch13 (25 * y1 ^ 3 - 1) 0 13
  have hx1_lt_cub : x1 ^ 3 < (x0 + 1) ^ 3 := by
    have hlt_z : (x1 : ℤ) ^ 3 < 25 * (y1 : ℤ) ^ 3 := by dsimp [d] at hd_pos'; linarith
    have hx1n : x1 ^ 3 < 25 * y1 ^ 3 := by exact_mod_cast hlt_z
    exact lt_of_lt_of_le hx1n hlow.1.2
  have hx1_le_x0 : x1 ≤ x0 := by
    by_contra hgt
    have : x0 + 1 ≤ x1 := by omega
    have : (x0 + 1) ^ 3 ≤ x1 ^ 3 := Nat.pow_le_pow_left this 3
    omega
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos')
  have hd_dvd : d.natAbs ∣ 15600 := (Nat.mem_divisors.mp hd_mem).1
  have hd_le_15600 : d.natAbs ≤ 15600 := Nat.le_of_dvd (by norm_num) hd_dvd
  have hd_nat_eq : 25 * y1 ^ 3 - x1 ^ 3 = d.natAbs := by
    have : (25 * y1 ^ 3 : ℤ) = (x1 : ℤ) ^ 3 + (d.natAbs : ℤ) := by
      rw [hdz_eq]; dsimp [d]; ring
    have hnat : 25 * y1 ^ 3 = x1 ^ 3 + d.natAbs := by exact_mod_cast this
    omega
  have hd_in_filt : d.natAbs ∈ (Nat.divisors 15600).filter (fun d => LocallyAdmissible3 d = true) :=
    Finset.mem_filter.mpr ⟨hd_mem, hadm⟩
  rw [locallyAdmissible3_filters_15600] at hd_in_filt
  have hd_surv : d.natAbs ∈ surv24 := by simpa [surv24] using hd_in_filt
  have hgap_nat : x1 + d.natAbs * D ^ 2 = 25 * y1 := by
    have : (x1 : ℤ) + (d.natAbs : ℤ) * (D : ℤ) ^ 2 = 25 * (y1 : ℤ) := by
      rw [hdz_eq]; linarith [hrel']
    exact_mod_cast this
  have hx1_lt_25y1 : x1 < 25 * y1 := by
    have : 0 < d.natAbs * D ^ 2 := Nat.mul_pos (Int.natAbs_pos.mpr (ne_of_gt hd_pos')) (by positivity)
    omega
  have hmod : (25 * y1 - x1) % (25 * y1 ^ 3 - x1 ^ 3) = 0 := by
    rw [hd_nat_eq]
    exact Nat.mod_eq_zero_of_dvd ⟨D ^ 2, by omega⟩
  exact checkDown_sound (25 * y1 ^ 3) y1 x0 hlow.2 x1 hx1_le_x0 hy1_lt_x1
    (by
      have : (x1 : ℤ) ^ 3 < 25 * (y1 : ℤ) ^ 3 := by dsimp [d] at hd_pos'; linarith
      exact_mod_cast this)
    (by omega) hx1_lt_3y1 hx1_lt_25y1 (by exact hmod) (by rw [hd_nat_eq]; exact hd_surv)

/-- Corollary covering the `y1 ≤ 1873` baseline directly. -/
theorem no_k3_solution_y1_le_1873 :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧ (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 1873 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, hy, heq⟩
  exact no_k3_solution_y1_le_2000 ⟨m, n, hmn, by omega, heq⟩

/-! ## 5. Pure-Integer Cubic Approximation Windows & Convergent Chain Past `10^73` -/

/-- Auxiliary cube-difference lower bound: if `v < u`, `29*A ≤ 10*u`, `29*A ≤ 10*v`,
then `25 * A^2 ≤ u^3 - v^3`. -/
private lemma cube_diff_ge_25 {u v A : ℕ} (huv : v < u)
    (hu : 29 * A ≤ 10 * u) (hv : 29 * A ≤ 10 * v) :
    25 * A ^ 2 ≤ u ^ 3 - v ^ 3 := by
  have huvz : (v : ℤ) + 1 ≤ (u : ℤ) := by exact_mod_cast huv
  have huz : 29 * (A : ℤ) ≤ 10 * (u : ℤ) := by exact_mod_cast hu
  have hvz : 29 * (A : ℤ) ≤ 10 * (v : ℤ) := by exact_mod_cast hv
  have hA0 : 0 ≤ (A : ℤ) := Int.natCast_nonneg A
  have hu0 : 0 ≤ (u : ℤ) := Int.natCast_nonneg u
  have h1 : 841 * (A : ℤ) ^ 2 ≤ 100 * (u : ℤ) ^ 2 := by nlinarith
  have h2 : 841 * (A : ℤ) ^ 2 ≤ 100 * ((u : ℤ) * (v : ℤ)) := by nlinarith
  have h3 : 841 * (A : ℤ) ^ 2 ≤ 100 * (v : ℤ) ^ 2 := by nlinarith
  have hcomb : 100 * ((u : ℤ) ^ 2 + (u : ℤ) * (v : ℤ) + (v : ℤ) ^ 2) =
      100 * (u : ℤ) ^ 2 + 100 * ((u : ℤ) * (v : ℤ)) + 100 * (v : ℤ) ^ 2 := by ring
  have hsum : 2500 * (A : ℤ) ^ 2 ≤ 100 * ((u : ℤ) ^ 2 + (u : ℤ) * (v : ℤ) + (v : ℤ) ^ 2) := by
    have hge : 2500 * (A : ℤ) ^ 2 ≤ 2523 * (A : ℤ) ^ 2 := by nlinarith
    rw [hcomb]
    linarith [hge, h1, h2, h3]
  have hsq : 25 * (A : ℤ) ^ 2 ≤ (u : ℤ) ^ 2 + (u : ℤ) * (v : ℤ) + (v : ℤ) ^ 2 := by linarith
  have hid : (u : ℤ) ^ 3 - (v : ℤ) ^ 3 =
      ((u : ℤ) - (v : ℤ)) * ((u : ℤ) ^ 2 + (u : ℤ) * (v : ℤ) + (v : ℤ) ^ 2) := by ring
  have hcub : 25 * (A : ℤ) ^ 2 ≤ (u : ℤ) ^ 3 - (v : ℤ) ^ 3 := by
    rw [hid]
    nlinarith
  have hnat : 25 * A ^ 2 ≤ u ^ 3 - v ^ 3 := by
    have heq_le : 25 * (A : ℤ) ^ 2 + (v : ℤ) ^ 3 ≤ (u : ℤ) ^ 3 := by linarith
    have heq_nat : 25 * A ^ 2 + v ^ 3 ≤ u ^ 3 := by exact_mod_cast heq_le
    omega
  exact hnat

/-- For any solution with `y1 ≥ 30` (in fact we have `y1 ≥ 2001`), `29 * y1 ≤ 10 * x1`. -/
lemma twenty_nine_y1_le_ten_x1 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (hy1 : 30 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2)) :
    29 * ((n + 2) / Nat.gcd (m + 2) (n + 2)) ≤ 10 * ((m + 2) / Nat.gcd (m + 2) (n + 2)) := by
  set D := Nat.gcd (m + 2) (n + 2)
  set x1 := (m + 2) / D
  set y1 := (n + 2) / D
  set d : ℤ := 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3
  rcases k3_thue_reduction hmn heq with
    ⟨_, _, _, _, _, _, hd_pos, _, _, _, hd_mem, _, _, _, _⟩
  have hd_pos' : 0 < d := by dsimp only [D, x1, y1, d] at hd_pos ⊢; exact hd_pos
  have hd_dvd : d.natAbs ∣ 15600 := (Nat.mem_divisors.mp hd_mem).1
  have hd_le : d.natAbs ≤ 15600 := Nat.le_of_dvd (by norm_num) hd_dvd
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos')
  have hcub : 25 * (y1 : ℤ) ^ 3 ≤ (x1 : ℤ) ^ 3 + 15600 := by
    have : d ≤ 15600 := by omega
    dsimp [d] at this
    linarith
  have hy3 : 15600000 < 611 * (y1 : ℤ) ^ 3 := by
    have hyz : (30 : ℤ) ≤ y1 := by exact_mod_cast hy1
    nlinarith
  have hdiff : (29 * (y1 : ℤ)) ^ 3 < (10 * (x1 : ℤ)) ^ 3 := by
    have h1000 : 1000 * (x1 : ℤ) ^ 3 ≥ 25000 * (y1 : ℤ) ^ 3 - 15600000 := by linarith
    have h29 : (29 * (y1 : ℤ)) ^ 3 = 24389 * (y1 : ℤ) ^ 3 := by ring
    have h10 : (10 * (x1 : ℤ)) ^ 3 = 1000 * (x1 : ℤ) ^ 3 := by ring
    linarith
  by_contra hlt
  have hge : 10 * (x1 : ℤ) < 29 * (y1 : ℤ) := by omega
  have hle : (10 * (x1 : ℤ)) ^ 3 < (29 * (y1 : ℤ)) ^ 3 := by
    have hx0 : 0 ≤ 10 * (x1 : ℤ) := by positivity
    gcongr
  omega

/-- Pure abstract integer core for `upper_cubic_approx_excludes_window` (keeps context small for `nlinarith`). -/
private theorem upper_cubic_approx_core {x1 y1 d_nat p q c ylo yhi : ℕ}
    (hd_pos : 0 < d_nat) (hd_le : d_nat ≤ 15600) (hd_eq : x1 ^ 3 + d_nat = 25 * y1 ^ 3)
    (hx1_ge : 29 * y1 ≤ 10 * x1)
    (hc : p ^ 3 - 25 * q ^ 3 = c) (hc_pos : 0 < c) (h25q_lt : 25 * q ^ 3 < p ^ 3)
    (hpq : 29 * q ≤ 10 * p)
    (hlo : 15600 * q < 12 * ylo ^ 2) (hhi : c * yhi ≤ 13 * q ^ 2)
    (hylo : ylo ≤ y1) (hyhi : y1 ≤ yhi) :
    False := by
  have hy1_pos : 0 < y1 := by
    by_contra hy0
    have hy0' : y1 = 0 := by omega
    subst hy0'
    omega
  have hq_pos : 0 < q := by
    by_contra hq0
    have hq0' : q = 0 := by omega
    subst hq0'
    have hc0 : c * yhi = 0 := by simpa using hhi
    have hy1_le : ylo ≤ yhi := le_trans hylo hyhi
    have hc_pos' : 0 < c := hc_pos
    have hlo' : 0 < ylo := by nlinarith
    nlinarith
  have hcz : (p : ℤ) ^ 3 - 25 * (q : ℤ) ^ 3 = (c : ℤ) := by
    have : 25 * q ^ 3 ≤ p ^ 3 := le_of_lt h25q_lt
    zify [this] at hc ⊢
    exact hc
  have hdz : 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 = (d_nat : ℤ) := by
    have : (x1 : ℤ) ^ 3 + (d_nat : ℤ) = 25 * (y1 : ℤ) ^ 3 := by exact_mod_cast hd_eq
    linarith
  have hpy_gt : q * x1 < p * y1 := by
    have hlhs : (q * x1 : ℤ) ^ 3 < (p * y1 : ℤ) ^ 3 := by
      have hid : (p * y1 : ℤ) ^ 3 - (q * x1 : ℤ) ^ 3 =
          (c : ℤ) * (y1 : ℤ) ^ 3 + (d_nat : ℤ) * (q : ℤ) ^ 3 := by
        linear_combination (y1 : ℤ) ^ 3 * hcz + (q : ℤ) ^ 3 * hdz
      have ht1 : 0 < (c : ℤ) * (y1 : ℤ) ^ 3 := by positivity
      have ht2 : 0 ≤ (d_nat : ℤ) * (q : ℤ) ^ 3 := by positivity
      linarith
    by_contra hle
    have h1 : (p * y1 : ℤ) ≤ (q * x1 : ℤ) := by omega
    have h2 : (p * y1 : ℤ) ^ 3 ≤ (q * x1 : ℤ) ^ 3 := by
      have hp0 : 0 ≤ (p * y1 : ℤ) := by positivity
      gcongr
    linarith
  have h25_diff : 25 * (q * y1) ^ 2 ≤ (p * y1) ^ 3 - (q * x1) ^ 3 :=
    cube_diff_ge_25 hpy_gt
      (by calc 29 * (q * y1) = (29 * q) * y1 := by ring
            _ ≤ (10 * p) * y1 := Nat.mul_le_mul_right y1 hpq
            _ = 10 * (p * y1) := by ring)
      (by calc 29 * (q * y1) = q * (29 * y1) := by ring
            _ ≤ q * (10 * x1) := Nat.mul_le_mul_left q hx1_ge
            _ = 10 * (q * x1) := by ring)
  have hlt_n : (q * x1) ^ 3 ≤ (p * y1) ^ 3 := Nat.pow_le_pow_left (le_of_lt hpy_gt) 3
  have hidz : ((p * y1 : ℕ) ^ 3 - (q * x1 : ℕ) ^ 3 : ℤ) =
      (c : ℤ) * (y1 : ℤ) ^ 3 + (d_nat : ℤ) * (q : ℤ) ^ 3 := by
    zify [hlt_n]
    linear_combination (y1 : ℤ) ^ 3 * hcz + (q : ℤ) ^ 3 * hdz
  have hdiff_z : 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 ≤ (c : ℤ) * (y1 : ℤ) ^ 3 + (d_nat : ℤ) * (q : ℤ) ^ 3 := by
    have h1 : 25 * ((q : ℤ) * (y1 : ℤ)) ^ 2 ≤ ((p * y1 : ℕ) ^ 3 - (q * x1 : ℕ) ^ 3 : ℤ) := by
      exact_mod_cast h25_diff
    rw [hidz] at h1
    have hmul_eq : 25 * ((q : ℤ) * (y1 : ℤ)) ^ 2 = 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
    linarith
  have h2 : (d_nat : ℤ) * (q : ℤ) ^ 3 ≤ 15600 * (q : ℤ) ^ 3 := by
    have : (d_nat : ℤ) ≤ 15600 := by exact_mod_cast hd_le
    exact mul_le_mul_of_nonneg_right this (pow_nonneg (Int.natCast_nonneg q) 3)
  have hpart1 : 15600 * (q : ℤ) ^ 3 < 12 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by
    have hloz : 15600 * (q : ℤ) < 12 * (ylo : ℤ) ^ 2 := by exact_mod_cast hlo
    have hylo_z : (ylo : ℤ) ≤ (y1 : ℤ) := by exact_mod_cast hylo
    have hy_sq : (ylo : ℤ) ^ 2 ≤ (y1 : ℤ) ^ 2 := by nlinarith [Int.natCast_nonneg ylo]
    have hlo2 : 15600 * (q : ℤ) < 12 * (y1 : ℤ) ^ 2 := by linarith
    have hq2_pos : 0 < (q : ℤ) ^ 2 := by positivity
    calc 15600 * (q : ℤ) ^ 3 = (15600 * (q : ℤ)) * (q : ℤ) ^ 2 := by ring
      _ < (12 * (y1 : ℤ) ^ 2) * (q : ℤ) ^ 2 := mul_lt_mul_of_pos_right hlo2 hq2_pos
      _ = 12 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
  have hpart2 : (c : ℤ) * (y1 : ℤ) ^ 3 ≤ 13 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by
    have hhiz : (c : ℤ) * (yhi : ℤ) ≤ 13 * (q : ℤ) ^ 2 := by exact_mod_cast hhi
    have hyhi_z : (y1 : ℤ) ≤ (yhi : ℤ) := by exact_mod_cast hyhi
    have hcz0 : 0 ≤ (c : ℤ) := Int.natCast_nonneg c
    have hcy : (c : ℤ) * (y1 : ℤ) ≤ 13 * (q : ℤ) ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hyhi_z hcz0) hhiz
    calc (c : ℤ) * (y1 : ℤ) ^ 3 = ((c : ℤ) * (y1 : ℤ)) * (y1 : ℤ) ^ 2 := by ring
      _ ≤ (13 * (q : ℤ) ^ 2) * (y1 : ℤ) ^ 2 := mul_le_mul_of_nonneg_right hcy (sq_nonneg _)
      _ = 13 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
  linarith

/-- **Upper Cubic Approximation Window Lemma**:
If `p^3 - 25*q^3 = c > 0`, `29*q ≤ 10*p`, `15600*q < 12 * ylo^2`, and `c * yhi ≤ 13 * q^2`,
then no `k = 3` solution can have `ylo ≤ y1 ≤ yhi` (whenever `30 ≤ y1`). -/
theorem upper_cubic_approx_excludes_window {p q c ylo yhi : ℕ}
    (hc : p ^ 3 - 25 * q ^ 3 = c) (hc_pos : 0 < c) (h25q_lt : 25 * q ^ 3 < p ^ 3)
    (hpq : 29 * q ≤ 10 * p)
    (hlo : 15600 * q < 12 * ylo ^ 2) (hhi : c * yhi ≤ 13 * q ^ 2)
    {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (hy30 : 30 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (hylo : ylo ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (hyhi : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ yhi) :
    False := by
  set D := Nat.gcd (m + 2) (n + 2)
  set x1 := (m + 2) / D
  set y1 := (n + 2) / D
  set d : ℤ := 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3
  rcases k3_thue_reduction hmn heq with
    ⟨_, _, _, _, _, _, hd_pos, _, _, _, hd_mem, _, _, _, _⟩
  have hd_pos' : 0 < d := by dsimp only [D, x1, y1, d] at hd_pos ⊢; exact hd_pos
  have hd_dvd : d.natAbs ∣ 15600 := (Nat.mem_divisors.mp hd_mem).1
  have hd_le : d.natAbs ≤ 15600 := Nat.le_of_dvd (by norm_num) hd_dvd
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos')
  have hd_nat_pos : 0 < d.natAbs := Int.natAbs_pos.mpr (ne_of_gt hd_pos')
  have hd_eq : x1 ^ 3 + d.natAbs = 25 * y1 ^ 3 := by
    have : (x1 : ℤ) ^ 3 + (d.natAbs : ℤ) = 25 * (y1 : ℤ) ^ 3 := by
      rw [hdz_eq]; dsimp [d]; ring
    exact_mod_cast this
  exact upper_cubic_approx_core hd_nat_pos hd_le hd_eq (twenty_nine_y1_le_ten_x1 hmn heq hy30)
    hc hc_pos h25q_lt hpq hlo hhi hylo hyhi

private lemma lower_cubic_cross_lt {x1 y1 d_nat p q c ylo : ℕ}
    (hd_le : d_nat ≤ 15600) (hq_pos : 0 < q)
    (hcop_xy : Nat.Coprime x1 y1) (hx1_ge : 29 * y1 ≤ 10 * x1)
    (hc_gt : 15600 < c) (hcop_pq : Nat.Coprime p q) (hpq : 29 * q ≤ 10 * p)
    (hlo : 15600 * q < 25 * ylo ^ 2) (hylo : ylo ≤ y1)
    (hcz : 25 * (q : ℤ) ^ 3 - (p : ℤ) ^ 3 = (c : ℤ))
    (hdz : 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 = (d_nat : ℤ)) :
    p * y1 < q * x1 := by
  have hne_cross : p * y1 ≠ q * x1 := by
    intro heqc
    have hy_dvd_q : y1 ∣ q := hcop_xy.symm.dvd_of_dvd_mul_right ⟨p, by linarith only [heqc]⟩
    have hq_dvd_y : q ∣ y1 := hcop_pq.symm.dvd_of_dvd_mul_right ⟨x1, by linarith only [heqc]⟩
    have hyq : y1 = q := Nat.dvd_antisymm hy_dvd_q hq_dvd_y
    subst hyq
    have hpx : p = x1 := Nat.mul_right_cancel hq_pos (by linarith only [heqc])
    subst hpx
    have : d_nat = c := by
      have hdc : (d_nat : ℤ) = (c : ℤ) := by linarith only [hcz, hdz]
      exact_mod_cast hdc
    omega
  rcases lt_trichotomy (p * y1) (q * x1) with hlt | heqc | hgt
  · exact hlt
  · exact absurd heqc hne_cross
  · exfalso
    have hdiff : 25 * (q * y1) ^ 2 ≤ (p * y1) ^ 3 - (q * x1) ^ 3 :=
      cube_diff_ge_25 hgt
        (by calc 29 * (q * y1) = (29 * q) * y1 := by ring
              _ ≤ (10 * p) * y1 := Nat.mul_le_mul_right y1 hpq
              _ = 10 * (p * y1) := by ring)
        (by calc 29 * (q * y1) = q * (29 * y1) := by ring
              _ ≤ q * (10 * x1) := Nat.mul_le_mul_left q hx1_ge
              _ = 10 * (q * x1) := by ring)
    have hlt_n : (q * x1) ^ 3 ≤ (p * y1) ^ 3 := Nat.pow_le_pow_left (le_of_lt hgt) 3
    have hidz : ((p * y1 : ℕ) ^ 3 - (q * x1 : ℕ) ^ 3 : ℤ) =
        (d_nat : ℤ) * (q : ℤ) ^ 3 - (c : ℤ) * (y1 : ℤ) ^ 3 := by
      zify [hlt_n]
      linear_combination -(y1 : ℤ) ^ 3 * hcz + (q : ℤ) ^ 3 * hdz
    have h1 : 25 * ((q : ℤ) * (y1 : ℤ)) ^ 2 ≤ ((p * y1 : ℕ) ^ 3 - (q * x1 : ℕ) ^ 3 : ℤ) := by
      exact_mod_cast hdiff
    rw [hidz] at h1
    have hmul_eq : 25 * ((q : ℤ) * (y1 : ℤ)) ^ 2 = 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
    have h3 : (d_nat : ℤ) * (q : ℤ) ^ 3 ≤ 15600 * (q : ℤ) ^ 3 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hd_le) (pow_nonneg (Int.natCast_nonneg q) 3)
    have h4 : 0 ≤ (c : ℤ) * (y1 : ℤ) ^ 3 := by positivity
    have hup_z : 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 ≤ 15600 * (q : ℤ) ^ 3 := by
      linarith only [h1, hmul_eq, h3, h4]
    have hloz : 15600 * (q : ℤ) < 25 * (ylo : ℤ) ^ 2 := by exact_mod_cast hlo
    have hylo_z : (ylo : ℤ) ≤ (y1 : ℤ) := by exact_mod_cast hylo
    have hy_sq : (ylo : ℤ) ^ 2 ≤ (y1 : ℤ) ^ 2 := by
      calc (ylo : ℤ) ^ 2 = (ylo : ℤ) * (ylo : ℤ) := sq (ylo : ℤ)
        _ ≤ (y1 : ℤ) * (y1 : ℤ) :=
          mul_le_mul hylo_z hylo_z (Int.natCast_nonneg ylo) (Int.natCast_nonneg y1)
        _ = (y1 : ℤ) ^ 2 := (sq (y1 : ℤ)).symm
    have hq2_pos : 0 < (q : ℤ) ^ 2 := by positivity
    have hlo_q : 15600 * (q : ℤ) ^ 3 < 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by
      calc 15600 * (q : ℤ) ^ 3 = (15600 * (q : ℤ)) * (q : ℤ) ^ 2 := by ring
        _ < (25 * (ylo : ℤ) ^ 2) * (q : ℤ) ^ 2 := mul_lt_mul_of_pos_right hloz hq2_pos
        _ ≤ (25 * (y1 : ℤ) ^ 2) * (q : ℤ) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy_sq (by norm_num)) (le_of_lt hq2_pos)
        _ = 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
    linarith only [hup_z, hlo_q]

/-- Pure abstract integer core for `lower_cubic_approx_excludes_window` (keeps context small). -/
private theorem lower_cubic_approx_core {x1 y1 d_nat p q c ylo yhi : ℕ}
    (hd_pos : 0 < d_nat) (hd_le : d_nat ≤ 15600) (hd_eq : x1 ^ 3 + d_nat = 25 * y1 ^ 3)
    (hcop_xy : Nat.Coprime x1 y1) (hx1_ge : 29 * y1 ≤ 10 * x1)
    (hc : 25 * q ^ 3 - p ^ 3 = c) (hc_gt : 15600 < c) (hp_lt : p ^ 3 < 25 * q ^ 3)
    (hcop_pq : Nat.Coprime p q) (hpq : 29 * q ≤ 10 * p)
    (hlo : 15600 * q < 25 * ylo ^ 2) (hhi : c * yhi ≤ 25 * q ^ 2)
    (hylo : ylo ≤ y1) (hyhi : y1 ≤ yhi) :
    False := by
  have hq_pos : 0 < q := by
    by_contra hq0
    have hq0' : q = 0 := by omega
    subst hq0'
    omega
  have hcz : 25 * (q : ℤ) ^ 3 - (p : ℤ) ^ 3 = (c : ℤ) := by
    zify [le_of_lt hp_lt] at hc ⊢
    exact hc
  have hdz : 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 = (d_nat : ℤ) := by
    have : (x1 : ℤ) ^ 3 + (d_nat : ℤ) = 25 * (y1 : ℤ) ^ 3 := by exact_mod_cast hd_eq
    linarith only [this]
  have hgt_cross : p * y1 < q * x1 :=
    lower_cubic_cross_lt hd_le hq_pos hcop_xy hx1_ge hc_gt hcop_pq hpq hlo hylo hcz hdz
  have hdiff2 : 25 * (q * y1) ^ 2 ≤ (q * x1) ^ 3 - (p * y1) ^ 3 :=
    cube_diff_ge_25 hgt_cross
      (by calc 29 * (q * y1) = q * (29 * y1) := by ring
            _ ≤ q * (10 * x1) := Nat.mul_le_mul_left q hx1_ge
            _ = 10 * (q * x1) := by ring)
      (by calc 29 * (q * y1) = (29 * q) * y1 := by ring
            _ ≤ (10 * p) * y1 := Nat.mul_le_mul_right y1 hpq
            _ = 10 * (p * y1) := by ring)
  have hlt_n2 : (p * y1) ^ 3 ≤ (q * x1) ^ 3 := Nat.pow_le_pow_left (le_of_lt hgt_cross) 3
  have hidz2 : ((q * x1 : ℕ) ^ 3 - (p * y1 : ℕ) ^ 3 : ℤ) =
      (c : ℤ) * (y1 : ℤ) ^ 3 - (d_nat : ℤ) * (q : ℤ) ^ 3 := by
    zify [hlt_n2]
    linear_combination (y1 : ℤ) ^ 3 * hcz - (q : ℤ) ^ 3 * hdz
  have h1 : 25 * ((q : ℤ) * (y1 : ℤ)) ^ 2 ≤ ((q * x1 : ℕ) ^ 3 - (p * y1 : ℕ) ^ 3 : ℤ) := by
    exact_mod_cast hdiff2
  rw [hidz2] at h1
  have hmul_eq : 25 * ((q : ℤ) * (y1 : ℤ)) ^ 2 = 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
  have hdq : 0 < (d_nat : ℤ) * (q : ℤ) ^ 3 := by positivity
  have hbound : 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 < (c : ℤ) * (y1 : ℤ) ^ 3 := by
    linarith only [h1, hmul_eq, hdq]
  have hhiz : (c : ℤ) * (yhi : ℤ) ≤ 25 * (q : ℤ) ^ 2 := by exact_mod_cast hhi
  have hyhi_z : (y1 : ℤ) ≤ (yhi : ℤ) := by exact_mod_cast hyhi
  have hc0 : 0 ≤ (c : ℤ) := Int.natCast_nonneg c
  have hcy : (c : ℤ) * (y1 : ℤ) ≤ 25 * (q : ℤ) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left hyhi_z hc0) hhiz
  have hcy3 : (c : ℤ) * (y1 : ℤ) ^ 3 ≤ 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by
    calc (c : ℤ) * (y1 : ℤ) ^ 3 = ((c : ℤ) * (y1 : ℤ)) * (y1 : ℤ) ^ 2 := by ring
      _ ≤ (25 * (q : ℤ) ^ 2) * (y1 : ℤ) ^ 2 := mul_le_mul_of_nonneg_right hcy (sq_nonneg _)
      _ = 25 * (q : ℤ) ^ 2 * (y1 : ℤ) ^ 2 := by ring
  linarith only [hbound, hcy3]

/-- **Lower Cubic Approximation Window Lemma**:
If `25*q^3 - p^3 = c > 15600`, `Nat.Coprime p q`, `29*q ≤ 10*p`, `15600*q < 25 * ylo^2`,
and `c * yhi ≤ 25 * q^2`, then no `k = 3` solution can have `ylo ≤ y1 ≤ yhi` (whenever `30 ≤ y1`). -/
theorem lower_cubic_approx_excludes_window {p q c ylo yhi : ℕ}
    (hc : 25 * q ^ 3 - p ^ 3 = c) (hc_gt : 15600 < c) (hp_lt : p ^ 3 < 25 * q ^ 3)
    (hcop_pq : Nat.Coprime p q) (hpq : 29 * q ≤ 10 * p)
    (hlo : 15600 * q < 25 * ylo ^ 2) (hhi : c * yhi ≤ 25 * q ^ 2)
    {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (hy30 : 30 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (hylo : ylo ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (hyhi : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ yhi) :
    False := by
  set D := Nat.gcd (m + 2) (n + 2)
  set x1 := (m + 2) / D
  set y1 := (n + 2) / D
  set d : ℤ := 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3
  rcases k3_thue_reduction hmn heq with
    ⟨_, _, _, hcop_xy, _, _, hd_pos, _, _, _, hd_mem, _, _, _, _⟩
  have hd_pos' : 0 < d := by dsimp only [D, x1, y1, d] at hd_pos ⊢; exact hd_pos
  have hcop' : Nat.Coprime x1 y1 := by dsimp only [D, x1, y1] at hcop_xy ⊢; exact hcop_xy
  have hd_dvd : d.natAbs ∣ 15600 := (Nat.mem_divisors.mp hd_mem).1
  have hd_le : d.natAbs ≤ 15600 := Nat.le_of_dvd (by norm_num) hd_dvd
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos')
  have hd_nat_pos : 0 < d.natAbs := Int.natAbs_pos.mpr (ne_of_gt hd_pos')
  have hd_eq : x1 ^ 3 + d.natAbs = 25 * y1 ^ 3 := by
    have : (x1 : ℤ) ^ 3 + (d.natAbs : ℤ) = 25 * (y1 : ℤ) ^ 3 := by
      rw [hdz_eq]; dsimp [d]; ring
    exact_mod_cast this
  exact lower_cubic_approx_core hd_nat_pos hd_le hd_eq hcop' (twenty_nine_y1_le_ten_x1 hmn heq hy30)
    hc hc_gt hp_lt hcop_pq hpq hlo hhi hylo hyhi

/-! ### Explicit 8-Convergent Pure-Integer Chain (`y1 = 2001 → 10^73`) -/

private theorem excl_conv_8 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 1873 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 3561) : False :=
  upper_cubic_approx_excludes_window
    (p := 7889) (q := 2698) (c := 26569) (ylo := 1873) (yhi := 3561)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

private theorem excl_conv_9 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 2021 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 37998) : False :=
  lower_cubic_approx_excludes_window
    (p := 19126) (q := 6541) (c := 28149) (ylo := 2021) (yhi := 37998)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num)
    (by norm_num) hmn heq (by omega) h1 h2

private theorem excl_conv_14 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 23607 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 783610) : False :=
  upper_cubic_approx_excludes_window
    (p := 1253465) (q := 428679) (c := 3048650) (ylo := 23607) (yhi := 783610)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

private theorem excl_conv_20 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 307361 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 121519959) : False :=
  upper_cubic_approx_excludes_window
    (p := 212487062) (q := 72669553) (c := 564937903) (ylo := 307361) (yhi := 121519959)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

private theorem excl_conv_24 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 76793596 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 2676503971937) : False :=
  upper_cubic_approx_excludes_window
    (p := 13264370981122) (q := 4536351065103) (c := 99951375234673)
    (ylo := 76793596) (yhi := 2676503971937)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

private theorem excl_conv_40 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 2383661920296 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 4411500000000000000000) : False :=
  upper_cubic_approx_excludes_window
    (p := 12779856216266899832234)
    (q := 4370649346360612571005)
    (c := 56286152799793918160779)
    (ylo := 2383661920296)
    (yhi := 4411500000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

private theorem excl_conv_74 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 2349063499829182467997 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 5175800000000000000000000000000000000000) :
    False :=
  upper_cubic_approx_excludes_window
    (p := 12411554085473990834615512790551366745769)
    (q := 4244691789407482723730103827106989869651)
    (c := 45252809324976827823623077522689072055334)
    (ylo := 2349063499829182467997)
    (yhi := 5175800000000000000000000000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

private theorem excl_conv_138 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 76596980855030298497917506466896834837 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 10 ^ 73) : False :=
  upper_cubic_approx_excludes_window
    (p := 13196536224582711247452905276884873280622134134453323241045717702371269729)
    (q := 4513151904696829290734496860328805504312258623791753045857750850072013749)
    (c := 6107175370588763129248177983267941428184777579101607953444996126144588764)
    (ylo := 76596980855030298497917506466896834837)
    (yhi := 10 ^ 73)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (by omega) h1 h2

/-- **Main Convergent-Chain Theorem (`y1 > 10^73`, Past `Y_max ≈ 4.69 × 10^56`)**:
No integers `m ≥ n + 3` solve `(m+1)(m+2)(m+3) = 25*(n+1)(n+2)(n+3)` with
`(n + 2) / gcd(m + 2, n + 2) ≤ 10 ^ 73`. -/
theorem no_k3_solution_y1_le_10_pow_73 :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧ (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 10 ^ 73 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, hy_le, heq⟩
  set y1 := (n + 2) / Nat.gcd (m + 2) (n + 2)
  by_cases h0 : y1 ≤ 2000
  · exact no_k3_solution_y1_le_2000 ⟨m, n, hmn, h0, heq⟩
  · by_cases h1 : y1 ≤ 3561
    · exact excl_conv_8 hmn heq (by omega) h1
    · by_cases h2 : y1 ≤ 37998
      · exact excl_conv_9 hmn heq (by omega) h2
      · by_cases h3 : y1 ≤ 783610
        · exact excl_conv_14 hmn heq (by omega) h3
        · by_cases h4 : y1 ≤ 121519959
          · exact excl_conv_20 hmn heq (by omega) h4
          · by_cases h5 : y1 ≤ 2676503971937
            · exact excl_conv_24 hmn heq (by omega) h5
            · by_cases h6 : y1 ≤ 4411500000000000000000
              · exact excl_conv_40 hmn heq (by omega) h6
              · by_cases h7 : y1 ≤ 5175800000000000000000000000000000000000
                · exact excl_conv_74 hmn heq (by omega) h7
                · exact excl_conv_138 hmn heq (by omega) hy_le

/-- **Immediate `D ≤ 10^34` Exclusion**: Since `22 * y1 < d * D^2 ≤ 15600 * D^2`, `y1 > 10^73`
forces `D > 10^34`. -/
theorem no_k3_solution_gcd_le_10_pow_34 :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧ Nat.gcd (m + 2) (n + 2) ≤ 10 ^ 34 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, hDle, heq⟩
  rcases k3_thue_reduction hmn heq with
    ⟨_, _, _, _, _, _, hd_pos, _, h22, _, hd_mem, _, _, _, _⟩
  set D := Nat.gcd (m + 2) (n + 2)
  set x1 := (m + 2) / D
  set y1 := (n + 2) / D
  set d : ℤ := 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3
  have hd_dvd : d.natAbs ∣ 15600 := (Nat.mem_divisors.mp hd_mem).1
  have hd_le : d.natAbs ≤ 15600 := Nat.le_of_dvd (by norm_num) hd_dvd
  have hdz_eq : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg (le_of_lt hd_pos)
  have h22n : 22 * y1 < d.natAbs * D ^ 2 := by
    have : (22 * y1 : ℤ) < (d.natAbs : ℤ) * (D : ℤ) ^ 2 := by
      rw [hdz_eq]
      exact h22
    exact_mod_cast this
  have hD2 : D ^ 2 ≤ (10 ^ 34) ^ 2 := Nat.pow_le_pow_left hDle 2
  have hy_small : y1 ≤ 10 ^ 73 := by
    have hmul : d.natAbs * D ^ 2 ≤ 15600 * (10 ^ 34) ^ 2 := Nat.mul_le_mul hd_le hD2
    omega
  exact no_k3_solution_y1_le_10_pow_73 ⟨m, n, hmn, hy_small, heq⟩

/-- **Strengthened `D ≤ 60` Exclusion** (corollary of `no_k3_solution_gcd_le_10_pow_34`). -/
theorem no_k3_solution_gcd_le_60 :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧ Nat.gcd (m + 2) (n + 2) ≤ 60 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, hD60, heq⟩
  exact no_k3_solution_gcd_le_10_pow_34 ⟨m, n, hmn, by omega, heq⟩

end Reduction

namespace Pade

/-! ## 1. Falling Factorials, Padé Polynomials, and Discrete Recurrence -/

noncomputable def fall (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => fall x k * (x - (k : ℝ))

noncomputable def gbinom (x : ℝ) (k : ℕ) : ℝ :=
  fall x k / (k.factorial : ℝ)

noncomputable def cRatio (m k : ℕ) : ℝ :=
  (Nat.choose (2 * m - k) m : ℝ) / (Nat.choose (2 * m) m : ℝ)

noncomputable def padeTerm (n k : ℕ) (β z : ℝ) : ℝ :=
  if k ≤ n then gbinom (n + β) k * cRatio n k * (-z) ^ k else 0

noncomputable def Xtilde (n : ℕ) (β z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), padeTerm n k β z

noncomputable def Ptilde (n : ℕ) (z : ℝ) : ℝ := Xtilde n (1 / 3) z

noncomputable def Qtilde (n : ℕ) (z : ℝ) : ℝ := Xtilde n (-1 / 3) z

noncomputable def Ppoly (n : ℕ) (z : ℝ) : ℝ := (Nat.choose (2 * n) n : ℝ) * Ptilde n z

noncomputable def Qpoly (n : ℕ) (z : ℝ) : ℝ := (Nat.choose (2 * n) n : ℝ) * Qtilde n z

private lemma choose_2n_n_pos (n : ℕ) : 0 < (Nat.choose (2 * n) n : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)

private lemma nat_add_beta_ne_zero {β : ℝ} (hβ : β = 1 / 3 ∨ β = -1 / 3) (j : ℤ) :
    (j : ℝ) + β ≠ 0 := by
  intro h
  rcases hβ with rfl | rfl
  · have h3 : ((3 * j + 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    have hz : 3 * j + 1 = 0 := by exact_mod_cast h3
    omega
  · have h3 : ((3 * j - 1 : ℤ) : ℝ) = 0 := by push_cast; linarith
    have hz : 3 * j - 1 = 0 := by exact_mod_cast h3
    omega

private lemma beta_sub_nat_ne_zero {β : ℝ} (hβ : β = 1 / 3 ∨ β = -1 / 3) (n j : ℕ) :
    (n : ℝ) + β - (j : ℝ) ≠ 0 := by
  have h := nat_add_beta_ne_zero hβ ((n : ℤ) - (j : ℤ))
  push_cast at h
  intro h0
  apply h
  linarith

private lemma fall_succ_left (x : ℝ) : ∀ k : ℕ, fall (x + 1) k * (x + 1 - k) = (x + 1) * fall x k
  | 0 => by simp [fall]
  | k + 1 => by
    have ih := fall_succ_left x k
    dsimp [fall]
    push_cast
    calc (fall (x + 1) k * (x + 1 - k)) * (x + 1 - (k + 1))
        = ((x + 1) * fall x k) * (x - k) := by rw [ih]; ring
      _ = (x + 1) * (fall x k * (x - k)) := by ring

private lemma gbinom_succ_left {x : ℝ} {k : ℕ} (hk : x + 1 - k ≠ 0) :
    gbinom (x + 1) k = ((x + 1) / (x + 1 - k)) * gbinom x k := by
  dsimp [gbinom]
  have h := fall_succ_left x k
  have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hk, hfac]
  linarith

private lemma gbinom_step_right (x : ℝ) (k : ℕ) :
    gbinom x (k + 1) = ((x - k) / (k + 1 : ℝ)) * gbinom x k := by
  dsimp [gbinom, fall]
  rw [Nat.factorial_succ]
  push_cast
  have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hfac, hk1]

private lemma choose_succ_sub_eq {a m : ℕ} (hm : m ≤ a) :
    (a + 1) * a.choose m = (a + 1).choose m * (a + 1 - m) := by
  rw [← Nat.choose_symm hm, Nat.add_one_mul_choose_eq, show a - m + 1 = a + 1 - m by omega,
    Nat.choose_symm (by omega : m ≤ a + 1)]

private lemma cRatio_zero (m : ℕ) : cRatio m 0 = 1 := by
  dsimp [cRatio]
  simp [div_self (choose_2n_n_pos m).ne']

private lemma cRatio_step {m k : ℕ} (hk : k < m) :
    (2 * m - k : ℝ) * cRatio m (k + 1) = (m - k : ℝ) * cRatio m k := by
  dsimp [cRatio]
  have hpos : (Nat.choose (2 * m) m : ℝ) ≠ 0 := (choose_2n_n_pos m).ne'
  have hnat := choose_succ_sub_eq (a := 2 * m - (k + 1)) (m := m) (by omega)
  have ha1 : 2 * m - (k + 1) + 1 = 2 * m - k := by omega
  have ha2 : 2 * m - k - m = m - k := by omega
  rw [ha1] at hnat
  rw [ha2] at hnat
  have hcast : ((2 * m - k : ℕ) : ℝ) * (Nat.choose (2 * m - (k + 1)) m : ℝ) =
      (Nat.choose (2 * m - k) m : ℝ) * ((m - k : ℕ) : ℝ) := by exact_mod_cast hnat
  rw [Nat.cast_sub (by omega : k ≤ 2 * m), Nat.cast_sub (by omega : k ≤ m)] at hcast
  push_cast at hcast
  field_simp [hpos]
  linarith [hcast]

private lemma cRatio_succ_rel (n : ℕ) :
    ∀ k ≤ n, 2 * (n + 1 - k : ℝ) * (2 * n + 1 : ℝ) * cRatio (n + 1) k =
      (2 * n + 2 - k : ℝ) * (2 * n + 1 - k : ℝ) * cRatio n k
  | 0, _ => by
    simp only [Nat.cast_zero, sub_zero, cRatio_zero]
    ring
  | k + 1, hk => by
    have ih := cRatio_succ_rel n k (by omega)
    have hstep1 := cRatio_step (m := n + 1) (k := k) (by omega)
    have hstep0 := cRatio_step (m := n) (k := k) (by omega)
    have hk0r : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1r : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hnz1 : (2 * (n : ℝ) + 2 - k) ≠ 0 := by linarith
    have hnz0 : (2 * (n : ℝ) - k) ≠ 0 := by linarith
    have hstep1' : (2 * (n : ℝ) + 2 - k) * cRatio (n + 1) (k + 1) =
        ((n : ℝ) + 1 - k) * cRatio (n + 1) k := by
      push_cast at hstep1; linear_combination hstep1
    have hstep0' : (2 * (n : ℝ) - k) * cRatio n (k + 1) = ((n : ℝ) - k) * cRatio n k := hstep0
    push_cast at ih ⊢
    apply mul_left_cancel₀ (mul_ne_zero hnz1 hnz0)
    calc (2 * (n : ℝ) + 2 - k) * (2 * (n : ℝ) - k) *
          (2 * ((n : ℝ) + 1 - ((k : ℝ) + 1)) * (2 * (n : ℝ) + 1) * cRatio (n + 1) (k + 1))
        = (2 * (n : ℝ) - k) * (2 * ((n : ℝ) - k) * (2 * (n : ℝ) + 1)) *
            ((2 * (n : ℝ) + 2 - k) * cRatio (n + 1) (k + 1)) := by ring
      _ = (2 * (n : ℝ) - k) * (2 * ((n : ℝ) - k) * (2 * (n : ℝ) + 1)) *
            (((n : ℝ) + 1 - k) * cRatio (n + 1) k) := by rw [hstep1']
      _ = (2 * (n : ℝ) - k) * ((n : ℝ) - k) *
            (2 * ((n : ℝ) + 1 - k) * (2 * (n : ℝ) + 1) * cRatio (n + 1) k) := by ring
      _ = (2 * (n : ℝ) - k) * ((n : ℝ) - k) *
            ((2 * (n : ℝ) + 2 - k) * (2 * (n : ℝ) + 1 - k) * cRatio n k) := by rw [ih]
      _ = (2 * (n : ℝ) + 2 - k) * (2 * (n : ℝ) + 1 - k) * (2 * (n : ℝ) - k) *
            (((n : ℝ) - k) * cRatio n k) := by ring
      _ = (2 * (n : ℝ) + 2 - k) * (2 * (n : ℝ) + 1 - k) * (2 * (n : ℝ) - k) *
            ((2 * (n : ℝ) - k) * cRatio n (k + 1)) := by rw [← hstep0']
      _ = (2 * (n : ℝ) + 2 - k) * (2 * (n : ℝ) - k) *
            ((2 * (n : ℝ) + 2 - ((k : ℝ) + 1)) * (2 * (n : ℝ) + 1 - ((k : ℝ) + 1)) * cRatio n (k + 1)) := by ring

private lemma cRatio_pred_rel {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n - 1) :
    (2 * n - k : ℝ) * (2 * n - 1 - k : ℝ) * cRatio (n - 1) k =
      2 * (n - k : ℝ) * (2 * n - 1 : ℝ) * cRatio n k := by
  have h := cRatio_succ_rel (n - 1) k hk
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  have h1 : n - 1 + 1 = n := by omega
  rw [h1] at h
  rw [hn1] at h
  linarith [h]

private noncomputable def Snum (k n : ℕ) (β z : ℝ) : ℝ :=
  (k : ℝ) * (β^2*k*z - β^2*n*z - β^2*z - β*k^2*z - β*k^2 + β*k*n*z + 2*β*k*n + 2*β*k*z + β*k
      - β*n*z - 2*β*n - β*z + k^2*n*z + 3*k^2*n + k^2 - 2*k*n^2*z - 10*k*n^2
      - 2*k*n*z - 7*k*n - k + n^3*z + 8*n^3 + 2*n^2*z + 10*n^2 + n*z + 2*n)

private noncomputable def Sdisc (n k : ℕ) (β z : ℝ) : ℝ :=
  Snum k n β z /
    (((k : ℝ) - 2*n) * (β + n + 1) * ((k : ℝ) - 2*n - 2) * ((k : ℝ) - 2*n - 1))

private lemma Sdisc_eq_div (n k : ℕ) (β z : ℝ) :
    Sdisc n k β z = Snum k n β z /
      (((k : ℝ) - 2*n) * (β + n + 1) * ((k : ℝ) - 2*n - 2) * ((k : ℝ) - 2*n - 1)) := rfl

private noncomputable def Gdisc (n k : ℕ) (β z : ℝ) : ℝ :=
  if k = 0 ∨ n + 1 < k then 0 else Sdisc n k β z * padeTerm (n + 1) k β z

private lemma Sdisc_self_succ {n : ℕ} (hn : 2 ≤ n) {β z : ℝ} (hβ : β = 1 / 3 ∨ β = -1 / 3) :
    Sdisc n (n + 1) β z = -1 := by
  rw [Sdisc_eq_div]
  dsimp only [Snum]
  push_cast
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have d1 : ((n : ℝ) + 1 - 2 * n) ≠ 0 := by linarith
  have d2 : β + (n : ℝ) + 1 ≠ 0 := by
    have h := beta_sub_nat_ne_zero hβ (n + 1) 0
    push_cast at h
    intro h0; apply h; linarith
  have d3 : ((n : ℝ) + 1 - 2 * n - 2) ≠ 0 := by linarith
  have d4 : ((n : ℝ) + 1 - 2 * n - 1) ≠ 0 := by linarith
  have hd_nz := mul_ne_zero (mul_ne_zero (mul_ne_zero d1 d2) d3) d4
  rw [div_eq_iff hd_nz]
  ring

private lemma Xtilde_rec_term {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n + 1) {β z : ℝ}
    (hβ : β = 1 / 3 ∨ β = -1 / 3) :
    padeTerm (n + 1) k β z - (1 - z / 2) * padeTerm n k β z +
        ((n ^ 2 - β ^ 2) / (4 * (2 * n - 1) * (2 * n + 1))) * z ^ 2 * padeTerm (n - 1) k β z =
      Gdisc n (k + 1) β z - Gdisc n k β z := by
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hz_b1 : β + (n : ℝ) + 1 ≠ 0 := by
    have h := nat_add_beta_ne_zero hβ (n + 1); push_cast at h; intro h0; apply h; linarith
  have hz_nb1 : (n : ℝ) + 1 + β ≠ 0 := by
    intro h0; apply hz_b1; linarith
  have hz_b0 : β + (n : ℝ) ≠ 0 := by
    have h := nat_add_beta_ne_zero hβ n; push_cast at h; intro h0; apply h; linarith
  have hz_nb0 : (n : ℝ) + β ≠ 0 := by
    intro h0; apply hz_b0; linarith
  have hz_bk : (n : ℝ) + 1 + β - k ≠ 0 := by
    have h := beta_sub_nat_ne_zero hβ (n + 1) k; push_cast at h; intro h0; apply h; linarith
  have hz_2m1 : 2 * (n : ℝ) - 1 ≠ 0 := by linarith
  have hz_2p1 : 2 * (n : ℝ) + 1 ≠ 0 := by linarith
  by_cases hk0 : k = 0
  · subst hk0
    have hT1 : padeTerm (n + 1) 0 β z = 1 := by simp [padeTerm, gbinom, fall, cRatio_zero]
    have hT0 : padeTerm n 0 β z = 1 := by simp [padeTerm, gbinom, fall, cRatio_zero]
    have hTm : padeTerm (n - 1) 0 β z = 1 := by simp [padeTerm, gbinom, fall, cRatio_zero]
    have hG0 : Gdisc n 0 β z = 0 := by simp [Gdisc]
    have hG1 : Gdisc n 1 β z = Sdisc n 1 β z * padeTerm (n + 1) 1 β z := by
      unfold Gdisc; rw [if_neg (by omega)]
    have hT1_1 : padeTerm (n + 1) 1 β z = ((n : ℝ) + 1 + β) * (1 / 2) * (-z) := by
      have hcr := cRatio_step (m := n + 1) (k := 0) (by omega)
      simp only [Nat.cast_zero, sub_zero, cRatio_zero, mul_one] at hcr
      have hnz : (n : ℝ) + 1 ≠ 0 := by linarith
      have hc1 : cRatio (n + 1) 1 = 1 / 2 := by
        push_cast at hcr
        apply mul_left_cancel₀ hnz
        calc ((n : ℝ) + 1) * cRatio (n + 1) 1
            = (2 * ((n : ℝ) + 1) * cRatio (n + 1) 1) / 2 := by ring
          _ = ((n : ℝ) + 1) / 2 := by rw [hcr]
          _ = ((n : ℝ) + 1) * (1 / 2) := by ring
      simp only [padeTerm, show 1 ≤ n + 1 by omega, ↓reduceIte, gbinom, fall,
        Nat.factorial_one, Nat.cast_one, div_one, pow_one, hc1]
      push_cast
      ring
    rw [hT1, hT0, hTm, hG0, hG1, hT1_1, Sdisc_eq_div]
    push_cast
    have hden_s1 : ((1 : ℝ) - 2 * n) * (β + n + 1) * ((1 : ℝ) - 2 * n - 2) * ((1 : ℝ) - 2 * n - 1) =
        (-2) * n * (β + n + 1) * (2 * n - 1) * (2 * n + 1) := by ring
    rw [hden_s1]
    have hnp : (n : ℝ) ≠ 0 := by linarith
    have hz_2m1' : (n : ℝ) * 2 - 1 ≠ 0 := by linarith
    have hz_2p1' : (n : ℝ) * 2 + 1 ≠ 0 := by linarith
    field_simp [hnp, hz_b1, hz_2m1, hz_2p1, hz_2m1', hz_2p1']
    dsimp only [Snum]
    push_cast
    ring
  · by_cases hkn1 : k = n + 1
    · subst hkn1
      have hTn : padeTerm n (n + 1) β z = 0 := by simp [padeTerm]
      have hTm : padeTerm (n - 1) (n + 1) β z = 0 := by simp [padeTerm]
      have hGn2 : Gdisc n (n + 2) β z = 0 := by simp [Gdisc]
      have hGn1 : Gdisc n (n + 1) β z = Sdisc n (n + 1) β z * padeTerm (n + 1) (n + 1) β z := by
        unfold Gdisc; rw [if_neg (by omega)]
      rw [hTn, hTm, hGn2, hGn1, Sdisc_self_succ hn hβ]
      ring
    · have hk_le_n : k ≤ n := by omega
      have hkr : (k : ℝ) ≤ n := by exact_mod_cast hk_le_n
      have hk1pos : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hz_n1k : (n : ℝ) + 1 - k ≠ 0 := by linarith
      have hz_2nk : 2 * (n : ℝ) - k ≠ 0 := by linarith
      have hz_2nk1 : 2 * (n : ℝ) - 1 - k ≠ 0 := by linarith
      have hz_2nk2 : 2 * (n : ℝ) + 2 - k ≠ 0 := by linarith
      have hz_2nk1p : 2 * (n : ℝ) + 1 - k ≠ 0 := by linarith
      have hkp1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
      set U : ℝ := gbinom (n + β) k * cRatio n k * (-z) ^ k
      have hTn : padeTerm n k β z = U := by simp [padeTerm, hk_le_n, U]
      have hTp1 : padeTerm (n + 1) k β z =
          (((n + 1 + β) / (n + 1 + β - k)) *
            ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1)))) * U := by
        simp only [padeTerm, show k ≤ n + 1 by omega, ↓reduceIte]
        have hg := gbinom_succ_left (x := (n : ℝ) + β) (k := k) (by intro h0; apply hz_bk; linarith)
        have hcr := cRatio_succ_rel n k hk_le_n
        have hc : cRatio (n + 1) k =
            ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) * cRatio n k := by
          field_simp [hz_n1k, hz_2p1]
          linarith [hcr]
        rw [show ((n + 1 : ℕ) : ℝ) + β = (n : ℝ) + β + 1 by push_cast; ring, hg, hc]
        dsimp [U]; ring
      have hGk : Gdisc n k β z = Sdisc n k β z * padeTerm (n + 1) k β z := by
        unfold Gdisc; rw [if_neg (by omega)]
      have hGk1 : Gdisc n (k + 1) β z = Sdisc n (k + 1) β z * padeTerm (n + 1) (k + 1) β z := by
        unfold Gdisc; rw [if_neg (by omega)]
      have hTp1_succ : padeTerm (n + 1) (k + 1) β z =
          (-z) * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1))) * U := by
        simp only [padeTerm, show k + 1 ≤ n + 1 by omega, ↓reduceIte]
        have hg_step := gbinom_step_right ((n + 1 : ℕ) + β) k
        have hcr_step := cRatio_step (m := n + 1) (k := k) (by omega)
        have hc_step : cRatio (n + 1) (k + 1) = (((n : ℝ) + 1 - k) / (2 * (n : ℝ) + 2 - k)) * cRatio (n + 1) k := by
          push_cast at hcr_step
          apply mul_left_cancel₀ hz_2nk2
          calc (2 * (n : ℝ) + 2 - k) * cRatio (n + 1) (k + 1)
              = (2 * ((n : ℝ) + 1) - k) * cRatio (n + 1) (k + 1) := by ring
            _ = ((n : ℝ) + 1 - k) * cRatio (n + 1) k := hcr_step
            _ = (((n : ℝ) + 1 - k) / (2 * (n : ℝ) + 2 - k) * (2 * (n : ℝ) + 2 - k)) * cRatio (n + 1) k := by
                  rw [div_mul_cancel₀ _ hz_2nk2]
            _ = (2 * (n : ℝ) + 2 - k) * ((((n : ℝ) + 1 - k) / (2 * (n : ℝ) + 2 - k)) * cRatio (n + 1) k) := by ring
        rw [hg_step, hc_step, pow_succ]
        calc ((((n + 1 : ℕ) : ℝ) + β - k) / (k + 1) * gbinom ((n + 1 : ℕ) + β) k) *
              ((((n : ℝ) + 1 - k) / (2 * (n : ℝ) + 2 - k)) * cRatio (n + 1) k) * ((-z) ^ k * -z)
            = (-z) * (((((n + 1 : ℕ) : ℝ) + β - k) / (k + 1)) * (((n : ℝ) + 1 - k) / (2 * (n : ℝ) + 2 - k))) *
                padeTerm (n + 1) k β z := by
                simp only [padeTerm, show k ≤ n + 1 by omega, ↓reduceIte]; ring
          _ = (-z) * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1))) * U := by
                rw [hTp1]
                have hfrac : ((((n + 1 : ℕ) : ℝ) + β - k) / ((k : ℝ) + 1)) * (((n : ℝ) + 1 - k) / (2 * n + 2 - k)) *
                    (((n + 1 + β) / (n + 1 + β - k)) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1)))) =
                    ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1))) := by
                  have hP : (2 * ((n : ℝ) + 1 - k) * (2 * n + 1)) ≠ 0 :=
                    mul_ne_zero (mul_ne_zero (by norm_num) hz_n1k) hz_2p1
                  have hL : (((k : ℝ) + 1) * (2 * n + 2 - k)) * ((n + 1 + β - k) * (2 * (n + 1 - k) * (2 * n + 1))) ≠ 0 :=
                    mul_ne_zero (mul_ne_zero hkp1_ne hz_2nk2) (mul_ne_zero hz_bk hP)
                  have hR : ((k : ℝ) + 1) * (2 * (2 * n + 1)) ≠ 0 :=
                    mul_ne_zero hkp1_ne (mul_ne_zero (by norm_num) hz_2p1)
                  rw [div_mul_div_comm ((n : ℝ) + 1 + β), div_mul_div_comm ((((n + 1 : ℕ) : ℝ) + β - k)),
                    div_mul_div_comm _ (((k : ℝ) + 1) * (2 * n + 2 - k)),
                    div_mul_div_comm ((n : ℝ) + 1 + β), div_eq_div_iff hL hR]
                  push_cast; ring
                calc (-z) * (((((n + 1 : ℕ) : ℝ) + β - k) / (k + 1)) * (((n : ℝ) + 1 - k) / (2 * (n : ℝ) + 2 - k))) *
                      (((n + 1 + β) / (n + 1 + β - k) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1)))) * U)
                    = (-z) * ((((((n + 1 : ℕ) : ℝ) + β - k) / ((k : ℝ) + 1)) * (((n : ℝ) + 1 - k) / (2 * n + 2 - k))) *
                        (((n + 1 + β) / (n + 1 + β - k)) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))))) * U := by ring
                  _ = (-z) * (((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1)))) * U := by rw [hfrac]
                  _ = (-z) * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1))) * U := by ring
      by_cases hkn : k = n
      · have hTm : padeTerm (n - 1) k β z = 0 := by simp [padeTerm, show ¬ k ≤ n - 1 by omega]
        rw [hTp1, hTn, hTm, hGk1, hGk, hTp1, hTp1_succ, Sdisc_eq_div, Sdisc_eq_div]
        have hLHS_fac :
            ((n + 1 + β) / (n + 1 + β - k) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) * U -
              (1 - z / 2) * U + (n ^ 2 - β ^ 2) / (4 * (2 * n - 1) * (2 * n + 1)) * z ^ 2 * 0) =
            ((n + 1 + β) / (n + 1 + β - k) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) -
              (1 - z / 2)) * U := by ring
        have hRHS_fac :
            Snum (k + 1) n β z / (((k + 1 : ℕ) - 2 * n) * (β + n + 1) * ((k + 1 : ℕ) - 2 * n - 2) * ((k + 1 : ℕ) - 2 * n - 1)) *
                (-z * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1))) * U) -
              Snum k n β z / ((k - 2 * n) * (β + n + 1) * (k - 2 * n - 2) * (k - 2 * n - 1)) *
                ((n + 1 + β) / (n + 1 + β - k) *
                  ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) * U) =
            (Snum (k + 1) n β z / (((k + 1 : ℕ) - 2 * n) * (β + n + 1) * ((k + 1 : ℕ) - 2 * n - 2) * ((k + 1 : ℕ) - 2 * n - 1)) *
                (-z * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1)))) -
              Snum k n β z / ((k - 2 * n) * (β + n + 1) * (k - 2 * n - 2) * (k - 2 * n - 1)) *
                ((n + 1 + β) / (n + 1 + β - k) *
                  ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))))) * U := by ring
        rw [hLHS_fac, hRHS_fac]
        congr 1
        push_cast
        have hknr : (k : ℝ) = n := by exact_mod_cast hkn
        have d1 : ((k : ℝ) - (n : ℝ) * 2) ≠ 0 := by linarith
        have d2 : ((k : ℝ) - (n : ℝ) * 2 - 2) ≠ 0 := by linarith
        have d3 : ((k : ℝ) - (n : ℝ) * 2 - 1) ≠ 0 := by linarith
        have d4 : ((k : ℝ) + 1 - (n : ℝ) * 2) ≠ 0 := by linarith
        have d5 : ((k : ℝ) + 1 - (n : ℝ) * 2 - 2) ≠ 0 := by linarith
        have d6 : ((k : ℝ) + 1 - (n : ℝ) * 2 - 1) ≠ 0 := by linarith
        have hz_2p1' : (n : ℝ) * 2 + 1 ≠ 0 := by linarith
        field_simp [hz_b1, hz_nb1, hz_bk, hz_n1k, hz_2p1, hz_2p1', hkp1_ne, d1, d2, d3, d4, d5, d6]
        dsimp only [Snum]
        push_cast
        rw [hknr]
        ring
      · have hk_lt_n : k ≤ n - 1 := by omega
        have hk1r : (k : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : k + 1 ≤ n)
        have hn1c : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
        have hz_nbk : (n : ℝ) + β - k ≠ 0 := beta_sub_nat_ne_zero hβ n k
        have hTm : padeTerm (n - 1) k β z =
            (((n + β - k) / (n + β)) * (2 * (n - k) * (2 * n - 1) / ((2 * n - k) * (2 * n - 1 - k)))) * U := by
          simp only [padeTerm, hk_lt_n, ↓reduceIte]
          have hg' : gbinom ((n : ℝ) + β) k = (((n : ℝ) + β) / ((n : ℝ) + β - k)) * gbinom (((n - 1 : ℕ) : ℝ) + β) k := by
            have hnz_arg : ((n - 1 : ℕ) : ℝ) + β + 1 - k ≠ 0 := by
              rw [hn1c]; intro h0; apply hz_nbk; linarith
            have hg0 := gbinom_succ_left (x := ((n - 1 : ℕ) : ℝ) + β) (k := k) hnz_arg
            rw [show ((n - 1 : ℕ) : ℝ) + β + 1 = (n : ℝ) + β by rw [hn1c]; ring] at hg0
            exact hg0
          have hcr := cRatio_pred_rel (by omega : 1 ≤ n) hk_lt_n
          have hg_inv : gbinom (((n - 1 : ℕ) : ℝ) + β) k = ((n + β - k) / (n + β)) * gbinom (n + β) k := by
            apply mul_left_cancel₀ hz_nb0
            rw [hg']; field_simp [hz_nb0, hz_nbk]
          have hc_inv : cRatio (n - 1) k = (2 * (n - k) * (2 * n - 1) / ((2 * n - k) * (2 * n - 1 - k))) * cRatio n k := by
            have hden : (2 * (n : ℝ) - k) * (2 * n - 1 - k) ≠ 0 := mul_ne_zero hz_2nk hz_2nk1
            apply mul_left_cancel₀ hden
            calc ((2 * (n : ℝ) - k) * (2 * n - 1 - k)) * cRatio (n - 1) k
                = 2 * ((n : ℝ) - k) * (2 * n - 1) * cRatio n k := hcr
              _ = ((2 * ((n : ℝ) - k) * (2 * n - 1) / ((2 * (n : ℝ) - k) * (2 * n - 1 - k))) *
                    ((2 * (n : ℝ) - k) * (2 * n - 1 - k))) * cRatio n k := by
                  rw [div_mul_cancel₀ _ hden]
              _ = ((2 * (n : ℝ) - k) * (2 * n - 1 - k)) *
                    ((2 * (n - k) * (2 * n - 1) / ((2 * n - k) * (2 * n - 1 - k))) * cRatio n k) := by ring
          rw [hg_inv, hc_inv]; dsimp [U]; ring
        rw [hTp1, hTn, hTm, hGk1, hGk, hTp1, hTp1_succ, Sdisc_eq_div, Sdisc_eq_div]
        have hLHS_fac :
            ((n + 1 + β) / (n + 1 + β - k) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) * U -
              (1 - z / 2) * U +
              (n ^ 2 - β ^ 2) / (4 * (2 * n - 1) * (2 * n + 1)) * z ^ 2 *
                ((n + β - k) / (n + β) * (2 * (n - k) * (2 * n - 1) / ((2 * n - k) * (2 * n - 1 - k))) * U)) =
            ((n + 1 + β) / (n + 1 + β - k) * ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) -
              (1 - z / 2) +
              (n ^ 2 - β ^ 2) / (4 * (2 * n - 1) * (2 * n + 1)) * z ^ 2 *
                ((n + β - k) / (n + β) * (2 * (n - k) * (2 * n - 1) / ((2 * n - k) * (2 * n - 1 - k))))) * U := by ring
        have hRHS_fac :
            Snum (k + 1) n β z / (((k + 1 : ℕ) - 2 * n) * (β + n + 1) * ((k + 1 : ℕ) - 2 * n - 2) * ((k + 1 : ℕ) - 2 * n - 1)) *
                (-z * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1))) * U) -
              Snum k n β z / ((k - 2 * n) * (β + n + 1) * (k - 2 * n - 2) * (k - 2 * n - 1)) *
                ((n + 1 + β) / (n + 1 + β - k) *
                  ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))) * U) =
            (Snum (k + 1) n β z / (((k + 1 : ℕ) - 2 * n) * (β + n + 1) * ((k + 1 : ℕ) - 2 * n - 2) * ((k + 1 : ℕ) - 2 * n - 1)) *
                (-z * ((n + 1 + β) / (k + 1)) * ((2 * n + 1 - k) / (2 * (2 * n + 1)))) -
              Snum k n β z / ((k - 2 * n) * (β + n + 1) * (k - 2 * n - 2) * (k - 2 * n - 1)) *
                ((n + 1 + β) / (n + 1 + β - k) *
                  ((2 * n + 2 - k) * (2 * n + 1 - k) / (2 * (n + 1 - k) * (2 * n + 1))))) * U := by ring
        rw [hLHS_fac, hRHS_fac]
        congr 1
        push_cast
        have d1 : ((k : ℝ) - (n : ℝ) * 2) ≠ 0 := by linarith
        have d2 : ((k : ℝ) - (n : ℝ) * 2 - 2) ≠ 0 := by linarith
        have d3 : ((k : ℝ) - (n : ℝ) * 2 - 1) ≠ 0 := by linarith
        have d4 : ((k : ℝ) + 1 - (n : ℝ) * 2) ≠ 0 := by linarith
        have d5 : ((k : ℝ) + 1 - (n : ℝ) * 2 - 2) ≠ 0 := by linarith
        have d6 : ((k : ℝ) + 1 - (n : ℝ) * 2 - 1) ≠ 0 := by linarith
        have hz_2m1' : (n : ℝ) * 2 - 1 ≠ 0 := by linarith
        have hz_2p1' : (n : ℝ) * 2 + 1 ≠ 0 := by linarith
        have hz_2nk' : (n : ℝ) * 2 - k ≠ 0 := by linarith
        have hz_2nk1' : (n : ℝ) * 2 - 1 - k ≠ 0 := by linarith
        have hz_2nk2' : (n : ℝ) * 2 + 2 - k ≠ 0 := by linarith
        field_simp [hz_bk, hz_n1k, hz_2p1, hz_2p1', hz_2m1, hz_2m1', hz_b0, hz_nb0, hz_b1, hz_nb1,
          hz_2nk, hz_2nk', hz_2nk1, hz_2nk1', hz_2nk2, hz_2nk2', hkp1_ne, d1, d2, d3, d4, d5, d6]
        dsimp only [Snum]
        push_cast
        ring

theorem Xtilde_rec {n : ℕ} (hn : 1 ≤ n) {β z : ℝ} (hβ : β = 1 / 3 ∨ β = -1 / 3) :
    Xtilde (n + 1) β z =
      (1 - z / 2) * Xtilde n β z -
        ((9 * (n : ℝ) ^ 2 - 1) / (36 * (2 * n - 1) * (2 * n + 1))) * z ^ 2 * Xtilde (n - 1) β z := by
  have hβsq : ((n : ℝ) ^ 2 - β ^ 2) / (4 * (2 * n - 1) * (2 * n + 1)) =
      (9 * (n : ℝ) ^ 2 - 1) / (36 * (2 * n - 1) * (2 * n + 1)) := by
    have h9b : 9 * β ^ 2 = 1 := by rcases hβ with rfl | rfl <;> ring
    have d : 36 * (2 * (n : ℝ) - 1) * (2 * n + 1) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have d4 : 4 * (2 * (n : ℝ) - 1) * (2 * n + 1) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    rcases hβ with rfl | rfl <;> field_simp [d, d4] <;> ring
  rw [← hβsq]
  rcases eq_or_lt_of_le hn with rfl | hn2
  · rw [Xtilde, Xtilde, Xtilde]
    rw [show (1 + 1 + 1 : ℕ) = 3 by rfl, show (1 - 1 : ℕ) = 0 by rfl]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    rw [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    simp only [padeTerm, Nat.zero_le, le_rfl, show (1 : ℕ) ≤ 2 by omega, ↓reduceIte,
      gbinom, fall, Nat.factorial_zero, Nat.factorial_one,
      cRatio_zero, pow_zero, pow_one, mul_one, one_mul, zero_add]
    have c1_1 : cRatio 1 1 = 1 / 2 := by
      have := cRatio_step (m := 1) (k := 0) (by omega)
      rw [cRatio_zero] at this; norm_num at this; linarith
    have c2_1 : cRatio 2 1 = 1 / 2 := by
      have := cRatio_step (m := 2) (k := 0) (by omega)
      rw [cRatio_zero] at this; norm_num at this; linarith
    have c2_2 : cRatio 2 2 = 1 / 6 := by
      have := cRatio_step (m := 2) (k := 1) (by omega)
      rw [c2_1] at this; norm_num at this; linarith
    rw [c1_1, c2_1, c2_2]
    rcases hβ with rfl | rfl <;> (norm_num; try ring)
  · have hsum := Finset.sum_congr (rfl : Finset.range (n + 2) = Finset.range (n + 2))
      fun k hk => Xtilde_rec_term hn2 (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) (z := z) hβ
    have htel : ∑ k ∈ Finset.range (n + 2), (Gdisc n (k + 1) β z - Gdisc n k β z) =
        Gdisc n (n + 2) β z - Gdisc n 0 β z :=
      Finset.sum_range_sub (fun k => Gdisc n k β z) (n + 2)
    have hG0 : Gdisc n 0 β z = 0 := by simp [Gdisc]
    have hGn2 : Gdisc n (n + 2) β z = 0 := by simp [Gdisc]
    rw [htel, hG0, hGn2, sub_self] at hsum
    have hsplit1 : ∑ k ∈ Finset.range (n + 2), padeTerm n k β z = Xtilde n β z := by
      rw [Finset.sum_range_succ]
      simp [Xtilde, padeTerm]
    have hsplitm : ∑ k ∈ Finset.range (n + 2), padeTerm (n - 1) k β z = Xtilde (n - 1) β z := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hp1 : padeTerm (n - 1) (n + 1) β z = 0 := by simp [padeTerm, show ¬ n + 1 ≤ n - 1 by omega]
      have hp0 : padeTerm (n - 1) n β z = 0 := by simp [padeTerm, show ¬ n ≤ n - 1 by omega]
      rw [hp1, hp0, add_zero, add_zero, Xtilde, show n - 1 + 1 = n by omega]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    rw [show ∑ k ∈ Finset.range (n + 2), padeTerm (n + 1) k β z = Xtilde (n + 1) β z from rfl,
      hsplit1, hsplitm] at hsum
    linarith

noncomputable def Wtilde (n : ℕ) (z : ℝ) : ℝ :=
  Ptilde (n + 1) z * Qtilde n z - Ptilde n z * Qtilde (n + 1) z

private lemma Xtilde_zero (β z : ℝ) : Xtilde 0 β z = 1 := by
  dsimp only [Xtilde]
  rw [Finset.sum_range_one]
  simp [padeTerm, gbinom, fall, cRatio_zero]

private lemma Xtilde_one (β z : ℝ) : Xtilde 1 β z = 1 - ((1 + β) / 2) * z := by
  dsimp only [Xtilde]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [padeTerm, Nat.zero_le, le_rfl, ↓reduceIte, cRatio_zero, gbinom, fall,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, pow_zero, pow_one, mul_one,
    one_mul]
  have hc11 : cRatio 1 1 = 1 / 2 := by
    have := cRatio_step (m := 1) (k := 0) (by omega)
    rw [cRatio_zero] at this; norm_num at this; linarith
  rw [hc11]
  push_cast
  ring

private lemma Wtilde_zero (z : ℝ) : Wtilde 0 z = -(1 / 3) * z := by
  dsimp only [Wtilde, Ptilde, Qtilde]
  rw [Xtilde_one, Xtilde_zero, Xtilde_zero, Xtilde_one]
  norm_num
  ring

private lemma Wtilde_step {n : ℕ} (hn : 1 ≤ n) (z : ℝ) :
    Wtilde n z = ((9 * (n : ℝ) ^ 2 - 1) / (36 * (2 * n - 1) * (2 * n + 1))) * z ^ 2 * Wtilde (n - 1) z := by
  dsimp only [Wtilde]
  have hP := Xtilde_rec hn (β := 1 / 3) (z := z) (Or.inl rfl)
  have hQ := Xtilde_rec hn (β := -1 / 3) (z := z) (Or.inr rfl)
  dsimp only [Ptilde] at *; dsimp only [Qtilde] at *
  have hns : n - 1 + 1 = n := by omega
  rw [hns, hP, hQ]
  ring

private lemma Wtilde_ne_zero : ∀ (n : ℕ) {z : ℝ}, z ≠ 0 → Wtilde n z ≠ 0
  | 0, z, hz => by rw [Wtilde_zero]; exact mul_ne_zero (by norm_num) hz
  | n + 1, z, hz => by
    rw [Wtilde_step (by omega) z, Nat.add_sub_cancel]
    have ih := Wtilde_ne_zero n hz
    have hc_pos : (9 * ((n + 1 : ℕ) : ℝ) ^ 2 - 1) / (36 * (2 * (n + 1 : ℕ) - 1) * (2 * (n + 1 : ℕ) + 1)) ≠ 0 := by
      push_cast
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hnum : (9 * ((n : ℝ) + 1) ^ 2 - 1) > 0 := by nlinarith
      have hden : 36 * (2 * ((n : ℝ) + 1) - 1) * (2 * ((n : ℝ) + 1) + 1) > 0 := by nlinarith
      exact div_ne_zero hnum.ne' hden.ne'
    exact mul_ne_zero (mul_ne_zero hc_pos (pow_ne_zero 2 hz)) ih

theorem Ppoly_Qpoly_det_ne_zero :
    ∀ (n : ℕ) {z : ℝ}, z ≠ 0 → Ppoly (n + 1) z * Qpoly n z - Ppoly n z * Qpoly (n + 1) z ≠ 0 := by
  intro n z hz
  dsimp only [Ppoly, Qpoly]
  have heq : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * Ptilde (n + 1) z * ((Nat.choose (2 * n) n : ℝ) * Qtilde n z) -
      (Nat.choose (2 * n) n : ℝ) * Ptilde n z * ((Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * Qtilde (n + 1) z) =
      (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * (Nat.choose (2 * n) n : ℝ) * Wtilde n z := by
    dsimp [Wtilde]; ring
  rw [heq]
  exact mul_ne_zero (mul_ne_zero (choose_2n_n_pos (n + 1)).ne' (choose_2n_n_pos n).ne') (Wtilde_ne_zero n hz)

/-! ## 2. Exact Euler Integral Representation and Elementary Remainder Bound -/

noncomputable def wInt (n : ℕ) (z t : ℝ) : ℝ :=
  t ^ n * (1 - t) ^ n * (1 - t * z) ^ (-(n : ℝ) - 2 / 3)

noncomputable def Jint (n : ℕ) (z : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, wInt n z t

noncomputable def cPad : ℕ → ℝ
  | 0 => 1 / 3
  | n + 1 => cPad n * ((3 * (n : ℝ) + 2) * (3 * (n : ℝ) + 4) / (9 * ((n : ℝ) + 1) ^ 2))

noncomputable def Erem (n : ℕ) (z : ℝ) : ℝ :=
  cPad n * z ^ (2 * n + 1) * Jint n z

noncomputable def Etilde (n : ℕ) (z : ℝ) : ℝ :=
  Erem n z / (Nat.choose (2 * n) n : ℝ)

private lemma cPad_bounds : ∀ n : ℕ, 0 < cPad n ∧ cPad n ≤ 1 / 3
  | 0 => by norm_num [cPad]
  | n + 1 => by
    obtain ⟨h0, h1⟩ := cPad_bounds n
    dsimp [cPad]
    have hratio0 : 0 < (3 * (n : ℝ) + 2) * (3 * (n : ℝ) + 4) / (9 * ((n : ℝ) + 1) ^ 2) := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      positivity
    have hratio1 : (3 * (n : ℝ) + 2) * (3 * (n : ℝ) + 4) / (9 * ((n : ℝ) + 1) ^ 2) ≤ 1 := by
      have hden : 0 < 9 * ((n : ℝ) + 1) ^ 2 := by positivity
      rw [div_le_one hden]
      nlinarith
    exact ⟨mul_pos h0 hratio0, by nlinarith⟩

private lemma one_sub_mul_pos {z t : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 - t * z := by
  have htz : t * z ≤ 1 * z := mul_le_mul_of_nonneg_right ht.2 hz0.le
  linarith

private lemma wInt_continuousOn (n : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ContinuousOn (wInt n z) (Set.Icc 0 1) := by
  unfold wInt
  refine ContinuousOn.mul (ContinuousOn.mul (continuousOn_pow n) ((continuousOn_const.sub continuousOn_id).pow n)) ?_
  have hlin : ContinuousOn (fun t : ℝ => 1 - t * z) (Set.Icc 0 1) :=
    continuousOn_const.sub (continuousOn_id.mul continuousOn_const)
  refine hlin.rpow continuousOn_const ?_
  intro t ht
  exact Or.inl (one_sub_mul_pos hz0 hz1 ht).ne'

private lemma wInt_intervalIntegrable (n : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    IntervalIntegrable (wInt n z) MeasureTheory.volume 0 1 := by
  have hc := wInt_continuousOn n hz0 hz1
  rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hc
  exact hc.intervalIntegrable

private lemma hlin_deriv (z t : ℝ) : HasDerivAt (fun s => 1 - s * z) (-z) t := by
  simpa using ((hasDerivAt_id t).mul_const z).const_sub 1

private noncomputable def H0 (z t : ℝ) : ℝ :=
  -(3 / z) * (1 - t * z) ^ ((1 : ℝ) / 3)

private lemma H0_hasDerivAt {z t : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (H0 z) (wInt 0 z t) t := by
  have hpos := one_sub_mul_pos hz0 hz1 ht
  have hrp : HasDerivAt (fun s => -(3 / z) * (1 - s * z) ^ ((1 : ℝ) / 3))
      (-(3 / z) * (-z * ((1 : ℝ) / 3) * (1 - t * z) ^ ((1 : ℝ) / 3 - 1))) t :=
    ((hlin_deriv z t).rpow_const (Or.inl hpos.ne')).const_mul (-(3 / z))
  have hze : z ≠ 0 := hz0.ne'
  have hz3 : -(3 / z) * (-z * ((1 : ℝ) / 3)) = 1 := by field_simp
  have hexp : (1 : ℝ) / 3 - 1 = -((0 : ℕ) : ℝ) - 2 / 3 := by norm_num
  have hval : -(3 / z) * (-z * ((1 : ℝ) / 3) * (1 - t * z) ^ ((1 : ℝ) / 3 - 1)) = wInt 0 z t := by
    unfold wInt
    rw [← hexp, pow_zero, pow_zero, one_mul, one_mul]
    calc -(3 / z) * (-z * ((1 : ℝ) / 3) * (1 - t * z) ^ ((1 : ℝ) / 3 - 1))
        = (-(3 / z) * (-z * ((1 : ℝ) / 3))) * (1 - t * z) ^ ((1 : ℝ) / 3 - 1) := by ring
      _ = (1 - t * z) ^ ((1 : ℝ) / 3 - 1) := by rw [hz3, one_mul]
  exact hval ▸ hrp

private lemma Etilde_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Etilde 0 z = Ptilde 0 z - (1 - z) ^ ((1 : ℝ) / 3) * Qtilde 0 z := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (H0 z) (wInt 0 z t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact H0_hasDerivAt hz0 hz1 ht
  have hJ : Jint 0 z = H0 z 1 - H0 z 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (wInt_intervalIntegrable 0 hz0 hz1)
  have hE0 : Erem 0 z = 1 - (1 - z) ^ ((1 : ℝ) / 3) := by
    show cPad 0 * z ^ (2 * 0 + 1) * Jint 0 z = _
    rw [hJ]
    unfold H0
    rw [show cPad 0 = 1 / 3 from rfl, show (1 : ℝ) - 0 * z = 1 by ring, Real.one_rpow,
      show (1 : ℝ) - 1 * z = 1 - z by ring, show 2 * 0 + 1 = 1 by rfl, pow_one]
    have hze : z ≠ 0 := hz0.ne'
    field_simp
    ring
  unfold Etilde Ptilde Qtilde
  rw [hE0, Xtilde_zero, Xtilde_zero]
  norm_num

private noncomputable def poly1 (z t : ℝ) : ℝ :=
  t ^ 2 * z ^ 2 - 4 * t * z ^ 2 + 6 * t * z + 6 * z - 9

private noncomputable def H1 (z t : ℝ) : ℝ :=
  (2 / 9) * poly1 z t * (1 - t * z) ^ (-(2 : ℝ) / 3)

private lemma H1_hasDerivAt {z t : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (H1 z) ((8 / 27) * z ^ 3 * wInt 1 z t) t := by
  have hpos := one_sub_mul_pos hz0 hz1 ht
  have h1 : HasDerivAt (fun s => s ^ 2 * z ^ 2) ((2 * t ^ (2 - 1)) * z ^ 2) t :=
    (hasDerivAt_pow 2 t).mul_const (z ^ 2)
  have h2 : HasDerivAt (fun s => 4 * s * z ^ 2) ((4 * 1) * z ^ 2) t :=
    ((hasDerivAt_id t).const_mul 4).mul_const (z ^ 2)
  have h3 : HasDerivAt (fun s => 6 * s * z) ((6 * 1) * z) t :=
    ((hasDerivAt_id t).const_mul 6).mul_const z
  have h4 : HasDerivAt (fun s => s ^ 2 * z ^ 2 - 4 * s * z ^ 2 + 6 * s * z + 6 * z - 9)
      (((2 * t ^ (2 - 1)) * z ^ 2 - (4 * 1) * z ^ 2 + (6 * 1) * z)) t :=
    (((h1.sub h2).add h3).add_const (6 * z)).sub_const 9
  have hpol : HasDerivAt (fun s => (2 / 9) * poly1 z s)
      ((2 / 9) * (2 * t * z ^ 2 - 4 * z ^ 2 + 6 * z)) t :=
    (h4.const_mul (2 / 9 : ℝ)).congr_deriv (by ring)
  have hrp : HasDerivAt (fun s => (1 - s * z) ^ (-(2 : ℝ) / 3))
      (-z * (-(2 : ℝ) / 3) * (1 - t * z) ^ (-(2 : ℝ) / 3 - 1)) t :=
    (hlin_deriv z t).rpow_const (Or.inl hpos.ne')
  have hprod : HasDerivAt (H1 z)
      ((2 / 9) * (2 * t * z ^ 2 - 4 * z ^ 2 + 6 * z) * (1 - t * z) ^ (-(2 : ℝ) / 3) +
        (2 / 9) * poly1 z t * (-z * (-(2 : ℝ) / 3) * (1 - t * z) ^ (-(2 : ℝ) / 3 - 1))) t :=
    hpol.mul hrp
  have hpow_rel : (1 - t * z) ^ (-(2 : ℝ) / 3) = (1 - t * z) * (1 - t * z) ^ (-(5 : ℝ) / 3) := by
    have heq : (-(2 : ℝ) / 3) = 1 + (-(5 : ℝ) / 3) := by norm_num
    rw [heq, Real.rpow_add hpos, Real.rpow_one]
  have hpow_e : (-(2 : ℝ) / 3 - 1) = -(5 : ℝ) / 3 := by norm_num
  have hpow_w : (-((1 : ℕ) : ℝ) - 2 / 3) = -(5 : ℝ) / 3 := by norm_num
  have hval : (2 / 9) * (2 * t * z ^ 2 - 4 * z ^ 2 + 6 * z) * (1 - t * z) ^ (-(2 : ℝ) / 3) +
      (2 / 9) * poly1 z t * (-z * (-(2 : ℝ) / 3) * (1 - t * z) ^ (-(2 : ℝ) / 3 - 1)) =
      (8 / 27) * z ^ 3 * wInt 1 z t := by
    unfold poly1 wInt
    rw [hpow_e, hpow_w, hpow_rel]
    ring
  exact hval ▸ hprod

private lemma Etilde_one {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Etilde 1 z = Ptilde 1 z - (1 - z) ^ ((1 : ℝ) / 3) * Qtilde 1 z := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (H1 z) ((8 / 27) * z ^ 3 * wInt 1 z t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact H1_hasDerivAt hz0 hz1 ht
  have hint : IntervalIntegrable (fun t => (8 / 27) * z ^ 3 * wInt 1 z t) MeasureTheory.volume 0 1 :=
    (wInt_intervalIntegrable 1 hz0 hz1).const_mul ((8 / 27) * z ^ 3)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  have hc1 : cPad 1 = 8 / 27 := by dsimp [cPad]; norm_num
  have h1z_pos : 0 < 1 - z := by linarith
  have hrp1 : (1 - z) * (1 - z) ^ (-(2 : ℝ) / 3) = (1 - z) ^ ((1 : ℝ) / 3) := by
    have heq : (1 : ℝ) / 3 = 1 + (-(2 : ℝ) / 3) := by norm_num
    rw [heq, Real.rpow_add h1z_pos, Real.rpow_one]
  have hJ : (8 / 27) * z ^ 3 * Jint 1 z = H1 z 1 - H1 z 0 := hftc
  have hE1 : Erem 1 z = (2 - (4 / 3) * z) - (1 - z) ^ ((1 : ℝ) / 3) * (2 - (2 / 3) * z) := by
    show cPad 1 * z ^ (2 * 1 + 1) * Jint 1 z = _
    rw [hc1, show 2 * 1 + 1 = 3 by rfl, hJ]
    unfold H1 poly1
    rw [show (1 : ℝ) - 0 * z = 1 by ring, Real.one_rpow, show (1 : ℝ) - 1 * z = 1 - z by ring]
    calc (2 / 9) * ((1 : ℝ) ^ 2 * z ^ 2 - 4 * 1 * z ^ 2 + 6 * 1 * z + 6 * z - 9) * (1 - z) ^ (-(2 : ℝ) / 3) -
          (2 / 9) * ((0 : ℝ) ^ 2 * z ^ 2 - 4 * 0 * z ^ 2 + 6 * 0 * z + 6 * z - 9) * 1
        = (-2 / 3) * (3 - z) * ((1 - z) * (1 - z) ^ (-(2 : ℝ) / 3)) - ((4 / 3) * z - 2) := by ring
      _ = (-2 / 3) * (3 - z) * (1 - z) ^ ((1 : ℝ) / 3) - ((4 / 3) * z - 2) := by rw [hrp1]
      _ = (2 - (4 / 3) * z) - (1 - z) ^ ((1 : ℝ) / 3) * (2 - (2 / 3) * z) := by ring
  unfold Etilde Ptilde Qtilde
  rw [hE1, Xtilde_one, Xtilde_one, show Nat.choose (2 * 1) 1 = 2 by decide]
  norm_num
  ring

private noncomputable def Qcont (m : ℕ) (z t : ℝ) : ℝ :=
  9 * ((m : ℝ) + 2) - (18 * ((m : ℝ) + 2) - 3 * z) * t + (9 * ((m : ℝ) + 1) + 6) * z * t ^ 2

private noncomputable def QcontDeriv (m : ℕ) (z t : ℝ) : ℝ :=
  -(18 * ((m : ℝ) + 2) - 3 * z) + 2 * (9 * ((m : ℝ) + 1) + 6) * z * t

private noncomputable def Gcont (m : ℕ) (z t : ℝ) : ℝ :=
  wInt (m + 1) z t * Qcont m z t

private lemma Gcont_hasDerivAt (m : ℕ) {z t : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (Gcont m z)
      (z ^ 2 * (3 * (m + 1 : ℝ) + 2) * (3 * (m + 1 : ℝ) + 4) * wInt (m + 2) z t +
        9 * ((m + 1 : ℝ) + 1) * (2 * (m + 1 : ℝ) + 1) * (z - 2) * wInt (m + 1) z t +
        9 * (m + 1 : ℝ) * ((m + 1 : ℝ) + 1) * wInt m z t) t := by
  have hpos := one_sub_mul_pos hz0 hz1 ht
  have hw1 : HasDerivAt (fun s : ℝ => s ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * t ^ (m + 1 - 1)) t :=
    hasDerivAt_pow (m + 1) t
  have hsub : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 1
  have hw2 : HasDerivAt (fun s : ℝ => (1 - s) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (1 - t) ^ (m + 1 - 1) * (-1)) t :=
    hsub.pow (m + 1)
  have hw3 : HasDerivAt (fun s : ℝ => (1 - s * z) ^ (-((m + 1 : ℕ) : ℝ) - 2 / 3))
      (-z * (-((m + 1 : ℕ) : ℝ) - 2 / 3) * (1 - t * z) ^ (-((m + 1 : ℕ) : ℝ) - 2 / 3 - 1)) t :=
    (hlin_deriv z t).rpow_const (Or.inl hpos.ne')
  have hQ : HasDerivAt (fun s => Qcont m z s) (QcontDeriv m z t) t := by
    have h1 : HasDerivAt (fun s : ℝ => (18 * ((m : ℝ) + 2) - 3 * z) * s)
        ((18 * ((m : ℝ) + 2) - 3 * z) * 1) t := (hasDerivAt_id t).const_mul _
    have h2 : HasDerivAt (fun s : ℝ => (9 * ((m : ℝ) + 1) + 6) * z * s ^ 2)
        ((9 * ((m : ℝ) + 1) + 6) * z * (↑2 * t ^ (2 - 1))) t := (hasDerivAt_pow 2 t).const_mul _
    exact ((h1.const_sub (9 * ((m : ℝ) + 2))).add h2).congr_deriv (by
      unfold QcontDeriv; push_cast; ring)
  have hG : HasDerivAt (Gcont m z)
      (((((m + 1 : ℕ) : ℝ) * t ^ (m + 1 - 1) * (1 - t) ^ (m + 1) +
            t ^ (m + 1) * (((m + 1 : ℕ) : ℝ) * (1 - t) ^ (m + 1 - 1) * (-1))) *
          (1 - t * z) ^ (-((m + 1 : ℕ) : ℝ) - 2 / 3) +
          t ^ (m + 1) * (1 - t) ^ (m + 1) *
            (-z * (-((m + 1 : ℕ) : ℝ) - 2 / 3) * (1 - t * z) ^ (-((m + 1 : ℕ) : ℝ) - 2 / 3 - 1))) *
        Qcont m z t +
        (t ^ (m + 1) * (1 - t) ^ (m + 1) * (1 - t * z) ^ (-((m + 1 : ℕ) : ℝ) - 2 / 3)) * QcontDeriv m z t) t :=
    ((hw1.mul hw2).mul hw3).mul hQ
  refine hG.congr_deriv ?_
  set E : ℝ := (1 - t * z) ^ (-((m + 1 : ℕ) : ℝ) - 5 / 3)
  set T : ℝ := t ^ m * (1 - t) ^ m * E
  have hpm1 : -((m + 1 : ℕ) : ℝ) - 2 / 3 - 1 = -((m + 1 : ℕ) : ℝ) - 5 / 3 := by ring
  have hrp1 : (1 - t * z) ^ (-((m + 1 : ℕ) : ℝ) - 2 / 3) = (1 - t * z) * E := by
    have heq : -((m + 1 : ℕ) : ℝ) - 2 / 3 = 1 + (-((m + 1 : ℕ) : ℝ) - 5 / 3) := by ring
    rw [heq, Real.rpow_add hpos, Real.rpow_one]
  have hrp0 : (1 - t * z) ^ (-(m : ℝ) - 2 / 3) = (1 - t * z) ^ 2 * E := by
    have heq : -(m : ℝ) - 2 / 3 = (1 + 1 : ℝ) + (-((m + 1 : ℕ) : ℝ) - 5 / 3) := by push_cast; ring
    rw [heq, Real.rpow_add hpos, Real.rpow_add hpos, Real.rpow_one]
    dsimp only [E]
    ring
  have hrp2 : (1 - t * z) ^ (-((m + 2 : ℕ) : ℝ) - 2 / 3) = E := by
    have heq : -((m + 2 : ℕ) : ℝ) - 2 / 3 = -((m + 1 : ℕ) : ℝ) - 5 / 3 := by push_cast; ring
    rw [heq]
  have hw_m2 : wInt (m + 2) z t = t ^ 2 * (1 - t) ^ 2 * T := by
    unfold wInt
    rw [hrp2]
    calc t ^ (m + 2) * (1 - t) ^ (m + 2) * E
        = (t ^ 2 * t ^ m) * ((1 - t) ^ 2 * (1 - t) ^ m) * E := by rw [pow_add, pow_add]; ring
      _ = t ^ 2 * (1 - t) ^ 2 * T := by dsimp [T]; ring
  have hw_m1 : wInt (m + 1) z t = t * (1 - t) * (1 - t * z) * T := by
    unfold wInt
    rw [hrp1]
    calc t ^ (m + 1) * (1 - t) ^ (m + 1) * ((1 - t * z) * E)
        = (t * t ^ m) * ((1 - t) * (1 - t) ^ m) * ((1 - t * z) * E) := by rw [pow_succ', pow_succ']
      _ = t * (1 - t) * (1 - t * z) * T := by dsimp [T]; ring
  have hw_m0 : wInt m z t = (1 - t * z) ^ 2 * T := by
    unfold wInt
    rw [hrp0]
    dsimp [T]; ring
  rw [hpm1, hrp1, hw_m2, hw_m1, hw_m0, Nat.add_sub_cancel]
  have hp_lhs :
      ((((m + 1 : ℕ) : ℝ) * t ^ m * (1 - t) ^ (m + 1) + t ^ (m + 1) * (((m + 1 : ℕ) : ℝ) * (1 - t) ^ m * (-1))) *
          ((1 - t * z) * E) +
        t ^ (m + 1) * (1 - t) ^ (m + 1) * ((-z) * (-((m + 1 : ℕ) : ℝ) - 2 / 3) * E)) * Qcont m z t +
      (t ^ (m + 1) * (1 - t) ^ (m + 1) * ((1 - t * z) * E)) * QcontDeriv m z t =
      ((((m : ℝ) + 1) * (1 - t) * (1 - t * z) - ((m : ℝ) + 1) * t * (1 - t * z) +
          ((m : ℝ) + 1 + 2 / 3) * z * t * (1 - t)) * Qcont m z t +
        t * (1 - t) * (1 - t * z) * QcontDeriv m z t) * T := by
    rw [pow_succ' t m, pow_succ' (1 - t) m]
    dsimp [T]
    push_cast
    ring
  rw [hp_lhs]
  have hpoly :
      ((((m : ℝ) + 1) * (1 - t) * (1 - t * z) - ((m : ℝ) + 1) * t * (1 - t * z) +
          ((m : ℝ) + 1 + 2 / 3) * z * t * (1 - t)) * Qcont m z t +
        t * (1 - t) * (1 - t * z) * QcontDeriv m z t) =
      z ^ 2 * (3 * (m + 1 : ℝ) + 2) * (3 * (m + 1 : ℝ) + 4) * (t ^ 2 * (1 - t) ^ 2) +
        9 * ((m + 1 : ℝ) + 1) * (2 * (m + 1 : ℝ) + 1) * (z - 2) * (t * (1 - t) * (1 - t * z)) +
        9 * (m + 1 : ℝ) * ((m + 1 : ℝ) + 1) * (1 - t * z) ^ 2 := by
    unfold Qcont QcontDeriv
    ring
  rw [hpoly]
  ring

private lemma Jint_rec (m : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    z ^ 2 * (3 * (m + 1 : ℝ) + 2) * (3 * (m + 1 : ℝ) + 4) * Jint (m + 2) z +
      9 * ((m + 1 : ℝ) + 1) * (2 * (m + 1 : ℝ) + 1) * (z - 2) * Jint (m + 1) z +
      9 * (m + 1 : ℝ) * ((m + 1 : ℝ) + 1) * Jint m z = 0 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (Gcont m z)
      (z ^ 2 * (3 * (m + 1 : ℝ) + 2) * (3 * (m + 1 : ℝ) + 4) * wInt (m + 2) z t +
        9 * ((m + 1 : ℝ) + 1) * (2 * (m + 1 : ℝ) + 1) * (z - 2) * wInt (m + 1) z t +
        9 * (m + 1 : ℝ) * ((m + 1 : ℝ) + 1) * wInt m z t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact Gcont_hasDerivAt m hz0 hz1 ht
  have i2 := (wInt_intervalIntegrable (m + 2) hz0 hz1).const_mul
    (z ^ 2 * (3 * (m + 1 : ℝ) + 2) * (3 * (m + 1 : ℝ) + 4))
  have i1 := (wInt_intervalIntegrable (m + 1) hz0 hz1).const_mul
    (9 * ((m + 1 : ℝ) + 1) * (2 * (m + 1 : ℝ) + 1) * (z - 2))
  have i0 := (wInt_intervalIntegrable m hz0 hz1).const_mul
    (9 * (m + 1 : ℝ) * ((m + 1 : ℝ) + 1))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((i2.add i1).add i0)
  have hG0 : Gcont m z 0 = 0 := by
    unfold Gcont wInt
    simp
  have hG1 : Gcont m z 1 = 0 := by
    unfold Gcont wInt
    simp
  rw [hG0, hG1, sub_self] at hftc
  rw [intervalIntegral.integral_add (i2.add i1) i0, intervalIntegral.integral_add i2 i1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hftc
  exact hftc

private lemma choose_two_mul_succ (k : ℕ) :
    (k + 1) * Nat.choose (2 * (k + 1)) (k + 1) = 2 * (2 * k + 1) * Nat.choose (2 * k) k := by
  have h1 : (2 * k + 2) * Nat.choose (2 * k + 1) k = Nat.choose (2 * k + 2) (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (2 * k + 1) k
  have h2 : (2 * k + 1) * Nat.choose (2 * k) k = Nat.choose (2 * k + 1) k * (k + 1) := by
    have hsym : Nat.choose (2 * k + 1) (k + 1) = Nat.choose (2 * k + 1) k := by
      rw [← Nat.choose_symm (by omega : k ≤ 2 * k + 1)]
      congr 1; omega
    have hstep := Nat.add_one_mul_choose_eq (2 * k) k
    rw [hsym] at hstep; exact hstep
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, mul_comm (k + 1)]
  calc Nat.choose (2 * k + 2) (k + 1) * (k + 1)
      = (2 * k + 2) * Nat.choose (2 * k + 1) k := h1.symm
    _ = 2 * (Nat.choose (2 * k + 1) k * (k + 1)) := by ring
    _ = 2 * ((2 * k + 1) * Nat.choose (2 * k) k) := by rw [← h2]
    _ = 2 * (2 * k + 1) * Nat.choose (2 * k) k := by ring

private lemma Etilde_rec (m : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Etilde (m + 2) z =
      (1 - z / 2) * Etilde (m + 1) z -
        ((9 * ((m + 1 : ℕ) : ℝ) ^ 2 - 1) / (36 * (2 * (m + 1 : ℕ) - 1) * (2 * (m + 1 : ℕ) + 1))) *
          z ^ 2 * Etilde m z := by
  have hrec := Jint_rec m hz0 hz1
  set n := m + 1
  have hc1 : cPad (m + 1) =
      cPad m * ((3 * (m : ℝ) + 2) * (3 * m + 4) / (9 * ((m : ℝ) + 1) ^ 2)) := rfl
  have hc2 : cPad (m + 2) =
      cPad (m + 1) * ((3 * ((m + 1 : ℕ) : ℝ) + 2) * (3 * (m + 1 : ℕ) + 4) / (9 * (((m + 1 : ℕ) : ℝ) + 1) ^ 2)) := rfl
  have hch1 : ((m + 1 : ℝ) * Nat.choose (2 * (m + 1)) (m + 1)) =
      2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m := by
    exact_mod_cast choose_two_mul_succ m
  have hch2 : ((m + 2 : ℝ) * Nat.choose (2 * (m + 2)) (m + 2)) =
      2 * (2 * ((m + 1 : ℕ) : ℝ) + 1) * Nat.choose (2 * (m + 1)) (m + 1) := by
    exact_mod_cast choose_two_mul_succ (m + 1)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcp0 : (0 : ℝ) < cPad m := (cPad_bounds m).1
  have hch0 : (Nat.choose (2 * m) m : ℝ) ≠ 0 := (choose_2n_n_pos m).ne'
  have hch1_pos : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) ≠ 0 := (choose_2n_n_pos (m + 1)).ne'
  have hch2_pos : (Nat.choose (2 * (m + 2)) (m + 2) : ℝ) ≠ 0 := (choose_2n_n_pos (m + 2)).ne'
  have hp_m1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hp_m2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hp_2m1 : 2 * (m : ℝ) + 1 ≠ 0 := by positivity
  have hp_2m3 : 2 * (m : ℝ) + 3 ≠ 0 := by positivity
  have hE2_rat : Etilde (m + 2) z =
      (cPad m * z ^ (2 * m + 1) / Nat.choose (2 * m) m) *
        (((3 * (m : ℝ) + 2) * (3 * m + 4) / (18 * (m + 1) * (2 * m + 1))) *
          ((3 * (m : ℝ) + 5) * (3 * m + 7) / (18 * (m + 2) * (2 * m + 3))) * z ^ 4 * Jint (m + 2) z) := by
    unfold Etilde Erem
    rw [hc2, hc1]
    have hch1' : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) =
        2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m / (m + 1) := by
      apply mul_left_cancel₀ hp_m1
      calc (m + 1 : ℝ) * Nat.choose (2 * (m + 1)) (m + 1)
          = 2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m := hch1
        _ = (m + 1 : ℝ) * (2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m / (m + 1)) :=
              (mul_div_cancel₀ _ hp_m1).symm
    have hch2' : (Nat.choose (2 * (m + 2)) (m + 2) : ℝ) =
        2 * (2 * (m : ℝ) + 3) * Nat.choose (2 * (m + 1)) (m + 1) / (m + 2) := by
      apply mul_left_cancel₀ hp_m2
      calc (m + 2 : ℝ) * Nat.choose (2 * (m + 2)) (m + 2)
          = 2 * (2 * ((m + 1 : ℕ) : ℝ) + 1) * Nat.choose (2 * (m + 1)) (m + 1) := hch2
        _ = (m + 2 : ℝ) * (2 * (2 * (m : ℝ) + 3) * Nat.choose (2 * (m + 1)) (m + 1) / (m + 2)) := by
              push_cast; rw [mul_div_cancel₀ _ hp_m2]; ring
    rw [hch2', hch1']
    rw [show 2 * (m + 2) + 1 = (2 * m + 1) + 4 by omega, pow_add]
    push_cast
    field_simp [hch0, hp_m1, hp_m2, hp_2m1, hp_2m3]
    ring
  have hE1_rat : Etilde (m + 1) z =
      (cPad m * z ^ (2 * m + 1) / Nat.choose (2 * m) m) *
        (((3 * (m : ℝ) + 2) * (3 * m + 4) / (18 * (m + 1) * (2 * m + 1))) * z ^ 2 * Jint (m + 1) z) := by
    unfold Etilde Erem
    rw [hc1]
    have hch1' : (Nat.choose (2 * (m + 1)) (m + 1) : ℝ) =
        2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m / (m + 1) := by
      apply mul_left_cancel₀ hp_m1
      calc (m + 1 : ℝ) * Nat.choose (2 * (m + 1)) (m + 1)
          = 2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m := hch1
        _ = (m + 1 : ℝ) * (2 * (2 * (m : ℝ) + 1) * Nat.choose (2 * m) m / (m + 1)) :=
              (mul_div_cancel₀ _ hp_m1).symm
    rw [hch1', show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, pow_add]
    field_simp [hch0, hp_m1, hp_2m1]
    ring
  have hE0_rat : Etilde m z = (cPad m * z ^ (2 * m + 1) / Nat.choose (2 * m) m) * Jint m z := by
    unfold Etilde Erem; ring
  rw [hE2_rat, hE1_rat, hE0_rat]
  set C : ℝ := cPad m * z ^ (2 * m + 1) / Nat.choose (2 * m) m
  have h_num :
      (((3 * (m : ℝ) + 2) * (3 * m + 4) / (18 * (m + 1) * (2 * m + 1))) *
        ((3 * (m : ℝ) + 5) * (3 * m + 7) / (18 * (m + 2) * (2 * m + 3))) * z ^ 4 * Jint (m + 2) z) -
      (1 - z / 2) *
        (((3 * (m : ℝ) + 2) * (3 * m + 4) / (18 * (m + 1) * (2 * m + 1))) * z ^ 2 * Jint (m + 1) z) +
      ((9 * ((m + 1 : ℕ) : ℝ) ^ 2 - 1) / (36 * (2 * (m + 1 : ℕ) - 1) * (2 * (m + 1 : ℕ) + 1))) * z ^ 2 * Jint m z =
      ((3 * (m : ℝ) + 2) * (3 * m + 4) * z ^ 2 / (324 * (m + 1) * (m + 2) * (2 * m + 1) * (2 * m + 3))) *
        (z ^ 2 * (3 * (m + 1 : ℝ) + 2) * (3 * (m + 1 : ℝ) + 4) * Jint (m + 2) z +
          9 * ((m + 1 : ℝ) + 1) * (2 * (m + 1 : ℝ) + 1) * (z - 2) * Jint (m + 1) z +
          9 * (m + 1 : ℝ) * ((m + 1 : ℝ) + 1) * Jint m z) := by
    push_cast
    rw [show 2 * ((m : ℝ) + 1) - 1 = 2 * m + 1 by ring, show 2 * ((m : ℝ) + 1) + 1 = 2 * m + 3 by ring]
    have hd1 : 18 * ((m : ℝ) + 1) * (2 * m + 1) ≠ 0 := by positivity
    have hd2 : 18 * ((m : ℝ) + 2) * (2 * m + 3) ≠ 0 := by positivity
    have hd3 : 36 * (2 * (m : ℝ) + 1) * (2 * m + 3) ≠ 0 := by positivity
    have hd4 : 324 * ((m : ℝ) + 1) * (m + 2) * (2 * m + 1) * (2 * m + 3) ≠ 0 := by positivity
    have hd1' : 18 * ((m : ℝ) + 1) * ((m : ℝ) * 2 + 1) ≠ 0 := by positivity
    have hd2' : 18 * ((m : ℝ) + 2) * ((m : ℝ) * 2 + 3) ≠ 0 := by positivity
    have hd3' : 36 * (1 + (m : ℝ) * 2) * (3 + (m : ℝ) * 2) ≠ 0 := by positivity
    have hd4' : 324 * ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) * 2 + 1) * ((m : ℝ) * 2 + 3) ≠ 0 := by positivity
    have hp1 : (m : ℝ) + 1 ≠ 0 := by positivity
    have hp2 : (m : ℝ) + 2 ≠ 0 := by positivity
    have hp3 : 1 + (m : ℝ) * 2 ≠ 0 := by positivity
    have hp4 : 3 + (m : ℝ) * 2 ≠ 0 := by positivity
    field_simp [hd1, hd2, hd3, hd4, hd1', hd2', hd3', hd4', hp1, hp2, hp3, hp4, hp_2m1, hp_2m3]
    ring
  rw [hrec, mul_zero] at h_num
  linear_combination C * h_num

private lemma Etilde_eq_Ptilde_sub_Qtilde {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ∀ n : ℕ, Etilde n z = Ptilde n z - (1 - z) ^ ((1 : ℝ) / 3) * Qtilde n z ∧
      Etilde (n + 1) z = Ptilde (n + 1) z - (1 - z) ^ ((1 : ℝ) / 3) * Qtilde (n + 1) z
  | 0 => ⟨Etilde_zero hz0 hz1, Etilde_one hz0 hz1⟩
  | m + 1 => by
    obtain ⟨ih0, ih1⟩ := Etilde_eq_Ptilde_sub_Qtilde hz0 hz1 m
    refine ⟨ih1, ?_⟩
    rw [Etilde_rec m hz0 hz1, ih1, ih0]
    have hP := Xtilde_rec (show 1 ≤ m + 1 by omega) (β := 1 / 3) (z := z) (Or.inl rfl)
    have hQ := Xtilde_rec (show 1 ≤ m + 1 by omega) (β := -1 / 3) (z := z) (Or.inr rfl)
    dsimp only [Ptilde, Qtilde] at hP hQ ⊢
    rw [show m + 1 + 1 = m + 2 by omega, show m + 1 - 1 = m by omega] at hP hQ
    rw [hP, hQ]
    ring

theorem Erem_eq_Ppoly_sub_Qpoly (n : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    Erem n z = Ppoly n z - (1 - z) ^ ((1 : ℝ) / 3) * Qpoly n z := by
  have h := (Etilde_eq_Ptilde_sub_Qtilde hz0 hz1 n).1
  unfold Etilde at h
  have hpos : (Nat.choose (2 * n) n : ℝ) ≠ 0 := (choose_2n_n_pos n).ne'
  unfold Ppoly Qpoly
  calc Erem n z = (Nat.choose (2 * n) n : ℝ) * (Erem n z / (Nat.choose (2 * n) n : ℝ)) :=
        (mul_div_cancel₀ _ hpos).symm
    _ = (Nat.choose (2 * n) n : ℝ) * (Ptilde n z - (1 - z) ^ ((1 : ℝ) / 3) * Qtilde n z) := by rw [h]
    _ = (Nat.choose (2 * n) n : ℝ) * Ptilde n z -
          (1 - z) ^ ((1 : ℝ) / 3) * ((Nat.choose (2 * n) n : ℝ) * Qtilde n z) := by ring

theorem Erem_bounds (n : ℕ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 ≤ Erem n z ∧ Erem n z ≤ (1 / 3) * z ^ (2 * n + 1) / (4 ^ n * (1 - z) ^ (n + 1)) := by
  have h1z : 0 < 1 - z := by linarith
  have hw_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ wInt n z t := by
    intro t ht
    unfold wInt
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have htz := (one_sub_mul_pos hz0 hz1 ht).le
    exact mul_nonneg (mul_nonneg (pow_nonneg ht.1 n) (pow_nonneg h1t n)) (Real.rpow_nonneg htz _)
  have hw_upper : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      wInt n z t ≤ 1 / (4 ^ n * (1 - z) ^ (n + 1)) := by
    intro t ht
    unfold wInt
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have hprod_nonneg : 0 ≤ t * (1 - t) := mul_nonneg ht.1 h1t
    have hprod_le : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * t - 1)]
    have hpow_le : t ^ n * (1 - t) ^ n ≤ 1 / 4 ^ n := by
      calc t ^ n * (1 - t) ^ n = (t * (1 - t)) ^ n := (mul_pow t (1 - t) n).symm
        _ ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ hprod_nonneg hprod_le n
        _ = 1 / 4 ^ n := by rw [one_div, one_div, inv_pow]
    have htz_ge : 1 - z ≤ 1 - t * z := by
      have := mul_le_mul_of_nonneg_right ht.2 hz0.le
      linarith
    have hrp_le1 : (1 - t * z) ^ (-(n : ℝ) - 2 / 3) ≤ (1 - z) ^ (-(n : ℝ) - 2 / 3) :=
      Real.rpow_le_rpow_of_nonpos h1z htz_ge (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hrp_le2 : (1 - z) ^ (-(n : ℝ) - 2 / 3) ≤ (1 - z) ^ (-(n : ℝ) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge h1z (by linarith) (by linarith)
    have hrp_eq : (1 - z) ^ (-(n : ℝ) - 1) = 1 / (1 - z) ^ (n + 1) := by
      rw [show -(n : ℝ) - 1 = -((n + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg h1z.le, Real.rpow_natCast, one_div]
    have hrp_le : (1 - t * z) ^ (-(n : ℝ) - 2 / 3) ≤ 1 / (1 - z) ^ (n + 1) :=
      le_trans hrp_le1 (hrp_le2.trans_eq hrp_eq)
    calc t ^ n * (1 - t) ^ n * (1 - t * z) ^ (-(n : ℝ) - 2 / 3)
        ≤ (1 / 4 ^ n) * (1 / (1 - z) ^ (n + 1)) :=
          mul_le_mul hpow_le hrp_le (Real.rpow_nonneg (one_sub_mul_pos hz0 hz1 ht).le _) (by positivity)
      _ = 1 / (4 ^ n * (1 - z) ^ (n + 1)) := by rw [one_div_mul_one_div]
  have hJ0 : 0 ≤ Jint n z := by
    unfold Jint
    have hi0 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 1 :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hi0
      (wInt_intervalIntegrable n hz0 hz1) hw_nonneg
    simpa using hmono
  have hJ1 : Jint n z ≤ 1 / (4 ^ n * (1 - z) ^ (n + 1)) := by
    unfold Jint
    have hic : IntervalIntegrable (fun _ : ℝ => 1 / (4 ^ n * (1 - z) ^ (n + 1))) MeasureTheory.volume 0 1 :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (wInt_intervalIntegrable n hz0 hz1) hic hw_upper
    simpa using hmono
  obtain ⟨hc_pos, hc_le⟩ := cPad_bounds n
  have hzpow : 0 ≤ z ^ (2 * n + 1) := pow_nonneg hz0.le _
  unfold Erem
  refine ⟨mul_nonneg (mul_nonneg hc_pos.le hzpow) hJ0, ?_⟩
  calc cPad n * z ^ (2 * n + 1) * Jint n z
      ≤ (1 / 3 * z ^ (2 * n + 1)) * (1 / (4 ^ n * (1 - z) ^ (n + 1))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hc_le hzpow) hJ1 hJ0 (by positivity)
    _ = (1 / 3) * z ^ (2 * n + 1) / (4 ^ n * (1 - z) ^ (n + 1)) := by ring

private lemma choose_2n_n_mul_cRatio (n k : ℕ) :
    (Nat.choose (2 * n) n : ℝ) * cRatio n k = (Nat.choose (2 * n - k) n : ℝ) := by
  dsimp [cRatio]
  exact mul_div_cancel₀ _ (choose_2n_n_pos n).ne'

private lemma Ppoly_eq_sum (n : ℕ) (z : ℝ) :
    Ppoly n z = ∑ k ∈ Finset.range (n + 1),
      gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z) ^ k := by
  unfold Ppoly Ptilde Xtilde
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [padeTerm, hk_le, ↓reduceIte]
  rw [← choose_2n_n_mul_cRatio n k]
  ring

private lemma Qpoly_eq_sum (n : ℕ) (z : ℝ) :
    Qpoly n z = ∑ k ∈ Finset.range (n + 1),
      gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z) ^ k := by
  unfold Qpoly Qtilde Xtilde
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [padeTerm, hk_le, ↓reduceIte]
  rw [← choose_2n_n_mul_cRatio n k, show (n : ℝ) + (-1 / 3 : ℝ) = (n : ℝ) - 1 / 3 by ring]
  ring

private lemma gbinom_third_nonneg_le (n : ℕ) :
    ∀ k ≤ n, 0 ≤ gbinom ((n : ℝ) + 1 / 3) k ∧ gbinom ((n : ℝ) + 1 / 3) k ≤ (Nat.choose (n + 1) k : ℝ)
  | 0, _ => by simp [gbinom, fall]
  | k + 1, hk => by
    obtain ⟨h0, hle⟩ := gbinom_third_nonneg_le n k (by omega)
    rw [gbinom_step_right]
    have hkr : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    have hfac_nonneg : 0 ≤ ((n : ℝ) + 1 / 3 - k) / (k + 1) := by
      have : (0 : ℝ) ≤ n + 1 / 3 - k := by linarith
      positivity
    have hfac_le : ((n : ℝ) + 1 / 3 - k) / (k + 1) ≤ ((n + 1 : ℝ) - k) / (k + 1) := by
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hch : (((n + 1 : ℝ) - k) / (k + 1)) * (Nat.choose (n + 1) k : ℝ) =
        (Nat.choose (n + 1) (k + 1) : ℝ) := by
      have hnat := Nat.choose_succ_right_eq (n + 1) k
      have hcast : (Nat.choose (n + 1) (k + 1) : ℝ) * ((k : ℝ) + 1) =
          (Nat.choose (n + 1) k : ℝ) * ((n + 1 : ℝ) - k) := by
        have hk1 : k ≤ n + 1 := by omega
        have h := congr_arg (Nat.cast : ℕ → ℝ) hnat
        push_cast at h
        rw [Nat.cast_sub hk1] at h
        push_cast at h
        exact h
      have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
      apply mul_left_cancel₀ hk1_ne
      calc ((k : ℝ) + 1) * ((((n + 1 : ℝ) - k) / (k + 1)) * Nat.choose (n + 1) k)
          = (Nat.choose (n + 1) k : ℝ) * ((n + 1 : ℝ) - k) * (((k : ℝ) + 1) / ((k : ℝ) + 1)) := by ring
        _ = (Nat.choose (n + 1) k : ℝ) * ((n + 1 : ℝ) - k) * 1 := by rw [div_self hk1_ne]
        _ = (Nat.choose (n + 1) (k + 1) : ℝ) * ((k : ℝ) + 1) := by rw [← hcast, mul_one]
        _ = ((k : ℝ) + 1) * Nat.choose (n + 1) (k + 1) := by ring
    refine ⟨mul_nonneg hfac_nonneg h0, ?_⟩
    calc (((n : ℝ) + 1 / 3 - k) / (k + 1)) * gbinom ((n : ℝ) + 1 / 3) k
        ≤ (((n + 1 : ℝ) - k) / (k + 1)) * (Nat.choose (n + 1) k : ℝ) :=
          mul_le_mul hfac_le hle h0 (div_nonneg (by linarith) (by positivity))
      _ = (Nat.choose (n + 1) (k + 1) : ℝ) := hch

theorem Ppoly_abs_le (n : ℕ) {z : ℝ} (hz0 : 0 ≤ z) :
    |Ppoly n z| ≤ 4 ^ n * (1 + z) ^ (n + 1) := by
  rw [Ppoly_eq_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ Finset.range (n + 1),
      |gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z) ^ k| ≤
        (4 : ℝ) ^ n * ((Nat.choose (n + 1) k : ℝ) * z ^ k) := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    obtain ⟨hg0, hgle⟩ := gbinom_third_nonneg_le n k hk_le
    have hch_le : (Nat.choose (2 * n - k) n : ℝ) ≤ (4 : ℝ) ^ n := by
      have h1 : Nat.choose (2 * n - k) n ≤ Nat.choose (2 * n) n :=
        Nat.choose_le_choose n (by omega)
      have h2 : Nat.choose (2 * n) n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow (2 * n) n
      have h3 : (2 ^ (2 * n) : ℝ) = (4 : ℝ) ^ n := by
        rw [pow_mul]; norm_num
      calc (Nat.choose (2 * n - k) n : ℝ) ≤ (Nat.choose (2 * n) n : ℝ) := by exact_mod_cast h1
        _ ≤ (2 ^ (2 * n) : ℝ) := by exact_mod_cast h2
        _ = (4 : ℝ) ^ n := h3
    rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_nonneg (Nat.cast_nonneg _), abs_pow, abs_neg,
      abs_of_nonneg hz0]
    calc gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * z ^ k
        ≤ (Nat.choose (n + 1) k : ℝ) * (4 : ℝ) ^ n * z ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul hgle hch_le (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (pow_nonneg hz0 k)
      _ = (4 : ℝ) ^ n * ((Nat.choose (n + 1) k : ℝ) * z ^ k) := by ring
  have hsum_le : ∑ k ∈ Finset.range (n + 1),
      |gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z) ^ k| ≤
      ∑ k ∈ Finset.range (n + 1), (4 : ℝ) ^ n * ((Nat.choose (n + 1) k : ℝ) * z ^ k) :=
    Finset.sum_le_sum hterm
  refine le_trans hsum_le ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) k : ℝ) * z ^ k ≤
      ∑ k ∈ Finset.range (n + 2), z ^ k * (1 : ℝ) ^ (n + 1 - k) * (Nat.choose (n + 1) k : ℝ) := by
    conv_rhs => rw [Finset.sum_range_succ]
    have hcongr : ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + 1) k : ℝ) * z ^ k =
        ∑ k ∈ Finset.range (n + 1), z ^ k * (1 : ℝ) ^ (n + 1 - k) * (Nat.choose (n + 1) k : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]
    rw [hcongr]
    have hlast : 0 ≤ z ^ (n + 1) * (1 : ℝ) ^ (n + 1 - (n + 1)) * (Nat.choose (n + 1) (n + 1) : ℝ) := by
      positivity
    linarith
  have hbin : (z + 1 : ℝ) ^ (n + 1) =
      ∑ k ∈ Finset.range (n + 2), z ^ k * (1 : ℝ) ^ (n + 1 - k) * (Nat.choose (n + 1) k : ℝ) :=
    add_pow z (1 : ℝ) (n + 1)
  linarith [hsub, hbin, show (1 + z : ℝ) ^ (n + 1) = (z + 1 : ℝ) ^ (n + 1) by ring]

/-! ## 3. 3-adic Integrality, Rational Approximants, and Explicit Bounds -/

private lemma two_mul_sum_div_pow3_le (k : ℕ) :
    ∀ b : ℕ, 2 * (∑ i ∈ Finset.Ico 1 (b + 1), k / 3 ^ i) + k / 3 ^ b ≤ k
  | 0 => by simp
  | b + 1 => by
    have ih := two_mul_sum_div_pow3_le k b
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ b + 1)]
    have hdiv3 : k / 3 ^ (b + 1) = (k / 3 ^ b) / 3 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have h3 : 3 * (k / 3 ^ (b + 1)) ≤ k / 3 ^ b := by
      rw [hdiv3]
      exact Nat.mul_div_le (k / 3 ^ b) 3
    omega

private lemma two_mul_v3_factorial_le (k : ℕ) : 2 * padicValNat 3 k.factorial ≤ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlt : Nat.log 3 k < k + 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : k < 3 ^ (k + 1) := by
        induction k with
        | zero => omega
        | succ m ih =>
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · norm_num
          · have : m + 1 < 3 * m := by omega
            have h3m : 3 * m < 3 * 3 ^ (m + 1) := Nat.mul_lt_mul_of_pos_left (ih hm) (by omega)
            rw [← pow_succ'] at h3m
            omega
      exact (Nat.log_lt_iff_lt_pow (by norm_num) hk.ne').mpr h1
  rw [padicValNat_factorial hlt]
  exact le_trans (Nat.le_add_right _ _) (two_mul_sum_div_pow3_le k k)

private lemma factorial_dvd_prod_sub (A : ℤ) (k : ℕ) :
    (k.factorial : ℤ) ∣ ∏ j ∈ Finset.range k, (A - (j : ℤ)) := by
  by_cases hA0 : 0 ≤ A
  · set aNat : ℕ := A.toNat
    have ha_eq : (aNat : ℤ) = A := Int.toNat_of_nonneg hA0
    by_cases hkn : k ≤ aNat + 1
    · have hprod : ∏ j ∈ Finset.range k, (A - (j : ℤ)) = (aNat.descFactorial k : ℤ) := by
        rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
        refine Finset.prod_congr rfl fun j hj => ?_
        have hj_lt : j < k := Finset.mem_range.mp hj
        have hj_le : j ≤ aNat := by omega
        rw [Nat.cast_sub hj_le, ha_eq]
      rw [hprod]
      exact_mod_cast Nat.factorial_dvd_descFactorial aNat k
    · have ha_lt : aNat ∈ Finset.range k := Finset.mem_range.mpr (by omega)
      have hzero : ∏ j ∈ Finset.range k, (A - (j : ℤ)) = 0 :=
        Finset.prod_eq_zero ha_lt (by rw [← ha_eq]; ring)
      rw [hzero]
      exact dvd_zero _
  · set m : ℕ := (-A).toNat
    have hm_eq : (m : ℤ) = -A := Int.toNat_of_nonneg (by omega)
    have hprod : ∏ j ∈ Finset.range k, (A - (j : ℤ)) = (-1 : ℤ) ^ k * (m.ascFactorial k : ℤ) := by
      rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
      calc ∏ j ∈ Finset.range k, (A - (j : ℤ))
          = ∏ j ∈ Finset.range k, ((-1 : ℤ) * ((m : ℤ) + (j : ℤ))) := by
              refine Finset.prod_congr rfl fun j _ => ?_
              rw [hm_eq]; ring
        _ = (∏ _ ∈ Finset.range k, (-1 : ℤ)) * ∏ j ∈ Finset.range k, ((m : ℤ) + (j : ℤ)) :=
              Finset.prod_mul_distrib
        _ = (-1 : ℤ) ^ k * ∏ j ∈ Finset.range k, ((m + j : ℕ) : ℤ) := by
              simp [Finset.prod_const, Finset.card_range]
    rw [hprod]
    exact dvd_mul_of_dvd_right (by exact_mod_cast Nat.factorial_dvd_ascFactorial m k) _

private lemma prod_sub_mul_dvd {M : ℤ} (f g : ℕ → ℤ) (s : Finset ℕ)
    (h : ∀ j ∈ s, M ∣ f j - g j) : M ∣ (∏ j ∈ s, f j) - ∏ j ∈ s, g j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hid : f a * ∏ j ∈ s, f j - g a * ∏ j ∈ s, g j =
        (f a - g a) * ∏ j ∈ s, f j + g a * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) := by ring
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

private lemma factorial_dvd_three_pow_mul_prod (a : ℤ) (k : ℕ) :
    (k.factorial : ℤ) ∣ (3 : ℤ) ^ (padicValNat 3 k.factorial) * ∏ j ∈ Finset.range k, (a - 3 * (j : ℤ)) := by
  set P : ℕ := 3 ^ (k.factorial.factorization 3)
  set M : ℕ := k.factorial / P
  have hPM : P * M = k.factorial := Nat.ordProj_mul_ordCompl_eq_self k.factorial 3
  have hcop : Nat.Coprime 3 M := Nat.coprime_ordCompl Nat.prime_three (Nat.factorial_ne_zero k)
  have hfac_eq : k.factorial.factorization 3 = padicValNat 3 k.factorial :=
    Nat.factorization_def k.factorial Nat.prime_three
  have hP_eq : P = 3 ^ (padicValNat 3 k.factorial) := by rw [← hfac_eq]
  conv_lhs => rw [← hPM, Nat.cast_mul, hP_eq]
  refine Int.mul_dvd_mul_left _ ?_
  have hbez := Int.gcd_eq_gcd_ab 3 M
  have hgcd1 : Int.gcd (3 : ℤ) (M : ℤ) = 1 := by exact_mod_cast hcop
  rw [hgcd1, Nat.cast_one] at hbez
  set x := Int.gcdA 3 M
  set y := Int.gcdB 3 M
  set A := a * x
  have hcongr : ∀ j ∈ Finset.range k, (M : ℤ) ∣ ((3 : ℤ) * (A - (j : ℤ)) - (a - 3 * (j : ℤ))) := by
    intro j _
    refine ⟨-(a * y), ?_⟩
    dsimp [A]
    linear_combination -a * hbez
  have hdiff := prod_sub_mul_dvd (fun j => (3 : ℤ) * (A - (j : ℤ))) (fun j => a - 3 * (j : ℤ))
    (Finset.range k) hcongr
  have h3A : ∏ j ∈ Finset.range k, ((3 : ℤ) * (A - (j : ℤ))) =
      (3 : ℤ) ^ k * ∏ j ∈ Finset.range k, (A - (j : ℤ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hMdvd_fac : (M : ℤ) ∣ (k.factorial : ℤ) := ⟨(P : ℤ), by exact_mod_cast hPM.symm.trans (mul_comm P M)⟩
  have hMdvd_3A : (M : ℤ) ∣ ∏ j ∈ Finset.range k, ((3 : ℤ) * (A - (j : ℤ))) := by
    rw [h3A]
    exact dvd_mul_of_dvd_right (dvd_trans hMdvd_fac (factorial_dvd_prod_sub A k)) _
  have hsub : (∏ j ∈ Finset.range k, (a - 3 * (j : ℤ))) =
      (∏ j ∈ Finset.range k, ((3 : ℤ) * (A - (j : ℤ)))) -
        ((∏ j ∈ Finset.range k, ((3 : ℤ) * (A - (j : ℤ)))) - ∏ j ∈ Finset.range k, (a - 3 * (j : ℤ))) := by
    ring
  rw [hsub]
  exact dvd_sub hMdvd_3A hdiff

private lemma three_pow_mul_fall_eq (n : ℕ) (β : ℝ) (s : ℤ) (hβs : 3 * β = (s : ℝ)) :
    ∀ k : ℕ, (3 : ℝ) ^ k * fall ((n : ℝ) + β) k =
      ((∏ j ∈ Finset.range k, ((3 * (n : ℤ) + s) - 3 * (j : ℤ)) : ℤ) : ℝ)
  | 0 => by simp [fall]
  | k + 1 => by
    have ih := three_pow_mul_fall_eq n β s hβs k
    rw [pow_succ', fall, Finset.prod_range_succ, Int.cast_mul]
    push_cast
    calc (3 : ℝ) * (3 : ℝ) ^ k * (fall ((n : ℝ) + β) k * ((n : ℝ) + β - k))
        = ((3 : ℝ) ^ k * fall ((n : ℝ) + β) k) * (3 * (n : ℝ) + 3 * β - 3 * k) := by ring
      _ = ((∏ j ∈ Finset.range k, ((3 * (n : ℤ) + s) - 3 * (j : ℤ)) : ℤ) : ℝ) *
            ((3 * (n : ℝ) + (s : ℝ)) - 3 * (k : ℝ)) := by rw [ih, hβs]
      _ = _ := by push_cast; ring

private lemma exists_int_three_pow_mul_gbinom (n k : ℕ) (hk : k ≤ n) (β : ℝ) (s : ℤ)
    (hβs : 3 * β = (s : ℝ)) :
    ∃ c : ℤ, (c : ℝ) = (3 : ℝ) ^ (n / 2) * (3 : ℝ) ^ k * gbinom ((n : ℝ) + β) k := by
  have hv3 : padicValNat 3 k.factorial ≤ n / 2 := by
    have h2 := two_mul_v3_factorial_le k
    omega
  have hdvd := factorial_dvd_three_pow_mul_prod (3 * (n : ℤ) + s) k
  have hpow : (k.factorial : ℤ) ∣
      (3 : ℤ) ^ (n / 2) * ∏ j ∈ Finset.range k, ((3 * (n : ℤ) + s) - 3 * (j : ℤ)) := by
    rw [show (3 : ℤ) ^ (n / 2) = (3 : ℤ) ^ (n / 2 - padicValNat 3 k.factorial) *
        (3 : ℤ) ^ (padicValNat 3 k.factorial) by rw [← pow_add, Nat.sub_add_cancel hv3], mul_assoc]
    exact dvd_mul_of_dvd_right hdvd _
  rcases hpow with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hfac_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hcr : (k.factorial : ℝ) * (c : ℝ) =
      (3 : ℝ) ^ (n / 2) * ((∏ j ∈ Finset.range k, ((3 * (n : ℤ) + s) - 3 * (j : ℤ)) : ℤ) : ℝ) := by
    have hc' : ((k.factorial : ℤ) : ℝ) * (c : ℝ) =
        (((3 : ℤ) ^ (n / 2) : ℤ) : ℝ) *
          ((∏ j ∈ Finset.range k, ((3 * (n : ℤ) + s) - 3 * (j : ℤ)) : ℤ) : ℝ) := by
      rw [← Int.cast_mul, ← Int.cast_mul, hc]
    simpa using hc'
  rw [← three_pow_mul_fall_eq n β s hβs k] at hcr
  apply mul_left_cancel₀ hfac_ne
  unfold gbinom
  calc (k.factorial : ℝ) * (c : ℝ)
      = (3 : ℝ) ^ (n / 2) * ((3 : ℝ) ^ k * fall ((n : ℝ) + β) k) := hcr
    _ = (3 : ℝ) ^ (n / 2) * (3 : ℝ) ^ k * ((k.factorial : ℝ) * (fall ((n : ℝ) + β) k / (k.factorial : ℝ))) := by
          rw [mul_div_cancel₀ _ hfac_ne]; ring
    _ = (k.factorial : ℝ) * ((3 : ℝ) ^ (n / 2) * (3 : ℝ) ^ k * (fall ((n : ℝ) + β) k / (k.factorial : ℝ))) := by ring

def a21 : ℕ := 700728535
def b21 : ℕ := 239645788
def a1 : ℕ := 140145707
def A0 : ℕ := 5 * a1 ^ 3
def B0 : ℕ := b21 ^ 3
def C0 : ℕ := 402657
def C1 : ℕ := 134219

noncomputable def z0 : ℝ := (C0 : ℝ) / (B0 : ℝ)
noncomputable def Dscale (n : ℕ) : ℝ := (3 : ℝ) ^ (n / 2) * (B0 : ℝ) ^ n

private lemma conv21_arith :
    B0 - A0 = C0 ∧ C0 = 3 * C1 ∧ 25 * A0 = a21 ^ 3 ∧ A0 < B0 := by
  unfold A0 B0 C0 C1 a1 a21 b21
  norm_num

private lemma z0_bounds : 0 < z0 ∧ z0 < 1 ∧ 1 - z0 = (A0 : ℝ) / (B0 : ℝ) := by
  unfold z0
  have hB : 0 < (B0 : ℝ) := by unfold B0 b21; norm_num
  have hC : 0 < (C0 : ℝ) := by unfold C0; norm_num
  have hA : (A0 : ℝ) + (C0 : ℝ) = (B0 : ℝ) := by
    have : A0 + C0 = B0 := by unfold A0 B0 C0 a1 b21; norm_num
    exact_mod_cast this
  refine ⟨div_pos hC hB, ?_, ?_⟩
  · rw [div_lt_one hB]
    linarith [show (0 : ℝ) < (A0 : ℝ) by unfold A0 a1; norm_num]
  · rw [eq_div_iff hB.ne']
    calc (1 - (C0 : ℝ) / (B0 : ℝ)) * (B0 : ℝ) = (B0 : ℝ) - (C0 : ℝ) := by
          rw [sub_mul, one_mul, div_mul_cancel₀ _ hB.ne']
      _ = (A0 : ℝ) := by linarith

private lemma exists_int_Ppoly (n : ℕ) :
    ∃ v : ℤ, (v : ℝ) = Dscale n * (b21 : ℝ) * Ppoly n z0 := by
  have hterm : ∀ k ∈ Finset.range (n + 1), ∃ t : ℤ,
      (t : ℝ) = Dscale n * (gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k) := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    obtain ⟨c, hc⟩ := exists_int_three_pow_mul_gbinom n k hk_le (1 / 3) 1 (by norm_num)
    refine ⟨c * (Nat.choose (2 * n - k) n : ℤ) * (-C1 : ℤ) ^ k * (B0 : ℤ) ^ (n - k), ?_⟩
    have hz_eq : (-z0) ^ k * (B0 : ℝ) ^ n = (3 : ℝ) ^ k * ((-C1 : ℤ) : ℝ) ^ k * (B0 : ℝ) ^ (n - k) := by
      have hB : (B0 : ℝ) ≠ 0 := by unfold B0 b21; norm_num
      have hC0 : (C0 : ℝ) = 3 * (C1 : ℝ) := by unfold C0 C1; norm_num
      have hz0_eq : -z0 = (3 * ((-C1 : ℤ) : ℝ)) / (B0 : ℝ) := by
        unfold z0
        rw [hC0]
        push_cast
        ring
      rw [hz0_eq, div_pow, mul_pow, show (B0 : ℝ) ^ n = (B0 : ℝ) ^ k * (B0 : ℝ) ^ (n - k) by
        rw [← pow_add, Nat.add_sub_of_le hk_le]]
      field_simp [hB]
    push_cast
    calc (c : ℝ) * (Nat.choose (2 * n - k) n : ℝ) * (-C1 : ℝ) ^ k * (B0 : ℝ) ^ (n - k)
        = ((3 : ℝ) ^ (n / 2) * (3 : ℝ) ^ k * gbinom ((n : ℝ) + 1 / 3) k) *
            (Nat.choose (2 * n - k) n : ℝ) * (-C1 : ℝ) ^ k * (B0 : ℝ) ^ (n - k) := by rw [hc]
      _ = (3 : ℝ) ^ (n / 2) * gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) *
            ((3 : ℝ) ^ k * (-C1 : ℝ) ^ k * (B0 : ℝ) ^ (n - k)) := by ring
      _ = (3 : ℝ) ^ (n / 2) * gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) *
            ((-z0) ^ k * (B0 : ℝ) ^ n) := by push_cast at hz_eq; rw [← hz_eq]
      _ = Dscale n * (gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k) := by
            unfold Dscale; ring
  choose tf htf using hterm
  refine ⟨(b21 : ℤ) * ∑ k ∈ (Finset.range (n + 1)).attach, tf k.1 k.2, ?_⟩
  rw [Ppoly_eq_sum]
  push_cast
  have hsum : (∑ k ∈ (Finset.range (n + 1)).attach, (tf k.1 k.2 : ℝ)) =
      ∑ k ∈ Finset.range (n + 1),
        Dscale n * (gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k) := by
    calc (∑ k ∈ (Finset.range (n + 1)).attach, (tf k.1 k.2 : ℝ))
        = ∑ k ∈ (Finset.range (n + 1)).attach,
            Dscale n * (gbinom ((n : ℝ) + 1 / 3) k.1 * (Nat.choose (2 * n - k.1) n : ℝ) * (-z0) ^ k.1) :=
          Finset.sum_congr rfl fun k _ => htf k.1 k.2
      _ = _ := by
          simpa using Finset.sum_attach (Finset.range (n + 1)) fun k =>
            Dscale n * (gbinom ((n : ℝ) + 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k)
  rw [hsum, ← Finset.mul_sum]
  ring

private lemma exists_int_Qpoly (n : ℕ) :
    ∃ u : ℤ, (u : ℝ) = Dscale n * (a21 : ℝ) * Qpoly n z0 := by
  have hterm : ∀ k ∈ Finset.range (n + 1), ∃ t : ℤ,
      (t : ℝ) = Dscale n * (gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k) := by
    intro k hk
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    obtain ⟨c, hc⟩ := exists_int_three_pow_mul_gbinom n k hk_le (-1 / 3) (-1) (by norm_num)
    refine ⟨c * (Nat.choose (2 * n - k) n : ℤ) * (-C1 : ℤ) ^ k * (B0 : ℤ) ^ (n - k), ?_⟩
    have hz_eq : (-z0) ^ k * (B0 : ℝ) ^ n = (3 : ℝ) ^ k * ((-C1 : ℤ) : ℝ) ^ k * (B0 : ℝ) ^ (n - k) := by
      have hB : (B0 : ℝ) ≠ 0 := by unfold B0 b21; norm_num
      have hC0 : (C0 : ℝ) = 3 * (C1 : ℝ) := by unfold C0 C1; norm_num
      have hz0_eq : -z0 = (3 * ((-C1 : ℤ) : ℝ)) / (B0 : ℝ) := by
        unfold z0
        rw [hC0]
        push_cast
        ring
      rw [hz0_eq, div_pow, mul_pow, show (B0 : ℝ) ^ n = (B0 : ℝ) ^ k * (B0 : ℝ) ^ (n - k) by
        rw [← pow_add, Nat.add_sub_of_le hk_le]]
      field_simp [hB]
    push_cast
    calc (c : ℝ) * (Nat.choose (2 * n - k) n : ℝ) * (-C1 : ℝ) ^ k * (B0 : ℝ) ^ (n - k)
        = ((3 : ℝ) ^ (n / 2) * (3 : ℝ) ^ k * gbinom ((n : ℝ) + -1 / 3) k) *
            (Nat.choose (2 * n - k) n : ℝ) * (-C1 : ℝ) ^ k * (B0 : ℝ) ^ (n - k) := by rw [hc]
      _ = (3 : ℝ) ^ (n / 2) * gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) *
            ((3 : ℝ) ^ k * (-C1 : ℝ) ^ k * (B0 : ℝ) ^ (n - k)) := by ring_nf
      _ = (3 : ℝ) ^ (n / 2) * gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) *
            ((-z0) ^ k * (B0 : ℝ) ^ n) := by push_cast at hz_eq; rw [← hz_eq]
      _ = Dscale n * (gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k) := by
            unfold Dscale; ring
  choose tf htf using hterm
  refine ⟨(a21 : ℤ) * ∑ k ∈ (Finset.range (n + 1)).attach, tf k.1 k.2, ?_⟩
  rw [Qpoly_eq_sum]
  push_cast
  have hsum : (∑ k ∈ (Finset.range (n + 1)).attach, (tf k.1 k.2 : ℝ)) =
      ∑ k ∈ Finset.range (n + 1),
        Dscale n * (gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k) := by
    calc (∑ k ∈ (Finset.range (n + 1)).attach, (tf k.1 k.2 : ℝ))
        = ∑ k ∈ (Finset.range (n + 1)).attach,
            Dscale n * (gbinom ((n : ℝ) - 1 / 3) k.1 * (Nat.choose (2 * n - k.1) n : ℝ) * (-z0) ^ k.1) :=
          Finset.sum_congr rfl fun k _ => htf k.1 k.2
      _ = _ := by
          simpa using Finset.sum_attach (Finset.range (n + 1)) fun k =>
            Dscale n * (gbinom ((n : ℝ) - 1 / 3) k * (Nat.choose (2 * n - k) n : ℝ) * (-z0) ^ k)
  rw [hsum, ← Finset.mul_sum]
  ring

noncomputable def vSeq (n : ℕ) : ℤ := Classical.choose (exists_int_Ppoly n)
noncomputable def uSeq (n : ℕ) : ℤ := Classical.choose (exists_int_Qpoly n)

private lemma vSeq_spec (n : ℕ) :
    (vSeq n : ℝ) = Dscale n * (b21 : ℝ) * Ppoly n z0 :=
  Classical.choose_spec (exists_int_Ppoly n)

private lemma uSeq_spec (n : ℕ) :
    (uSeq n : ℝ) = Dscale n * (a21 : ℝ) * Qpoly n z0 :=
  Classical.choose_spec (exists_int_Qpoly n)

private lemma wronskian_ne_zero (n : ℕ) :
    uSeq n * vSeq (n + 1) - uSeq (n + 1) * vSeq n ≠ 0 := by
  intro h0
  have hr : ((uSeq n * vSeq (n + 1) - uSeq (n + 1) * vSeq n : ℤ) : ℝ) = 0 := by
    rw [h0]; norm_num
  push_cast at hr
  rw [uSeq_spec n, uSeq_spec (n + 1), vSeq_spec n, vSeq_spec (n + 1)] at hr
  have hfac : Dscale n * (a21 : ℝ) * Qpoly n z0 * (Dscale (n + 1) * (b21 : ℝ) * Ppoly (n + 1) z0) -
      Dscale (n + 1) * (a21 : ℝ) * Qpoly (n + 1) z0 * (Dscale n * (b21 : ℝ) * Ppoly n z0) =
      Dscale n * Dscale (n + 1) * (a21 : ℝ) * (b21 : ℝ) *
        (Ppoly (n + 1) z0 * Qpoly n z0 - Ppoly n z0 * Qpoly (n + 1) z0) := by ring
  rw [hfac] at hr
  have hB : (B0 : ℝ) ≠ 0 := by unfold B0 b21; norm_num
  have hD0 : Dscale n ≠ 0 := by unfold Dscale; positivity
  have hD1 : Dscale (n + 1) ≠ 0 := by unfold Dscale; positivity
  have ha : (a21 : ℝ) ≠ 0 := by unfold a21; norm_num
  have hb : (b21 : ℝ) ≠ 0 := by unfold b21; norm_num
  have hpref : Dscale n * Dscale (n + 1) * (a21 : ℝ) * (b21 : ℝ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hD0 hD1) ha) hb
  rcases mul_eq_zero.mp hr with hbad | hdet
  · exact hpref hbad
  · exact Ppoly_Qpoly_det_ne_zero n z0_bounds.1.ne' hdet

private noncomputable def M0 : ℝ := 48 * 10 ^ 7
private noncomputable def M : ℝ := 955 * 10 ^ 23
private noncomputable def E0 : ℝ := 702 / 10 ^ 14
private noncomputable def E : ℝ := 511 / 10 ^ 17
private noncomputable def α : ℝ := (25 : ℝ) ^ ((1 : ℝ) / 3)

private lemma three_pow_half_le (n : ℕ) :
    (3 : ℝ) ^ (n / 2) ≤ (1733 / 1000 : ℝ) ^ n := by
  have h0 : 0 ≤ (3 : ℝ) ^ (n / 2) := by positivity
  have h1 : 0 ≤ (1733 / 1000 : ℝ) ^ n := by positivity
  have hsq : ((3 : ℝ) ^ (n / 2)) ^ 2 ≤ ((1733 / 1000 : ℝ) ^ n) ^ 2 := by
    calc ((3 : ℝ) ^ (n / 2)) ^ 2 = (3 : ℝ) ^ (2 * (n / 2)) := by rw [← pow_mul]; ring
      _ ≤ (3 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ ((1733 / 1000 : ℝ) ^ 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      _ = ((1733 / 1000 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, mul_comm 2 n, pow_mul]
  nlinarith

private lemma vSeq_abs_le (n : ℕ) : |(vSeq n : ℝ)| ≤ M0 * M ^ n := by
  rw [vSeq_spec n, abs_mul, abs_mul]
  obtain ⟨hz0, hz1, _⟩ := z0_bounds
  have hb0 : 0 ≤ (b21 : ℝ) := Nat.cast_nonneg _
  have hD0 : 0 ≤ Dscale n := by unfold Dscale; positivity
  rw [abs_of_nonneg hD0, abs_of_nonneg hb0]
  have hp := Ppoly_abs_le n hz0.le
  have hD_le : Dscale n ≤ ((1733 / 1000 : ℝ) * (B0 : ℝ)) ^ n := by
    unfold Dscale
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (three_pow_half_le n) (by positivity)
  have hM0_ok : (b21 : ℝ) * (1 + z0) ≤ M0 := by
    unfold M0 z0 B0 C0 b21; norm_num
  have hM_ok : 4 * (1733 / 1000 : ℝ) * (B0 : ℝ) * (1 + z0) ≤ M := by
    unfold M z0 B0 C0 b21; norm_num
  calc Dscale n * (b21 : ℝ) * |Ppoly n z0|
      ≤ (((1733 / 1000 : ℝ) * (B0 : ℝ)) ^ n) * (b21 : ℝ) * (4 ^ n * (1 + z0) ^ (n + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hD_le hb0) hp (abs_nonneg _) (by positivity)
    _ = ((b21 : ℝ) * (1 + z0)) * (4 * (1733 / 1000 : ℝ) * (B0 : ℝ) * (1 + z0)) ^ n := by
        rw [pow_succ (1 + z0) n]
        simp only [mul_pow]
        ring
    _ ≤ M0 * M ^ n :=
        mul_le_mul hM0_ok (pow_le_pow_left₀ (by positivity) hM_ok n) (by positivity) (by unfold M0; positivity)

private lemma alpha_pos_cube : 0 < α ∧ α ^ 3 = 25 := by
  unfold α
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  rw [← Real.rpow_natCast ((25 : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by norm_num)]
  norm_num

private lemma alpha_bounds : (29 : ℝ) / 10 < α ∧ α < 3 := by
  obtain ⟨hpos, hcube⟩ := alpha_pos_cube
  constructor
  · by_contra h
    have hle : α ≤ 29 / 10 := le_of_not_gt h
    have hp := pow_le_pow_left₀ hpos.le hle 3
    norm_num at hp
    linarith [hcube]
  · by_contra h
    have hge : (3 : ℝ) ≤ α := le_of_not_gt h
    have hp := pow_le_pow_left₀ (by norm_num) hge 3
    norm_num at hp
    linarith [hcube]

private lemma b21_mul_alpha_mul_cbrt_eq_a21 :
    (b21 : ℝ) * α * (1 - z0) ^ ((1 : ℝ) / 3) = (a21 : ℝ) := by
  obtain ⟨_, _, h1z⟩ := z0_bounds
  have h1z_pos : 0 < 1 - z0 := by rw [h1z]; unfold A0 B0 a1 b21; positivity
  obtain ⟨hα_pos, hα_cube⟩ := alpha_pos_cube
  set L : ℝ := (b21 : ℝ) * α * (1 - z0) ^ ((1 : ℝ) / 3)
  set R : ℝ := (a21 : ℝ)
  have hL_pos : 0 < L := mul_pos (mul_pos (by unfold b21; norm_num) hα_pos) (Real.rpow_pos_of_pos h1z_pos _)
  have hR_pos : 0 < R := by dsimp [R]; unfold a21; norm_num
  have hcbrt3 : ((1 - z0) ^ ((1 : ℝ) / 3)) ^ 3 = 1 - z0 := by
    rw [← Real.rpow_natCast ((1 - z0) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul h1z_pos.le]
    norm_num
  have hcube_eq : L ^ 3 = R ^ 3 := by
    dsimp [L, R]
    rw [mul_pow, mul_pow, hα_cube, hcbrt3, h1z]
    have hB : (B0 : ℝ) ≠ 0 := by unfold B0 b21; norm_num
    have h25A : (25 : ℝ) * (A0 : ℝ) = (a21 : ℝ) ^ 3 := by
      exact_mod_cast conv21_arith.2.2.1
    calc (b21 : ℝ) ^ 3 * 25 * ((A0 : ℝ) / (B0 : ℝ))
        = (B0 : ℝ) * 25 * ((A0 : ℝ) / (B0 : ℝ)) := by unfold B0; push_cast; ring
      _ = 25 * (A0 : ℝ) := by rw [mul_comm (B0 : ℝ) 25, mul_assoc, mul_div_cancel₀ _ hB]
      _ = (a21 : ℝ) ^ 3 := h25A
  have hdiff : (L - R) * (L ^ 2 + L * R + R ^ 2) = 0 := by linarith [hcube_eq, show (L - R) * (L ^ 2 + L * R + R ^ 2) = L ^ 3 - R ^ 3 by ring]
  have hq : 0 < L ^ 2 + L * R + R ^ 2 := by positivity
  rcases mul_eq_zero.mp hdiff with hlr | hzero
  · linarith
  · linarith

private lemma linform_abs_le (n : ℕ) :
    |(vSeq n : ℝ) * α - (uSeq n : ℝ)| ≤ E0 * E ^ n := by
  obtain ⟨hz0, hz1, h1z⟩ := z0_bounds
  have hE := Erem_eq_Ppoly_sub_Qpoly n hz0 hz1
  have hlin : (vSeq n : ℝ) * α - (uSeq n : ℝ) = Dscale n * (b21 : ℝ) * α * Erem n z0 := by
    rw [vSeq_spec n, uSeq_spec n, hE]
    calc Dscale n * (b21 : ℝ) * Ppoly n z0 * α - Dscale n * (a21 : ℝ) * Qpoly n z0
        = Dscale n * (b21 : ℝ) * α * Ppoly n z0 -
            Dscale n * ((b21 : ℝ) * α * (1 - z0) ^ ((1 : ℝ) / 3)) * Qpoly n z0 := by
              rw [b21_mul_alpha_mul_cbrt_eq_a21]; ring
      _ = Dscale n * (b21 : ℝ) * α * (Ppoly n z0 - (1 - z0) ^ ((1 : ℝ) / 3) * Qpoly n z0) := by ring
  obtain ⟨hE0_nn, hE_up⟩ := Erem_bounds n hz0 hz1
  have hD_pos : 0 ≤ Dscale n := by unfold Dscale; positivity
  have hb_pos : 0 ≤ (b21 : ℝ) := Nat.cast_nonneg _
  have hα_pos := alpha_pos_cube.1
  have hα_lt3 := alpha_bounds.2
  rw [hlin, abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hD_pos hb_pos) hα_pos.le) hE0_nn)]
  have hrew : Dscale n * (b21 : ℝ) * α * ((1 / 3) * z0 ^ (2 * n + 1) / (4 ^ n * (1 - z0) ^ (n + 1))) ≤
      E0 * E ^ n := by
    have h1z_pow : (1 - z0) ^ (n + 1) = (A0 : ℝ) ^ (n + 1) / (B0 : ℝ) ^ (n + 1) := by
      rw [h1z, div_pow]
    have hz_pow : z0 ^ (2 * n + 1) = (C0 : ℝ) ^ (2 * n + 1) / (B0 : ℝ) ^ (2 * n + 1) := by
      unfold z0; rw [div_pow]
    have hB : (B0 : ℝ) ≠ 0 := by unfold B0 b21; norm_num
    have hA : (A0 : ℝ) ≠ 0 := by unfold A0 a1; norm_num
    have hsimp : Dscale n * (b21 : ℝ) * 3 * ((1 / 3) * z0 ^ (2 * n + 1) / (4 ^ n * (1 - z0) ^ (n + 1))) =
        ((b21 : ℝ) * (C0 : ℝ) / (A0 : ℝ)) *
          ((3 : ℝ) ^ (n / 2) * ((C0 : ℝ) ^ 2 / (4 * (A0 : ℝ))) ^ n) := by
      unfold Dscale
      rw [hz_pow, h1z_pow]
      rw [show (2 * n + 1 : ℕ) = 1 + 2 * n by omega, pow_add (C0 : ℝ), pow_mul (C0 : ℝ)]
      rw [pow_succ (A0 : ℝ) n]
      have hBpow : (B0 : ℝ) ^ (1 + 2 * n) = (B0 : ℝ) ^ n * (B0 : ℝ) ^ (n + 1) := by
        rw [← pow_add, show n + (n + 1) = 1 + 2 * n by omega]
      rw [hBpow, div_pow (C0 ^ 2 : ℝ)]
      field_simp [hB, hA]
      ring
    have hE0_ok : (b21 : ℝ) * (C0 : ℝ) / (A0 : ℝ) ≤ E0 := by
      unfold E0 b21 C0 A0 a1; norm_num
    have hE_ok : (1733 / 1000 : ℝ) * ((C0 : ℝ) ^ 2 / (4 * (A0 : ℝ))) ≤ E := by
      unfold E C0 A0 a1; norm_num
    have h1 : Dscale n * (b21 : ℝ) * α * ((1 / 3) * z0 ^ (2 * n + 1) / (4 ^ n * (1 - z0) ^ (n + 1))) ≤
        Dscale n * (b21 : ℝ) * 3 * ((1 / 3) * z0 ^ (2 * n + 1) / (4 ^ n * (1 - z0) ^ (n + 1))) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hα_lt3.le (mul_nonneg hD_pos hb_pos)
    refine le_trans h1 ?_
    rw [hsimp]
    calc ((b21 : ℝ) * (C0 : ℝ) / (A0 : ℝ)) * ((3 : ℝ) ^ (n / 2) * ((C0 : ℝ) ^ 2 / (4 * (A0 : ℝ))) ^ n)
        ≤ E0 * ((1733 / 1000 : ℝ) ^ n * ((C0 : ℝ) ^ 2 / (4 * (A0 : ℝ))) ^ n) :=
          mul_le_mul hE0_ok (mul_le_mul_of_nonneg_right (three_pow_half_le n) (by positivity))
            (by positivity) (by unfold E0; positivity)
      _ = E0 * ((1733 / 1000 : ℝ) * ((C0 : ℝ) ^ 2 / (4 * (A0 : ℝ)))) ^ n := by rw [← mul_pow]
      _ ≤ E0 * E ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hE_ok n)
            (by unfold E0; positivity)
  exact le_trans (mul_le_mul_of_nonneg_left hE_up (mul_nonneg (mul_nonneg hD_pos hb_pos) hα_pos.le)) hrew

/-! ## 4. Main Padé Tail Theorem (`y1 > 10^276`) -/

theorem pade_no_thue_solution_gt_10_pow_276 {x1 y1 : ℕ}
    (hy : 10 ^ 276 < y1) (hx : 29 * y1 ≤ 10 * x1)
    (hd_pos : 0 < 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3)
    (hd_le : 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 ≤ 15600) : False := by
  have hy_pos : (0 : ℝ) < (y1 : ℝ) := by
    have : 0 < y1 := by omega
    exact Nat.cast_pos.mpr this
  obtain ⟨hα_pos, hα_cube⟩ := alpha_pos_cube
  obtain ⟨hα_lo, _⟩ := alpha_bounds
  have hy_r : (10 : ℝ) ^ 276 < (y1 : ℝ) := by exact_mod_cast hy
  have hx_r : (29 / 10 : ℝ) * (y1 : ℝ) ≤ (x1 : ℝ) := by
    have : (29 * y1 : ℝ) ≤ 10 * x1 := by exact_mod_cast hx
    linarith
  have hd_pos_r : 0 < 25 * (y1 : ℝ) ^ 3 - (x1 : ℝ) ^ 3 := by exact_mod_cast hd_pos
  have hd_le_r : 25 * (y1 : ℝ) ^ 3 - (x1 : ℝ) ^ 3 ≤ 15600 := by exact_mod_cast hd_le
  have hxy_lt : (x1 : ℝ) < (y1 : ℝ) * α := by
    by_contra h
    have hge : (y1 : ℝ) * α ≤ (x1 : ℝ) := le_of_not_gt h
    have h3 : ((y1 : ℝ) * α) ^ 3 ≤ (x1 : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hge 3
    rw [mul_pow, hα_cube] at h3
    linarith
  have hdiff_id : (((y1 : ℝ) * α) ^ 2 + ((y1 : ℝ) * α) * (x1 : ℝ) + (x1 : ℝ) ^ 2) *
      ((y1 : ℝ) * α - (x1 : ℝ)) = 25 * (y1 : ℝ) ^ 3 - (x1 : ℝ) ^ 3 := by
    calc (((y1 : ℝ) * α) ^ 2 + ((y1 : ℝ) * α) * (x1 : ℝ) + (x1 : ℝ) ^ 2) * ((y1 : ℝ) * α - (x1 : ℝ))
        = (y1 : ℝ) ^ 3 * α ^ 3 - (x1 : ℝ) ^ 3 := by ring
      _ = 25 * (y1 : ℝ) ^ 3 - (x1 : ℝ) ^ 3 := by rw [hα_cube]; ring
  have hquad_lo : 25 * (y1 : ℝ) ^ 2 ≤ ((y1 : ℝ) * α) ^ 2 + ((y1 : ℝ) * α) * (x1 : ℝ) + (x1 : ℝ) ^ 2 := by
    have h1 : (29 / 10 : ℝ) * (y1 : ℝ) ≤ (y1 : ℝ) * α := by
      linarith [mul_lt_mul_of_pos_right hα_lo hy_pos]
    have h29_pos : (0 : ℝ) ≤ (29 / 10 : ℝ) * (y1 : ℝ) := by positivity
    have hs1 : (841 / 100 : ℝ) * (y1 : ℝ) ^ 2 ≤ ((y1 : ℝ) * α) ^ 2 := by
      have h := pow_le_pow_left₀ h29_pos h1 2
      rw [mul_pow] at h
      calc (841 / 100 : ℝ) * (y1 : ℝ) ^ 2 = ((29 / 10 : ℝ) ^ 2) * (y1 : ℝ) ^ 2 := by norm_num
        _ ≤ ((y1 : ℝ) * α) ^ 2 := h
    have hs2 : (841 / 100 : ℝ) * (y1 : ℝ) ^ 2 ≤ ((y1 : ℝ) * α) * (x1 : ℝ) := by
      have h := mul_le_mul h1 hx_r h29_pos (mul_nonneg hy_pos.le hα_pos.le)
      calc (841 / 100 : ℝ) * (y1 : ℝ) ^ 2 = ((29 / 10 : ℝ) * (y1 : ℝ)) * ((29 / 10 : ℝ) * (y1 : ℝ)) := by ring
        _ ≤ ((y1 : ℝ) * α) * (x1 : ℝ) := h
    have hs3 : (841 / 100 : ℝ) * (y1 : ℝ) ^ 2 ≤ (x1 : ℝ) ^ 2 := by
      have h := pow_le_pow_left₀ h29_pos hx_r 2
      rw [mul_pow] at h
      calc (841 / 100 : ℝ) * (y1 : ℝ) ^ 2 = ((29 / 10 : ℝ) ^ 2) * (y1 : ℝ) ^ 2 := by norm_num
        _ ≤ (x1 : ℝ) ^ 2 := h
    linarith [pow_nonneg hy_pos.le 2]
  have hdioph : |(y1 : ℝ) * α - (x1 : ℝ)| ≤ 624 / (y1 : ℝ) ^ 2 := by
    rw [abs_of_pos (sub_pos.mpr hxy_lt)]
    have hmul : 25 * (y1 : ℝ) ^ 2 * ((y1 : ℝ) * α - (x1 : ℝ)) ≤ 15600 := by
      have hnonneg : 0 ≤ (y1 : ℝ) * α - (x1 : ℝ) := sub_nonneg.mpr hxy_lt.le
      calc 25 * (y1 : ℝ) ^ 2 * ((y1 : ℝ) * α - (x1 : ℝ))
          ≤ (((y1 : ℝ) * α) ^ 2 + ((y1 : ℝ) * α) * (x1 : ℝ) + (x1 : ℝ) ^ 2) * ((y1 : ℝ) * α - (x1 : ℝ)) :=
            mul_le_mul_of_nonneg_right hquad_lo hnonneg
        _ = 25 * (y1 : ℝ) ^ 3 - (x1 : ℝ) ^ 3 := hdiff_id
        _ ≤ 15600 := hd_le_r
    rw [le_div_iff₀ (pow_pos hy_pos 2)]
    linarith
  have hM0_pos : 0 < M0 := by unfold M0; norm_num
  have hM_gt1 : 1 < M := by unfold M; norm_num
  have hM_pos : 0 < M := by linarith
  have h18_lt : 1248 * M0 * M ^ 18 < (y1 : ℝ) ^ 2 := by
    have hM_lt : M < 10 ^ 26 := by unfold M; norm_num
    have hM0_lt : 1248 * M0 < 10 ^ 12 := by unfold M0; norm_num
    have h18_le : M ^ 18 ≤ (10 ^ 26 : ℝ) ^ 18 := pow_le_pow_left₀ hM_pos.le hM_lt.le 18
    have h480 : 1248 * M0 * M ^ 18 < (10 : ℝ) ^ 480 := by
      calc 1248 * M0 * M ^ 18
          ≤ 1248 * M0 * (10 ^ 26 : ℝ) ^ 18 :=
            mul_le_mul_of_nonneg_left h18_le (mul_nonneg (by positivity) hM0_pos.le)
        _ < (10 : ℝ) ^ 12 * (10 ^ 26 : ℝ) ^ 18 :=
            mul_lt_mul_of_pos_right hM0_lt (by positivity)
        _ = (10 : ℝ) ^ 480 := by rw [← pow_mul, ← pow_add]
    have h480_552 : (10 : ℝ) ^ 480 < (10 : ℝ) ^ 552 :=
      pow_lt_pow_right₀ (by norm_num) (by norm_num)
    have hsq : ((10 : ℝ) ^ 276) ^ 2 = (10 : ℝ) ^ 552 := by rw [← pow_mul]
    have hy2_0 : ((10 : ℝ) ^ 276) ^ 2 < (y1 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ hy_r (pow_nonneg (by norm_num) 276) (by decide : 2 ≠ 0)
    have hy2 : (10 : ℝ) ^ 552 < (y1 : ℝ) ^ 2 := hsq ▸ hy2_0
    exact lt_trans (lt_trans h480 h480_552) hy2
  have hex : ∃ m : ℕ, ¬ (1248 * M0 * M ^ (m + 1) < (y1 : ℝ) ^ 2) := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (1248 * M0) / (y1 : ℝ) ^ 2 by positivity)
      (show (1 / M : ℝ) < 1 by rw [div_lt_one hM_pos]; exact hM_gt1)
    refine ⟨m, ?_⟩
    push Not
    have hm_pos : 0 < M ^ m := pow_pos hM_pos m
    rw [one_div, inv_pow, lt_div_iff₀ (pow_pos hy_pos 2)] at hm
    have hm' := mul_lt_mul_of_pos_right hm hm_pos
    rw [mul_assoc ((M ^ m)⁻¹), mul_comm ((y1 : ℝ) ^ 2) (M ^ m), ← mul_assoc ((M ^ m)⁻¹),
      inv_mul_cancel₀ hm_pos.ne', one_mul] at hm'
    exact le_trans hm'.le (by
      calc 1248 * M0 * M ^ m = 1248 * M0 * M ^ m * 1 := by ring
        _ ≤ 1248 * M0 * M ^ m * M := mul_le_mul_of_nonneg_left hM_gt1.le (by positivity)
        _ = 1248 * M0 * M ^ (m + 1) := by rw [pow_succ]; ring)
  classical
  set m : ℕ := Nat.find hex
  have hm_not : ¬ (1248 * M0 * M ^ (m + 1) < (y1 : ℝ) ^ 2) := Nat.find_spec hex
  have hm_ge18 : 18 ≤ m := by
    by_contra hlt
    have hm_le17 : m + 1 ≤ 18 := by omega
    have hpow : M ^ (m + 1) ≤ M ^ 18 := pow_le_pow_right₀ hM_gt1.le hm_le17
    have hlt' : 1248 * M0 * M ^ (m + 1) < (y1 : ℝ) ^ 2 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow (by positivity)) h18_lt
    exact hm_not hlt'
  set n : ℕ := m - 1
  have hn_ge17 : 17 ≤ n := by omega
  have hm_eq : m = n + 1 := by omega
  have h_lo : 1248 * M0 * M ^ (n + 1) < (y1 : ℝ) ^ 2 := by
    have hfind := Nat.find_min hex (show n < m by omega)
    push Not at hfind
    simpa [hm_eq] using hfind
  have h_hi : (y1 : ℝ) ^ 2 ≤ 1248 * M0 * M ^ (n + 2) := by
    have hle := le_of_not_gt hm_not
    simpa [hm_eq, Nat.add_assoc] using hle
  have hpick : ∃ k : ℕ, (k = n ∨ k = n + 1) ∧ (x1 : ℤ) * vSeq k - (y1 : ℤ) * uSeq k ≠ 0 := by
    by_cases h0 : (x1 : ℤ) * vSeq n - (y1 : ℤ) * uSeq n = 0
    · refine ⟨n + 1, Or.inr rfl, ?_⟩
      intro h1
      have hmul0 : (y1 : ℤ) * (uSeq n * vSeq (n + 1) - uSeq (n + 1) * vSeq n) = 0 := by
        linear_combination vSeq (n + 1) * (-h0) - vSeq n * (-h1)
      rcases mul_eq_zero.mp hmul0 with hy0 | hwr
      · have : (y1 : ℤ) ≠ 0 := by exact_mod_cast (by omega : y1 ≠ 0)
        exact this hy0
      · exact wronskian_ne_zero n hwr
    · exact ⟨n, Or.inl rfl, h0⟩
  rcases hpick with ⟨k, hk_cases, hnz_int⟩
  have h_ge1 : (1 : ℝ) ≤ |((x1 : ℝ) * (vSeq k : ℝ) - (y1 : ℝ) * (uSeq k : ℝ))| := by
    have h1 : 1 ≤ Int.natAbs ((x1 : ℤ) * vSeq k - (y1 : ℤ) * uSeq k) :=
      Int.natAbs_pos.mpr hnz_int
    have h1r : (1 : ℝ) ≤ ((Int.natAbs ((x1 : ℤ) * vSeq k - (y1 : ℤ) * uSeq k) : ℕ) : ℝ) := by
      exact_mod_cast h1
    simpa [Int.cast_abs] using h1r
  have hv_k : |(vSeq k : ℝ)| ≤ M0 * M ^ (n + 1) := by
    rcases hk_cases with hkn | hkn
    · rw [hkn]
      exact le_trans (vSeq_abs_le n) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM_gt1.le (Nat.le_succ n)) hM0_pos.le)
    · rw [hkn]
      exact vSeq_abs_le (n + 1)
  have hlin_k : |(vSeq k : ℝ) * α - (uSeq k : ℝ)| ≤ E0 * E ^ n := by
    have hE0_pos : 0 ≤ E0 := by unfold E0; norm_num
    have hE_pos : 0 ≤ E := by unfold E; norm_num
    have hE_le1 : E ≤ 1 := by unfold E; norm_num
    rcases hk_cases with hkn | hkn
    · rw [hkn]
      exact linform_abs_le n
    · rw [hkn]
      exact le_trans (linform_abs_le (n + 1)) (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hE_pos hE_le1 (Nat.le_succ n)) hE0_pos)
  have hterm1 : |(vSeq k : ℝ)| * |(y1 : ℝ) * α - (x1 : ℝ)| < 1 / 2 := by
    have h1 : |(vSeq k : ℝ)| * |(y1 : ℝ) * α - (x1 : ℝ)| ≤ (M0 * M ^ (n + 1)) * (624 / (y1 : ℝ) ^ 2) :=
      mul_le_mul hv_k hdioph (abs_nonneg _) (by positivity)
    have h2 : (M0 * M ^ (n + 1)) * (624 / (y1 : ℝ) ^ 2) < 1 / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ (pow_pos hy_pos 2) (by norm_num : (0 : ℝ) < 2)]
      linarith [h_lo]
    exact lt_of_le_of_lt h1 h2
  have hterm2 : (y1 : ℝ) * |(vSeq k : ℝ) * α - (uSeq k : ℝ)| < 1 / 2 := by
    have hE0_pos : 0 < E0 := by unfold E0; norm_num
    have hE_pos : 0 < E := by unfold E; norm_num
    have hME2_le : M * E ^ 2 ≤ 1 / 400 := by unfold M E; norm_num
    have hsq_lt : (2 * (y1 : ℝ) * E0 * E ^ n) ^ 2 < 1 := by
      have hpow_17 : (M * E ^ 2) ^ n ≤ (1 / 400 : ℝ) ^ 17 :=
        le_trans (pow_le_pow_left₀ (by positivity) hME2_le n)
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn_ge17)
      have hnum_lt : 4992 * M0 * E0 ^ 2 * M ^ 2 * (1 / 400 : ℝ) ^ 17 < 1 := by
        unfold M0 E0 M; norm_num
      calc (2 * (y1 : ℝ) * E0 * E ^ n) ^ 2
          = 4 * E0 ^ 2 * (E ^ 2) ^ n * (y1 : ℝ) ^ 2 := by rw [← pow_mul, mul_comm 2 n, pow_mul]; ring
        _ ≤ 4 * E0 ^ 2 * (E ^ 2) ^ n * (1248 * M0 * M ^ (n + 2)) :=
            mul_le_mul_of_nonneg_left h_hi (by positivity)
        _ = 4992 * M0 * E0 ^ 2 * M ^ 2 * (M * E ^ 2) ^ n := by
            rw [pow_add, mul_pow]; ring
        _ ≤ 4992 * M0 * E0 ^ 2 * M ^ 2 * (1 / 400 : ℝ) ^ 17 :=
            mul_le_mul_of_nonneg_left hpow_17 (by positivity)
        _ < 1 := hnum_lt
    have h2_lt : 2 * (y1 : ℝ) * E0 * E ^ n < 1 := by
      by_contra h
      have hge : 1 ≤ 2 * (y1 : ℝ) * E0 * E ^ n := le_of_not_gt h
      nlinarith
    have h1 : (y1 : ℝ) * |(vSeq k : ℝ) * α - (uSeq k : ℝ)| ≤ (y1 : ℝ) * (E0 * E ^ n) :=
      mul_le_mul_of_nonneg_left hlin_k hy_pos.le
    linarith
  have htri : |((x1 : ℝ) * (vSeq k : ℝ) - (y1 : ℝ) * (uSeq k : ℝ))| ≤
      |(vSeq k : ℝ)| * |(y1 : ℝ) * α - (x1 : ℝ)| + (y1 : ℝ) * |(vSeq k : ℝ) * α - (uSeq k : ℝ)| := by
    have hid : (x1 : ℝ) * (vSeq k : ℝ) - (y1 : ℝ) * (uSeq k : ℝ) =
        (-(vSeq k : ℝ)) * ((y1 : ℝ) * α - (x1 : ℝ)) + (y1 : ℝ) * ((vSeq k : ℝ) * α - (uSeq k : ℝ)) := by
      ring
    rw [hid]
    calc |(-(vSeq k : ℝ)) * ((y1 : ℝ) * α - (x1 : ℝ)) + (y1 : ℝ) * ((vSeq k : ℝ) * α - (uSeq k : ℝ))|
        ≤ |(-(vSeq k : ℝ)) * ((y1 : ℝ) * α - (x1 : ℝ))| + |(y1 : ℝ) * ((vSeq k : ℝ) * α - (uSeq k : ℝ))| :=
          abs_add_le _ _
      _ = |(vSeq k : ℝ)| * |(y1 : ℝ) * α - (x1 : ℝ)| + (y1 : ℝ) * |(vSeq k : ℝ) * α - (uSeq k : ℝ)| := by
          rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hy_pos.le]
  linarith [h_ge1, htri, hterm1, hterm2]

end Pade

/-! ## Bridging Extra Convergents (`10^73 < y1 ≤ 10^276`) and Final Theorems -/

private theorem excl_conv_275 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 10 ^ 73 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 10 ^ 140) : False :=
  Reduction.upper_cubic_approx_excludes_window
    (p := 315422583239487876282947656193790809099221195488433754213830516211369756212794960476533286207910346459278315593960679763413098610203157272843)
    (q := 107873006075630507650921241318740563946786489441337506235240053216569031926106228746329537204603235379907191057615954992812239120888589748925)
    (c := 273878916565723096484188742145415304052626729675160102782632757276433947513168025085456032812327920729354292661517017699068430460477979832982)
    (ylo := 10 ^ 73)
    (yhi := 10 ^ 140)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (le_trans (by norm_num : 30 ≤ 10 ^ 73) h1) h1 h2

private theorem excl_conv_511 {m n : ℕ} (hmn : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)))
    (h1 : 10 ^ 140 ≤ (n + 2) / Nat.gcd (m + 2) (n + 2))
    (h2 : (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ (10 ^ 138) ^ 2) : False :=
  Reduction.upper_cubic_approx_excludes_window
    (p := 4402555720167675715655797140938604777651500162735010480200875406607096001598236477604117331405123702036785863222405141303177624816350601734978882212225063199705313456304716949301754871502792674658492773869414258796171224982480233590644643921633243998111665746616674644863261953)
    (q := 1505652877078125752359304589006642835748068802004543852801040378201684112715058028428081045437023928030440317476999212082900297075232953005699940584170220870690506740959661686553367554522882044726252047635093223958139626038549159521165363195257963170758228941967321838912559357)
    (c := 3234360307005490581888429624539469296571746237395437645835800039341646637583330810312476492034753848282576274186393996655752329922809044999590435047149559879626779684173002024997596648644150304693278724064459396497717543939710658996978827540864514174394847591135501106221362852)
    (ylo := 10 ^ 140)
    (yhi := (10 ^ 138) ^ 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hmn heq (le_trans (by norm_num : 30 ≤ 10 ^ 140) h1) h1 h2

/-- Extended pure-integer convergent exclusion up to `y1 ≤ 10^276`. -/
theorem no_k3_solution_y1_le_10_pow_276 :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧ (n + 2) / Nat.gcd (m + 2) (n + 2) ≤ 10 ^ 276 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, hy_le, heq⟩
  set y1 := (n + 2) / Nat.gcd (m + 2) (n + 2)
  by_cases h1 : y1 ≤ 10 ^ 73
  · exact Reduction.no_k3_solution_y1_le_10_pow_73 ⟨m, n, hmn, h1, heq⟩
  · have h73 : 10 ^ 73 ≤ y1 := Nat.le_of_lt (Nat.not_le.mp h1)
    by_cases h2 : y1 ≤ 10 ^ 140
    · exact excl_conv_275 hmn heq h73 h2
    · have h140 : 10 ^ 140 ≤ y1 := Nat.le_of_lt (Nat.not_le.mp h2)
      have hpow : (10 ^ 138 : ℕ) ^ 2 = 10 ^ 276 := by
        conv_rhs => rw [show (276 : ℕ) = 138 * 2 by norm_num, pow_mul]
      rw [← hpow] at hy_le
      exact excl_conv_511 hmn heq h140 hy_le

/-- Full unconditional `k = 3` exclusion for Erdős #686 (`N = 25`) with `m ≥ n + 3`. -/
theorem no_sol_twenty_five_three :
    ¬ ∃ m n : ℕ, m ≥ n + 3 ∧
      (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨m, n, hmn, heq⟩
  set D := Nat.gcd (m + 2) (n + 2)
  set x1 := (m + 2) / D
  set y1 := (n + 2) / D
  by_cases hy : y1 ≤ 10 ^ 276
  · exact no_k3_solution_y1_le_10_pow_276 ⟨m, n, hmn, hy, heq⟩
  · have hy_gt : 10 ^ 276 < y1 := Nat.not_le.mp hy
    have h30_276 : 30 ≤ 10 ^ 276 := by
      have h30 : 30 ≤ (10 ^ 138 : ℕ) := by norm_num
      have hpow1 : (10 ^ 138 : ℕ) ≤ (10 ^ 138 : ℕ) ^ 2 :=
        Nat.le_self_pow (by norm_num : 2 ≠ 0) _
      have hpow2 : (10 ^ 138 : ℕ) ^ 2 = 10 ^ 276 := by
        conv_rhs => rw [show (276 : ℕ) = 138 * 2 by norm_num, pow_mul]
      rw [← hpow2]
      exact le_trans h30 hpow1
    have hy30 : 30 ≤ y1 := le_trans h30_276 hy_gt.le
    have hx : 29 * y1 ≤ 10 * x1 := Reduction.twenty_nine_y1_le_ten_x1 hmn heq hy30
    rcases Reduction.k3_thue_reduction hmn heq with
      ⟨_, _, _, _, _, _, hd_pos, _, _, _, hd_mem, _, _, _, _⟩
    have hd_pos' : 0 < 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 := hd_pos
    have hd_dvd : (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3).natAbs ∣ 15600 :=
      (Nat.mem_divisors.mp hd_mem).1
    have hd_abs_le : (25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3).natAbs ≤ 15600 :=
      Nat.le_of_dvd (by norm_num) hd_dvd
    have hd_le : 25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3 ≤ 15600 := by
      have hcoe : ((25 * (y1 : ℤ) ^ 3 - (x1 : ℤ) ^ 3).natAbs : ℤ) ≤ 15600 := by
        exact_mod_cast hd_abs_le
      rwa [Int.natAbs_of_nonneg hd_pos'.le] at hcoe
    exact Pade.pade_no_thue_solution_gt_10_pow_276 hy_gt hx hd_pos' hd_le

/-- Unrestricted `k = 3` product exclusion: no `m, n : ℕ` satisfy the cubic product equation. -/
theorem no_sol_twenty_five_three_unrestricted (m n : ℕ) :
    (m + 1) * (m + 2) * (m + 3) ≠ 25 * ((n + 1) * (n + 2) * (n + 3)) := by
  intro heq
  by_cases hmn : m ≥ n + 3
  · exact no_sol_twenty_five_three ⟨m, n, hmn, heq⟩
  · have hm1 : m + 1 ≤ n + 3 := by omega
    have hm2 : m + 2 ≤ n + 4 := by omega
    have hm3 : m + 3 ≤ n + 5 := by omega
    have hprod_le : (m + 1) * (m + 2) * (m + 3) ≤ (n + 3) * (n + 4) * (n + 5) :=
      Nat.mul_le_mul (Nat.mul_le_mul hm1 hm2) hm3
    have hquad : (n + 4) * (n + 5) < 25 * ((n + 1) * (n + 2)) := by nlinarith
    have hcub : (n + 3) * ((n + 4) * (n + 5)) < (n + 3) * (25 * ((n + 1) * (n + 2))) :=
      Nat.mul_lt_mul_of_pos_left hquad (by omega)
    have hlhs : (n + 3) * ((n + 4) * (n + 5)) = (n + 3) * (n + 4) * (n + 5) := by ring
    have hrhs : (n + 3) * (25 * ((n + 1) * (n + 2))) = 25 * ((n + 1) * (n + 2) * (n + 3)) := by ring
    rw [hlhs, hrhs] at hcub
    omega

private lemma prod_Icc_three (a : ℕ) :
    ∏ i ∈ Finset.Icc 1 3, (a + i) = (a + 1) * (a + 2) * (a + 3) := by
  simp only [Finset.prod_Icc_succ_top (by decide : 1 ≤ 3),
    Finset.prod_Icc_succ_top (by decide : 1 ≤ 2),
    Finset.Icc_self, Finset.prod_singleton]

/-- `Finset.Icc 1 3` form of the unrestricted exclusion. -/
theorem no_sol_twenty_five_three_Icc (m n : ℕ) :
    ∏ i ∈ Finset.Icc 1 3, (m + i) ≠ 25 * ∏ i ∈ Finset.Icc 1 3, (n + i) := by
  rw [prod_Icc_three m, prod_Icc_three n]
  exact no_sol_twenty_five_three_unrestricted m n

/-- Rational quotient exclusion matching `Erdos686.erdos_686.variants.twenty_five`. -/
theorem no_ratio_twenty_five_three (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 3, (m + i)) / (∏ i ∈ Finset.Icc 1 3, (n + i)) := by
  intro h
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton] at h
  have hd : ((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3) ≠ 0 := by positivity
  have h1 : (25 : ℚ) = ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) /
      (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3)) := by
    simpa [mul_assoc] using h
  have hz : (25 : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) + 3)) =
      ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) := (eq_div_iff hd).mp h1
  have hn : 25 * ((n + 1) * (n + 2) * (n + 3)) = (m + 1) * (m + 2) * (m + 3) := by
    exact_mod_cast hz
  exact no_sol_twenty_five_three_unrestricted m n hn.symm

/-- Bridge theorem discharging the `k = 3` branch of `Erdos686.erdos_686.variants.twenty_five`. -/
theorem erdos_686_variants_twenty_five_k3_bridge :
    ¬ ∃ n : ℕ, ∃ m ≥ n + 3,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 3, (m + i)) / (∏ i ∈ Finset.Icc 1 3, (n + i)) := by
  rintro ⟨n, m, _, h⟩
  exact no_ratio_twenty_five_three m n h

end Contribution.Erdos686ThreeTwentyFive
