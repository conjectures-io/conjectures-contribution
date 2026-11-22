import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Universal Structural Bounds for Erdős Problem #686 (N = 25, All k ≥ 2)

Formalizes the universal structural lemmas for any integer solution
`m, n : ℕ`, `k ≥ 2`, `m ≥ n + k` to
`∏ i ∈ Finset.Icc 1 k, (m + i) = 25 * ∏ i ∈ Finset.Icc 1 k, (n + i)`:
1. Exact ratio sandwich (`ratio_upper_pow_nat`, `ratio_lower_pow_nat`, `ratio_sandwich_rat`).
2. Linear gap upper bound (`gap_upper_bound`) and quadratic lower bound on `n` (`quadratic_lower_bound`,
   `quadratic_lower_bound_k_ge_8`, `quadratic_lower_bound_k_ge_16`).
3. Prime-divisor transfer (`prime_dvd_transfer`), uniqueness in blocks (`prime_unique_in_block`),
   and upper bound `p ≤ (m - n) + k - 1` (`prime_upper_bound`).
4. Exact 5-adic valuation shift (`padicValNat_five_shift`).
-/

namespace Contribution.Erdos686GeneralBoundsTwentyFive

private lemma mul_lt_mul_of_le_of_pos_nat {a b c d : ℕ}
    (hab : a < b) (hcd : c ≤ d) (hc : 0 < c) : a * c < b * d :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hab hc) (Nat.mul_le_mul_left b hcd)

lemma prod_Icc_pos (k m : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 k, (m + i) := by
  apply Nat.pos_of_ne_zero
  intro h0
  obtain ⟨i, hi, hzi⟩ := Finset.prod_eq_zero_iff.mp h0
  rw [Finset.mem_Icc] at hi
  omega

/-- Exact upper power bound: `(m + k)^k < 25 * (n + k)^k`. -/
theorem ratio_upper_pow_nat {k m n : ℕ} (hk : 2 ≤ k) (hnm : n < m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    (m + k) ^ k < 25 * (n + k) ^ k := by
  have h1mem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  have hL_prod : ∏ i ∈ Finset.Icc 1 k, ((m + k) * (n + i)) =
      (m + k) ^ k * ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hR_prod : ∏ i ∈ Finset.Icc 1 k, ((m + i) * (n + k)) =
      (∏ i ∈ Finset.Icc 1 k, (m + i)) * (n + k) ^ k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have h_pt : ∀ i ∈ (Finset.Icc 1 k).erase 1, (m + k) * (n + i) ≤ (m + i) * (n + k) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)
    nlinarith [hi'.1, hi'.2]
  have h_erase_le : ∏ i ∈ (Finset.Icc 1 k).erase 1, ((m + k) * (n + i)) ≤
      ∏ i ∈ (Finset.Icc 1 k).erase 1, ((m + i) * (n + k)) :=
    Finset.prod_le_prod' h_pt
  have h_erase_pos : 0 < ∏ i ∈ (Finset.Icc 1 k).erase 1, ((m + k) * (n + i)) := by
    apply Nat.pos_of_ne_zero
    intro h0
    obtain ⟨i, hi, hzi⟩ := Finset.prod_eq_zero_iff.mp h0
    have hi' := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)
    nlinarith [hi'.1]
  have h1_lt : (m + k) * (n + 1) < (m + 1) * (n + k) := by nlinarith
  have h_splitL := (Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => (m + k) * (n + i)) h1mem).symm
  have h_splitR := (Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => (m + i) * (n + k)) h1mem).symm
  have h_strict : ∏ i ∈ Finset.Icc 1 k, ((m + k) * (n + i)) <
      ∏ i ∈ Finset.Icc 1 k, ((m + i) * (n + k)) := by
    rw [h_splitL, h_splitR]
    exact mul_lt_mul_of_le_of_pos_nat h1_lt h_erase_le h_erase_pos
  have hPn_pos : 0 < ∏ i ∈ Finset.Icc 1 k, (n + i) := prod_Icc_pos k n
  have hmul : (m + k) ^ k * (∏ i ∈ Finset.Icc 1 k, (n + i)) <
      (25 * (n + k) ^ k) * (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
    calc (m + k) ^ k * (∏ i ∈ Finset.Icc 1 k, (n + i))
        = ∏ i ∈ Finset.Icc 1 k, ((m + k) * (n + i)) := hL_prod.symm
      _ < ∏ i ∈ Finset.Icc 1 k, ((m + i) * (n + k)) := h_strict
      _ = (∏ i ∈ Finset.Icc 1 k, (m + i)) * (n + k) ^ k := hR_prod
      _ = (25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) * (n + k) ^ k := by rw [heq]
      _ = (25 * (n + k) ^ k) * (∏ i ∈ Finset.Icc 1 k, (n + i)) := by ring
  exact Nat.lt_of_mul_lt_mul_right hmul

/-- Exact lower power bound: `25 * (n + 1)^k < (m + 1)^k`. -/
theorem ratio_lower_pow_nat {k m n : ℕ} (hk : 2 ≤ k) (hnm : n < m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    25 * (n + 1) ^ k < (m + 1) ^ k := by
  have hkmem : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hcard : (Finset.Icc 1 k).card = k := by simp [Nat.card_Icc]
  have hL_prod : ∏ i ∈ Finset.Icc 1 k, ((m + i) * (n + 1)) =
      (∏ i ∈ Finset.Icc 1 k, (m + i)) * (n + 1) ^ k := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hR_prod : ∏ i ∈ Finset.Icc 1 k, ((m + 1) * (n + i)) =
      (m + 1) ^ k * ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have h_pt : ∀ i ∈ (Finset.Icc 1 k).erase k, (m + i) * (n + 1) ≤ (m + 1) * (n + i) := by
    intro i hi
    have hi' := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)
    nlinarith [hi'.1, hi'.2]
  have h_erase_le : ∏ i ∈ (Finset.Icc 1 k).erase k, ((m + i) * (n + 1)) ≤
      ∏ i ∈ (Finset.Icc 1 k).erase k, ((m + 1) * (n + i)) :=
    Finset.prod_le_prod' h_pt
  have h_erase_pos : 0 < ∏ i ∈ (Finset.Icc 1 k).erase k, ((m + i) * (n + 1)) := by
    apply Nat.pos_of_ne_zero
    intro h0
    obtain ⟨i, hi, hzi⟩ := Finset.prod_eq_zero_iff.mp h0
    have hi' := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)
    nlinarith [hi'.1]
  have hk_lt : (m + k) * (n + 1) < (m + 1) * (n + k) := by nlinarith
  have h_splitL := (Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => (m + i) * (n + 1)) hkmem).symm
  have h_splitR := (Finset.mul_prod_erase (Finset.Icc 1 k) (fun i => (m + 1) * (n + i)) hkmem).symm
  have h_strict : ∏ i ∈ Finset.Icc 1 k, ((m + i) * (n + 1)) <
      ∏ i ∈ Finset.Icc 1 k, ((m + 1) * (n + i)) := by
    rw [h_splitL, h_splitR]
    exact mul_lt_mul_of_le_of_pos_nat hk_lt h_erase_le h_erase_pos
  have hPn_pos : 0 < ∏ i ∈ Finset.Icc 1 k, (n + i) := prod_Icc_pos k n
  have hmul : (25 * (n + 1) ^ k) * (∏ i ∈ Finset.Icc 1 k, (n + i)) <
      (m + 1) ^ k * (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
    calc (25 * (n + 1) ^ k) * (∏ i ∈ Finset.Icc 1 k, (n + i))
        = (25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) * (n + 1) ^ k := by ring
      _ = (∏ i ∈ Finset.Icc 1 k, (m + i)) * (n + 1) ^ k := by rw [← heq]
      _ = ∏ i ∈ Finset.Icc 1 k, ((m + i) * (n + 1)) := hL_prod.symm
      _ < ∏ i ∈ Finset.Icc 1 k, ((m + 1) * (n + i)) := h_strict
      _ = (m + 1) ^ k * (∏ i ∈ Finset.Icc 1 k, (n + i)) := hR_prod
  exact Nat.lt_of_mul_lt_mul_right hmul

/-- Rational form of the ratio sandwich: `((m + k)/(n + k))^k < 25 < ((m + 1)/(n + 1))^k`. -/
theorem ratio_sandwich_rat {k m n : ℕ} (hk : 2 ≤ k) (hnm : n < m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    (((m : ℚ) + k) / ((n : ℚ) + k)) ^ k < 25 ∧
    (25 : ℚ) < (((m : ℚ) + 1) / ((n : ℚ) + 1)) ^ k := by
  have hup_q : (((m : ℚ) + k) ^ k) < 25 * ((n : ℚ) + k) ^ k := by
    exact_mod_cast ratio_upper_pow_nat hk hnm heq
  have hlo_q : (25 : ℚ) * ((n : ℚ) + 1) ^ k < ((m : ℚ) + 1) ^ k := by
    exact_mod_cast ratio_lower_pow_nat hk hnm heq
  have hnk_pos : (0 : ℚ) < ((n : ℚ) + k) ^ k := by positivity
  have hn1_pos : (0 : ℚ) < ((n : ℚ) + 1) ^ k := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_pow]
    exact (div_lt_iff₀ hnk_pos).mpr hup_q
  · rw [div_pow]
    exact (lt_div_iff₀ hn1_pos).mpr hlo_q

/-! ### First- and Second-Order Binomial Lower Bounds and Quadratic Lower Bound on `n` -/

lemma binom_linear_le (A B : ℕ) : ∀ k : ℕ, 1 ≤ k →
    A ^ k + k * A ^ (k - 1) * B ≤ (A + B) ^ k
  | 0, hk => by omega
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := binom_linear_le A B (k + 1) (by omega)
    have hpow : A ^ (k + 1) = A * A ^ k := by ring
    calc A ^ (k + 2) + (k + 2) * A ^ (k + 1) * B
        ≤ A * (A ^ (k + 1) + (k + 1) * A ^ k * B) + B * (A ^ (k + 1) + (k + 1) * A ^ k * B) := by
          have : A * (A ^ (k + 1) + (k + 1) * A ^ k * B) + B * (A ^ (k + 1) + (k + 1) * A ^ k * B) =
              A ^ (k + 2) + (k + 2) * A ^ (k + 1) * B + (k + 1) * A ^ k * B ^ 2 := by
            rw [hpow]; ring
          omega
      _ = (A + B) * (A ^ (k + 1) + (k + 1) * A ^ k * B) := by ring
      _ ≤ (A + B) * (A + B) ^ (k + 1) := Nat.mul_le_mul_left (A + B) ih
      _ = (A + B) ^ (k + 2) := by ring

lemma binom_quad_le (A B : ℕ) : ∀ k : ℕ, 2 ≤ k →
    2 * A ^ k + k * (k - 1) * A ^ (k - 2) * B ^ 2 ≤ 2 * (A + B) ^ k
  | 0, hk => by omega
  | 1, hk => by omega
  | 2, _ => by
    calc 2 * A ^ 2 + 2 * (2 - 1) * A ^ 0 * B ^ 2
        = 2 * A ^ 2 + 2 * B ^ 2 := by ring
      _ ≤ 2 * A ^ 2 + 4 * A * B + 2 * B ^ 2 := by omega
      _ = 2 * (A + B) ^ 2 := by ring
  | k + 3, _ => by
    have ih_q := binom_quad_le A B (k + 2) (by omega)
    have ih_l := binom_linear_le A B (k + 2) (by omega)
    have hA_pow1 : A ^ (k + 3) = A * A ^ (k + 2) := by ring
    have hA_pow2 : A ^ (k + 1) = A * A ^ k := by ring
    have hmulA : 2 * A ^ (k + 3) + (k + 2) * (k + 1) * A ^ (k + 1) * B ^ 2 ≤
        A * (2 * (A + B) ^ (k + 2)) := by
      calc 2 * A ^ (k + 3) + (k + 2) * (k + 1) * A ^ (k + 1) * B ^ 2
          = A * (2 * A ^ (k + 2) + (k + 2) * (k + 1) * A ^ k * B ^ 2) := by
            rw [hA_pow1, hA_pow2]; ring
        _ ≤ A * (2 * (A + B) ^ (k + 2)) := Nat.mul_le_mul_left A ih_q
    have hmulB : 2 * (k + 2) * A ^ (k + 1) * B ^ 2 ≤ B * (2 * (A + B) ^ (k + 2)) := by
      calc 2 * (k + 2) * A ^ (k + 1) * B ^ 2
          ≤ 2 * B * (A ^ (k + 2) + (k + 2) * A ^ (k + 1) * B) := by
            have : 2 * B * (A ^ (k + 2) + (k + 2) * A ^ (k + 1) * B) =
                2 * B * A ^ (k + 2) + 2 * (k + 2) * A ^ (k + 1) * B ^ 2 := by ring
            omega
        _ ≤ 2 * B * (A + B) ^ (k + 2) := Nat.mul_le_mul_left (2 * B) ih_l
        _ = B * (2 * (A + B) ^ (k + 2)) := by ring
    have hsum : (k + 3) * (k + 2) = (k + 2) * (k + 1) + 2 * (k + 2) := by ring
    calc 2 * A ^ (k + 3) + (k + 3) * (k + 2) * A ^ (k + 1) * B ^ 2
        = (2 * A ^ (k + 3) + (k + 2) * (k + 1) * A ^ (k + 1) * B ^ 2) +
            2 * (k + 2) * A ^ (k + 1) * B ^ 2 := by rw [hsum]; ring
      _ ≤ A * (2 * (A + B) ^ (k + 2)) + B * (2 * (A + B) ^ (k + 2)) := Nat.add_le_add hmulA hmulB
      _ = 2 * (A + B) ^ (k + 3) := by ring

/-- Linear gap upper bound: `k * (m - n) < 24 * (n + k)` for any solution with `m ≥ n + k`. -/
theorem gap_upper_bound {k m n : ℕ} (hk : 2 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k * (m - n) < 24 * (n + k) := by
  have hup := ratio_upper_pow_nat hk (by omega) heq
  have hm_eq : m + k = (n + k) + (m - n) := by omega
  have hlin := binom_linear_le (n + k) (m - n) k (by omega)
  rw [← hm_eq] at hlin
  have hlt : k * (n + k) ^ (k - 1) * (m - n) < 24 * (n + k) ^ k := by omega
  have hpow : (n + k) ^ k = (n + k) * (n + k) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  rw [hpow] at hlt
  have hpos : 0 < (n + k) ^ (k - 1) := pow_pos (by omega) _
  have hlt2 : (k * (m - n)) * (n + k) ^ (k - 1) < (24 * (n + k)) * (n + k) ^ (k - 1) := by
    calc (k * (m - n)) * (n + k) ^ (k - 1)
        = k * (n + k) ^ (k - 1) * (m - n) := by ring
      _ < 24 * ((n + k) * (n + k) ^ (k - 1)) := hlt
      _ = (24 * (n + k)) * (n + k) ^ (k - 1) := by ring
  exact Nat.lt_of_mul_lt_mul_right hlt2

/-- Raw quadratic lower bound: `k * (k - 1) * k^2 < 48 * (n + k)^2`. -/
theorem quadratic_lower_bound_raw {k m n : ℕ} (hk : 2 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k * (k - 1) * k ^ 2 < 48 * (n + k) ^ 2 := by
  have hup := ratio_upper_pow_nat hk (by omega) heq
  have hm_eq : m + k = (n + k) + (m - n) := by omega
  have hquad := binom_quad_le (n + k) (m - n) k hk
  rw [← hm_eq] at hquad
  have hlt : k * (k - 1) * (n + k) ^ (k - 2) * (m - n) ^ 2 < 48 * (n + k) ^ k := by omega
  have hpow : (n + k) ^ k = (n + k) ^ 2 * (n + k) ^ (k - 2) := by
    have hkeq : 2 + (k - 2) = k := by omega
    rw [← pow_add, hkeq]
  rw [hpow] at hlt
  have hpos : 0 < (n + k) ^ (k - 2) := pow_pos (by omega) _
  have hlt2 : (k * (k - 1) * (m - n) ^ 2) * (n + k) ^ (k - 2) <
      (48 * (n + k) ^ 2) * (n + k) ^ (k - 2) := by
    calc (k * (k - 1) * (m - n) ^ 2) * (n + k) ^ (k - 2)
        = k * (k - 1) * (n + k) ^ (k - 2) * (m - n) ^ 2 := by ring
      _ < 48 * ((n + k) ^ 2 * (n + k) ^ (k - 2)) := hlt
      _ = (48 * (n + k) ^ 2) * (n + k) ^ (k - 2) := by ring
  have hgap := Nat.lt_of_mul_lt_mul_right hlt2
  have hk_le : k ^ 2 ≤ (m - n) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hmul_le : k * (k - 1) * k ^ 2 ≤ k * (k - 1) * (m - n) ^ 2 :=
    Nat.mul_le_mul_left _ hk_le
  exact lt_of_le_of_lt hmul_le hgap

/-- Explicit quadratic lower bound: `k * (k - 1) < 7 * (n + k)` for all `k ≥ 2`. -/
theorem quadratic_lower_bound {k m n : ℕ} (hk : 2 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k * (k - 1) < 7 * (n + k) := by
  have hraw := quadratic_lower_bound_raw hk hmn heq
  by_contra hge
  have hle : 7 * (n + k) ≤ k * (k - 1) := by omega
  have hsq : 49 * (n + k) ^ 2 ≤ (k * (k - 1)) ^ 2 := by nlinarith
  have hkk : (k * (k - 1)) ^ 2 ≤ k * (k - 1) * k ^ 2 := by
    have hk1 : k - 1 ≤ k := Nat.sub_le k 1
    nlinarith [Nat.pow_le_pow_left hk1 2]
  have h48 : 49 * (n + k) ^ 2 < 48 * (n + k) ^ 2 := lt_of_le_of_lt (le_trans hsq hkk) hraw
  omega

/-- For `k ≥ 8`, `n ≥ 1` and `k * (k - 8) < 7 * n` follow unconditionally. -/
theorem quadratic_lower_bound_k_ge_8 {k m n : ℕ} (hk : 8 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    1 ≤ n ∧ k * (k - 8) < 7 * n := by
  have hq := quadratic_lower_bound (by omega) hmn heq
  have hsub : k * (k - 8) + 7 * k = k * (k - 1) := by
    zify [show 8 ≤ k from hk, show 1 ≤ k by omega]
    ring
  have hlt : k * (k - 8) < 7 * n := by omega
  refine ⟨by nlinarith [Nat.zero_le (k * (k - 8))], hlt⟩

/-- For `k ≥ 16`, explicit quadratic lower bound `k^2 < 14 * n`. -/
theorem quadratic_lower_bound_k_ge_16 {k m n : ℕ} (hk : 16 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k ^ 2 < 14 * n := by
  have hk8 := (quadratic_lower_bound_k_ge_8 (by omega) hmn heq).2
  have hk2 : k ≤ 2 * (k - 8) := by omega
  nlinarith [Nat.mul_le_mul_left k hk2]

/-! ### Prime-Divisor Transfer, Block Uniqueness, Upper Bound, and 5-Adic Valuation -/

private lemma coprime_prime_25 {p : ℕ} (hp : Nat.Prime p) (hp5 : p ≠ 5) : Nat.Coprime p 25 := by
  rw [hp.coprime_iff_not_dvd]
  intro h25
  have h5sq : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [h5sq] at h25
  have h5 := hp.dvd_of_dvd_pow h25
  exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5)

/-- Prime-divisor transfer: for any prime `p ≠ 5`, `p ∣ ∏ (m + i) ↔ p ∣ ∏ (n + i)`. -/
theorem prime_dvd_transfer {k m n p : ℕ} (hp : Nat.Prime p) (hp5 : p ≠ 5)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    p ∣ (∏ i ∈ Finset.Icc 1 k, (m + i)) ↔ p ∣ (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  rw [heq]
  constructor
  · intro h
    exact (coprime_prime_25 hp hp5).dvd_of_dvd_mul_left h
  · intro h
    exact dvd_mul_of_dvd_right h 25

/-- Any prime `p > k` divides at most one factor in a block of length `k`. -/
theorem prime_unique_in_block {k m p i₁ i₂ : ℕ} (hpk : k < p)
    (hi₁ : i₁ ∈ Finset.Icc 1 k) (hi₂ : i₂ ∈ Finset.Icc 1 k)
    (hd₁ : p ∣ m + i₁) (hd₂ : p ∣ m + i₂) : i₁ = i₂ := by
  rw [Finset.mem_Icc] at hi₁ hi₂
  rcases le_total i₁ i₂ with hle | hle
  · have hd : p ∣ (m + i₂) - (m + i₁) := Nat.dvd_sub hd₂ hd₁
    have hdiff_eq : (m + i₂) - (m + i₁) = i₂ - i₁ := by omega
    rw [hdiff_eq] at hd
    rcases eq_or_lt_of_le (Nat.zero_le (i₂ - i₁)) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd
      omega
  · have hd : p ∣ (m + i₁) - (m + i₂) := Nat.dvd_sub hd₁ hd₂
    have hdiff_eq : (m + i₁) - (m + i₂) = i₁ - i₂ := by omega
    rw [hdiff_eq] at hd
    rcases eq_or_lt_of_le (Nat.zero_le (i₁ - i₂)) with h0 | hpos
    · omega
    · have := Nat.le_of_dvd hpos hd
      omega

/-- Prime upper-bound lemma: any prime `p ≠ 5` dividing `∏ (m + i)` satisfies `p ≤ (m - n) + k - 1`. -/
theorem prime_upper_bound {k m n p : ℕ} (hp : Nat.Prime p) (hp5 : p ≠ 5)
    (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hdvd : p ∣ (∏ i ∈ Finset.Icc 1 k, (m + i))) :
    (∃ i ∈ Finset.Icc 1 k, ∃ j ∈ Finset.Icc 1 k, p ∣ (m + i) ∧ p ∣ (n + j)) ∧
    p ≤ (m - n) + k - 1 := by
  have hdvd_n : p ∣ (∏ i ∈ Finset.Icc 1 k, (n + i)) :=
    (prime_dvd_transfer hp hp5 heq).mp hdvd
  obtain ⟨i, hi, hpi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
  obtain ⟨j, hj, hpj⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd_n
  have hi' := Finset.mem_Icc.mp hi
  have hj' := Finset.mem_Icc.mp hj
  have hk_ge1 : 1 ≤ k := le_trans hi'.1 hi'.2
  have hsub_pos : 0 < (m + i) - (n + j) := by omega
  have hsub_dvd : p ∣ (m + i) - (n + j) := Nat.dvd_sub hpi hpj
  have hle1 : p ≤ (m + i) - (n + j) := Nat.le_of_dvd hsub_pos hsub_dvd
  have hle2 : (m + i) - (n + j) ≤ (m - n) + k - 1 := by omega
  exact ⟨⟨i, hi, j, hj, hpi, hpj⟩, le_trans hle1 hle2⟩

/-- Exact 5-adic valuation shift lemma. -/
theorem padicValNat_five_shift {k m n : ℕ}
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    padicValNat 5 (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      2 + padicValNat 5 (∏ i ∈ Finset.Icc 1 k, (n + i)) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hPn_ne : (∏ i ∈ Finset.Icc 1 k, (n + i)) ≠ 0 := (prod_Icc_pos k n).ne'
  rw [heq, padicValNat.mul (by norm_num) hPn_ne]
  have h25 : (25 : ℕ) = 5 ^ 2 := by norm_num
  rw [h25, padicValNat.prime_pow 2]

end Contribution.Erdos686GeneralBoundsTwentyFive
