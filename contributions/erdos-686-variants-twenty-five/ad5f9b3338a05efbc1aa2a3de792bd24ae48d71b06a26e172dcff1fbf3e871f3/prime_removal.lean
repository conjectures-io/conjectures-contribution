import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Erdős Prime-Removal Combinatorial & Super-Quadratic Bounds (N = 25, All k ≥ 2)

Formalizes the standalone Erdős prime-removal divisibility lemma and resulting lower bounds
on the distinct prime-factor count `ω(∏_{i=1}^k (m + i))` for any solution `k ≥ 2`, `m ≥ n + k`
to `∏ i ∈ Finset.Icc 1 k, (m + i) = 25 * ∏ i ∈ Finset.Icc 1 k, (n + i)`:
1. Standalone general bounds (`ratio_upper_pow_nat`, `quadratic_lower_bound`,
   `prime_dvd_transfer`, `prime_unique_in_block`, `prime_upper_bound`).
2. `erdos_prime_removal_dvd_factorial`: removing at most one maximizing index per prime factor
   yields `S ⊆ Finset.Icc 1 k` with `k ≤ S.card + P.card` and `∏ i ∈ S, (m + i) ∣ (k - 1)!`.
3. `erdos_prime_removal_master_bound`: `(m + 1) ^ (k - P.card) ≤ (k - 1)!` and every prime
   `p ∈ P \ {5}` satisfies `p ≤ (m - n) + k - 1`.
4. `prime_count_gt_third_k`: `51 ≤ k → k < 3 * P.card`.
5. `prime_count_ratio_lower_bound`: `1 ≤ r → 7 ^ r * k ≤ (k - 1) ^ r → k < (r + 1) * P.card`.
6. `prime_count_gt_half_k`: `11 ≤ k → k < 2 * P.card` (via elementary 5-term binomial proof
   that `(k + 1)^k ≥ 7 * (k - 1)^k` for all `k ≥ 4`).
-/

namespace Contribution.Erdos686PrimeRemovalTwentyFive

/-! ## 1. Standalone General Structural Bounds -/

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

private lemma binom_linear_le (A B : ℕ) : ∀ k : ℕ, 1 ≤ k →
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

private lemma binom_quad_le (A B : ℕ) : ∀ k : ℕ, 2 ≤ k →
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

/-- Explicit quadratic lower bound: `k * (k - 1) < 7 * (n + k)` for all `k ≥ 2`. -/
theorem quadratic_lower_bound {k m n : ℕ} (hk : 2 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k * (k - 1) < 7 * (n + k) := by
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
  have hraw : k * (k - 1) * k ^ 2 < 48 * (n + k) ^ 2 :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ hk_le) hgap
  by_contra hge
  have hle : 7 * (n + k) ≤ k * (k - 1) := by omega
  have hsq : 49 * (n + k) ^ 2 ≤ (k * (k - 1)) ^ 2 := by nlinarith
  have hkk : (k * (k - 1)) ^ 2 ≤ k * (k - 1) * k ^ 2 := by
    have hk1 : k - 1 ≤ k := Nat.sub_le k 1
    nlinarith [Nat.pow_le_pow_left hk1 2]
  have h48 : 49 * (n + k) ^ 2 < 48 * (n + k) ^ 2 := lt_of_le_of_lt (le_trans hsq hkk) hraw
  omega

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

/-- Prime upper-bound lemma: any prime `p ≠ 5` dividing `∏ (m + i)` satisfies `p ≤ (m - n) + k - 1`. -/
theorem prime_upper_bound {k m n p : ℕ} (hp : Nat.Prime p) (hp5 : p ≠ 5)
    (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hdvd : p ∣ (∏ i ∈ Finset.Icc 1 k, (m + i))) :
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
  exact le_trans (Nat.le_of_dvd hsub_pos hsub_dvd) (by omega)

/-! ## 2. Erdős Prime-Removal Divisibility and Master Bound -/

/-- Distance between two distinct indices `i, j ∈ [1, k]` inside `ℕ`. -/
private def idxDist (i j : ℕ) : ℕ := max i j - min i j

private lemma idxDist_pos {i j : ℕ} (hne : i ≠ j) : 0 < idxDist i j := by
  dsimp [idxDist]
  omega

/-- If `(m + j).factorization p ≤ (m + i₀).factorization p` and `j ≠ i₀`, then
`(m + j).factorization p ≤ (idxDist j i₀).factorization p`. -/
private lemma factorization_le_idxDist {m p j i₀ : ℕ} (hp : Nat.Prime p)
    (hj_pos : m + j ≠ 0) (hi_pos : m + i₀ ≠ 0)
    (hne : j ≠ i₀) (hle : (m + j).factorization p ≤ (m + i₀).factorization p) :
    (m + j).factorization p ≤ (idxDist j i₀).factorization p := by
  set a := (m + j).factorization p
  have ha_j : p ^ a ∣ m + j := (hp.pow_dvd_iff_le_factorization hj_pos).mpr le_rfl
  have ha_i : p ^ a ∣ m + i₀ := (hp.pow_dvd_iff_le_factorization hi_pos).mpr hle
  have ha_dist : p ^ a ∣ idxDist j i₀ := by
    dsimp [idxDist]
    rcases lt_trichotomy j i₀ with hlt | rfl | hgt
    · have hmax : max j i₀ = i₀ := max_eq_right (le_of_lt hlt)
      have hmin : min j i₀ = j := min_eq_left (le_of_lt hlt)
      rw [hmax, hmin, show i₀ - j = (m + i₀) - (m + j) by omega]
      exact Nat.dvd_sub ha_i ha_j
    · exact absurd rfl hne
    · have hmax : max j i₀ = j := max_eq_left (le_of_lt hgt)
      have hmin : min j i₀ = i₀ := min_eq_right (le_of_lt hgt)
      rw [hmax, hmin, show j - i₀ = (m + j) - (m + i₀) by omega]
      exact Nat.dvd_sub ha_j ha_i
  exact (hp.pow_dvd_iff_le_factorization (idxDist_pos hne).ne').mp ha_dist

/-- Product of distances from `i₀ ∈ [1, k]` to all other `j ∈ [1, k]` divides `(k - 1)!`. -/
private lemma prod_idxDist_erase_dvd_factorial {k i₀ : ℕ} (hi₀ : i₀ ∈ Finset.Icc 1 k) :
    (∏ j ∈ (Finset.Icc 1 k).erase i₀, idxDist j i₀) ∣ Nat.factorial (k - 1) := by
  have hi₀' := Finset.mem_Icc.mp hi₀
  have h1k : 1 ≤ k := le_trans hi₀'.1 hi₀'.2
  have hdecomp : (Finset.Icc 1 k).erase i₀ = Finset.Ico 1 i₀ ∪ Finset.Icc (i₀ + 1) k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.Ico 1 i₀) (Finset.Icc (i₀ + 1) k) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rw [Finset.mem_Ico] at hj1
    rw [Finset.mem_Icc] at hj2
    omega
  rw [hdecomp, Finset.prod_union hdisj]
  have hleft : ∏ j ∈ Finset.Ico 1 i₀, idxDist j i₀ = Nat.factorial (i₀ - 1) := by
    calc ∏ j ∈ Finset.Ico 1 i₀, idxDist j i₀
        = ∏ j ∈ Finset.Ico 1 i₀, (i₀ - j) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [Finset.mem_Ico] at hj
          dsimp [idxDist]
          omega
      _ = ∏ a ∈ Finset.Ico 1 i₀, a := by
          refine Finset.prod_bij (fun j _ => i₀ - j) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_Ico] at hj ⊢; omega
          · intro j₁ hj₁ j₂ hj₂ h; rw [Finset.mem_Ico] at hj₁ hj₂; omega
          · intro a ha; rw [Finset.mem_Ico] at ha; exact ⟨i₀ - a, by rw [Finset.mem_Ico]; omega, by omega⟩
          · intro _ _; rfl
      _ = Nat.factorial (i₀ - 1) := by
          have hsub : i₀ - 1 + 1 = i₀ := Nat.sub_add_cancel hi₀'.1
          rw [← hsub]
          exact Finset.prod_Ico_id_eq_factorial (i₀ - 1)
  have hright : ∏ j ∈ Finset.Icc (i₀ + 1) k, idxDist j i₀ = Nat.factorial (k - i₀) := by
    calc ∏ j ∈ Finset.Icc (i₀ + 1) k, idxDist j i₀
        = ∏ j ∈ Finset.Icc (i₀ + 1) k, (j - i₀) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [Finset.mem_Icc] at hj
          dsimp [idxDist]
          omega
      _ = ∏ a ∈ Finset.Ico 1 (k - i₀ + 1), a := by
          refine Finset.prod_bij (fun j _ => j - i₀) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_Ico]; omega
          · intro j₁ hj₁ j₂ hj₂ h; rw [Finset.mem_Icc] at hj₁ hj₂; omega
          · intro a ha; rw [Finset.mem_Ico] at ha; exact ⟨i₀ + a, by rw [Finset.mem_Icc]; omega, by omega⟩
          · intro _ _; rfl
      _ = Nat.factorial (k - i₀) := Finset.prod_Ico_id_eq_factorial (k - i₀)
  rw [hleft, hright]
  have hle_sub : i₀ - 1 ≤ k - 1 := by omega
  have hdvd := Nat.factorial_mul_factorial_dvd_factorial hle_sub
  rwa [show (k - 1) - (i₀ - 1) = k - i₀ by omega] at hdvd

/-- **Erdős Prime-Removal Divisibility Lemma**:
For any `k ≥ 2` and `m : ℕ`, let `P` be the finset of prime factors dividing `∏_{i=1}^k (m + i)`.
Removing at most one maximizing index per prime `p ∈ P` leaves a subset `S ⊆ Finset.Icc 1 k`
such that `k ≤ S.card + P.card` and `(∏ i ∈ S, (m + i)) ∣ Nat.factorial (k - 1)`. -/
theorem erdos_prime_removal_dvd_factorial {k m : ℕ} (hk : 2 ≤ k) :
    let P := (∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors
    ∃ S ⊆ Finset.Icc 1 k, k ≤ S.card + P.card ∧
      (∏ i ∈ S, (m + i)) ∣ Nat.factorial (k - 1) := by
  intro P
  have hIcc_ne : (Finset.Icc 1 k).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hex : ∀ p : ℕ, ∃ i ∈ Finset.Icc 1 k,
      ∀ j ∈ Finset.Icc 1 k, (m + j).factorization p ≤ (m + i).factorization p := by
    intro p
    exact Finset.exists_max_image (Finset.Icc 1 k) (fun i => (m + i).factorization p) hIcc_ne
  choose maxIdx hmaxIdx_mem hmaxIdx_max using hex
  set E : Finset ℕ := P.image maxIdx
  set S : Finset ℕ := Finset.Icc 1 k \ E
  have hS_sub : S ⊆ Finset.Icc 1 k := Finset.sdiff_subset
  have hE_sub : E ⊆ Finset.Icc 1 k := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, _, rfl⟩
    exact hmaxIdx_mem p
  have hcard_sum : S.card + E.card = k := by
    have hs := Finset.card_sdiff_add_card_eq_card hE_sub
    simpa [S, E, Nat.card_Icc] using hs
  have hE_card : E.card ≤ P.card := Finset.card_image_le
  have hcard_ge : k ≤ S.card + P.card := by omega
  have hS_pos : ∀ i ∈ S, m + i ≠ 0 := by
    intro i hi
    have hi' := Finset.mem_Icc.mp (hS_sub hi)
    omega
  have hprodS_pos : (∏ i ∈ S, (m + i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hS_pos
  have hfact_pos : Nat.factorial (k - 1) ≠ 0 := Nat.factorial_ne_zero _
  refine ⟨S, hS_sub, hcard_ge, ?_⟩
  rw [← Nat.factorization_le_iff_dvd hprodS_pos hfact_pos]
  intro p
  rw [Nat.factorization_prod hS_pos]
  simp only [Finset.sum_apply']
  by_cases hpP : p ∈ P
  · set i₀ := maxIdx p
    have hi₀_mem : i₀ ∈ Finset.Icc 1 k := hmaxIdx_mem p
    have hi₀_E : i₀ ∈ E := Finset.mem_image.mpr ⟨p, hpP, rfl⟩
    have hS_sub_erase : S ⊆ (Finset.Icc 1 k).erase i₀ := by
      intro j hj
      refine Finset.mem_erase.mpr ⟨?_, hS_sub hj⟩
      intro heqj
      subst heqj
      exact (Finset.mem_sdiff.mp hj).2 hi₀_E
    have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hpP).1
    have hsum_le : ∑ j ∈ S, (m + j).factorization p ≤
        ∑ j ∈ (Finset.Icc 1 k).erase i₀, (idxDist j i₀).factorization p := by
      calc ∑ j ∈ S, (m + j).factorization p
          ≤ ∑ j ∈ S, (idxDist j i₀).factorization p := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hne : j ≠ i₀ := (Finset.mem_erase.mp (hS_sub_erase hj)).1
            have hi₀' := Finset.mem_Icc.mp hi₀_mem
            exact factorization_le_idxDist hp_prime (hS_pos j hj) (by omega) hne
              (hmaxIdx_max p j (hS_sub hj))
        _ ≤ ∑ j ∈ (Finset.Icc 1 k).erase i₀, (idxDist j i₀).factorization p :=
            Finset.sum_le_sum_of_subset hS_sub_erase
    have hdist_ne : ∀ j ∈ (Finset.Icc 1 k).erase i₀, idxDist j i₀ ≠ 0 := fun j hj =>
      (idxDist_pos (Finset.mem_erase.mp hj).1).ne'
    have hprod_dist_ne : (∏ j ∈ (Finset.Icc 1 k).erase i₀, idxDist j i₀) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hdist_ne
    have hfac_dist := (Nat.factorization_le_iff_dvd hprod_dist_ne hfact_pos).mpr
      (prod_idxDist_erase_dvd_factorial hi₀_mem) p
    rw [Nat.factorization_prod hdist_ne] at hfac_dist
    simp only [Finset.sum_apply'] at hfac_dist
    exact le_trans hsum_le hfac_dist
  · have hsum0 : ∑ i ∈ S, (m + i).factorization p = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      by_contra hnz
      have hne : ¬ (¬ Nat.Prime p ∨ ¬ p ∣ (m + i) ∨ m + i = 0) :=
        mt (Nat.factorization_eq_zero_iff (m + i) p).mpr hnz
      push Not at hne
      have hp_dvd : p ∣ ∏ j ∈ Finset.Icc 1 k, (m + j) :=
        dvd_trans hne.2.1 (Finset.dvd_prod_of_mem (fun j => m + j) (hS_sub hi))
      exact hpP (Nat.mem_primeFactors.mpr ⟨hne.1, hp_dvd, (prod_Icc_pos k m).ne'⟩)
    rw [hsum0]
    exact Nat.zero_le _

/-- **Erdős Prime-Removal Master Bound**:
For any solution `k ≥ 2`, `m ≥ n + k`, letting `P` be the finset of prime factors of
`∏_{i=1}^k (m + i)`:
1. `(m + 1) ^ (k - P.card) ≤ Nat.factorial (k - 1)`.
2. Every prime `p ∈ P` with `p ≠ 5` satisfies `p ≤ (m - n) + k - 1`.
3. `k * (k - 1) < 7 * (m + 1)`. -/
theorem erdos_prime_removal_master_bound {k m n : ℕ} (hk : 2 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    let P := (∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors
    (m + 1) ^ (k - P.card) ≤ Nat.factorial (k - 1) ∧
      (∀ p ∈ P, p ≠ 5 → p ≤ (m - n) + k - 1) ∧
      k * (k - 1) < 7 * (m + 1) := by
  intro P
  obtain ⟨S, hS_sub, hcard_ge, hdvd⟩ := erdos_prime_removal_dvd_factorial (m := m) hk
  change k ≤ S.card + P.card at hcard_ge
  have hpow_le : (m + 1) ^ (k - P.card) ≤ Nat.factorial (k - 1) := by
    have hpow_card : (m + 1) ^ (k - P.card) ≤ (m + 1) ^ S.card :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hprod_ge : (m + 1) ^ S.card ≤ ∏ i ∈ S, (m + i) := by
      calc (m + 1) ^ S.card = ∏ _i ∈ S, (m + 1) := (Finset.prod_const _).symm
        _ ≤ ∏ i ∈ S, (m + i) := by
          refine Finset.prod_le_prod' fun i hi => ?_
          have hi' := Finset.mem_Icc.mp (hS_sub hi)
          omega
    have hle_fac : ∏ i ∈ S, (m + i) ≤ Nat.factorial (k - 1) :=
      Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    exact le_trans hpow_card (le_trans hprod_ge hle_fac)
  have hp_up : ∀ p ∈ P, p ≠ 5 → p ≤ (m - n) + k - 1 := by
    intro p hpP hp5
    have hp_mem := Nat.mem_primeFactors.mp hpP
    exact prime_upper_bound hp_mem.1 hp5 hmn heq hp_mem.2.1
  have hquad : k * (k - 1) < 7 * (m + 1) := by
    have hq := quadratic_lower_bound hk hmn heq
    omega
  exact ⟨hpow_le, hp_up, hquad⟩

private lemma factorial_pred_le_pow : ∀ k : ℕ, 1 ≤ k → Nat.factorial (k - 1) ≤ k ^ (k - 1)
  | 0, hk => by omega
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := factorial_pred_le_pow (k + 1) (by omega)
    have hle1 : Nat.factorial k ≤ (k + 1) ^ k := ih
    have hle2 : (k + 1) ^ k ≤ (k + 2) ^ k := Nat.pow_le_pow_left (by omega) k
    calc Nat.factorial ((k + 2) - 1) = (k + 1) * Nat.factorial k := by
          simp [Nat.factorial_succ]
      _ ≤ (k + 2) * (k + 2) ^ k := Nat.mul_le_mul (by omega) (le_trans hle1 hle2)
      _ = (k + 2) ^ ((k + 2) - 1) := by rw [← pow_succ']; simp

/-! ## 3. Lower Bounds on Prime-Factor Count `ω(∏ (m + i))` -/

/-- General parametric prime-count ratio lower bound:
whenever `r ≥ 1` and `7 ^ r * k ≤ (k - 1) ^ r`, any solution has `k < (r + 1) * P.card`. -/
theorem prime_count_ratio_lower_bound {k m n r : ℕ} (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hthr : 7 ^ r * k ≤ (k - 1) ^ r) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k < (r + 1) * ((∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors.card) := by
  set P := (∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors
  obtain ⟨hpow_le, _, hquad⟩ := erdos_prime_removal_master_bound hk hmn heq
  by_contra hle
  have hPc_le : (r + 1) * P.card ≤ k := by omega
  have hP_le_k : P.card ≤ k := by nlinarith
  have hexp : r * k ≤ (r + 1) * (k - P.card) := by
    zify [hP_le_k] at hPc_le ⊢
    linarith
  have hm_pow : (m + 1) ^ (r * k) ≤ (Nat.factorial (k - 1)) ^ (r + 1) := by
    calc (m + 1) ^ (r * k)
        ≤ (m + 1) ^ ((r + 1) * (k - P.card)) := Nat.pow_le_pow_right (by omega) hexp
      _ = ((m + 1) ^ (k - P.card)) ^ (r + 1) := by rw [mul_comm, pow_mul]
      _ ≤ (Nat.factorial (k - 1)) ^ (r + 1) := Nat.pow_le_pow_left hpow_le _
  have hfac_pow : (Nat.factorial (k - 1)) ^ (r + 1) ≤ k ^ ((r + 1) * k) := by
    have hf1 : Nat.factorial (k - 1) ≤ k ^ k :=
      le_trans (factorial_pred_le_pow k (by omega)) (Nat.pow_le_pow_right (by omega) (by omega))
    calc (Nat.factorial (k - 1)) ^ (r + 1)
        ≤ (k ^ k) ^ (r + 1) := Nat.pow_le_pow_left hf1 _
      _ = k ^ ((r + 1) * k) := by rw [← pow_mul, mul_comm]
  have hrk_pos : 0 < r * k := Nat.mul_pos hr (by omega)
  have hlt_pow : (k * (k - 1)) ^ (r * k) < (7 * (m + 1)) ^ (r * k) :=
    Nat.pow_lt_pow_left hquad hrk_pos.ne'
  have hcontra : (k * (k - 1)) ^ (r * k) < (7 ^ r * k) ^ k * k ^ (r * k) := by
    calc (k * (k - 1)) ^ (r * k)
        < (7 * (m + 1)) ^ (r * k) := hlt_pow
      _ = 7 ^ (r * k) * (m + 1) ^ (r * k) := mul_pow 7 (m + 1) (r * k)
      _ ≤ 7 ^ (r * k) * k ^ ((r + 1) * k) := Nat.mul_le_mul_left _ (le_trans hm_pow hfac_pow)
      _ = (7 ^ r) ^ k * (k ^ k * k ^ (r * k)) := by
          rw [pow_mul, show (r + 1) * k = k + r * k by ring, pow_add]
      _ = ((7 ^ r) ^ k * k ^ k) * k ^ (r * k) := by ring
      _ = (7 ^ r * k) ^ k * k ^ (r * k) := by rw [← mul_pow]
  have hlhs_eq : (k * (k - 1)) ^ (r * k) = ((k - 1) ^ r) ^ k * k ^ (r * k) := by
    calc (k * (k - 1)) ^ (r * k) = k ^ (r * k) * (k - 1) ^ (r * k) := mul_pow k (k - 1) (r * k)
      _ = ((k - 1) ^ r) ^ k * k ^ (r * k) := by rw [pow_mul]; ring
  have hthr_k : (7 ^ r * k) ^ k ≤ ((k - 1) ^ r) ^ k := Nat.pow_le_pow_left hthr k
  have hk_pow_pos : 0 < k ^ (r * k) := pow_pos (by omega) _
  have hrhs_le : (7 ^ r * k) ^ k * k ^ (r * k) ≤ (k * (k - 1)) ^ (r * k) := by
    rw [hlhs_eq]
    exact Nat.mul_le_mul_right _ hthr_k
  exact lt_irrefl _ (lt_of_lt_of_le hcontra hrhs_le)

/-- For all `k ≥ 51`, any solution satisfies `k < 3 * ω(∏_{i=1}^k (m + i))`. -/
theorem prime_count_gt_third_k {k m n : ℕ} (hk : 51 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k < 3 * ((∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors.card) := by
  have hthr : 7 ^ 2 * k ≤ (k - 1) ^ 2 := by
    zify [show 1 ≤ k by omega]
    nlinarith
  exact prime_count_ratio_lower_bound (by omega) (by norm_num) hthr hmn heq

/-- Five-term binomial lower bound: `7 * (k - 1)^k ≤ (k + 1)^k` for all `k ≥ 4`. -/
theorem seven_mul_pred_pow_le_succ_pow {k : ℕ} (hk : 4 ≤ k) :
    7 * (k - 1) ^ k ≤ (k + 1) ^ k := by
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, k = a + 4 := ⟨k - 4, by omega⟩
  set t := a + 3
  have hsub_t : a + 4 - 1 = t := by omega
  have hbinom : (t + 2) ^ (a + 4) =
      ∑ j ∈ Finset.range (a + 5), t ^ j * 2 ^ (a + 4 - j) * (a + 4).choose j :=
    add_pow t 2 (a + 4)
  have hsub : Finset.Icc a (a + 4) ⊆ Finset.range (a + 5) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Finset.mem_range]
    omega
  have hsum_ge : ∑ j ∈ Finset.Icc a (a + 4), t ^ j * 2 ^ (a + 4 - j) * (a + 4).choose j ≤
      (a + 5) ^ (a + 4) := by
    have heq_base : a + 5 = t + 2 := by omega
    rw [heq_base, hbinom]
    exact Finset.sum_le_sum_of_subset hsub
  have hk_sum : ∑ j ∈ Finset.Icc a (a + 4), t ^ j * 2 ^ (a + 4 - j) * (a + 4).choose j =
      t ^ a * 16 * (a + 4).choose 4 +
      t ^ (a + 1) * 8 * (a + 4).choose 3 +
      t ^ (a + 2) * 4 * (a + 4).choose 2 +
      t ^ (a + 3) * 2 * (a + 4).choose 1 +
      t ^ (a + 4) * 1 * (a + 4).choose 0 := by
    let f : ℕ → ℕ := fun j => t ^ j * 2 ^ (a + 4 - j) * (a + 4).choose j
    change ∑ j ∈ Finset.Icc a (a + 4), f j = _
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ a + 4),
        Finset.sum_Icc_succ_top (by omega : a ≤ a + 3),
        Finset.sum_Icc_succ_top (by omega : a ≤ a + 2),
        Finset.sum_Icc_succ_top (by omega : a ≤ a + 1),
        Finset.Icc_self, Finset.sum_singleton]
    have hc4 : (a + 4).choose a = (a + 4).choose 4 := by
      simpa [show a + 4 - a = 4 by omega] using (Nat.choose_symm (by omega : a ≤ a + 4)).symm
    have hc3 : (a + 4).choose (a + 1) = (a + 4).choose 3 := by
      simpa [show a + 4 - (a + 1) = 3 by omega] using
        (Nat.choose_symm (by omega : a + 1 ≤ a + 4)).symm
    have hc2 : (a + 4).choose (a + 2) = (a + 4).choose 2 := by
      simpa [show a + 4 - (a + 2) = 2 by omega] using
        (Nat.choose_symm (by omega : a + 2 ≤ a + 4)).symm
    have hc1 : (a + 4).choose (a + 3) = (a + 4).choose 1 := by
      rw [← Nat.choose_symm (by omega : a + 3 ≤ a + 4), show a + 4 - (a + 3) = 1 by omega]
    have hc0 : (a + 4).choose (a + 4) = (a + 4).choose 0 := by simp
    dsimp [f]
    rw [hc4, hc3, hc2, hc1, hc0]
    norm_num [show a + 4 - a = 4 by omega, show a + 4 - (a + 1) = 3 by omega,
      show a + 4 - (a + 2) = 2 by omega, show a + 4 - (a + 3) = 1 by omega,
      show a + 4 - (a + 4) = 0 by omega]
  have hd4 : 24 * (a + 4).choose 4 = (a + 4) * (a + 3) * (a + 2) * (a + 1) := by
    have h := (Nat.descFactorial_eq_factorial_mul_choose (a + 4) 4).symm
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
      Nat.factorial_zero] at h
    rw [show a + 4 - 3 = a + 1 by omega, show a + 4 - 2 = a + 2 by omega,
      show a + 4 - 1 = a + 3 by omega] at h
    norm_num at h
    linarith
  have hd3 : 6 * (a + 4).choose 3 = (a + 4) * (a + 3) * (a + 2) := by
    have h := (Nat.descFactorial_eq_factorial_mul_choose (a + 4) 3).symm
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
      Nat.factorial_zero] at h
    rw [show a + 4 - 2 = a + 2 by omega, show a + 4 - 1 = a + 3 by omega] at h
    norm_num at h
    linarith
  have hd2 : 2 * (a + 4).choose 2 = (a + 4) * (a + 3) := by
    have h := (Nat.descFactorial_eq_factorial_mul_choose (a + 4) 2).symm
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial_succ,
      Nat.factorial_zero] at h
    rw [show a + 4 - 1 = a + 3 by omega] at h
    norm_num at h
    linarith
  have hd1 : (a + 4).choose 1 = a + 4 := Nat.choose_one_right (a + 4)
  have hd0 : (a + 4).choose 0 = 1 := Nat.choose_zero_right (a + 4)
  have hmul3 : 3 * (7 * t ^ (a + 4)) ≤
      3 * (∑ j ∈ Finset.Icc a (a + 4), t ^ j * 2 ^ (a + 4 - j) * (a + 4).choose j) := by
    rw [hk_sum]
    have hpoly :
        3 * (t ^ a * 16 * (a + 4).choose 4 +
            t ^ (a + 1) * 8 * (a + 4).choose 3 +
            t ^ (a + 2) * 4 * (a + 4).choose 2 +
            t ^ (a + 3) * 2 * (a + 4).choose 1 +
            t ^ (a + 4) * 1 * (a + 4).choose 0) =
          t ^ a * (21 * t ^ 4 + 2 * t * (4 * a ^ 2 + 21 * a + 29)) := by
      have hp1 : 3 * (t ^ a * 16 * (a + 4).choose 4) =
          t ^ a * (2 * ((a + 4) * (a + 3) * (a + 2) * (a + 1))) := by
        calc 3 * (t ^ a * 16 * (a + 4).choose 4)
            = t ^ a * (2 * (24 * (a + 4).choose 4)) := by ring
          _ = t ^ a * (2 * ((a + 4) * (a + 3) * (a + 2) * (a + 1))) := by rw [hd4]
      have hp2 : 3 * (t ^ (a + 1) * 8 * (a + 4).choose 3) =
          t ^ a * (4 * ((a + 4) * (a + 3) * (a + 2)) * t) := by
        calc 3 * (t ^ (a + 1) * 8 * (a + 4).choose 3)
            = t ^ a * (4 * (6 * (a + 4).choose 3) * t) := by rw [pow_succ]; ring
          _ = t ^ a * (4 * ((a + 4) * (a + 3) * (a + 2)) * t) := by rw [hd3]
      have hp3 : 3 * (t ^ (a + 2) * 4 * (a + 4).choose 2) =
          t ^ a * (6 * ((a + 4) * (a + 3)) * t ^ 2) := by
        calc 3 * (t ^ (a + 2) * 4 * (a + 4).choose 2)
            = t ^ a * (6 * (2 * (a + 4).choose 2) * t ^ 2) := by
                rw [pow_add]; ring
          _ = t ^ a * (6 * ((a + 4) * (a + 3)) * t ^ 2) := by rw [hd2]
      have hp4 : 3 * (t ^ (a + 3) * 2 * (a + 4).choose 1) =
          t ^ a * (6 * (a + 4) * t ^ 3) := by
        rw [hd1, pow_add]; ring
      have hp5 : 3 * (t ^ (a + 4) * 1 * (a + 4).choose 0) = t ^ a * (3 * t ^ 4) := by
        rw [hd0, pow_add]; ring
      calc 3 * (t ^ a * 16 * (a + 4).choose 4 + t ^ (a + 1) * 8 * (a + 4).choose 3 +
              t ^ (a + 2) * 4 * (a + 4).choose 2 + t ^ (a + 3) * 2 * (a + 4).choose 1 +
              t ^ (a + 4) * 1 * (a + 4).choose 0)
          = t ^ a * (2 * ((a + 4) * (a + 3) * (a + 2) * (a + 1)) +
              4 * ((a + 4) * (a + 3) * (a + 2)) * t +
              6 * ((a + 4) * (a + 3)) * t ^ 2 +
              6 * (a + 4) * t ^ 3 + 3 * t ^ 4) := by
              rw [show 3 * (_ + _ + _ + _ + _) =
                3 * (t ^ a * 16 * (a + 4).choose 4) + 3 * (t ^ (a + 1) * 8 * (a + 4).choose 3) +
                3 * (t ^ (a + 2) * 4 * (a + 4).choose 2) + 3 * (t ^ (a + 3) * 2 * (a + 4).choose 1) +
                3 * (t ^ (a + 4) * 1 * (a + 4).choose 0) by ring]
              rw [hp1, hp2, hp3, hp4, hp5]; ring
        _ = t ^ a * (21 * t ^ 4 + 2 * t * (4 * a ^ 2 + 21 * a + 29)) := by
              dsimp [t]; ring
    rw [hpoly]
    have hlhs : 3 * (7 * t ^ (a + 4)) = t ^ a * (21 * t ^ 4) := by
      rw [pow_add]; ring
    rw [hlhs]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hle_all : 3 * (7 * t ^ (a + 4)) ≤ 3 * (a + 5) ^ (a + 4) :=
    le_trans hmul3 (Nat.mul_le_mul_left 3 hsum_ge)
  rw [hsub_t]
  exact Nat.le_of_mul_le_mul_left hle_all (by decide : 0 < 3)

/-- Inductive Stirling-free factorial bound: `7^k * ((k - 1)!)^2 ≤ (k * (k - 1))^k` for `k ≥ 11`. -/
theorem seven_pow_mul_factorial_sq_le :
    ∀ k : ℕ, 11 ≤ k → 7 ^ k * (Nat.factorial (k - 1)) ^ 2 ≤ (k * (k - 1)) ^ k
  | 0, hk => by omega
  | 1, hk => by omega
  | k + 1, hk => by
    rcases eq_or_lt_of_le hk with heq | hgt
    · have hk10 : k = 10 := by omega
      subst hk10
      decide
    · have ih := seven_pow_mul_factorial_sq_le k (by omega)
      have hfac : Nat.factorial k = k * Nat.factorial (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, Nat.factorial_succ, show k - 1 + 1 = k by omega]
      have hstep : 7 * (k - 1) ^ k ≤ (k + 1) ^ k := seven_mul_pred_pow_le_succ_pow (by omega)
      have hmul_step : 7 * k * (k - 1) ^ k ≤ (k + 1) ^ (k + 1) := by
        calc 7 * k * (k - 1) ^ k = k * (7 * (k - 1) ^ k) := by ring
          _ ≤ (k + 1) * (k + 1) ^ k := Nat.mul_le_mul (by omega) hstep
          _ = (k + 1) ^ (k + 1) := by rw [← pow_succ']
      calc 7 ^ (k + 1) * (Nat.factorial ((k + 1) - 1)) ^ 2
          = 7 * k ^ 2 * (7 ^ k * (Nat.factorial (k - 1)) ^ 2) := by
              rw [show k + 1 - 1 = k by omega, hfac, pow_succ']; ring
        _ ≤ 7 * k ^ 2 * (k * (k - 1)) ^ k := Nat.mul_le_mul_left _ ih
        _ = k ^ (k + 1) * (7 * k * (k - 1) ^ k) := by
              rw [mul_pow, pow_succ']; ring
        _ ≤ k ^ (k + 1) * (k + 1) ^ (k + 1) := Nat.mul_le_mul_left _ hmul_step
        _ = ((k + 1) * k) ^ (k + 1) := by rw [mul_pow]; ring
        _ = ((k + 1) * ((k + 1) - 1)) ^ (k + 1) := by simp

/-- For all `k ≥ 11`, any solution satisfies `k < 2 * ω(∏_{i=1}^k (m + i))`. -/
theorem prime_count_gt_half_k {k m n : ℕ} (hk : 11 ≤ k) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 k, (n + i))) :
    k < 2 * ((∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors.card) := by
  set P := (∏ i ∈ Finset.Icc 1 k, (m + i)).primeFactors
  obtain ⟨hpow_le, _, hquad⟩ := erdos_prime_removal_master_bound (by omega : 2 ≤ k) hmn heq
  by_contra hle
  have h2P : 2 * P.card ≤ k := by omega
  have hP_le : P.card ≤ k := by omega
  have hexp : k ≤ 2 * (k - P.card) := by
    zify [hP_le] at h2P ⊢
    linarith
  have hm_pow : (m + 1) ^ k ≤ (Nat.factorial (k - 1)) ^ 2 := by
    calc (m + 1) ^ k
        ≤ (m + 1) ^ (2 * (k - P.card)) := Nat.pow_le_pow_right (by omega) hexp
      _ = ((m + 1) ^ (k - P.card)) ^ 2 := by rw [mul_comm, pow_mul]
      _ ≤ (Nat.factorial (k - 1)) ^ 2 := Nat.pow_le_pow_left hpow_le 2
  have hlt : (k * (k - 1)) ^ k < (7 * (m + 1)) ^ k :=
    Nat.pow_lt_pow_left hquad (by omega)
  have hstirl := seven_pow_mul_factorial_sq_le k hk
  have hcontra : (k * (k - 1)) ^ k < (k * (k - 1)) ^ k := by
    calc (k * (k - 1)) ^ k
        < (7 * (m + 1)) ^ k := hlt
      _ = 7 ^ k * (m + 1) ^ k := mul_pow 7 (m + 1) k
      _ ≤ 7 ^ k * (Nat.factorial (k - 1)) ^ 2 := Nat.mul_le_mul_left _ hm_pow
      _ ≤ (k * (k - 1)) ^ k := hstirl
  exact lt_irrefl _ hcontra

end Contribution.Erdos686PrimeRemovalTwentyFive
