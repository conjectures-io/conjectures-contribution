import Mathlib
import FormalConjectures.ErdosProblems.«252»

-- ==== from Harvest0_252k0.lean ====
/-!
Erdős 252, k = 0 (Erdős–Straus 1971): `∑ σ₀(n)/n!` is irrational.

Proof sketch: if the sum were `q ∈ ℚ`, then for every `N ≥ q.den` the scaled tail
`T N = N! * ∑_{n > N} σ₀(n)/n!` is a positive integer, and
`(N+1) * T N = σ₀(N+1) + T (N+1)`.  Hence for a prime `p > q.den` we get
`p ∣ T p + 2`.  But `0 < T p < 2` (geometric estimate using `σ₀(n) ≤ n`),
so `T p = 1` and `p ∣ 3`, absurd for `p ≥ 5`.
-/

open scoped Nat ArithmeticFunction.sigma

namespace Contribution.Erdos252KEqZero

/-- The summand of the Erdős 252 series. -/
noncomputable def g (k n : ℕ) : ℝ := (σ k n : ℝ) / (n ! : ℝ)

lemma erdos_sum_eq (k : ℕ) : Erdos252.erdos_252_sum k = ∑' n, g k n := rfl

lemma g_nonneg (k n : ℕ) : 0 ≤ g k n := by
  unfold g
  positivity

lemma factorial_cast_pos (n : ℕ) : (0 : ℝ) < (n ! : ℝ) :=
  Nat.cast_pos.mpr (Nat.factorial_pos n)

lemma one_le_sigma (k n : ℕ) (hn : n ≠ 0) : 1 ≤ σ k n := by
  rw [ArithmeticFunction.sigma_apply]
  calc 1 = 1 ^ k := (one_pow k).symm
  _ ≤ ∑ d ∈ n.divisors, d ^ k :=
      Finset.single_le_sum (f := fun d => d ^ k) (fun i _ => Nat.zero_le _)
        (Nat.one_mem_divisors.mpr hn)

lemma g_pos (k n : ℕ) (hn : n ≠ 0) : 0 < g k n := by
  unfold g
  exact div_pos (by exact_mod_cast one_le_sigma k n hn) (factorial_cast_pos n)

lemma card_divisors_le_self (n : ℕ) : n.divisors.card ≤ n := by
  calc n.divisors.card ≤ (Finset.Icc 1 n).card :=
        Finset.card_le_card fun d hd =>
          Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  _ = n := by rw [Nat.card_Icc]; omega

lemma sigma_le_pow (k n : ℕ) : σ k n ≤ (2 ^ (k + 1)) ^ n := by
  have h1 : σ k n ≤ n ^ (k + 1) := by
    rw [ArithmeticFunction.sigma_apply]
    calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ _d ∈ n.divisors, n ^ k :=
          Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ = n.divisors.card * n ^ k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n ^ k := Nat.mul_le_mul (card_divisors_le_self n) (Nat.le_refl _)
    _ = n ^ (k + 1) := by ring
  calc σ k n ≤ n ^ (k + 1) := h1
  _ ≤ (2 ^ n) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) _
  _ = (2 ^ (k + 1)) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

lemma summable_g (k : ℕ) : Summable (g k) := by
  apply Summable.of_nonneg_of_le (g_nonneg k) (fun n => ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ (k + 1)))
  unfold g
  gcongr
  calc (σ k n : ℝ) ≤ (((2 ^ (k + 1)) ^ n : ℕ) : ℝ) := Nat.cast_le.mpr (sigma_le_pow k n)
  _ = ((2 : ℝ) ^ (k + 1)) ^ n := by push_cast; ring

lemma summable_g_shift (k N : ℕ) : Summable (fun j : ℕ => g k (j + N)) :=
  (summable_nat_add_iff N).mpr (summable_g k)

/-- The tail `∑_{n ≥ N} σ_k(n)/n!`. -/
noncomputable def tail (k N : ℕ) : ℝ := ∑' j : ℕ, g k (j + N)

/-- The scaled tail `N! * ∑_{n > N} σ_k(n)/n!`. -/
noncomputable def T (k N : ℕ) : ℝ := (N ! : ℝ) * tail k (N + 1)

lemma tail_pos (k N : ℕ) (hN : N ≠ 0) : 0 < tail k N :=
  Summable.tsum_pos (summable_g_shift k N) (fun j => g_nonneg k (j + N)) 0
    (g_pos k (0 + N) (by omega))

lemma T_pos (k N : ℕ) : 0 < T k N :=
  mul_pos (factorial_cast_pos N) (tail_pos k (N + 1) (Nat.succ_ne_zero N))

lemma tail_eq (k N : ℕ) :
    tail k N = Erdos252.erdos_252_sum k - ∑ i ∈ Finset.range N, g k i := by
  have h := (summable_g k).sum_add_tsum_nat_add N
  rw [erdos_sum_eq k]
  unfold tail
  linarith

lemma tail_rec (k N : ℕ) : tail k N = g k N + tail k (N + 1) := by
  unfold tail
  rw [(summable_g_shift k N).tsum_eq_zero_add]
  congr 1
  · rw [Nat.zero_add]
  · apply tsum_congr
    intro j
    congr 1
    omega

lemma T_rec (k N : ℕ) : ((N : ℝ) + 1) * T k N = (σ k (N + 1) : ℝ) + T k (N + 1) := by
  have hF : (0 : ℝ) < (N ! : ℝ) := factorial_cast_pos N
  have hF' : (N ! : ℝ) ≠ 0 := ne_of_gt hF
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hF1 : (((N + 1)! : ℕ) : ℝ) = ((N : ℝ) + 1) * (N ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold T
  rw [tail_rec k (N + 1)]
  unfold g
  rw [hF1]
  field_simp

lemma T_int (k : ℕ) (q : ℚ) (hq : (q : ℝ) = Erdos252.erdos_252_sum k) (N : ℕ)
    (hN : q.den ≤ N) : ∃ t : ℤ, (t : ℝ) = T k N := by
  have hden0 : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hdvd : q.den ∣ N ! := Nat.dvd_factorial q.pos hN
  refine ⟨q.num * ((N ! / q.den : ℕ) : ℤ)
      - ∑ i ∈ Finset.range (N + 1), (σ k i : ℤ) * ((N ! / i ! : ℕ) : ℤ), ?_⟩
  have h1 : ((N ! / q.den : ℕ) : ℝ) = (N ! : ℝ) / (q.den : ℝ) := Nat.cast_div hdvd hden0
  have h2 : ∀ i ∈ Finset.range (N + 1),
      (σ k i : ℝ) * ((N ! / i ! : ℕ) : ℝ) = (N ! : ℝ) * g k i := by
    intro i hi
    have hiN : i ! ∣ N ! := Nat.factorial_dvd_factorial (by
      have := Finset.mem_range.mp hi
      omega)
    have hifac : ((i ! : ℕ) : ℝ) ≠ 0 := ne_of_gt (factorial_cast_pos i)
    rw [Nat.cast_div hiN hifac]
    unfold g
    ring
  have h3 : (q : ℝ) * (N ! : ℝ) = (q.num : ℝ) * ((N ! / q.den : ℕ) : ℝ) := by
    rw [h1, Rat.cast_def]
    ring
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
  rw [Finset.sum_congr rfl h2]
  unfold T
  rw [tail_eq k (N + 1), ← hq, mul_sub, Finset.mul_sum]
  linear_combination -h3

lemma sigma_prime (k p : ℕ) (hp : p.Prime) : σ k p = 1 + p ^ k := by
  rw [ArithmeticFunction.sigma_apply, hp.divisors,
    Finset.sum_insert (by simp [Finset.mem_singleton, hp.one_lt.ne]),
    Finset.sum_singleton, one_pow]

/-- `(N+1)^j * N! ≤ (N+j)!`. -/
lemma pow_mul_factorial_le (N j : ℕ) : (N + 1) ^ j * N ! ≤ (N + j)! := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc (N + 1) ^ (j + 1) * N ! = (N + 1) * ((N + 1) ^ j * N !) := by ring
      _ ≤ (N + 1) * (N + j)! := Nat.mul_le_mul (Nat.le_refl _) ih
      _ ≤ (N + j + 1) * (N + j)! := Nat.mul_le_mul (by omega) (Nat.le_refl _)
      _ = (N + j + 1)! := (Nat.factorial_succ _).symm

lemma fact_ratio_le (N j : ℕ) :
    (N ! : ℝ) / ((N + j)! : ℝ) ≤ (1 / ((N : ℝ) + 1)) ^ j := by
  rw [div_pow, one_pow, div_le_div_iff₀ (factorial_cast_pos _) (by positivity)]
  calc (N ! : ℝ) * ((N : ℝ) + 1) ^ j = (((N + 1) ^ j * N ! : ℕ) : ℝ) := by push_cast; ring
  _ ≤ (((N + j)! : ℕ) : ℝ) := Nat.cast_le.mpr (pow_mul_factorial_le N j)
  _ = 1 * ((N + j)! : ℝ) := by ring

lemma T_le_of_terms (k N : ℕ) (c r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hterm : ∀ j : ℕ, (N ! : ℝ) * g k (j + (N + 1)) ≤ c * r ^ j) :
    T k N ≤ c / (1 - r) := by
  unfold T tail
  rw [← tsum_mul_left]
  have hsum1 : Summable (fun j : ℕ => (N ! : ℝ) * g k (j + (N + 1))) :=
    (summable_g_shift k (N + 1)).mul_left _
  have hsum2 : Summable (fun j : ℕ => c * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  calc ∑' j : ℕ, (N ! : ℝ) * g k (j + (N + 1)) ≤ ∑' j : ℕ, c * r ^ j :=
        hsum1.tsum_le_tsum hterm hsum2
  _ = c * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  _ = c / (1 - r) := (div_eq_mul_inv c _).symm

/- ### Specifics for `k = 0` -/

lemma sigma0_le (n : ℕ) : σ 0 n ≤ n := by
  rw [ArithmeticFunction.sigma_zero_apply]
  exact card_divisors_le_self n

lemma term_le_k0 (N j : ℕ) :
    (N ! : ℝ) * g 0 (j + (N + 1)) ≤ (1 / ((N : ℝ) + 1)) ^ j := by
  rw [show j + (N + 1) = (N + j) + 1 from by omega]
  unfold g
  have hM0 : (0 : ℝ) < ((N + j : ℕ) : ℝ) + 1 := by positivity
  have h2 : (((N + j + 1)! : ℕ) : ℝ) = (((N + j : ℕ) : ℝ) + 1) * ((N + j)! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h1 : (σ 0 (N + j + 1) : ℝ) ≤ ((N + j : ℕ) : ℝ) + 1 := by
    calc (σ 0 (N + j + 1) : ℝ) ≤ ((N + j + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (sigma0_le _)
    _ = ((N + j : ℕ) : ℝ) + 1 := by push_cast; ring
  calc (N ! : ℝ) * ((σ 0 (N + j + 1) : ℝ) / (((N + j + 1)! : ℕ) : ℝ))
      ≤ (N ! : ℝ) * ((((N + j : ℕ) : ℝ) + 1) / (((N + j + 1)! : ℕ) : ℝ)) := by
        gcongr
  _ = (N ! : ℝ) / ((N + j)! : ℝ) := by
        rw [h2, div_mul_cancel_left₀ (ne_of_gt hM0), ← div_eq_mul_inv]
  _ ≤ (1 / ((N : ℝ) + 1)) ^ j := fact_ratio_le N j

theorem k_eq_zero : Irrational (Erdos252.erdos_252_sum 0) := by
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨p, hpmax, hp⟩ := Nat.exists_infinite_primes (max (q.den + 1) 5)
  have hp5 : 5 ≤ p := le_trans (le_max_right _ _) hpmax
  have hpden : q.den + 1 ≤ p := le_trans (le_max_left _ _) hpmax
  obtain ⟨t1, ht1⟩ := T_int 0 q hq (p - 1) (by omega)
  obtain ⟨t2, ht2⟩ := T_int 0 q hq p (by omega)
  have hσ : σ 0 p = 2 := by norm_num [sigma_prime 0 p hp]
  have hrec := T_rec 0 (p - 1)
  rw [show p - 1 + 1 = p from by omega] at hrec
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  rw [hcast, ← ht1, ← ht2, hσ] at hrec
  have hrec' : (p : ℤ) * t1 = 2 + t2 := by exact_mod_cast hrec
  have ht2pos : (0 : ℤ) < t2 := by
    have h := T_pos 0 p
    rw [← ht2] at h
    exact_mod_cast h
  have hple : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
  have hr0 : (0 : ℝ) ≤ 1 / ((p : ℝ) + 1) := by positivity
  have hr1 : 1 / ((p : ℝ) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hb := T_le_of_terms 0 p 1 (1 / ((p : ℝ) + 1)) hr0 hr1 (fun j => by
    rw [one_mul]
    exact term_le_k0 p j)
  have hlt2 : T 0 p < 2 := by
    have h1r : (1 : ℝ) - 1 / ((p : ℝ) + 1) = (p : ℝ) / ((p : ℝ) + 1) := by
      field_simp
      ring
    rw [h1r, one_div_div] at hb
    have hlt : ((p : ℝ) + 1) / (p : ℝ) < 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    linarith
  have ht2lt : t2 < 2 := by
    have h : (t2 : ℝ) < 2 := by rw [ht2]; exact hlt2
    exact_mod_cast h
  have ht2eq : t2 = 1 := by omega
  rw [ht2eq] at hrec'
  have hdvd3 : (p : ℤ) ∣ 3 := ⟨t1, by linarith⟩
  have hle3 : (p : ℤ) ≤ 3 := Int.le_of_dvd (by norm_num) hdvd3
  have : p ≤ 3 := by exact_mod_cast hle3
  omega

end Contribution.Erdos252KEqZero

-- ==== from Harvest0_252k1.lean ====
/-
Erdős 252, k = 1 (Erdős–Straus 1974): `∑ σ₁(n)/n!` is irrational.

Proof sketch: if the sum were `q ∈ ℚ`, then for every `N ≥ q.den` the scaled tail
`T N = N! * ∑_{n > N} σ₁(n)/n!` is a positive integer, and
`(N+1) * T N = σ₁(N+1) + T (N+1)`.  Hence for a prime `p > q.den` we get
`p ∣ T p + 1` (as `σ₁(p) = p + 1`), so `p ≤ T p + 1`.  But the geometric
estimate using `σ₁(n) ≤ n(n+1)/2` gives `T p ≤ (p+2)(p+1)/(2(p-1)) ≤ p - 2`
for `p ≥ 11`, a contradiction.
-/

open scoped Nat ArithmeticFunction.sigma

namespace Contribution.Erdos252KEqOne

/-- The summand of the Erdős 252 series. -/
noncomputable def g (k n : ℕ) : ℝ := (σ k n : ℝ) / (n ! : ℝ)

lemma erdos_sum_eq (k : ℕ) : Erdos252.erdos_252_sum k = ∑' n, g k n := rfl

lemma g_nonneg (k n : ℕ) : 0 ≤ g k n := by
  unfold g
  positivity

lemma factorial_cast_pos (n : ℕ) : (0 : ℝ) < (n ! : ℝ) :=
  Nat.cast_pos.mpr (Nat.factorial_pos n)

lemma one_le_sigma (k n : ℕ) (hn : n ≠ 0) : 1 ≤ σ k n := by
  rw [ArithmeticFunction.sigma_apply]
  calc 1 = 1 ^ k := (one_pow k).symm
  _ ≤ ∑ d ∈ n.divisors, d ^ k :=
      Finset.single_le_sum (f := fun d => d ^ k) (fun i _ => Nat.zero_le _)
        (Nat.one_mem_divisors.mpr hn)

lemma g_pos (k n : ℕ) (hn : n ≠ 0) : 0 < g k n := by
  unfold g
  exact div_pos (by exact_mod_cast one_le_sigma k n hn) (factorial_cast_pos n)

lemma card_divisors_le_self (n : ℕ) : n.divisors.card ≤ n := by
  calc n.divisors.card ≤ (Finset.Icc 1 n).card :=
        Finset.card_le_card fun d hd =>
          Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  _ = n := by rw [Nat.card_Icc]; omega

lemma sigma_le_pow (k n : ℕ) : σ k n ≤ (2 ^ (k + 1)) ^ n := by
  have h1 : σ k n ≤ n ^ (k + 1) := by
    rw [ArithmeticFunction.sigma_apply]
    calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ _d ∈ n.divisors, n ^ k :=
          Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ = n.divisors.card * n ^ k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n ^ k := Nat.mul_le_mul (card_divisors_le_self n) (Nat.le_refl _)
    _ = n ^ (k + 1) := by ring
  calc σ k n ≤ n ^ (k + 1) := h1
  _ ≤ (2 ^ n) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) _
  _ = (2 ^ (k + 1)) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

lemma summable_g (k : ℕ) : Summable (g k) := by
  apply Summable.of_nonneg_of_le (g_nonneg k) (fun n => ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ (k + 1)))
  unfold g
  gcongr
  calc (σ k n : ℝ) ≤ (((2 ^ (k + 1)) ^ n : ℕ) : ℝ) := Nat.cast_le.mpr (sigma_le_pow k n)
  _ = ((2 : ℝ) ^ (k + 1)) ^ n := by push_cast; ring

lemma summable_g_shift (k N : ℕ) : Summable (fun j : ℕ => g k (j + N)) :=
  (summable_nat_add_iff N).mpr (summable_g k)

/-- The tail `∑_{n ≥ N} σ_k(n)/n!`. -/
noncomputable def tail (k N : ℕ) : ℝ := ∑' j : ℕ, g k (j + N)

/-- The scaled tail `N! * ∑_{n > N} σ_k(n)/n!`. -/
noncomputable def T (k N : ℕ) : ℝ := (N ! : ℝ) * tail k (N + 1)

lemma tail_pos (k N : ℕ) (hN : N ≠ 0) : 0 < tail k N :=
  Summable.tsum_pos (summable_g_shift k N) (fun j => g_nonneg k (j + N)) 0
    (g_pos k (0 + N) (by omega))

lemma T_pos (k N : ℕ) : 0 < T k N :=
  mul_pos (factorial_cast_pos N) (tail_pos k (N + 1) (Nat.succ_ne_zero N))

lemma tail_eq (k N : ℕ) :
    tail k N = Erdos252.erdos_252_sum k - ∑ i ∈ Finset.range N, g k i := by
  have h := (summable_g k).sum_add_tsum_nat_add N
  rw [erdos_sum_eq k]
  unfold tail
  linarith

lemma tail_rec (k N : ℕ) : tail k N = g k N + tail k (N + 1) := by
  unfold tail
  rw [(summable_g_shift k N).tsum_eq_zero_add]
  congr 1
  · rw [Nat.zero_add]
  · apply tsum_congr
    intro j
    congr 1
    omega

lemma T_rec (k N : ℕ) : ((N : ℝ) + 1) * T k N = (σ k (N + 1) : ℝ) + T k (N + 1) := by
  have hF : (0 : ℝ) < (N ! : ℝ) := factorial_cast_pos N
  have hF' : (N ! : ℝ) ≠ 0 := ne_of_gt hF
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hF1 : (((N + 1)! : ℕ) : ℝ) = ((N : ℝ) + 1) * (N ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold T
  rw [tail_rec k (N + 1)]
  unfold g
  rw [hF1]
  field_simp

lemma T_int (k : ℕ) (q : ℚ) (hq : (q : ℝ) = Erdos252.erdos_252_sum k) (N : ℕ)
    (hN : q.den ≤ N) : ∃ t : ℤ, (t : ℝ) = T k N := by
  have hden0 : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hdvd : q.den ∣ N ! := Nat.dvd_factorial q.pos hN
  refine ⟨q.num * ((N ! / q.den : ℕ) : ℤ)
      - ∑ i ∈ Finset.range (N + 1), (σ k i : ℤ) * ((N ! / i ! : ℕ) : ℤ), ?_⟩
  have h1 : ((N ! / q.den : ℕ) : ℝ) = (N ! : ℝ) / (q.den : ℝ) := Nat.cast_div hdvd hden0
  have h2 : ∀ i ∈ Finset.range (N + 1),
      (σ k i : ℝ) * ((N ! / i ! : ℕ) : ℝ) = (N ! : ℝ) * g k i := by
    intro i hi
    have hiN : i ! ∣ N ! := Nat.factorial_dvd_factorial (by
      have := Finset.mem_range.mp hi
      omega)
    have hifac : ((i ! : ℕ) : ℝ) ≠ 0 := ne_of_gt (factorial_cast_pos i)
    rw [Nat.cast_div hiN hifac]
    unfold g
    ring
  have h3 : (q : ℝ) * (N ! : ℝ) = (q.num : ℝ) * ((N ! / q.den : ℕ) : ℝ) := by
    rw [h1, Rat.cast_def]
    ring
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
  rw [Finset.sum_congr rfl h2]
  unfold T
  rw [tail_eq k (N + 1), ← hq, mul_sub, Finset.mul_sum]
  linear_combination -h3

lemma sigma_prime (k p : ℕ) (hp : p.Prime) : σ k p = 1 + p ^ k := by
  rw [ArithmeticFunction.sigma_apply, hp.divisors,
    Finset.sum_insert (by simp [Finset.mem_singleton, hp.one_lt.ne]),
    Finset.sum_singleton, one_pow]

/-- `(N+1)^j * N! ≤ (N+j)!`. -/
lemma pow_mul_factorial_le (N j : ℕ) : (N + 1) ^ j * N ! ≤ (N + j)! := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc (N + 1) ^ (j + 1) * N ! = (N + 1) * ((N + 1) ^ j * N !) := by ring
      _ ≤ (N + 1) * (N + j)! := Nat.mul_le_mul (Nat.le_refl _) ih
      _ ≤ (N + j + 1) * (N + j)! := Nat.mul_le_mul (by omega) (Nat.le_refl _)
      _ = (N + j + 1)! := (Nat.factorial_succ _).symm

lemma fact_ratio_le (N j : ℕ) :
    (N ! : ℝ) / ((N + j)! : ℝ) ≤ (1 / ((N : ℝ) + 1)) ^ j := by
  rw [div_pow, one_pow, div_le_div_iff₀ (factorial_cast_pos _) (by positivity)]
  calc (N ! : ℝ) * ((N : ℝ) + 1) ^ j = (((N + 1) ^ j * N ! : ℕ) : ℝ) := by push_cast; ring
  _ ≤ (((N + j)! : ℕ) : ℝ) := Nat.cast_le.mpr (pow_mul_factorial_le N j)
  _ = 1 * ((N + j)! : ℝ) := by ring

lemma T_le_of_terms (k N : ℕ) (c r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hterm : ∀ j : ℕ, (N ! : ℝ) * g k (j + (N + 1)) ≤ c * r ^ j) :
    T k N ≤ c / (1 - r) := by
  unfold T tail
  rw [← tsum_mul_left]
  have hsum1 : Summable (fun j : ℕ => (N ! : ℝ) * g k (j + (N + 1))) :=
    (summable_g_shift k (N + 1)).mul_left _
  have hsum2 : Summable (fun j : ℕ => c * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  calc ∑' j : ℕ, (N ! : ℝ) * g k (j + (N + 1)) ≤ ∑' j : ℕ, c * r ^ j :=
        hsum1.tsum_le_tsum hterm hsum2
  _ = c * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  _ = c / (1 - r) := (div_eq_mul_inv c _).symm

/- ### Specifics for `k = 1` -/

lemma sigma1_le (n : ℕ) : σ 1 n * 2 ≤ n * (n + 1) := by
  rw [ArithmeticFunction.sigma_one_apply]
  have h1 : ∑ d ∈ n.divisors, d ≤ ∑ d ∈ Finset.Icc 1 n, d :=
    Finset.sum_le_sum_of_subset fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  have h2 : (∑ d ∈ Finset.Icc 1 n, d) * 2 = n * (n + 1) := by
    have hins : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have h3 : ∑ d ∈ Finset.range (n + 1), d = ∑ d ∈ Finset.Icc 1 n, d := by
      rw [hins, Finset.sum_insert (by simp)]
      exact Nat.zero_add _
    calc (∑ d ∈ Finset.Icc 1 n, d) * 2 = (∑ d ∈ Finset.range (n + 1), d) * 2 := by rw [h3]
    _ = (n + 1) * (n + 1 - 1) := Finset.sum_range_id_mul_two (n + 1)
    _ = n * (n + 1) := by rw [Nat.add_sub_cancel]; ring
  calc (∑ d ∈ n.divisors, d) * 2 ≤ (∑ d ∈ Finset.Icc 1 n, d) * 2 :=
        Nat.mul_le_mul h1 (Nat.le_refl 2)
  _ = n * (n + 1) := h2

lemma sigma1_le_real (n : ℕ) : (σ 1 n : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  have h' : ((σ 1 n * 2 : ℕ) : ℝ) ≤ ((n * (n + 1) : ℕ) : ℝ) := Nat.cast_le.mpr (sigma1_le n)
  push_cast at h'
  linarith

lemma nat_bound (N j : ℕ) : N + j + 2 ≤ (N + 2) * 2 ^ j := by
  have h1 : j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt j.lt_two_pow_self
  have h2 : (N + 2) * (j + 1) ≤ (N + 2) * 2 ^ j := Nat.mul_le_mul (Nat.le_refl _) h1
  have h3 : (N + 2) * (j + 1) = N * j + N + 2 * j + 2 := by ring
  omega

lemma term_le_k1 (N j : ℕ) :
    (N ! : ℝ) * g 1 (j + (N + 1)) ≤ (((N : ℝ) + 2) / 2) * (2 / ((N : ℝ) + 1)) ^ j := by
  rw [show j + (N + 1) = (N + j) + 1 from by omega]
  unfold g
  have hfac : (((N + j + 1)! : ℕ) : ℝ) = ((N + j + 1 : ℕ) : ℝ) * (((N + j)! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hMne : ((N + j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hFne : (((N + j)! : ℕ) : ℝ) ≠ 0 := ne_of_gt (factorial_cast_pos _)
  have hnat : ((N + j + 1 : ℕ) : ℝ) + 1 ≤ (((N + 2) * 2 ^ j : ℕ) : ℝ) := by
    have h' : ((N + j + 2 : ℕ) : ℝ) ≤ (((N + 2) * 2 ^ j : ℕ) : ℝ) := Nat.cast_le.mpr (nat_bound N j)
    push_cast at h' ⊢
    linarith
  calc (N ! : ℝ) * ((σ 1 (N + j + 1) : ℝ) / (((N + j + 1)! : ℕ) : ℝ))
      ≤ (N ! : ℝ) * ((((N + j + 1 : ℕ) : ℝ) * (((N + j + 1 : ℕ) : ℝ) + 1) / 2)
          / (((N + j + 1)! : ℕ) : ℝ)) := by
        gcongr
        exact sigma1_le_real (N + j + 1)
  _ = ((((N + j + 1 : ℕ) : ℝ) + 1) / 2) * ((N ! : ℝ) / (((N + j)! : ℕ) : ℝ)) := by
        rw [hfac]
        field_simp
  _ ≤ ((((N + 2) * 2 ^ j : ℕ) : ℝ) / 2) * ((1 / ((N : ℝ) + 1)) ^ j) := by
        gcongr
        exact fact_ratio_le N j
  _ = (((N : ℝ) + 2) / 2) * (2 / ((N : ℝ) + 1)) ^ j := by
        push_cast
        rw [div_pow, div_pow, one_pow]
        ring

theorem k_eq_one : Irrational (Erdos252.erdos_252_sum 1) := by
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨p, hpmax, hp⟩ := Nat.exists_infinite_primes (max (q.den + 1) 11)
  have hp11 : 11 ≤ p := le_trans (le_max_right _ _) hpmax
  have hpden : q.den + 1 ≤ p := le_trans (le_max_left _ _) hpmax
  obtain ⟨t1, ht1⟩ := T_int 1 q hq (p - 1) (by omega)
  obtain ⟨t2, ht2⟩ := T_int 1 q hq p (by omega)
  have hσ : σ 1 p = p + 1 := by
    rw [sigma_prime 1 p hp, pow_one]
    omega
  have hrec := T_rec 1 (p - 1)
  rw [show p - 1 + 1 = p from by omega] at hrec
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  rw [hcast, ← ht1, ← ht2, hσ] at hrec
  have hrec' : (p : ℤ) * t1 = ((p : ℤ) + 1) + t2 := by exact_mod_cast hrec
  have ht2pos : (0 : ℤ) < t2 := by
    have h := T_pos 1 p
    rw [← ht2] at h
    exact_mod_cast h
  have hple : (11 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp11
  have hr0 : (0 : ℝ) ≤ 2 / ((p : ℝ) + 1) := by positivity
  have hr1 : 2 / ((p : ℝ) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hb := T_le_of_terms 1 p (((p : ℝ) + 2) / 2) (2 / ((p : ℝ) + 1)) hr0 hr1
    (fun j => term_le_k1 p j)
  have hub : T 1 p ≤ (p : ℝ) - 2 := by
    have h1r : (1 : ℝ) - 2 / ((p : ℝ) + 1) = ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
      field_simp
      ring
    rw [h1r] at hb
    have hb2 : (((p : ℝ) + 2) / 2) / (((p : ℝ) - 1) / ((p : ℝ) + 1))
        = ((p : ℝ) + 2) * ((p : ℝ) + 1) / (2 * ((p : ℝ) - 1)) := by
      field_simp
    rw [hb2] at hb
    have hfin : ((p : ℝ) + 2) * ((p : ℝ) + 1) / (2 * ((p : ℝ) - 1)) ≤ (p : ℝ) - 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have ht2le : t2 ≤ (p : ℤ) - 2 := by
    have h : (t2 : ℝ) ≤ (p : ℝ) - 2 := by rw [ht2]; exact hub
    exact_mod_cast h
  have hdvd : (p : ℤ) ∣ t2 + 1 := ⟨t1 - 1, by linear_combination -hrec'⟩
  have hple2 : (p : ℤ) ≤ t2 + 1 := Int.le_of_dvd (by omega) hdvd
  omega

end Contribution.Erdos252KEqOne

-- ==== from Harvest0_252k2.lean ====
/-
Erdős 252, k = 2 (Erdős–Kac 1954, Amer. Math. Monthly Problem 4518):
`∑ σ₂(n)/n!` is irrational.

Proof sketch: if the sum were `q ∈ ℚ`, then for every `N ≥ q.den` the scaled tail
`T N = N! * ∑_{n > N} σ₂(n)/n!` is a positive integer, and
`(N+1) * T N = σ₂(N+1) + T (N+1)`.  Hence for a prime `p > q.den` we get
`p ∣ T p + 1` (as `σ₂(p) = p² + 1`).  But `σ₂(p+1) ≥ (p+1)² + 1` gives
`T p > p + 1`, while `σ₂(n) ≤ (7/4)n²` (telescoping bound on `∑ 1/d²`) gives
`T p < 2p - 1` for `p ≥ 29`.  So `T p + 1` would be a multiple of `p`
strictly between `p` and `2p`, absurd.
-/

open scoped Nat ArithmeticFunction.sigma

namespace Contribution.Erdos252KEqTwo

/-- The summand of the Erdős 252 series. -/
noncomputable def g (k n : ℕ) : ℝ := (σ k n : ℝ) / (n ! : ℝ)

lemma erdos_sum_eq (k : ℕ) : Erdos252.erdos_252_sum k = ∑' n, g k n := rfl

lemma g_nonneg (k n : ℕ) : 0 ≤ g k n := by
  unfold g
  positivity

lemma factorial_cast_pos (n : ℕ) : (0 : ℝ) < (n ! : ℝ) :=
  Nat.cast_pos.mpr (Nat.factorial_pos n)

lemma one_le_sigma (k n : ℕ) (hn : n ≠ 0) : 1 ≤ σ k n := by
  rw [ArithmeticFunction.sigma_apply]
  calc 1 = 1 ^ k := (one_pow k).symm
  _ ≤ ∑ d ∈ n.divisors, d ^ k :=
      Finset.single_le_sum (f := fun d => d ^ k) (fun i _ => Nat.zero_le _)
        (Nat.one_mem_divisors.mpr hn)

lemma g_pos (k n : ℕ) (hn : n ≠ 0) : 0 < g k n := by
  unfold g
  exact div_pos (by exact_mod_cast one_le_sigma k n hn) (factorial_cast_pos n)

lemma card_divisors_le_self (n : ℕ) : n.divisors.card ≤ n := by
  calc n.divisors.card ≤ (Finset.Icc 1 n).card :=
        Finset.card_le_card fun d hd =>
          Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  _ = n := by rw [Nat.card_Icc]; omega

lemma sigma_le_pow (k n : ℕ) : σ k n ≤ (2 ^ (k + 1)) ^ n := by
  have h1 : σ k n ≤ n ^ (k + 1) := by
    rw [ArithmeticFunction.sigma_apply]
    calc ∑ d ∈ n.divisors, d ^ k ≤ ∑ _d ∈ n.divisors, n ^ k :=
          Finset.sum_le_sum fun d hd => Nat.pow_le_pow_left (Nat.divisor_le hd) k
    _ = n.divisors.card * n ^ k := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n ^ k := Nat.mul_le_mul (card_divisors_le_self n) (Nat.le_refl _)
    _ = n ^ (k + 1) := by ring
  calc σ k n ≤ n ^ (k + 1) := h1
  _ ≤ (2 ^ n) ^ (k + 1) := Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) _
  _ = (2 ^ (k + 1)) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

lemma summable_g (k : ℕ) : Summable (g k) := by
  apply Summable.of_nonneg_of_le (g_nonneg k) (fun n => ?_)
    (Real.summable_pow_div_factorial ((2 : ℝ) ^ (k + 1)))
  unfold g
  gcongr
  calc (σ k n : ℝ) ≤ (((2 ^ (k + 1)) ^ n : ℕ) : ℝ) := Nat.cast_le.mpr (sigma_le_pow k n)
  _ = ((2 : ℝ) ^ (k + 1)) ^ n := by push_cast; ring

lemma summable_g_shift (k N : ℕ) : Summable (fun j : ℕ => g k (j + N)) :=
  (summable_nat_add_iff N).mpr (summable_g k)

/-- The tail `∑_{n ≥ N} σ_k(n)/n!`. -/
noncomputable def tail (k N : ℕ) : ℝ := ∑' j : ℕ, g k (j + N)

/-- The scaled tail `N! * ∑_{n > N} σ_k(n)/n!`. -/
noncomputable def T (k N : ℕ) : ℝ := (N ! : ℝ) * tail k (N + 1)

lemma tail_pos (k N : ℕ) (hN : N ≠ 0) : 0 < tail k N :=
  Summable.tsum_pos (summable_g_shift k N) (fun j => g_nonneg k (j + N)) 0
    (g_pos k (0 + N) (by omega))

lemma T_pos (k N : ℕ) : 0 < T k N :=
  mul_pos (factorial_cast_pos N) (tail_pos k (N + 1) (Nat.succ_ne_zero N))

lemma tail_eq (k N : ℕ) :
    tail k N = Erdos252.erdos_252_sum k - ∑ i ∈ Finset.range N, g k i := by
  have h := (summable_g k).sum_add_tsum_nat_add N
  rw [erdos_sum_eq k]
  unfold tail
  linarith

lemma tail_rec (k N : ℕ) : tail k N = g k N + tail k (N + 1) := by
  unfold tail
  rw [(summable_g_shift k N).tsum_eq_zero_add]
  congr 1
  · rw [Nat.zero_add]
  · apply tsum_congr
    intro j
    congr 1
    omega

lemma T_rec (k N : ℕ) : ((N : ℝ) + 1) * T k N = (σ k (N + 1) : ℝ) + T k (N + 1) := by
  have hF : (0 : ℝ) < (N ! : ℝ) := factorial_cast_pos N
  have hF' : (N ! : ℝ) ≠ 0 := ne_of_gt hF
  have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hF1 : (((N + 1)! : ℕ) : ℝ) = ((N : ℝ) + 1) * (N ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  unfold T
  rw [tail_rec k (N + 1)]
  unfold g
  rw [hF1]
  field_simp

lemma T_int (k : ℕ) (q : ℚ) (hq : (q : ℝ) = Erdos252.erdos_252_sum k) (N : ℕ)
    (hN : q.den ≤ N) : ∃ t : ℤ, (t : ℝ) = T k N := by
  have hden0 : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hdvd : q.den ∣ N ! := Nat.dvd_factorial q.pos hN
  refine ⟨q.num * ((N ! / q.den : ℕ) : ℤ)
      - ∑ i ∈ Finset.range (N + 1), (σ k i : ℤ) * ((N ! / i ! : ℕ) : ℤ), ?_⟩
  have h1 : ((N ! / q.den : ℕ) : ℝ) = (N ! : ℝ) / (q.den : ℝ) := Nat.cast_div hdvd hden0
  have h2 : ∀ i ∈ Finset.range (N + 1),
      (σ k i : ℝ) * ((N ! / i ! : ℕ) : ℝ) = (N ! : ℝ) * g k i := by
    intro i hi
    have hiN : i ! ∣ N ! := Nat.factorial_dvd_factorial (by
      have := Finset.mem_range.mp hi
      omega)
    have hifac : ((i ! : ℕ) : ℝ) ≠ 0 := ne_of_gt (factorial_cast_pos i)
    rw [Nat.cast_div hiN hifac]
    unfold g
    ring
  have h3 : (q : ℝ) * (N ! : ℝ) = (q.num : ℝ) * ((N ! / q.den : ℕ) : ℝ) := by
    rw [h1, Rat.cast_def]
    ring
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast]
  rw [Finset.sum_congr rfl h2]
  unfold T
  rw [tail_eq k (N + 1), ← hq, mul_sub, Finset.mul_sum]
  linear_combination -h3

lemma sigma_prime (k p : ℕ) (hp : p.Prime) : σ k p = 1 + p ^ k := by
  rw [ArithmeticFunction.sigma_apply, hp.divisors,
    Finset.sum_insert (by simp [Finset.mem_singleton, hp.one_lt.ne]),
    Finset.sum_singleton, one_pow]

/-- `(N+1)^j * N! ≤ (N+j)!`. -/
lemma pow_mul_factorial_le (N j : ℕ) : (N + 1) ^ j * N ! ≤ (N + j)! := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc (N + 1) ^ (j + 1) * N ! = (N + 1) * ((N + 1) ^ j * N !) := by ring
      _ ≤ (N + 1) * (N + j)! := Nat.mul_le_mul (Nat.le_refl _) ih
      _ ≤ (N + j + 1) * (N + j)! := Nat.mul_le_mul (by omega) (Nat.le_refl _)
      _ = (N + j + 1)! := (Nat.factorial_succ _).symm

lemma fact_ratio_le (N j : ℕ) :
    (N ! : ℝ) / ((N + j)! : ℝ) ≤ (1 / ((N : ℝ) + 1)) ^ j := by
  rw [div_pow, one_pow, div_le_div_iff₀ (factorial_cast_pos _) (by positivity)]
  calc (N ! : ℝ) * ((N : ℝ) + 1) ^ j = (((N + 1) ^ j * N ! : ℕ) : ℝ) := by push_cast; ring
  _ ≤ (((N + j)! : ℕ) : ℝ) := Nat.cast_le.mpr (pow_mul_factorial_le N j)
  _ = 1 * ((N + j)! : ℝ) := by ring

lemma T_le_of_terms (k N : ℕ) (c r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hterm : ∀ j : ℕ, (N ! : ℝ) * g k (j + (N + 1)) ≤ c * r ^ j) :
    T k N ≤ c / (1 - r) := by
  unfold T tail
  rw [← tsum_mul_left]
  have hsum1 : Summable (fun j : ℕ => (N ! : ℝ) * g k (j + (N + 1))) :=
    (summable_g_shift k (N + 1)).mul_left _
  have hsum2 : Summable (fun j : ℕ => c * r ^ j) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  calc ∑' j : ℕ, (N ! : ℝ) * g k (j + (N + 1)) ≤ ∑' j : ℕ, c * r ^ j :=
        hsum1.tsum_le_tsum hterm hsum2
  _ = c * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  _ = c / (1 - r) := (div_eq_mul_inv c _).symm

/- ### Specifics for `k = 2` -/

lemma sum_inv_sq_le (n : ℕ) (hn : 2 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
      have h : Finset.Icc 1 2 = {1, 2} := by decide
      rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]
      norm_num
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      have hn1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have he : (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      have hkey : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
        rw [he, div_le_div_iff₀ (by positivity) (mul_pos hn0 (by linarith))]
        nlinarith
      linarith [ih]

lemma sigma2_le_real_aux (n : ℕ) (hn : 2 ≤ n) : (σ 2 n : ℝ) ≤ 7 / 4 * (n : ℝ) ^ 2 := by
  have h1 : σ 2 n = ∑ d ∈ n.divisors, (n / d) ^ 2 := by
    rw [ArithmeticFunction.sigma_apply]
    exact (Nat.sum_div_divisors n (fun d => d ^ 2)).symm
  have h2 : (σ 2 n : ℝ) = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ 2 := by
    rw [h1]
    push_cast
    rfl
  rw [h2]
  calc ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ 2
      ≤ ∑ d ∈ n.divisors, ((n : ℝ) / (d : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro d _
        gcongr
        exact Nat.cast_div_le
  _ = (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [div_pow]
        ring
  _ ≤ (n : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 n, 1 / (d : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact fun d hd => Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
        · intro i _ _
          positivity
  _ ≤ (n : ℝ) ^ 2 * (7 / 4 - 1 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le n hn) (by positivity)
  _ ≤ 7 / 4 * (n : ℝ) ^ 2 := by
        have h1n : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        nlinarith [sq_nonneg (n : ℝ)]

lemma sigma2_le_real (n : ℕ) : (σ 2 n : ℝ) ≤ 7 / 4 * (n : ℝ) ^ 2 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · norm_num
    · norm_num [ArithmeticFunction.sigma_apply, Nat.divisors_one]
  · exact sigma2_le_real_aux n h

lemma sigma2_lb (n : ℕ) (hn : 2 ≤ n) : n ^ 2 + 1 ≤ σ 2 n := by
  rw [ArithmeticFunction.sigma_apply]
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    rcases Finset.mem_insert.mp hd with h1 | h1
    · exact h1 ▸ Nat.one_mem_divisors.mpr (by omega)
    · rw [Finset.mem_singleton] at h1
      exact h1 ▸ Nat.mem_divisors_self n (by omega)
  calc n ^ 2 + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d ^ 2 := by
        rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
          Finset.sum_singleton, one_pow]
        omega
  _ ≤ ∑ d ∈ n.divisors, d ^ 2 := Finset.sum_le_sum_of_subset hsub

lemma sigma2_lb_real (n : ℕ) (hn : 2 ≤ n) : (n : ℝ) ^ 2 + 1 ≤ (σ 2 n : ℝ) := by
  have h : ((n ^ 2 + 1 : ℕ) : ℝ) ≤ ((σ 2 n : ℕ) : ℝ) := Nat.cast_le.mpr (sigma2_lb n hn)
  push_cast at h
  linarith

lemma nat_bound2 (N j : ℕ) : N + j + 1 ≤ (N + 1) * 2 ^ j := by
  have h1 : j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt j.lt_two_pow_self
  have h2 : (N + 1) * (j + 1) ≤ (N + 1) * 2 ^ j := Nat.mul_le_mul (Nat.le_refl _) h1
  have h3 : (N + 1) * (j + 1) = N * j + N + j + 1 := by ring
  omega

lemma term_le_k2 (N j : ℕ) :
    (N ! : ℝ) * g 2 (j + (N + 1)) ≤ (7 / 4 * ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1)) ^ j := by
  rw [show j + (N + 1) = (N + j) + 1 from by omega]
  unfold g
  have hfac : (((N + j + 1)! : ℕ) : ℝ) = ((N + j + 1 : ℕ) : ℝ) * (((N + j)! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hMne : ((N + j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hFne : (((N + j)! : ℕ) : ℝ) ≠ 0 := ne_of_gt (factorial_cast_pos _)
  have hnat : ((N + j + 1 : ℕ) : ℝ) ≤ (((N + 1) * 2 ^ j : ℕ) : ℝ) :=
    Nat.cast_le.mpr (nat_bound2 N j)
  calc (N ! : ℝ) * ((σ 2 (N + j + 1) : ℝ) / (((N + j + 1)! : ℕ) : ℝ))
      ≤ (N ! : ℝ) * ((7 / 4 * ((N + j + 1 : ℕ) : ℝ) ^ 2) / (((N + j + 1)! : ℕ) : ℝ)) := by
        gcongr
        exact sigma2_le_real (N + j + 1)
  _ = (7 / 4 * ((N + j + 1 : ℕ) : ℝ)) * ((N ! : ℝ) / (((N + j)! : ℕ) : ℝ)) := by
        rw [hfac]
        field_simp
  _ ≤ (7 / 4 * (((N + 1) * 2 ^ j : ℕ) : ℝ)) * ((1 / ((N : ℝ) + 1)) ^ j) := by
        gcongr
        exact fact_ratio_le N j
  _ = (7 / 4 * ((N : ℝ) + 1)) * (2 / ((N : ℝ) + 1)) ^ j := by
        push_cast
        rw [div_pow, div_pow, one_pow]
        ring

lemma T_lb (k N : ℕ) : (N ! : ℝ) * g k (0 + (N + 1)) ≤ T k N := by
  unfold T tail
  apply mul_le_mul_of_nonneg_left _ (factorial_cast_pos N).le
  exact (summable_g_shift k (N + 1)).le_tsum 0 (fun j _ => g_nonneg k _)

theorem k_eq_two : Irrational (Erdos252.erdos_252_sum 2) := by
  intro hmem
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨p, hpmax, hp⟩ := Nat.exists_infinite_primes (max (q.den + 1) 29)
  have hp29 : 29 ≤ p := le_trans (le_max_right _ _) hpmax
  have hpden : q.den + 1 ≤ p := le_trans (le_max_left _ _) hpmax
  obtain ⟨t1, ht1⟩ := T_int 2 q hq (p - 1) (by omega)
  obtain ⟨t2, ht2⟩ := T_int 2 q hq p (by omega)
  have hσ : σ 2 p = 1 + p ^ 2 := sigma_prime 2 p hp
  have hrec := T_rec 2 (p - 1)
  rw [show p - 1 + 1 = p from by omega] at hrec
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  rw [hcast, ← ht1, ← ht2, hσ] at hrec
  have hrec' : (p : ℤ) * t1 = 1 + (p : ℤ) ^ 2 + t2 := by exact_mod_cast hrec
  have hple : (29 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp29
  have hr0 : (0 : ℝ) ≤ 2 / ((p : ℝ) + 1) := by positivity
  have hr1 : 2 / ((p : ℝ) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hb := T_le_of_terms 2 p (7 / 4 * ((p : ℝ) + 1)) (2 / ((p : ℝ) + 1)) hr0 hr1
    (fun j => term_le_k2 p j)
  have hub : T 2 p < 2 * (p : ℝ) - 1 := by
    have h1r : (1 : ℝ) - 2 / ((p : ℝ) + 1) = ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
      field_simp
      ring
    rw [h1r] at hb
    have hb2 : (7 / 4 * ((p : ℝ) + 1)) / (((p : ℝ) - 1) / ((p : ℝ) + 1))
        = 7 * ((p : ℝ) + 1) ^ 2 / (4 * ((p : ℝ) - 1)) := by
      field_simp
    rw [hb2] at hb
    have hfin : 7 * ((p : ℝ) + 1) ^ 2 / (4 * ((p : ℝ) - 1)) < 2 * (p : ℝ) - 1 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hlow : (p : ℝ) + 1 < T 2 p := by
    have h0 := T_lb 2 p
    have he : (p ! : ℝ) * g 2 (0 + (p + 1)) = (σ 2 (p + 1) : ℝ) / ((p + 1 : ℕ) : ℝ) := by
      unfold g
      rw [Nat.zero_add]
      have hfac : (((p + 1)! : ℕ) : ℝ) = ((p + 1 : ℕ) : ℝ) * ((p ! : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac]
      have hp1 : ((p + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpf : ((p ! : ℕ) : ℝ) ≠ 0 := ne_of_gt (factorial_cast_pos p)
      field_simp
    rw [he] at h0
    have hσlb : ((p + 1 : ℕ) : ℝ) ^ 2 + 1 ≤ (σ 2 (p + 1) : ℝ) := sigma2_lb_real (p + 1) (by omega)
    have hp1 : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) := by
      have : (0 : ℕ) < p + 1 := by omega
      exact_mod_cast this
    have hgt : (p : ℝ) + 1 < (σ 2 (p + 1) : ℝ) / ((p + 1 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ hp1]
      push_cast at hσlb ⊢
      nlinarith [hσlb]
    linarith
  have ht2lb : (p : ℤ) + 2 ≤ t2 := by
    have h : (p : ℝ) + 1 < (t2 : ℝ) := by rw [ht2]; exact hlow
    have h' : (p : ℤ) + 1 < t2 := by exact_mod_cast h
    omega
  have ht2ub : t2 ≤ 2 * (p : ℤ) - 2 := by
    have h : (t2 : ℝ) < 2 * (p : ℝ) - 1 := by rw [ht2]; exact hub
    have h' : t2 < 2 * (p : ℤ) - 1 := by exact_mod_cast h
    omega
  have hdvd : (p : ℤ) ∣ t2 + 1 := ⟨t1 - p, by linear_combination -hrec'⟩
  have hdvd2 : (p : ℤ) ∣ t2 + 1 - p := dvd_sub hdvd (dvd_refl _)
  have hge : (p : ℤ) ≤ t2 + 1 - p := Int.le_of_dvd (by omega) hdvd2
  omega

end Contribution.Erdos252KEqTwo
