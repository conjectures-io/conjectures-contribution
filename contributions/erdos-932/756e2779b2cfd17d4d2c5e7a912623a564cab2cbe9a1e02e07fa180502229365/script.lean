import Mathlib
import FormalConjectures.ErdosProblems.«932»

/-!
# Erdős Problem 932, solved variant `one_le`

We prove that the set of indices `r` such that some integer `n` with
`p_r < n < p_{r+1}` has all prime factors `< p_{r+1} - p_r` has natural density `0`.

Outline (Erdős): fix `ε > 0` and a threshold `T`.
* The number of `r < N` with prime gap `≥ T` is at most `p_N / T` (gaps telescope),
  and `p_N = O(N log N)` by a Chebyshev-type bound proved here from the central
  binomial coefficient.
* Each remaining `r < N` in our set yields a witness `n < p_N` all of whose prime
  factors are `< T`; distinct `r` give distinct witnesses.  By Rankin's trick at
  `s = 1/2` (via Mathlib's Euler product over smooth numbers) the number of such
  `n` is at most `√(p_N) · exp(8√T)`, which is `o(N)` for `T ≈ C·log N`.
-/

namespace Contribution.Erdos932OneLe

open Filter Finset Real Topology

/- ## Basic finsets -/

/-- The witness set for index `r`: integers strictly between `p_r` and `p_{r+1}` whose
largest prime factor is smaller than the gap. -/
noncomputable def W (r : ℕ) : Finset ℕ :=
  (Finset.Ioo (Nat.nth Nat.Prime r) (Nat.nth Nat.Prime (r + 1))).filter
    (fun m => m.maxPrimeFac < Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r)

/-- The elements of the target set below `N`. -/
noncomputable def SF (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun r => 1 ≤ (W r).card)

/-- Indices below `N` whose prime gap is at least `T`. -/
noncomputable def AA (N T : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun r => T ≤ Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r)

/-- Indices below `N` with gap `< T` that lie in the target set. -/
noncomputable def BB (N T : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun r =>
    Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r < T ∧ 1 ≤ (W r).card)

/-- Numbers `1 < m < x` whose largest prime factor is `< T`. -/
noncomputable def Sm (x T : ℕ) : Finset ℕ :=
  (Finset.range x).filter (fun m => 1 < m ∧ m.maxPrimeFac < T)

lemma card_SF_split (N T : ℕ) : (SF N).card ≤ (AA N T).card + (BB N T).card := by
  classical
  have hsub : SF N ⊆ AA N T ∪ BB N T := by
    intro r hr
    simp only [SF, Finset.mem_filter] at hr
    rcases Nat.lt_or_ge (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) T with h | h
    · exact Finset.mem_union_right _
        (by simp only [BB, Finset.mem_filter]; exact ⟨hr.1, h, hr.2⟩)
    · exact Finset.mem_union_left _ (by simp only [AA, Finset.mem_filter]; exact ⟨hr.1, h⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/- ## The large-gap count -/

lemma gap_card (N T : ℕ) : T * (AA N T).card ≤ Nat.nth Nat.Prime N := by
  classical
  have h1 : (AA N T).card • T ≤
      ∑ r ∈ AA N T, (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) := by
    apply Finset.card_nsmul_le_sum
    intro r hr
    simp only [AA, Finset.mem_filter] at hr
    exact hr.2
  have h2 : ∑ r ∈ AA N T, (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) ≤
      ∑ r ∈ Finset.range N, (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) :=
    Finset.sum_le_sum_of_subset (by simp only [AA]; exact Finset.filter_subset _ _)
  have h3 : ∑ r ∈ Finset.range N, (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) =
      Nat.nth Nat.Prime N - Nat.nth Nat.Prime 0 :=
    Finset.sum_range_tsub (Nat.nth_monotone Nat.infinite_setOf_prime) N
  calc T * (AA N T).card = (AA N T).card • T := by rw [smul_eq_mul, mul_comm]
  _ ≤ ∑ r ∈ AA N T, (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) := h1
  _ ≤ ∑ r ∈ Finset.range N, (Nat.nth Nat.Prime (r + 1) - Nat.nth Nat.Prime r) := h2
  _ = Nat.nth Nat.Prime N - Nat.nth Nat.Prime 0 := h3
  _ ≤ Nat.nth Nat.Prime N := Nat.sub_le _ _

/- ## The witness injection -/

lemma card_BB_le (N T : ℕ) : (BB N T).card ≤ (Sm (Nat.nth Nat.Prime N) T).card := by
  classical
  set f : ℕ → ℕ := fun r => sInf {m : ℕ | m ∈ W r} with hf
  have hwit : ∀ r : ℕ, 1 ≤ (W r).card → f r ∈ W r := by
    intro r hr
    have hne : {m : ℕ | m ∈ W r}.Nonempty := by
      obtain ⟨m, hm⟩ := Finset.card_pos.mp hr
      exact ⟨m, hm⟩
    exact Nat.sInf_mem hne
  apply Finset.card_le_card_of_injOn f
  · intro r hr
    rw [Finset.mem_coe] at hr ⊢
    simp only [BB, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrN, hgap, hcard⟩ := hr
    have hm := hwit r hcard
    simp only [W, Finset.mem_filter, Finset.mem_Ioo] at hm
    obtain ⟨⟨hm1, hm2⟩, hm3⟩ := hm
    simp only [Sm, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · exact lt_of_lt_of_le hm2 (Nat.nth_monotone Nat.infinite_setOf_prime (by omega))
    · exact lt_trans (Nat.prime_nth_prime r).one_lt hm1
    · exact lt_trans hm3 hgap
  · have key : ∀ r s : ℕ, r ∈ BB N T → s ∈ BB N T → r < s → f r < f s := by
      intro r s hr hs hrs
      simp only [BB, Finset.mem_filter, Finset.mem_range] at hr hs
      have hmr := hwit r hr.2.2
      have hms := hwit s hs.2.2
      simp only [W, Finset.mem_filter, Finset.mem_Ioo] at hmr hms
      calc f r < Nat.nth Nat.Prime (r + 1) := hmr.1.2
      _ ≤ Nat.nth Nat.Prime s := Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
      _ < f s := hms.1.1
    intro r hr s hs heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd heq (ne_of_lt (key r s (Finset.mem_coe.mp hr) (Finset.mem_coe.mp hs) h))
    · exact absurd heq.symm (ne_of_lt (key s r (Finset.mem_coe.mp hs) (Finset.mem_coe.mp hr) h))

/- ## Chebyshev-type lower bound for the prime counting function -/

lemma four_pow_le (n : ℕ) (hn : 0 < n) :
    4 ^ n ≤ (2 * n + 1) * (2 * n) ^ ((2 * n + 1).primeCounting') := by
  classical
  have h1 : 4 ^ n ≤ (2 * n + 1) * n.centralBinom := by
    have h := Nat.four_pow_le_two_mul_add_one_mul_central_binom n
    rwa [← Nat.centralBinom_eq_two_mul_choose] at h
  have h2 : ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p =
      ∏ p ∈ (2 * n + 1).primesBelow, p ^ n.centralBinom.factorization p := by
    symm
    apply Finset.prod_subset
    · intro p hp
      exact Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp)
    · intro p hp hnp
      have hnotp : ¬ p.Prime := fun hprime =>
        hnp (Nat.mem_primesBelow.mpr ⟨Finset.mem_range.mp hp, hprime⟩)
      rw [Nat.factorization_eq_zero_of_not_prime _ hnotp, pow_zero]
  have h4 : ∏ p ∈ (2 * n + 1).primesBelow, p ^ n.centralBinom.factorization p ≤
      ∏ _p ∈ (2 * n + 1).primesBelow, (2 * n) := by
    apply Finset.prod_le_prod (fun i _ => Nat.zero_le _)
    intro p _
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.pow_factorization_choose_le (by omega)
  have h5 : ∏ _p ∈ (2 * n + 1).primesBelow, (2 * n) =
      (2 * n) ^ ((2 * n + 1).primeCounting') := by
    rw [Finset.prod_const, Nat.primesBelow_card_eq_primeCounting']
  calc 4 ^ n ≤ (2 * n + 1) * n.centralBinom := h1
  _ = (2 * n + 1) * ∏ p ∈ Finset.range (2 * n + 1), p ^ n.centralBinom.factorization p := by
      rw [Nat.prod_pow_factorization_centralBinom]
  _ = (2 * n + 1) * ∏ p ∈ (2 * n + 1).primesBelow, p ^ n.centralBinom.factorization p := by
      rw [h2]
  _ ≤ (2 * n + 1) * ∏ _p ∈ (2 * n + 1).primesBelow, (2 * n) := Nat.mul_le_mul le_rfl h4
  _ = (2 * n + 1) * (2 * n) ^ ((2 * n + 1).primeCounting') := by rw [h5]

lemma log_cheb (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log 4 ≤
      Real.log (2 * (n : ℝ) + 1) +
        ((2 * n + 1).primeCounting' : ℝ) * Real.log (2 * (n : ℝ)) := by
  have h := four_pow_le n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR : (4 : ℝ) ^ n ≤ (2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ ((2 * n + 1).primeCounting') := by
    exact_mod_cast h
  have h1 : (n : ℝ) * Real.log 4 = Real.log ((4 : ℝ) ^ n) := by
    rw [Real.log_pow]
  have h2 : Real.log ((4 : ℝ) ^ n) ≤
      Real.log ((2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ ((2 * n + 1).primeCounting')) :=
    Real.log_le_log (by positivity) hR
  have h3 : Real.log ((2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ ((2 * n + 1).primeCounting')) =
      Real.log (2 * (n : ℝ) + 1) +
        Real.log ((2 * (n : ℝ)) ^ ((2 * n + 1).primeCounting')) := by
    apply Real.log_mul (by positivity) (by positivity)
  have h4 : Real.log ((2 * (n : ℝ)) ^ ((2 * n + 1).primeCounting')) =
      ((2 * n + 1).primeCounting' : ℝ) * Real.log (2 * (n : ℝ)) := Real.log_pow _ _
  linarith [h1, h2, h3.symm.le, h3.le, h4.le, h4.symm.le]

/-- Eventually, the `N`-th prime is at most `5 N log N`. -/
lemma nth_prime_le : ∀ᶠ N : ℕ in atTop, (Nat.nth Nat.Prime N : ℝ) ≤ 5 * N * Real.log N := by
  filter_upwards [eventually_ge_atTop 100] with N hN
  have hN' : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    have h1 : Real.exp 1 ≤ 100 := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 : Real.exp 1 ≤ (N : ℝ) := by linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) h2
  have hlogpos : (0 : ℝ) < Real.log N := by linarith
  set n : ℕ := ⌈2 * (N : ℝ) * Real.log N⌉₊ with hn_def
  have hn_pos : 0 < n := Nat.ceil_pos.mpr (by positivity)
  have hn_ge : 2 * (N : ℝ) * Real.log N ≤ (n : ℝ) := Nat.le_ceil _
  have hn_le : (n : ℝ) ≤ 2 * (N : ℝ) * Real.log N + 1 := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * (N : ℝ) * Real.log N by positivity)
    rw [hn_def]
    exact this.le
  -- square root facts
  have hsN : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt (by linarith)
  have hs10 : (10 : ℝ) ≤ Real.sqrt N := by
    have h100 : Real.sqrt 100 = 10 := by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    calc (10 : ℝ) = Real.sqrt 100 := h100.symm
    _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hN'
  have hlog_sqrt : Real.log N ≤ 2 * Real.sqrt N := by
    have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hNpos)
    have h2 : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt (by linarith)
    linarith
  -- 2n+1 ≤ N²
  have h2n1 : 2 * (n : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by
    have e1 : 2 * (n : ℝ) + 1 ≤ 4 * (N : ℝ) * Real.log N + 3 := by linarith
    have e2 : 4 * (N : ℝ) * Real.log N ≤ 8 * (N : ℝ) * Real.sqrt N := by
      nlinarith [hlog_sqrt, hNpos.le]
    have h100 : (100 : ℝ) ≤ Real.sqrt N * Real.sqrt N := by nlinarith [hs10]
    have h1000 : (1000 : ℝ) ≤ Real.sqrt N * Real.sqrt N * Real.sqrt N := by
      nlinarith [hs10, h100]
    have hcube : Real.sqrt N * Real.sqrt N * Real.sqrt N * 2 ≤
        Real.sqrt N * Real.sqrt N * Real.sqrt N * (Real.sqrt N - 8) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e3 : 8 * (N : ℝ) * Real.sqrt N = 8 * (Real.sqrt N * Real.sqrt N * Real.sqrt N) := by
      linear_combination (-8 * Real.sqrt (N : ℝ)) * hsN
    have e4 : (N : ℝ) ^ 2 = (Real.sqrt N * Real.sqrt N) * (Real.sqrt N * Real.sqrt N) := by
      linear_combination (-((N : ℝ) + Real.sqrt N * Real.sqrt N)) * hsN
    nlinarith [e1, e2, e3, e4, hcube, h1000]
  -- the prime counting must exceed N
  have hkey : N < (2 * n + 1).primeCounting' := by
    by_contra hcon
    push_neg at hcon
    have hcheb := log_cheb n hn_pos
    have hπN : ((2 * n + 1).primeCounting' : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcon
    have hl1 : Real.log (2 * (n : ℝ) + 1) ≤ 2 * Real.log N := by
      have h1 : Real.log (2 * (n : ℝ) + 1) ≤ Real.log ((N : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) h2n1
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have hl2 : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log N := by
      have h0 : Real.log (2 * (n : ℝ)) ≤ Real.log (2 * (n : ℝ) + 1) :=
        Real.log_le_log (by positivity) (by linarith)
      linarith
    have hlog4 : (1.38 : ℝ) ≤ Real.log 4 := by
      have h2 := Real.log_two_gt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        ring
      linarith
    have hlogn_nonneg : 0 ≤ Real.log (2 * (n : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
      linarith
    have hprod : ((2 * n + 1).primeCounting' : ℝ) * Real.log (2 * (n : ℝ)) ≤
        (N : ℝ) * (2 * Real.log N) :=
      mul_le_mul hπN hl2 hlogn_nonneg (by linarith)
    have hup : (n : ℝ) * Real.log 4 ≤ 2 * Real.log N + (N : ℝ) * (2 * Real.log N) := by
      linarith
    have hdown : 2 * (N : ℝ) * Real.log N * 1.38 ≤ (n : ℝ) * Real.log 4 :=
      mul_le_mul hn_ge hlog4 (by norm_num) (Nat.cast_nonneg n)
    have hcontr : (0.76 * (N : ℝ) - 2) * Real.log N ≤ 0 := by nlinarith [hup, hdown]
    have h76 : (0 : ℝ) < 0.76 * (N : ℝ) - 2 := by linarith
    exact absurd hcontr (not_le.mpr (mul_pos h76 hlogpos))
  have hlt : Nat.nth Nat.Prime N < 2 * n + 1 := by
    have hc : N < Nat.count Nat.Prime (2 * n + 1) := hkey
    exact Nat.nth_lt_of_lt_count hc
  have hle : (Nat.nth Nat.Prime N : ℝ) ≤ 2 * (n : ℝ) := by
    have h : Nat.nth Nat.Prime N ≤ 2 * n := by omega
    exact_mod_cast h
  have hNlog : (2 : ℝ) ≤ (N : ℝ) * Real.log N := by nlinarith
  calc (Nat.nth Nat.Prime N : ℝ) ≤ 2 * (n : ℝ) := hle
  _ ≤ 4 * (N : ℝ) * Real.log N + 2 := by linarith
  _ ≤ 5 * (N : ℝ) * Real.log N := by nlinarith [hNlog]

/- ## Rankin's trick at `s = 1/2` -/

/-- The completely multiplicative function `n ↦ n^(-1/2)`. -/
noncomputable def rp : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-(1 / 2) : ℝ)
  map_one' := by
    rw [Nat.cast_one, Real.one_rpow]
  map_mul' m k := by
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg k)

lemma rp_norm_lt {p : ℕ} (hp : p.Prime) : ‖rp p‖ < 1 := by
  show ‖(p : ℝ) ^ (-(1 / 2) : ℝ)‖ < 1
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  calc (p : ℝ) ^ (-(1 / 2) : ℝ) < (p : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
  _ = 1 := Real.rpow_zero _

lemma smooth_hasSum (T : ℕ) :
    HasSum (fun m : T.smoothNumbers => ((m : ℕ) : ℝ) ^ (-(1 / 2) : ℝ))
      (∏ p ∈ T.primesBelow, (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) :=
  (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rp) (fun hp => rp_norm_lt hp) T).2

lemma sum_inv_sqrt (T : ℕ) :
    ∑ k ∈ Finset.Icc 1 T, ((k : ℝ) ^ (-(1 / 2) : ℝ)) ≤ 2 * Real.sqrt T := by
  induction T with
  | zero =>
    rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by rfl, Finset.sum_empty]
    positivity
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hb : (0 : ℝ) < Real.sqrt ((T : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha2 : Real.sqrt (T : ℝ) * Real.sqrt (T : ℝ) = (T : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg T)
    have hb2 : Real.sqrt ((T : ℝ) + 1) * Real.sqrt ((T : ℝ) + 1) = (T : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hstep : (((T : ℝ) + 1)) ^ (-(1 / 2) : ℝ) ≤
        2 * Real.sqrt ((T : ℝ) + 1) - 2 * Real.sqrt (T : ℝ) := by
      have hrw : (((T : ℝ) + 1)) ^ (-(1 / 2) : ℝ) = (Real.sqrt ((T : ℝ) + 1))⁻¹ := by
        rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]
      rw [hrw, inv_eq_one_div, div_le_iff₀ hb]
      have key : 2 * Real.sqrt (T : ℝ) * Real.sqrt ((T : ℝ) + 1) ≤ 2 * (T : ℝ) + 1 := by
        nlinarith [sq_nonneg (Real.sqrt (T : ℝ) - Real.sqrt ((T : ℝ) + 1)), ha2, hb2]
      nlinarith [key, hb2]
    push_cast
    linarith [ih, hstep]

lemma factor_le {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ ≤ Real.exp (4 * (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have ht0 : (0 : ℝ) < (p : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have ht2 : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by norm_num)
  have h34 : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow]
    have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hspos : (0 : ℝ) < Real.sqrt 2 := by positivity
    rw [inv_eq_one_div, div_le_iff₀ hspos]
    nlinarith [hs]
  have hlt : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := le_trans ht2 h34
  have hpos : (0 : ℝ) < 1 - (p : ℝ) ^ (-(1 / 2) : ℝ) := by linarith
  have h1 : (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ ≤ 1 + 4 * (p : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith [ht0, hlt]
  have h2' : 1 + 4 * (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ Real.exp (4 * (p : ℝ) ^ (-(1 / 2) : ℝ)) := by
    have := Real.add_one_le_exp (4 * (p : ℝ) ^ (-(1 / 2) : ℝ))
    linarith
  linarith

lemma prod_bound (T : ℕ) :
    ∏ p ∈ T.primesBelow, (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ ≤ Real.exp (8 * Real.sqrt T) := by
  have hnn : ∀ p ∈ T.primesBelow, (0 : ℝ) ≤ (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ := by
    intro p hp
    have hp' := Nat.prime_of_mem_primesBelow hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    have ht2 : (p : ℝ) ^ (-(1 / 2) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by norm_num)
    have hlt1 : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
      calc (2 : ℝ) ^ (-(1 / 2) : ℝ) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 1 := Real.rpow_zero _
    exact inv_nonneg.mpr (by linarith)
  calc ∏ p ∈ T.primesBelow, (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹
      ≤ ∏ p ∈ T.primesBelow, Real.exp (4 * (p : ℝ) ^ (-(1 / 2) : ℝ)) :=
        Finset.prod_le_prod hnn (fun p hp => factor_le (Nat.prime_of_mem_primesBelow hp))
  _ = Real.exp (∑ p ∈ T.primesBelow, 4 * (p : ℝ) ^ (-(1 / 2) : ℝ)) := (Real.exp_sum _ _).symm
  _ ≤ Real.exp (8 * Real.sqrt T) := by
      rw [Real.exp_le_exp, ← Finset.mul_sum]
      have h1 : ∑ p ∈ T.primesBelow, (p : ℝ) ^ (-(1 / 2) : ℝ) ≤
          ∑ k ∈ Finset.Icc 1 T, ((k : ℝ) ^ (-(1 / 2) : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hp2 := Nat.prime_of_mem_primesBelow hp
          have hp3 := Nat.lt_of_mem_primesBelow hp
          exact Finset.mem_Icc.mpr ⟨hp2.one_lt.le, by omega⟩
        · intro i _ _
          positivity
      have h2 := sum_inv_sqrt T
      have h3 : (0 : ℝ) ≤ Real.sqrt T := Real.sqrt_nonneg _
      linarith

lemma smooth_card (x T : ℕ) :
    ((Sm x T).card : ℝ) ≤ Real.sqrt x * Real.exp (8 * Real.sqrt T) := by
  classical
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have : Sm 0 T = ∅ := by
      simp [Sm]
    rw [this]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hsub : ∀ m ∈ Sm x T, m ∈ T.smoothNumbers := by
    intro m hm
    simp only [Sm, Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmr, hm1, hmp⟩ := hm
    refine ⟨by omega, ?_⟩
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    have hpd := Nat.dvd_of_mem_primeFactorsList hp
    have hle : p ≤ m.maxPrimeFac := by
      apply le_csSup
      · exact ⟨m, fun q hq => Nat.le_of_dvd (by omega) hq.2⟩
      · exact ⟨hpp, hpd⟩
    omega
  have hhs := smooth_hasSum T
  have hInd : HasSum ((T.smoothNumbers).indicator (fun k : ℕ => (k : ℝ) ^ (-(1 / 2) : ℝ)))
      (∏ p ∈ T.primesBelow, (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) :=
    (hasSum_subtype_iff_indicator
      (f := fun k : ℕ => (k : ℝ) ^ (-(1 / 2) : ℝ))).mp hhs
  have hsum1 : ∑ m ∈ Sm x T,
      (T.smoothNumbers).indicator (fun k : ℕ => (k : ℝ) ^ (-(1 / 2) : ℝ)) m ≤
      ∏ p ∈ T.primesBelow, (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ :=
    sum_le_hasSum (Sm x T)
      (fun i _ => Set.indicator_nonneg (fun a _ => by positivity) i) hInd
  have hsum2 : ∑ m ∈ Sm x T,
      (T.smoothNumbers).indicator (fun k : ℕ => (k : ℝ) ^ (-(1 / 2) : ℝ)) m =
      ∑ m ∈ Sm x T, ((m : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) :=
    Finset.sum_congr rfl (fun m hm => Set.indicator_of_mem (hsub m hm) _)
  have hterm : ∀ m ∈ Sm x T, ((x : ℝ)) ^ (-(1 / 2) : ℝ) ≤ ((m : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
    intro m hm
    simp only [Sm, Finset.mem_filter, Finset.mem_range] at hm
    have h1m : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hmx : (m : ℝ) ≤ (x : ℝ) := by exact_mod_cast hm.1.le
    exact Real.rpow_le_rpow_of_nonpos h1m hmx (by norm_num)
  have hcard : ((Sm x T).card : ℝ) * ((x : ℝ)) ^ (-(1 / 2) : ℝ) ≤
      ∑ m ∈ Sm x T, ((m : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
    calc ((Sm x T).card : ℝ) * ((x : ℝ)) ^ (-(1 / 2) : ℝ)
        = ∑ _m ∈ Sm x T, ((x : ℝ)) ^ (-(1 / 2) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ Sm x T, ((m : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := Finset.sum_le_sum hterm
  have hprod := prod_bound T
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hxrp : ((x : ℝ)) ^ (-(1 / 2) : ℝ) * Real.sqrt x = 1 := by
    rw [Real.rpow_neg hxpos.le, Real.sqrt_eq_rpow]
    exact inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hxpos _))
  calc ((Sm x T).card : ℝ)
      = ((Sm x T).card : ℝ) * (((x : ℝ)) ^ (-(1 / 2) : ℝ) * Real.sqrt x) := by
        rw [hxrp, mul_one]
  _ = (((Sm x T).card : ℝ) * ((x : ℝ)) ^ (-(1 / 2) : ℝ)) * Real.sqrt x := by ring
  _ ≤ (∏ p ∈ T.primesBelow, (1 - (p : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) * Real.sqrt x := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      calc ((Sm x T).card : ℝ) * ((x : ℝ)) ^ (-(1 / 2) : ℝ)
          ≤ ∑ m ∈ Sm x T, ((m : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := hcard
      _ ≤ _ := by rw [← hsum2]; exact hsum1
  _ ≤ Real.exp (8 * Real.sqrt T) * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hprod (Real.sqrt_nonneg _)
  _ = Real.sqrt x * Real.exp (8 * Real.sqrt T) := mul_comm _ _

/- ## The decay estimate -/

lemma exp_identity (b x : ℝ) (hx : 0 < x) :
    Real.sqrt 5 * Real.sqrt x * Real.log x * Real.exp (Real.log x / 4 + b) / x =
      Real.sqrt 5 * Real.exp b * (Real.log x * Real.exp (-(Real.log x / 4))) := by
  have h1 : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [← Real.log_sqrt hx.le, Real.exp_log (Real.sqrt_pos.mpr hx)]
  have h2 : x = Real.exp (Real.log x) := (Real.exp_log hx).symm
  set l := Real.log x with hl
  rw [h1]
  rw [h2]
  have hne : Real.exp l ≠ 0 := (Real.exp_pos l).ne'
  have key : Real.exp (l / 2) * Real.exp (l / 4 + b) =
      Real.exp b * Real.exp (-(l / 4)) * Real.exp l := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc Real.sqrt 5 * Real.exp (l / 2) * l * Real.exp (l / 4 + b) / Real.exp l
      = (Real.exp (l / 2) * Real.exp (l / 4 + b)) * (Real.sqrt 5 * l) / Real.exp l := by
        ring
  _ = (Real.exp b * Real.exp (-(l / 4)) * Real.exp l) * (Real.sqrt 5 * l) / Real.exp l := by
        rw [key]
  _ = Real.sqrt 5 * Real.exp b * (l * Real.exp (-(l / 4))) := by
        field_simp

lemma decay (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun N : ℕ => Real.sqrt (5 * N * Real.log N) *
      Real.exp (8 * Real.sqrt (c * Real.log N + 1)) / N) atTop (𝓝 0) := by
  set a : ℝ := 8 * Real.sqrt (c + 1) with ha_def
  have ha : 0 ≤ a := by positivity
  -- the dominating sequence tends to zero
  have h1 : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
    have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    simpa using this
  have hL : Tendsto (fun N : ℕ => Real.log N / 4) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have h4 := h1.comp hL
  have hcomp : Tendsto (fun N : ℕ =>
      Real.sqrt 5 * Real.exp (a ^ 2) * (Real.log N * Real.exp (-(Real.log N / 4))))
      atTop (𝓝 0) := by
    have h5 := h4.const_mul (4 * Real.sqrt 5 * Real.exp (a ^ 2))
    rw [mul_zero] at h5
    refine h5.congr fun N => ?_
    simp only [Function.comp]
    ring
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hcomp
  filter_upwards [eventually_ge_atTop 3] with N hN3
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    have h1' : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hLpos : (0 : ℝ) < Real.log N := by linarith
  -- (i) √(5·N·log N) ≤ √5·√N·log N
  have hi : Real.sqrt (5 * (N : ℝ) * Real.log N) ≤
      Real.sqrt 5 * Real.sqrt N * Real.log N := by
    have e1 : Real.sqrt (5 * (N : ℝ) * Real.log N) =
        Real.sqrt 5 * Real.sqrt N * Real.sqrt (Real.log N) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num)]
    rw [e1]
    have hsl : Real.sqrt (Real.log N) ≤ Real.log N := by
      nlinarith [sq_nonneg (Real.sqrt (Real.log N) - 1), Real.sq_sqrt hLpos.le, hL1]
    exact mul_le_mul_of_nonneg_left hsl (by positivity)
  -- (ii) 8√(c·L+1) ≤ a·√L
  have hii : 8 * Real.sqrt (c * Real.log N + 1) ≤ a * Real.sqrt (Real.log N) := by
    have h1' : c * Real.log N + 1 ≤ (c + 1) * Real.log N := by
      have hexp : (c + 1) * Real.log N = c * Real.log N + Real.log N := by ring
      linarith [hL1]
    calc 8 * Real.sqrt (c * Real.log N + 1) ≤ 8 * Real.sqrt ((c + 1) * Real.log N) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1') (by norm_num)
    _ = 8 * (Real.sqrt (c + 1) * Real.sqrt (Real.log N)) := by
        rw [Real.sqrt_mul (by linarith)]
    _ = a * Real.sqrt (Real.log N) := by rw [ha_def]; ring
  -- (iii) a·√L ≤ L/4 + a²
  have hiii : a * Real.sqrt (Real.log N) ≤ Real.log N / 4 + a ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (Real.log N) / 2 - a), Real.sq_sqrt hLpos.le]
  calc Real.sqrt (5 * (N : ℝ) * Real.log N) *
      Real.exp (8 * Real.sqrt (c * Real.log N + 1)) / N
      ≤ Real.sqrt 5 * Real.sqrt N * Real.log N *
          Real.exp (Real.log N / 4 + a ^ 2) / N := by
        gcongr
        linarith [hii, hiii]
  _ = Real.sqrt 5 * Real.exp (a ^ 2) * (Real.log N * Real.exp (-(Real.log N / 4))) :=
      exp_identity (a ^ 2) N hNpos

/- ## The main theorem -/

theorem one_le :
    { r : ℕ | 1 ≤ (Finset.Ioo (r.nth Nat.Prime) (r.succ.nth Nat.Prime) |>.filter
      (fun m => m.maxPrimeFac < r.succ.nth Nat.Prime - r.nth Nat.Prime)).card }.HasDensity 0 := by
  classical
  have hfun : ∀ N : ℕ,
      Set.partialDensity { r : ℕ | 1 ≤ (Finset.Ioo (r.nth Nat.Prime) (r.succ.nth Nat.Prime)
        |>.filter (fun m => m.maxPrimeFac < r.succ.nth Nat.Prime - r.nth Nat.Prime)).card }
        Set.univ N = ((SF N).card : ℝ) / N := by
    intro N
    have h1 : ({ r : ℕ | 1 ≤ (Finset.Ioo (r.nth Nat.Prime) (r.succ.nth Nat.Prime)
        |>.filter (fun m => m.maxPrimeFac < r.succ.nth Nat.Prime - r.nth Nat.Prime)).card }
        ∩ Set.univ) ∩ Set.Iio N = ↑(SF N) := by
      ext r
      constructor
      · rintro ⟨⟨hS, -⟩, hlt⟩
        rw [Finset.mem_coe]
        simp only [SF, Finset.mem_filter, Finset.mem_range]
        refine ⟨hlt, ?_⟩
        exact hS
      · intro h
        rw [Finset.mem_coe] at h
        simp only [SF, Finset.mem_filter, Finset.mem_range] at h
        exact ⟨⟨h.2, trivial⟩, h.1⟩
    simp only [Set.partialDensity]
    rw [h1, Set.ncard_coe_finset, Set.univ_inter, Nat.ncard_Iio]
  unfold Set.HasDensity
  rw [tendsto_congr hfun, tendsto_order]
  constructor
  · intro a ha
    refine Eventually.of_forall fun N => lt_of_lt_of_le ha (by positivity)
  · intro ε hε
    set K : ℕ := ⌈2 / ε⌉₊ with hK_def
    have hKpos : 0 < K := Nat.ceil_pos.mpr (by positivity)
    have hK2 : 2 / ε ≤ (K : ℝ) := Nat.le_ceil _
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hKinv : 1 / (K : ℝ) ≤ ε / 2 := by
      rw [div_le_iff₀ hKR]
      rw [div_le_iff₀ hε] at hK2
      linarith
    have hdec := decay (5 * (K : ℝ)) (by positivity)
    have hev2 := hdec.eventually_lt_const (show (0 : ℝ) < ε / 2 by positivity)
    filter_upwards [nth_prime_le, hev2, eventually_ge_atTop 3] with N hPN hvN hN3
    have hNpos : 0 < N := by omega
    have hNRpos : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNne : (N : ℝ) ≠ 0 := hNRpos.ne'
    have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hppos : 0 < Nat.nth Nat.Prime N := (Nat.prime_nth_prime N).pos
    set T : ℕ := Nat.nth Nat.Prime N * K / N + 1 with hT_def
    -- the ℕ-counting
    have hsplit := card_SF_split N T
    have hAcount : K * (AA N T).card < N := by
      rcases Nat.eq_zero_or_pos (AA N T).card with h0 | hApos
      · rw [h0, Nat.mul_zero]
        exact hNpos
      · have h1 : T * (AA N T).card ≤ Nat.nth Nat.Prime N := gap_card N T
        have h2 : Nat.nth Nat.Prime N * K < N * T := by
          rw [hT_def]
          exact Nat.lt_mul_div_succ _ hNpos
        have h3 : Nat.nth Nat.Prime N * (K * (AA N T).card) < Nat.nth Nat.Prime N * N := by
          calc Nat.nth Nat.Prime N * (K * (AA N T).card)
              = (Nat.nth Nat.Prime N * K) * (AA N T).card := by ring
          _ < (N * T) * (AA N T).card := mul_lt_mul_of_pos_right h2 hApos
          _ = N * (T * (AA N T).card) := by ring
          _ ≤ N * Nat.nth Nat.Prime N := Nat.mul_le_mul le_rfl h1
          _ = Nat.nth Nat.Prime N * N := by ring
        exact lt_of_mul_lt_mul_left h3 (Nat.zero_le _)
    have hAreal : ((AA N T).card : ℝ) / N ≤ ε / 2 := by
      have h1 : ((AA N T).card : ℝ) * K ≤ (N : ℝ) := by
        have h2 : K * (AA N T).card ≤ N := hAcount.le
        have h3 : ((K * (AA N T).card : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
        push_cast at h3
        linarith
      have h2 : ((AA N T).card : ℝ) ≤ (N : ℝ) / K := by
        rw [le_div_iff₀ hKR]
        exact h1
      calc ((AA N T).card : ℝ) / N ≤ ((N : ℝ) / K) / N := by gcongr
      _ = 1 / K := by field_simp
      _ ≤ ε / 2 := hKinv
    -- the B-count
    have hT_le : (T : ℝ) ≤ 5 * (K : ℝ) * Real.log N + 1 := by
      have hle1 : ((Nat.nth Nat.Prime N * K / N : ℕ) : ℝ) ≤
          ((Nat.nth Nat.Prime N * K : ℕ) : ℝ) / (N : ℝ) := Nat.cast_div_le
      have hle2 : ((Nat.nth Nat.Prime N * K : ℕ) : ℝ) / (N : ℝ) =
          (Nat.nth Nat.Prime N : ℝ) * K / N := by push_cast; ring
      have hle3 : (Nat.nth Nat.Prime N : ℝ) * K / N ≤ (5 * N * Real.log N) * K / N := by
        gcongr
      have hle4 : (5 * (N : ℝ) * Real.log N) * K / N = 5 * (K : ℝ) * Real.log N := by
        field_simp
      rw [hT_def]
      push_cast
      linarith [hle1, hle2.le, hle3, hle4.le]
    have hBk : ((BB N T).card : ℝ) ≤ Real.sqrt (5 * N * Real.log N) *
        Real.exp (8 * Real.sqrt (5 * (K : ℝ) * Real.log N + 1)) := by
      have h1 : (BB N T).card ≤ (Sm (Nat.nth Nat.Prime N) T).card := card_BB_le N T
      calc ((BB N T).card : ℝ) ≤ ((Sm (Nat.nth Nat.Prime N) T).card : ℝ) := by exact_mod_cast h1
      _ ≤ Real.sqrt (Nat.nth Nat.Prime N) * Real.exp (8 * Real.sqrt T) :=
          smooth_card (Nat.nth Nat.Prime N) T
      _ ≤ Real.sqrt (5 * N * Real.log N) *
          Real.exp (8 * Real.sqrt (5 * (K : ℝ) * Real.log N + 1)) := by
            gcongr
    -- combine
    have hsplit' : ((SF N).card : ℝ) ≤ ((AA N T).card : ℝ) + ((BB N T).card : ℝ) := by
      exact_mod_cast hsplit
    have hfrac : ((SF N).card : ℝ) / N ≤
        ((AA N T).card : ℝ) / N + ((BB N T).card : ℝ) / N := by
      rw [← add_div]
      gcongr
    have hBfrac : ((BB N T).card : ℝ) / N < ε / 2 := by
      calc ((BB N T).card : ℝ) / N ≤ Real.sqrt (5 * N * Real.log N) *
          Real.exp (8 * Real.sqrt (5 * (K : ℝ) * Real.log N + 1)) / N := by gcongr
      _ < ε / 2 := hvN
    calc ((SF N).card : ℝ) / N
        ≤ ((AA N T).card : ℝ) / N + ((BB N T).card : ℝ) / N := hfrac
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hAreal hBfrac
    _ = ε := by ring

end Contribution.Erdos932OneLe
