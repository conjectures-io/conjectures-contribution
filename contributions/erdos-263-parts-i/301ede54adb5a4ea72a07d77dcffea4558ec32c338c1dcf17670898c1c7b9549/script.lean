import FormalConjectures.ErdosProblems.«263»

/-!
# Erdős 263(i): the bounded-tail case

Target: `IsIrrationalitySequence (fun n => 2 ^ 2 ^ n)`, i.e. every positive `b` with
`2 ^ 2 ^ n / b n → 1` has irrational `∑ 1 / b n`.

Suppose instead `∑ 1 / b n = p / q`. The scaled tails `tailInt b p q n = q * (b 0 ⋯ b (n-1)) *
∑_{k ≥ n} 1 / b k` are then positive integers with `tailInt (n+1) = b n * tailInt n - q * P n`.

* `sylvester_not_asymp` — a sequence eventually following Sylvester's recursion
  `b (n+1) = b n ^ 2 - b n + 1` never satisfies `2 ^ 2 ^ n / b n → 1`.
* `eventually_sylvester_of_bounded` — for any positive integers obeying that recursion, if they are
  bounded then `b` eventually follows Sylvester's recursion.
* `tailInt_eq` — the integer `tailInt` equals the real scaled tail.
* `tailInt_unbounded` — **main result**: in any counterexample the scaled tails are unbounded.

So the remaining (open) case of Erdős 263(i) is exactly: positive integer tails `I n → ∞` (along a
subsequence) with `I (n+1) / I n → 1`.
-/

open Filter Topology

namespace Contribution.Erdos263Partial


/-- A sequence that eventually follows Sylvester's recursion `b (n+1) = b n ^ 2 - b n + 1`
cannot satisfy `2 ^ 2 ^ n / b n → 1`. -/
theorem sylvester_not_asymp (b : ℕ → ℕ) (N0 : ℕ)
    (hrec : ∀ n ≥ N0, (b (n + 1) : ℝ) = (b n : ℝ) ^ 2 - b n + 1)
    (hlim : Tendsto (fun n => ((2 : ℝ) ^ 2 ^ n) / (b n : ℝ)) atTop (𝓝 1)) : False := by
  set M : ℕ → ℝ := fun n => (2 : ℝ) ^ 2 ^ n with hM
  have hMpos : ∀ n, 0 < M n := fun n => by positivity
  have hMsq : ∀ n, M (n + 1) = M n ^ 2 := fun n => by
    simp only [hM, pow_succ, pow_mul]
  -- r n = (b n - 1/2) / M n
  set r : ℕ → ℝ := fun n => ((b n : ℝ) - 1 / 2) / M n with hr
  -- b n / M n → 1
  have hbM : Tendsto (fun n => (b n : ℝ) / M n) atTop (𝓝 1) := by
    have h := hlim.inv₀ (by norm_num)
    simpa [inv_div] using h
  have hMinv : Tendsto (fun n => 1 / (2 * M n)) atTop (𝓝 0) := by
    have hM_top : Tendsto M atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have h1 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
      have h2 : 2 ^ n ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
      simp only [hM]; exact_mod_cast h1.trans h2
    have : Tendsto (fun n => 2 * M n) atTop atTop := hM_top.const_mul_atTop (by norm_num)
    exact this.inv_tendsto_atTop.congr (fun n => (one_div _).symm)
  have hr_lim : Tendsto r atTop (𝓝 1) := by
    have : r = fun n => (b n : ℝ) / M n - 1 / (2 * M n) := by
      funext n; simp only [hr]; field_simp [(hMpos n).ne']
    rw [this]; simpa using hbM.sub hMinv
  -- recursion for r
  have hr_rec : ∀ n ≥ N0, r (n + 1) = r n ^ 2 + 1 / (4 * M n ^ 2) := by
    intro n hn
    simp only [hr, hMsq, hrec n hn]
    field_simp [(hMpos n).ne']
    ring
  -- r n ≠ 1 : b n - 1/2 is a half-integer, M n an integer
  have hr_ne : ∀ n, r n ≠ 1 := by
    intro n h
    have h' : (b n : ℝ) - 1 / 2 = M n := by
      simp only [hr] at h; field_simp [(hMpos n).ne'] at h; linarith
    have hint : ((2 * b n : ℕ) : ℝ) = ((2 * 2 ^ 2 ^ n + 1 : ℕ) : ℝ) := by
      push_cast; simp only [hM] at h'; linarith
    have := Nat.cast_injective hint
    omega
  -- Step 1: r n < 1 for n ≥ N0
  have hr_lt : ∀ n ≥ N0, r n < 1 := by
    intro m hm
    by_contra hge
    push Not at hge
    have hgt : 1 < r m := lt_of_le_of_ne hge (Ne.symm (hr_ne m))
    -- d k = r (m+k) - 1 at least doubles
    have hgrow : ∀ k, 2 ^ k * (r m - 1) ≤ r (m + k) - 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have hge1 : 1 ≤ r (m + k) := by nlinarith [pow_pos (two_pos (α := ℝ)) k]
        have hrec' := hr_rec (m + k) (by omega)
        rw [show m + (k + 1) = m + k + 1 by ring, hrec']
        have : 0 ≤ 1 / (4 * M (m + k) ^ 2) := by positivity
        rw [pow_succ]; nlinarith
    -- contradiction with r → 1
    have hev : ∀ᶠ n in atTop, r n < 1 + (r m - 1) := by
      have := hr_lim.eventually (Iio_mem_nhds (show (1 : ℝ) < 1 + (r m - 1) by linarith))
      simpa using this
    obtain ⟨K, hK⟩ := eventually_atTop.mp hev
    have h1 := hK (m + (K + 1)) (by omega)
    have h2 := hgrow (K + 1)
    have h3 : (1 : ℝ) ≤ 2 ^ (K + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  -- Step 2: s n = 1 - r n ≥ 1/(2 M n), and s grows by 3/2 while ≤ 1/4
  have hs_low : ∀ n ≥ N0, 1 / (2 * M n) ≤ 1 - r n := by
    intro n hn
    have hlt := hr_lt n hn
    have hb_lt : (b n : ℝ) - 1 / 2 < M n := by
      simp only [hr] at hlt; rwa [div_lt_one (hMpos n)] at hlt
    have hb_le : (b n : ℝ) ≤ M n := by
      have : b n < 2 ^ 2 ^ n + 1 := by
        have : (b n : ℝ) < ((2 ^ 2 ^ n + 1 : ℕ) : ℝ) := by push_cast; simp only [hM] at hb_lt; linarith
        exact_mod_cast this
      have : b n ≤ 2 ^ 2 ^ n := by omega
      simp only [hM]; exact_mod_cast this
    simp only [hr]
    rw [div_le_iff₀ (by positivity)]
    field_simp [(hMpos n).ne']
    nlinarith [hMpos n]
  have hs_step : ∀ n ≥ N0, 1 - r n ≤ 1 / 4 → (3 / 2) * (1 - r n) ≤ 1 - r (n + 1) := by
    intro n hn hsmall
    have hlow := hs_low n hn
    have heps : 1 / (4 * M n ^ 2) ≤ (1 - r n) ^ 2 := by
      have h0 : 0 < 1 / (2 * M n) := by have := hMpos n; positivity
      have : (1 / (2 * M n)) ^ 2 ≤ (1 - r n) ^ 2 := pow_le_pow_left₀ h0.le hlow 2
      calc 1 / (4 * M n ^ 2) = (1 / (2 * M n)) ^ 2 := by field_simp [(hMpos n).ne']; ring
        _ ≤ (1 - r n) ^ 2 := this
    rw [hr_rec n hn]
    have hpos : 0 < 1 - r n := by linarith [hr_lt n hn]
    nlinarith
  -- s → 0, so eventually s ≤ 1/4; then geometric growth contradicts boundedness
  have hs_lim : Tendsto (fun n => 1 - r n) atTop (𝓝 0) := by simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hr_lim
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hs_lim.eventually (Iic_mem_nhds (show (0:ℝ) < 1 / 4 by norm_num)))
  set n1 := max K N0 with hn1
  have hpos1 : 0 < 1 - r n1 := by linarith [hr_lt n1 (le_max_right _ _)]
  have hgeo : ∀ k, (3 / 2 : ℝ) ^ k * (1 - r n1) ≤ 1 - r (n1 + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsmall : 1 - r (n1 + k) ≤ 1 / 4 := hK _ (by omega)
      have := hs_step (n1 + k) (by omega) hsmall
      rw [show n1 + (k + 1) = n1 + k + 1 by ring, pow_succ]
      nlinarith
  -- (3/2)^k * s n1 is unbounded
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 4 / (1 - r n1)) (by norm_num : (1:ℝ) < 3 / 2)
  have h1 := hgeo k
  have h2 : 1 - r (n1 + k) ≤ 1 / 4 := hK _ (by omega)
  rw [div_lt_iff₀ hpos1] at hk
  linarith



/-- If positive integers `I n` satisfy `I (n+1) = b n * I n - Q n` with `Q (n+1) = Q n * b n`,
`b n → ∞` and `b (n+1) / b n ^ 2 → 1`, and `I` is bounded, then `b` eventually satisfies
Sylvester's recursion `b (n+1) = b n ^ 2 - b n + 1`. -/
theorem eventually_sylvester_of_bounded (b : ℕ → ℕ) (I Q : ℕ → ℤ)
    (hI : ∀ n, 0 < I n) (B : ℤ) (hB : ∀ n, I n ≤ B)
    (hrecI : ∀ n, I (n + 1) = b n * I n - Q n) (hrecQ : ∀ n, Q (n + 1) = Q n * b n)
    (hb_top : Tendsto (fun n => (b n : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (b (n + 1) : ℝ) / (b n : ℝ) ^ 2) atTop (𝓝 1)) :
    ∃ N0, ∀ n ≥ N0, (b (n + 1) : ℝ) = (b n : ℝ) ^ 2 - b n + 1 := by
  -- the eliminated relation, in ℝ
  have hkey : ∀ n, (b (n + 1) : ℝ) * I (n + 1) =
      I (n + 2) + (b n : ℝ) ^ 2 * I n - b n * I (n + 1) := by
    intro n
    have h1 : (I (n + 1) : ℝ) = b n * I n - Q n := by exact_mod_cast hrecI n
    have h2 : (I (n + 2) : ℝ) = b (n + 1) * I (n + 1) - Q (n + 1) := by exact_mod_cast hrecI (n + 1)
    have h3 : (Q (n + 1) : ℝ) = Q n * b n := by exact_mod_cast hrecQ n
    rw [h2, h3]; rw [h1]; ring
  have hIpos : ∀ n, (0 : ℝ) < I n := fun n => by exact_mod_cast hI n
  have hBr : ∀ n, (I n : ℝ) ≤ B := fun n => by exact_mod_cast hB n
  -- ratio I n / I (n+1) → 1
  have hbsq_top : Tendsto (fun n => (b n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hb_top
  have hinv_b : Tendsto (fun n => 1 / (b n : ℝ)) atTop (𝓝 0) := by
    refine hb_top.inv_tendsto_atTop.congr (fun n => ?_)
    simp [one_div]
  have hsmall : Tendsto (fun n => (I (n + 2) : ℝ) / ((b n : ℝ) ^ 2 * I (n + 1))) atTop (𝓝 0) := by
    have hb2 : Tendsto (fun n => (B : ℝ) / (b n : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hbsq_top
    refine squeeze_zero' (Eventually.of_forall fun n =>
      div_nonneg (hIpos _).le (mul_nonneg (sq_nonneg _) (hIpos _).le)) ?_ hb2
    filter_upwards [hbsq_top.eventually_gt_atTop 0] with n hn
    rw [div_le_div_iff₀ (by have := hIpos (n + 1); positivity) hn]
    have h1 : (1 : ℝ) ≤ I (n + 1) := by exact_mod_cast hI (n + 1)
    have hB0 : (0 : ℝ) ≤ B := (hIpos 0).le.trans (hBr 0)
    have e1 : (I (n + 2) : ℝ) * (b n : ℝ) ^ 2 ≤ B * (b n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (hBr _) hn.le
    have e2 : (B : ℝ) * (b n : ℝ) ^ 2 ≤ B * ((b n : ℝ) ^ 2 * I (n + 1)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hn.le h1) hB0
    linarith
  have hrat : Tendsto (fun n => (I n : ℝ) / I (n + 1)) atTop (𝓝 1) := by
    have hexpr : ∀ᶠ n in atTop, (I n : ℝ) / I (n + 1) =
        (b (n + 1) : ℝ) / (b n : ℝ) ^ 2 - (I (n + 2) : ℝ) / ((b n : ℝ) ^ 2 * I (n + 1)) + 1 / (b n : ℝ) := by
      filter_upwards [hb_top.eventually_gt_atTop 0] with n hn
      have hI1 := hIpos (n + 1)
      field_simp
      have := hkey n
      nlinarith [this]
    have : Tendsto (fun n => (b (n + 1) : ℝ) / (b n : ℝ) ^ 2 -
        (I (n + 2) : ℝ) / ((b n : ℝ) ^ 2 * I (n + 1)) + 1 / (b n : ℝ)) atTop (𝓝 1) := by
      simpa using (hratio.sub hsmall).add hinv_b
    exact this.congr' (hexpr.mono fun n h => h.symm)
  -- eventually I n = I (n+1)
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le (hIpos 0) (hBr 0)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp
    (hrat.eventually (Metric.ball_mem_nhds (1 : ℝ) (show (0 : ℝ) < 1 / B by positivity)))
  have hconst : ∀ n ≥ N1, I n = I (n + 1) := by
    intro n hn
    have h := hN1 n hn
    rw [Real.dist_eq] at h
    have hI1 := hIpos (n + 1)
    have habs : |(I n : ℝ) - I (n + 1)| < 1 := by
      have hlt : |(I n : ℝ) / I (n + 1) - 1| * I (n + 1) < 1 := by
        have h2 := hBr (n + 1)
        calc |(I n : ℝ) / I (n + 1) - 1| * I (n + 1) ≤ |(I n : ℝ) / I (n + 1) - 1| * B := by
              gcongr
          _ < 1 / B * B := by gcongr
          _ = 1 := by field_simp
      have heq : (I n : ℝ) - I (n + 1) = ((I n : ℝ) / I (n + 1) - 1) * I (n + 1) := by
        field_simp
      rw [heq, abs_mul, abs_of_pos hI1]; exact hlt
    have : |I n - I (n + 1)| < 1 := by exact_mod_cast habs
    have := abs_lt.mp this
    omega
  -- constant I ⇒ Sylvester
  refine ⟨N1, fun n hn => ?_⟩
  have e1 := hconst n hn
  have e2 := hconst (n + 1) (by omega)
  have r1 := hrecI n
  have r2 := hrecI (n + 1)
  have rq := hrecQ n
  have hIn := hI n
  -- from e1,r1: Q n = (b n - 1) * I n ; from e2,r2,rq: (b(n+1) - 1) * I n = Q n * b n
  have hz : ((b (n + 1) : ℤ) - (b n ^ 2 - b n + 1)) * I n = 0 := by
    rw [← e1] at r1
    rw [← e2, ← e1] at r2
    rw [rq] at r2
    have hQ : Q n = (b n - 1) * I n := by linarith
    rw [hQ] at r2
    nlinarith [r2]
  have hz' : (b (n + 1) : ℤ) = b n ^ 2 - b n + 1 := by
    rcases mul_eq_zero.mp hz with h | h
    · linarith
    · exact absurd h (ne_of_gt hIn)
  exact_mod_cast hz'


/-- The integer "scaled tail" `q * (∏_{k<n} b k) * ∑_{k ≥ n} 1 / b k`, written without reals:
`p * P n - q * ∑_{k<n} P n / b k` where `P n = ∏_{k<n} b k`. -/
def tailInt (b : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℤ :=
  p * (∏ k ∈ Finset.range n, (b k : ℤ)) -
    q * ∑ k ∈ Finset.range n, (∏ j ∈ Finset.range n, (b j : ℤ)) / (b k : ℤ)

section Tails
variable (b : ℕ → ℕ) (hb : ∀ n, 0 < b n)

include hb in
lemma prod_ne_zero (n : ℕ) : (∏ k ∈ Finset.range n, (b k : ℤ)) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => by exact_mod_cast (hb k).ne'

lemma dvd_prod {n k : ℕ} (hk : k ∈ Finset.range n) :
    (b k : ℤ) ∣ ∏ j ∈ Finset.range n, (b j : ℤ) := Finset.dvd_prod_of_mem _ hk

include hb in
/-- Real form of the tail integer. -/
lemma tailInt_eq (p : ℤ) (q : ℕ) (hq : 0 < q) (hsumm : Summable fun n => 1 / (b n : ℝ))
    (hsum : ∑' n, 1 / (b n : ℝ) = p / q) (n : ℕ) :
    (tailInt b p q n : ℝ) =
      q * (∏ k ∈ Finset.range n, (b k : ℝ)) * ∑' k, 1 / (b (k + n) : ℝ) := by
  have hsplit := hsumm.sum_add_tsum_nat_add n
  rw [hsum] at hsplit
  have htail : ∑' k, 1 / (b (k + n) : ℝ) = p / q - ∑ k ∈ Finset.range n, 1 / (b k : ℝ) := by
    linarith
  rw [htail, tailInt]
  push_cast
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdiv : ∀ k ∈ Finset.range n, (((∏ j ∈ Finset.range n, (b j : ℤ)) / (b k : ℤ) : ℤ) : ℝ) =
      (∏ j ∈ Finset.range n, (b j : ℝ)) / (b k : ℝ) := by
    intro k hk
    rw [Int.cast_div (dvd_prod b hk) (by exact_mod_cast (hb k).ne')]
    push_cast; rfl
  rw [Finset.sum_congr rfl hdiv, mul_sub, Finset.mul_sum, Finset.mul_sum]
  field_simp

end Tails

/-- **Bounded case of Erdős 263(i).** Let `b` be positive with `2 ^ 2 ^ n / b n → 1` and suppose
`∑ 1 / b n = p / q` is rational. Then the integer scaled tails `tailInt b p q n` are unbounded.
Equivalently: in any counterexample to `IsIrrationalitySequence (2 ^ 2 ^ ·)`, the scaled tails
`q * (b 0 ⋯ b (n-1)) * ∑_{k ≥ n} 1/b k` (positive integers) must tend to infinity along a
subsequence; a bounded tail forces Sylvester's recursion, which is incompatible with
`b n ~ 2 ^ 2 ^ n`. -/
theorem tailInt_unbounded (b : ℕ → ℕ) (hb : ∀ n, 0 < b n)
    (hlim : Tendsto (fun n => ((2 : ℝ) ^ 2 ^ n) / (b n : ℝ)) atTop (𝓝 1))
    (p : ℤ) (q : ℕ) (hq : 0 < q) (hsum : ∑' n, 1 / (b n : ℝ) = p / q) :
    ¬ ∃ B : ℤ, ∀ n, tailInt b p q n ≤ B := by
  rintro ⟨B, hB⟩
  set u : ℕ → ℝ := fun n => ((2 : ℝ) ^ 2 ^ n) / (b n : ℝ) with hu
  have hbpos : ∀ n, (0 : ℝ) < b n := fun n => by exact_mod_cast hb n
  have hupos : ∀ n, 0 < u n := fun n => by simp only [hu]; have := hbpos n; positivity
  have hbu : ∀ n, (b n : ℝ) = (2 : ℝ) ^ 2 ^ n / u n := fun n => by
    simp only [hu]; field_simp [(hbpos n).ne']
  -- summability: 1 / b n = u n * (1/2)^(2^n) ≤ 2 * (1/2)^n eventually
  have hsumm : Summable fun n => 1 / (b n : ℝ) := by
    have hev : ∀ᶠ n in atTop, u n ≤ 2 := hlim.eventually (Iic_mem_nhds (by norm_num))
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_geometric_two).mul_left 2) ?_
    filter_upwards [hev] with n hn
    rw [Real.norm_eq_abs, abs_of_pos (by have := hbpos n; positivity), hbu n, one_div_div]
    have h2n : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ 2 ^ n :=
      pow_le_pow_right₀ (by norm_num) (Nat.lt_two_pow_self).le
    calc u n / (2 : ℝ) ^ 2 ^ n ≤ 2 / (2 : ℝ) ^ n := by
          gcongr
      _ = 2 * (1 / 2) ^ n := by rw [one_div_pow, mul_one_div]
  -- tails are positive
  have hR : ∀ n, 0 < ∑' k, 1 / (b (k + n) : ℝ) := fun n =>
    ((summable_nat_add_iff n).mpr hsumm).tsum_pos (fun k => by have := hbpos (k + n); positivity) 0
      (by have := hbpos (0 + n); positivity)
  have hP : ∀ n, (0 : ℝ) < ∏ k ∈ Finset.range n, (b k : ℝ) :=
    fun n => Finset.prod_pos fun k _ => hbpos k
  have hI : ∀ n, 0 < tailInt b p q n := by
    intro n
    have h := tailInt_eq b hb p q hq hsumm hsum n
    have : (0 : ℝ) < tailInt b p q n := by
      rw [h]; have := hR n; have := hP n; have : (0:ℝ) < q := by exact_mod_cast hq
      positivity
    exact_mod_cast this
  set Q : ℕ → ℤ := fun n => q * ∏ k ∈ Finset.range n, (b k : ℤ) with hQ
  have hrecQ : ∀ n, Q (n + 1) = Q n * b n := fun n => by
    simp only [hQ, Finset.prod_range_succ]; ring
  have hrecI : ∀ n, tailInt b p q (n + 1) = b n * tailInt b p q n - Q n := by
    intro n
    have h1 := tailInt_eq b hb p q hq hsumm hsum (n + 1)
    have h0 := tailInt_eq b hb p q hq hsumm hsum n
    have hsplit : ∑' k, 1 / (b (k + n) : ℝ) = 1 / (b n : ℝ) + ∑' k, 1 / (b (k + (n + 1)) : ℝ) := by
      rw [((summable_nat_add_iff n).mpr hsumm).tsum_eq_zero_add]
      simp only [zero_add]
      congr 1; refine tsum_congr fun k => ?_; congr 3; ring
    have : ((tailInt b p q (n + 1) : ℤ) : ℝ) = ((b n * tailInt b p q n - Q n : ℤ) : ℝ) := by
      push_cast; rw [h1, h0, hsplit, Finset.prod_range_succ]; simp only [hQ]; push_cast
      field_simp [(hbpos n).ne']; ring
    exact_mod_cast this
  have hb_top : Tendsto (fun n => (b n : ℝ)) atTop atTop := by
    have hM : Tendsto (fun n => (2 : ℝ) ^ 2 ^ n) atTop atTop := by
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have h1 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
      have h2 : 2 ^ n ≤ 2 ^ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h1
      exact_mod_cast h1.trans h2
    have hinv : Tendsto (fun n => (u n)⁻¹) atTop (𝓝 1) := by simpa using hlim.inv₀ (by norm_num)
    have := hM.atTop_mul_pos (by norm_num : (0:ℝ) < 1) hinv
    refine this.congr (fun n => ?_)
    rw [hbu n, div_eq_mul_inv]
  have hratio : Tendsto (fun n => (b (n + 1) : ℝ) / (b n : ℝ) ^ 2) atTop (𝓝 1) := by
    have hform : ∀ n, (b (n + 1) : ℝ) / (b n : ℝ) ^ 2 = (u n) ^ 2 / u (n + 1) := by
      intro n
      rw [hbu (n + 1), hbu n]
      have h2 : (2 : ℝ) ^ 2 ^ (n + 1) = ((2 : ℝ) ^ 2 ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [h2]; field_simp [(hupos n).ne', (hupos (n + 1)).ne']
    simp_rw [hform]
    have h := (hlim.pow 2).div (hlim.comp (tendsto_add_atTop_nat 1)) one_ne_zero
    norm_num at h
    exact h.congr (fun n => rfl)
  obtain ⟨N0, hN0⟩ := eventually_sylvester_of_bounded b (tailInt b p q) Q hI B hB hrecI hrecQ hb_top hratio
  exact sylvester_not_asymp b N0 hN0 hlim

end Contribution.Erdos263Partial
