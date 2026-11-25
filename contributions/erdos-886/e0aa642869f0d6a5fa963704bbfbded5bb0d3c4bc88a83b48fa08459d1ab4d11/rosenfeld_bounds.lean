import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 886: Erdős–Rosenfeld Theorems

Self-contained Lean 4 proofs of both `[research solved]` variants of Erdős Problem 886
from [ErRo97] (Erdős & Rosenfeld 1997):
1. `erdos_886_rosenfeld_bound`: For any `C > 0`, every positive integer `n ≥ 1` has at most
   `1 + C ^ 2` divisors in `[n ^ (1 / 2), n ^ (1 / 2) + C * n ^ (1 / 4)]`, proved by the
   injective map `d ↦ d + n / d` into integers inside `[2 n ^ (1 / 2), 2 n ^ (1 / 2) + C ^ 2]`.
2. `erdos_886_rosenfeld_infinite`: Infinitely many integers `n` have at least `4` divisors in
   `(n ^ (1 / 2), n ^ (1 / 2) + 16 * n ^ (1 / 4))`, witnessed explicitly by
   `n(t) = ∏ i ∈ [0, 7], (t + i)` for `t ≥ 25`.
-/

namespace Contribution.Erdos886

open Nat Filter

/--
The set of divisors of `n` in the interval `(n^{1/2}, n^{1/2} + C n^{1/2 - ε})`.
Matches `Erdos886.Erdos886Divisors` definitionally.
-/
noncomputable def Erdos886Divisors (n : ℕ) (ε : ℝ) (C : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d =>
    (n : ℝ) ^ (1/2 : ℝ) < d ∧ (d : ℝ) < (n : ℝ) ^ (1/2 : ℝ) + C * (n : ℝ) ^ (1/2 - ε))

/-! ### Helper identities for real fractional powers -/

private lemma rpow_half_mul_self {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp
  · rw [← Real.rpow_add hxpos]
    norm_num

private lemma rpow_quarter_sq {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 2 = x ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma lt_rpow_of_pow_lt {x y : ℝ} {k : ℕ} (hk : k ≠ 0) (hx : 0 ≤ x)
    (hlt : x ^ k < y) : x < y ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h1kpos : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr hkpos
  have hpow : (x ^ k) ^ (1 / (k : ℝ)) < y ^ (1 / (k : ℝ)) :=
    Real.rpow_lt_rpow (pow_nonneg hx k) hlt h1kpos
  rwa [← Real.rpow_natCast x k, ← Real.rpow_mul hx, mul_one_div_cancel hkpos.ne',
    Real.rpow_one] at hpow

/-! ### Part 1: Erdős–Rosenfeld Upper Bound (`≤ 1 + C ^ 2`) -/

private lemma rosenfeld_bound_of_pos {C : ℝ} (hC : 0 < C) {n : ℕ} (hn : 1 ≤ n) :
    (((divisors n).filter (fun (d : ℕ) =>
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
        (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
      ≤ 1 + C ^ 2 := by
  let S : Finset ℕ := (divisors n).filter (fun (d : ℕ) =>
    (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧
      (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))
  change (S.card : ℝ) ≤ 1 + C ^ 2
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [hS, Finset.card_empty]
    simp only [Nat.cast_zero]
    positivity
  · let s : ℝ := (n : ℝ) ^ (1 / 2 : ℝ)
    let q : ℝ := (n : ℝ) ^ (1 / 4 : ℝ)
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hspos : 0 < s := Real.rpow_pos_of_pos hnpos _
    have hss : s * s = n := rpow_half_mul_self hn0
    have hq2 : q ^ 2 = s := rpow_quarter_sq hn0
    let f : ℕ → ℕ := fun d => d + n / d
    let T : Finset ℕ := S.image f
    have h_div_mul : ∀ d ∈ S, d ∣ n ∧ (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
      intro d hd
      have hd_div : d ∈ divisors n := (Finset.mem_filter.mp hd).1
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd_div).1
      refine ⟨hdvd, ?_⟩
      exact_mod_cast Nat.mul_div_cancel' hdvd
    have h_inj : Set.InjOn f S := by
      intro d₁ hd₁ d₂ hd₂ hfeq
      obtain ⟨_, hm₁⟩ := h_div_mul d₁ hd₁
      obtain ⟨_, hm₂⟩ := h_div_mul d₂ hd₂
      have hs₁ : s ≤ d₁ := (Finset.mem_filter.mp hd₁).2.1
      have hs₂ : s ≤ d₂ := (Finset.mem_filter.mp hd₂).2.1
      have hfeqR : (d₁ : ℝ) + ((n / d₁ : ℕ) : ℝ) = (d₂ : ℝ) + ((n / d₂ : ℕ) : ℝ) := by
        exact_mod_cast hfeq
      have hmul : ((d₁ : ℝ) - d₂) * ((d₁ : ℝ) * d₂ - n) = 0 := by
        calc
          ((d₁ : ℝ) - d₂) * ((d₁ : ℝ) * d₂ - n)
              = (d₁ : ℝ) ^ 2 * d₂ - d₁ * d₂ ^ 2 - d₁ * n + d₂ * n := by ring
          _ = (d₁ : ℝ) ^ 2 * d₂ + d₂ * ((d₁ : ℝ) * ((n / d₁ : ℕ) : ℝ))
              - d₁ * d₂ ^ 2 - d₁ * ((d₂ : ℝ) * ((n / d₂ : ℕ) : ℝ)) := by rw [hm₁, hm₂]; ring
          _ = (d₁ : ℝ) * d₂ * (((d₁ : ℝ) + ((n / d₁ : ℕ) : ℝ)) - ((d₂ : ℝ) + ((n / d₂ : ℕ) : ℝ))) := by ring
          _ = 0 := by rw [hfeqR, sub_self, mul_zero]
      rcases mul_eq_zero.mp hmul with hdiff | hprod
      · have : (d₁ : ℝ) = d₂ := sub_eq_zero.mp hdiff
        exact Nat.cast_injective this
      · have hprod' : (d₁ : ℝ) * d₂ = s * s := by linarith only [hprod, hss]
        have hsum0 : ((d₁ : ℝ) - s) * s + (d₁ : ℝ) * ((d₂ : ℝ) - s) = 0 := by
          linarith only [show ((d₁ : ℝ) - s) * s + (d₁ : ℝ) * ((d₂ : ℝ) - s) = (d₁ : ℝ) * d₂ - s * s by ring, hprod']
        have h1 : 0 ≤ ((d₁ : ℝ) - s) * s := mul_nonneg (sub_nonneg.mpr hs₁) hspos.le
        have h2 : 0 ≤ (d₁ : ℝ) * ((d₂ : ℝ) - s) := mul_nonneg (hspos.le.trans hs₁) (sub_nonneg.mpr hs₂)
        have hd1eq : (d₁ : ℝ) = s := by nlinarith only [hspos, h1, h2, hsum0]
        have hd2eq : (d₂ : ℝ) = s := by nlinarith only [hspos, h1, h2, hsum0, hd1eq]
        exact Nat.cast_injective (hd1eq.trans hd2eq.symm)
    have h_bounds : ∀ y ∈ T, 2 * s ≤ (y : ℝ) ∧ (y : ℝ) ≤ 2 * s + C ^ 2 := by
      intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨_, hm⟩ := h_div_mul d hd
      have hlo : s ≤ d := (Finset.mem_filter.mp hd).2.1
      have hhi : (d : ℝ) ≤ s + C * q := (Finset.mem_filter.mp hd).2.2
      have hdpos : (0 : ℝ) < d := lt_of_lt_of_le hspos hlo
      have hfd_cast : (f d : ℝ) = (d : ℝ) + ((n / d : ℕ) : ℝ) := by
        dsimp [f]
        push_cast
        rfl
      have h_id : ((f d : ℝ) - 2 * s) * (d : ℝ) = ((d : ℝ) - s) ^ 2 := by
        rw [hfd_cast]
        calc
          ((d : ℝ) + ((n / d : ℕ) : ℝ) - 2 * s) * (d : ℝ)
              = (d : ℝ) ^ 2 + (d : ℝ) * ((n / d : ℕ) : ℝ) - 2 * s * (d : ℝ) := by ring
          _ = (d : ℝ) ^ 2 + s * s - 2 * s * (d : ℝ) := by rw [hm, hss]
          _ = ((d : ℝ) - s) ^ 2 := by ring
      have hsq_nonneg : 0 ≤ ((d : ℝ) - s) ^ 2 := sq_nonneg _
      have hy_lo : 2 * s ≤ (f d : ℝ) := by nlinarith only [h_id, hsq_nonneg, hdpos]
      have hdiff_le : (d : ℝ) - s ≤ C * q := by linarith only [hhi]
      have hdiff_nonneg : 0 ≤ (d : ℝ) - s := sub_nonneg.mpr hlo
      have hsq_le : ((d : ℝ) - s) ^ 2 ≤ C ^ 2 * s := by
        calc
          ((d : ℝ) - s) ^ 2 ≤ (C * q) ^ 2 := by nlinarith only [hdiff_nonneg, hdiff_le]
          _ = C ^ 2 * q ^ 2 := by ring
          _ = C ^ 2 * s := by rw [hq2]
      have h_upper_mul : ((f d : ℝ) - 2 * s) * (d : ℝ) ≤ C ^ 2 * (d : ℝ) := by
        have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
        nlinarith only [h_id, hsq_le, hlo, hC2]
      have hy_hi : (f d : ℝ) ≤ 2 * s + C ^ 2 := by nlinarith only [h_upper_mul, hdpos]
      exact ⟨hy_lo, hy_hi⟩
    have hT : T.Nonempty := hS.image f
    let a := T.min' hT
    let b := T.max' hT
    have ha_mem : a ∈ T := Finset.min'_mem T hT
    have hb_mem : b ∈ T := Finset.max'_mem T hT
    have hab : a ≤ b := Finset.min'_le T b hb_mem
    have hsub : T ⊆ Finset.Icc a b := by
      intro y hy
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le T y hy, Finset.le_max' T y hy⟩
    have hcard_le : S.card ≤ b + 1 - a := by
      rw [← Finset.card_image_of_injOn h_inj]
      calc
        T.card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
        _ = b + 1 - a := Nat.card_Icc a b
    have hcard_real : (S.card : ℝ) ≤ (b : ℝ) + 1 - (a : ℝ) := by
      have hle_cast : ((S.card : ℕ) : ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := Nat.cast_le.mpr hcard_le
      have hsub_cast : ((b + 1 - a : ℕ) : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        rfl
      linarith only [hle_cast, hsub_cast]
    have ha_lo : 2 * s ≤ (a : ℝ) := (h_bounds a ha_mem).1
    have hb_hi : (b : ℝ) ≤ 2 * s + C ^ 2 := (h_bounds b hb_mem).2
    linarith only [hcard_real, ha_lo, hb_hi]

/--
Erdős and Rosenfeld [ErRo97] proved that, for any constant `C > 0`, all large `n` have at most
`1 + C^2` many divisors in `[n^{1/2}, n^{1/2} + C n^{1/4}]`.
Matches `Erdos886.erdos_886.variants.rosenfeld_bound` definitionally.
-/
theorem erdos_886_rosenfeld_bound :
    ∀ C > 0, ∀ᶠ (n : ℕ) in atTop,
    ((divisors n).filter (fun (d : ℕ) =>
      (n : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 4 : ℝ))).card
      ≤ 1 + C ^ 2 := by
  intro C hC
  exact Filter.eventually_atTop.mpr ⟨1, fun n hn => rosenfeld_bound_of_pos hC hn⟩

/-! ### Part 2: Erdős–Rosenfeld Infinite Family (`4` divisors in `(n^{1/2}, n^{1/2} + 16 n^{1/4})`) -/

private def polyN (t : ℕ) : ℕ :=
  t * (t + 1) * (t + 2) * (t + 3) * (t + 4) * (t + 5) * (t + 6) * (t + 7)

private def polyD1 (t : ℕ) : ℕ := (t + 1) * (t + 2) * (t + 4) * (t + 7)
private def polyD2 (t : ℕ) : ℕ := (t + 1) * (t + 2) * (t + 5) * (t + 6)
private def polyD3 (t : ℕ) : ℕ := (t + 1) * (t + 3) * (t + 4) * (t + 6)
private def polyD4 (t : ℕ) : ℕ := (t + 2) * (t + 3) * (t + 4) * (t + 5)
private def polyE1 (t : ℕ) : ℕ := t * (t + 3) * (t + 5) * (t + 6)

private lemma polyN_strictMono : StrictMono polyN := by
  intro a b hab
  unfold polyN
  gcongr

private lemma polyN_pos (k : ℕ) : 0 < polyN (k + 25) := by
  unfold polyN
  positivity

private lemma polyD_dvd_polyN (t : ℕ) :
    polyD1 t ∣ polyN t ∧ polyD2 t ∣ polyN t ∧ polyD3 t ∣ polyN t ∧ polyD4 t ∣ polyN t := by
  refine ⟨⟨polyE1 t, ?_⟩, ⟨t * (t + 3) * (t + 4) * (t + 7), ?_⟩,
    ⟨t * (t + 2) * (t + 5) * (t + 7), ?_⟩, ⟨t * (t + 1) * (t + 6) * (t + 7), ?_⟩⟩
  all_goals
    dsimp only [polyN, polyD1, polyD2, polyD3, polyD4, polyE1]
    ring

private lemma polyD_chain_lt (t : ℕ) :
    polyD1 t < polyD2 t ∧ polyD2 t < polyD3 t ∧ polyD3 t < polyD4 t := by
  have h12 : polyD1 t + (2 * t ^ 2 + 6 * t + 4) = polyD2 t := by
    unfold polyD1 polyD2
    ring
  have h23 : polyD2 t + (2 * t ^ 2 + 14 * t + 12) = polyD3 t := by
    unfold polyD2 polyD3
    ring
  have h34 : polyD3 t + (4 * t ^ 2 + 28 * t + 48) = polyD4 t := by
    unfold polyD3 polyD4
    ring
  omega

private lemma polyN_lt_polyD1_sq (k : ℕ) :
    polyN (k + 25) < polyD1 (k + 25) * polyD1 (k + 25) := by
  let t := k + 25
  have hmul : polyN t = polyD1 t * polyE1 t := by
    unfold polyN polyD1 polyE1
    ring
  have hlt : polyE1 t < polyD1 t := by
    have hdiff : polyE1 t + (16 * t + 56) = polyD1 t := by
      unfold polyE1 polyD1
      ring
    omega
  have hdpos : 0 < polyD1 t := by
    unfold polyD1
    positivity
  rw [hmul]
  exact Nat.mul_lt_mul_of_pos_left hlt hdpos

private lemma base_sq_lt_polyN (k : ℕ) :
    let t := k + 25
    let B := t ^ 4 + 14 * t ^ 3 + 63 * t ^ 2
    B * B < polyN t := by
  intro t B
  have hBpos : 0 < B := by positivity
  have hltE : B < polyE1 t := by
    have hdiff : B + 90 * t = polyE1 t := by
      dsimp [B]
      unfold polyE1
      ring
    have htpos : 0 < t := by omega
    omega
  have hltD : B < polyD1 t :=
    hltE.trans (by
      have hdiff : polyE1 t + (16 * t + 56) = polyD1 t := by
        unfold polyE1 polyD1
        ring
      omega)
  have hmul : polyN t = polyD1 t * polyE1 t := by
    unfold polyN polyD1 polyE1
    ring
  calc
    B * B < B * polyE1 t := Nat.mul_lt_mul_of_pos_left hltE hBpos
    _ < polyD1 t * polyE1 t := Nat.mul_lt_mul_of_pos_right hltD (hltE.trans' hBpos)
    _ = polyN t := hmul.symm

private lemma t_pow_8_lt_polyN (k : ℕ) :
    (k + 25) ^ 8 < polyN (k + 25) := by
  have hdiff : polyN (k + 25) = (k + 25) ^ 8 + (28 * (k + 25) ^ 7 + 322 * (k + 25) ^ 6 +
      1960 * (k + 25) ^ 5 + 6769 * (k + 25) ^ 4 + 13132 * (k + 25) ^ 3 +
      13068 * (k + 25) ^ 2 + 5040 * (k + 25)) := by
    unfold polyN
    ring
  have hgap : 0 < 28 * (k + 25) ^ 7 := by positivity
  omega

private lemma polyD4_lt_B_add_16_sq (k : ℕ) :
    let t := k + 25
    let B := t ^ 4 + 14 * t ^ 3 + 63 * t ^ 2
    polyD4 t < B + 16 * t ^ 2 := by
  intro t B
  have hgap : polyD4 t + (8 * k ^ 2 + 246 * k + 1030) = B + 16 * t ^ 2 := by
    dsimp [B, t]
    unfold polyD4
    ring
  omega

private lemma polyN_card_ge_four (k : ℕ) :
    4 ≤ (Erdos886Divisors (polyN (k + 25)) (1 / 4) 16).card := by
  let t := k + 25
  let n := polyN t
  let B := t ^ 4 + 14 * t ^ 3 + 63 * t ^ 2
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hne : n ≠ 0 := (polyN_pos k).ne'
  obtain ⟨hd1, hd2, hd3, hd4⟩ := polyD_dvd_polyN t
  obtain ⟨h12, h23, h34⟩ := polyD_chain_lt t
  have hsqrt_lt_D1 : (n : ℝ) ^ (1 / 2 : ℝ) < (polyD1 t : ℝ) := by
    have hlt : (n : ℝ) < (polyD1 t : ℝ) ^ 2 := by
      have : n < polyD1 t * polyD1 t := polyN_lt_polyD1_sq k
      exact_mod_cast (by simpa [sq] using this)
    have h1 : (n : ℝ) ^ (1 / 2 : ℝ) < ((polyD1 t : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_lt_rpow hn0 hlt (by norm_num)
    rw [← Real.rpow_natCast (polyD1 t : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg _)] at h1
    norm_num at h1
    exact h1
  have hB_lt_sqrt : (B : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := by
    have hlt : (B : ℝ) ^ 2 < (n : ℝ) := by
      have : B * B < n := base_sq_lt_polyN k
      exact_mod_cast (by simpa [sq] using this)
    have hres := lt_rpow_of_pow_lt (k := 2) (by decide) (Nat.cast_nonneg B) hlt
    simpa using hres
  have ht2_lt_q : ((t : ℝ) ^ 2) < (n : ℝ) ^ (1 / 4 : ℝ) := by
    have hlt : ((t : ℝ) ^ 2) ^ 4 < (n : ℝ) := by
      have : t ^ 8 < n := t_pow_8_lt_polyN k
      exact_mod_cast (by simpa [← pow_mul] using this)
    have hres := lt_rpow_of_pow_lt (k := 4) (by decide) (sq_nonneg (t : ℝ)) hlt
    simpa using hres
  have hD4_lt_ub : (polyD4 t : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + 16 * (n : ℝ) ^ (1 / 2 - 1 / 4 : ℝ) := by
    have hB_ub : (polyD4 t : ℝ) < (B : ℝ) + 16 * (t : ℝ) ^ 2 := by
      exact_mod_cast polyD4_lt_B_add_16_sq k
    have hexp : (1 / 2 - 1 / 4 : ℝ) = 1 / 4 := by norm_num
    rw [hexp]
    linarith only [hB_ub, hB_lt_sqrt, ht2_lt_q]
  have mem_interval : ∀ d : ℕ, d ∣ n → polyD1 t ≤ d → d ≤ polyD4 t →
      d ∈ Erdos886Divisors n (1 / 4) 16 := by
    intro d hdvd hlo hhi
    unfold Erdos886Divisors
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hne⟩, ?_, ?_⟩
    · exact lt_of_lt_of_le hsqrt_lt_D1 (Nat.cast_le.mpr hlo)
    · exact lt_of_le_of_lt (Nat.cast_le.mpr hhi) hD4_lt_ub
  have hmem1 : polyD1 t ∈ Erdos886Divisors n (1 / 4) 16 :=
    mem_interval (polyD1 t) hd1 le_rfl (h12.le.trans (h23.le.trans h34.le))
  have hmem2 : polyD2 t ∈ Erdos886Divisors n (1 / 4) 16 :=
    mem_interval (polyD2 t) hd2 h12.le (h23.le.trans h34.le)
  have hmem3 : polyD3 t ∈ Erdos886Divisors n (1 / 4) 16 :=
    mem_interval (polyD3 t) hd3 (h12.le.trans h23.le) h34.le
  have hmem4 : polyD4 t ∈ Erdos886Divisors n (1 / 4) 16 :=
    mem_interval (polyD4 t) hd4 (h12.le.trans (h23.le.trans h34.le)) le_rfl
  let Q : Finset ℕ := {polyD1 t, polyD2 t, polyD3 t, polyD4 t}
  have hQ_sub : Q ⊆ Erdos886Divisors n (1 / 4) 16 := by
    intro x hx
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hQ_card : Q.card = 4 := by
    dsimp [Q]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  calc
    4 = Q.card := hQ_card.symm
    _ ≤ (Erdos886Divisors n (1 / 4) 16).card := Finset.card_le_card hQ_sub

/--
Erdős and Rosenfeld [ErRo97] proved that there are infinitely many `n` such that there are
four divisors of `n` in `(n^{1/2}, n^{1/2} + 16 n^{1/4})`.
Matches `Erdos886.erdos_886.variants.rosenfeld_infinite` definitionally.
-/
theorem erdos_886_rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1/4) 16).card} := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => polyN (k + 25))
  · intro a b hab
    have hlt := polyN_strictMono.injective hab
    omega
  · intro k
    exact polyN_card_ge_four k

end Contribution.Erdos886
