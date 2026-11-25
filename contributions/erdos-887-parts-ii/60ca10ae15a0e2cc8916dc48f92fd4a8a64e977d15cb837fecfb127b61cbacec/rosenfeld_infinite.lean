import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem 887: Erdős–Rosenfeld Infinite 4-Divisor Family

Self-contained Lean 4 proof of `[research solved]` variant `Erdos887.erdos_887.variants.rosenfeld_infinite`
from [ErRo97] (Erdős & Rosenfeld 1997), showing there exists `C > 0` (explicitly `C = 16`) such that
infinitely many natural numbers `n` have at least `4` divisors in `(√n, √n + C * n ^ (1 / 4))`.

Witnessed by `polyN (k + 25) = ∏ i ∈ [0, 7], (k + 25 + i)` and its four explicit degree-4
balanced divisors `polyD1 < polyD2 < polyD3 < polyD4`.
-/

namespace Contribution.Erdos887

open Filter Finset Real

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

private lemma lt_rpow_of_pow_lt {x y : ℝ} {k : ℕ} (hk : k ≠ 0) (hx : 0 ≤ x)
    (hlt : x ^ k < y) : x < y ^ (1 / (k : ℝ)) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h1kpos : (0 : ℝ) < 1 / (k : ℝ) := one_div_pos.mpr hkpos
  have hpow : (x ^ k) ^ (1 / (k : ℝ)) < y ^ (1 / (k : ℝ)) :=
    Real.rpow_lt_rpow (pow_nonneg hx k) hlt h1kpos
  rwa [← Real.rpow_natCast x k, ← Real.rpow_mul hx, mul_one_div_cancel hkpos.ne',
    Real.rpow_one] at hpow

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
    4 ≤ #{ d ∈ Ioo ⌊√(polyN (k + 25))⌋₊ ⌈√(polyN (k + 25)) + 16 * (polyN (k + 25))^((1 : ℝ) / 4)⌉₊ |
      d ∣ polyN (k + 25) } := by
  let t := k + 25
  let n := polyN t
  let B := t ^ 4 + 14 * t ^ 3 + 63 * t ^ 2
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  obtain ⟨hd1, hd2, hd3, hd4⟩ := polyD_dvd_polyN t
  obtain ⟨h12, h23, h34⟩ := polyD_chain_lt t
  have hsqrt_lt_D1 : √(n : ℝ) < (polyD1 t : ℝ) := by
    have hlt : (n : ℝ) < (polyD1 t : ℝ) ^ 2 := by
      have : n < polyD1 t * polyD1 t := polyN_lt_polyD1_sq k
      exact_mod_cast (by simpa [sq] using this)
    have h1 : √(n : ℝ) < √((polyD1 t : ℝ) ^ 2) := Real.sqrt_lt_sqrt hn0 hlt
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at h1
  have hfloor_lt_D1 : ⌊√(n : ℝ)⌋₊ < polyD1 t := by
    have hle : (⌊√(n : ℝ)⌋₊ : ℝ) ≤ √(n : ℝ) := Nat.floor_le (Real.sqrt_nonneg _)
    exact Nat.cast_lt.mp (lt_of_le_of_lt hle hsqrt_lt_D1)
  have hB_lt_sqrt : (B : ℝ) < √(n : ℝ) := by
    have hlt : (B : ℝ) ^ 2 < (n : ℝ) := by
      have : B * B < n := base_sq_lt_polyN k
      exact_mod_cast (by simpa [sq] using this)
    have hres := Real.sqrt_lt_sqrt (sq_nonneg _) hlt
    rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at hres
  have ht2_lt_q : ((t : ℝ) ^ 2) < (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hlt : ((t : ℝ) ^ 2) ^ 4 < (n : ℝ) := by
      have : t ^ 8 < n := t_pow_8_lt_polyN k
      exact_mod_cast (by simpa [← pow_mul] using this)
    have hres := lt_rpow_of_pow_lt (k := 4) (by decide) (sq_nonneg (t : ℝ)) hlt
    simpa using hres
  have hD4_lt_ub : (polyD4 t : ℝ) < √(n : ℝ) + 16 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hB_ub : (polyD4 t : ℝ) < (B : ℝ) + 16 * (t : ℝ) ^ 2 := by
      exact_mod_cast polyD4_lt_B_add_16_sq k
    linarith only [hB_ub, hB_lt_sqrt, ht2_lt_q]
  have hD4_lt_ceil : polyD4 t < ⌈√(n : ℝ) + 16 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ := by
    have hle : √(n : ℝ) + 16 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤
        (⌈√(n : ℝ) + 16 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ : ℝ) := Nat.le_ceil _
    exact Nat.cast_lt.mp (lt_of_lt_of_le hD4_lt_ub hle)
  let S := { d ∈ Ioo ⌊√(n : ℝ)⌋₊ ⌈√(n : ℝ) + 16 * (n : ℝ) ^ ((1 : ℝ) / 4)⌉₊ | d ∣ n }
  have mem_S : ∀ d : ℕ, d ∣ n → polyD1 t ≤ d → d ≤ polyD4 t → d ∈ S := by
    intro d hdvd hlo hhi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨lt_of_lt_of_le hfloor_lt_D1 hlo,
      lt_of_le_of_lt hhi hD4_lt_ceil⟩, hdvd⟩
  have hmem1 : polyD1 t ∈ S := mem_S (polyD1 t) hd1 le_rfl (h12.le.trans (h23.le.trans h34.le))
  have hmem2 : polyD2 t ∈ S := mem_S (polyD2 t) hd2 h12.le (h23.le.trans h34.le)
  have hmem3 : polyD3 t ∈ S := mem_S (polyD3 t) hd3 (h12.le.trans h23.le) h34.le
  have hmem4 : polyD4 t ∈ S := mem_S (polyD4 t) hd4 (h12.le.trans (h23.le.trans h34.le)) le_rfl
  let Q : Finset ℕ := {polyD1 t, polyD2 t, polyD3 t, polyD4 t}
  have hQ_sub : Q ⊆ S := by
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
    _ ≤ S.card := Finset.card_le_card hQ_sub

/--
Erdős and Rosenfeld proved that there exist `C > 0` and infinitely many `n` with at least `4`
divisors in `(√n, √n + C n^{1/4})`.
Matches `Erdos887.erdos_887.variants.rosenfeld_infinite` definitionally.
-/
theorem erdos_887_rosenfeld_infinite :
    ∃ C > (0 : ℝ),
      Infinite {n : ℕ | 4 ≤ #{ d ∈ Ioo ⌊√n⌋₊ ⌈√n + C * n^((1 : ℝ) / 4)⌉₊ | d ∣ n }} := by
  refine ⟨16, by norm_num, Set.infinite_coe_iff.mpr ?_⟩
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => polyN (k + 25))
  · intro a b hab
    have heq := polyN_strictMono.injective hab
    omega
  · intro k
    exact polyN_card_ge_four k

end Contribution.Erdos887
