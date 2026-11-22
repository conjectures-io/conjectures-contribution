import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Unified Even-Length Polynomial Square-Completion Theory for Erdős #686 (`N = 25`)

This file formalizes the general symmetric midpoint transformation and parameterized
polynomial square-completion / `d`-pinching machinery for even block lengths `k = 2 * r`
(`r ≥ 1`) in the equation

  `∏ i ∈ Finset.Icc 1 (2 * r), (m + i) = 25 * ∏ i ∈ Finset.Icc 1 (2 * r), (n + i)`
  `(m ≥ n + 2 * r)`.

## Main Results
* `midpoint_prod_general`: For all `r m : ℕ`, `2 ^ (2 * r) * ∏ i ∈ Icc 1 (2 * r), (m + i)`
  equals `P_even r (2 * m + 2 * r + 1)`, where `P_even r x = ∏ j ∈ Icc 1 r, (x^2 - (2j - 1)^2)`.
* `even_k_iff_P_even`: Reduction of the consecutive product equation to `P_even r u = 25 * P_even r v`.
* `P_even_pos`, `P_even_strictMono`: Positivity and strict monotonicity of `P_even r` for `x ≥ 2 * r`.
* `even_k_gap_pos`, `even_k_odd_parity_step`: Universal positivity `5 * Q v - Q u ≥ 1` and
  automatic upgrade to `5 * Q v - Q u ≥ 2` whenever `Q` preserves oddness.
* `even_k_square_completion_bound`: General Level-1 polynomial square-completion exclusion
  above any threshold `v0` where `10 * f_d * Q v + 24 * R v - f_d ^ 2 > 0`.
* `even_k_d_pinching_step`: General Level-2 `d`-pinching reduction narrowing all solutions
  with `5 * Q v - Q u ≥ D0` and bounding remaining `d < D0` into exact remainder windows.
* `even_k_finite_reduction` and a concrete instantiation (`k4_excluded_via_master`).
-/

namespace Contribution.Erdos686GeneralEvenKTwentyFive

open Finset

/-- Symmetric midpoint polynomial `P_{2r}(x) = ∏_{j=1}^r (x^2 - (2j - 1)^2)`. -/
def P_even (r : ℕ) (x : ℤ) : ℤ :=
  ∏ j ∈ Finset.Icc 1 r, (x ^ 2 - (2 * (j : ℤ) - 1) ^ 2)

/-- Product of the first `r` factors multiplied by `2^r` matches the negative-offset factors. -/
private lemma left_half_prod (r m : ℕ) :
    (2 : ℤ) ^ r * ∏ i ∈ Finset.Icc 1 r, ((m : ℤ) + i) =
      ∏ j ∈ Finset.Icc 1 r, ((2 * (m : ℤ) + 2 * (r : ℤ) + 1) - (2 * (j : ℤ) - 1)) := by
  have hpow : (2 : ℤ) ^ r = ∏ _i ∈ Finset.Icc 1 r, (2 : ℤ) := by
    simp [Finset.prod_const, Nat.card_Icc]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_bij (fun i _ => r + 1 - i) ?hi ?hinj ?hsurj ?heq
  · intro i hi
    rw [Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_Icc] at hi₁ hi₂
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨r + 1 - j, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have hle : i ≤ r + 1 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring

/-- Product of the upper `r` factors multiplied by `2^r` matches the positive-offset factors. -/
private lemma right_half_prod (r m : ℕ) :
    (2 : ℤ) ^ r * ∏ i ∈ Finset.Icc (r + 1) (2 * r), ((m : ℤ) + i) =
      ∏ j ∈ Finset.Icc 1 r, ((2 * (m : ℤ) + 2 * (r : ℤ) + 1) + (2 * (j : ℤ) - 1)) := by
  have hcard : (Finset.Icc (r + 1) (2 * r)).card = r := by
    simp only [Nat.card_Icc]
    omega
  have hpow : (2 : ℤ) ^ r = ∏ _i ∈ Finset.Icc (r + 1) (2 * r), (2 : ℤ) := by
    rw [Finset.prod_const, hcard]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_bij (fun i _ => i - r) ?hi ?hinj ?hsurj ?heq
  · intro i hi
    rw [Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_Icc] at hi₁ hi₂
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨j + r, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have hle : r ≤ i := by omega
    rw [Nat.cast_sub hle]
    ring

/-- **General Midpoint Identity**:
`2 ^ (2 * r) * ∏_{i=1}^{2r} (m + i) = P_even r (2 * m + 2 * r + 1)` for all `r, m : ℕ`. -/
theorem midpoint_prod_general (r m : ℕ) :
    (2 : ℤ) ^ (2 * r) * ∏ i ∈ Finset.Icc 1 (2 * r), ((m : ℤ) + i) =
      P_even r (2 * (m : ℤ) + 2 * (r : ℤ) + 1) := by
  have hsplit : Finset.Icc 1 (2 * r) = Finset.Icc 1 r ∪ Finset.Icc (r + 1) (2 * r) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) (2 * r)) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    rw [Finset.mem_Icc] at hx₁ hx₂
    omega
  rw [hsplit, Finset.prod_union hdisj]
  have hpow : (2 : ℤ) ^ (2 * r) = (2 : ℤ) ^ r * (2 : ℤ) ^ r := by
    rw [← pow_add, two_mul]
  rw [hpow, mul_mul_mul_comm, left_half_prod, right_half_prod, ← Finset.prod_mul_distrib]
  unfold P_even
  refine Finset.prod_congr rfl ?_
  intro j _
  ring

/-- Equivalence between the natural consecutive product equation of even length `2 * r`
and the symmetric polynomial equation `P_even r u = 25 * P_even r v`. -/
theorem even_k_iff_P_even (r m n : ℕ) :
    (∏ i ∈ Finset.Icc 1 (2 * r), (m + i) =
        25 * ∏ i ∈ Finset.Icc 1 (2 * r), (n + i)) ↔
      P_even r (2 * (m : ℤ) + 2 * (r : ℤ) + 1) =
        25 * P_even r (2 * (n : ℤ) + 2 * (r : ℤ) + 1) := by
  constructor
  · intro h
    have hz :
        (∏ i ∈ Finset.Icc 1 (2 * r), ((m : ℤ) + i)) =
          25 * ∏ i ∈ Finset.Icc 1 (2 * r), ((n : ℤ) + i) := by
      exact_mod_cast h
    have hm := midpoint_prod_general r m
    have hn := midpoint_prod_general r n
    calc
      P_even r (2 * (m : ℤ) + 2 * (r : ℤ) + 1)
          = (2 : ℤ) ^ (2 * r) * ∏ i ∈ Finset.Icc 1 (2 * r), ((m : ℤ) + i) := hm.symm
      _ = 25 * ((2 : ℤ) ^ (2 * r) * ∏ i ∈ Finset.Icc 1 (2 * r), ((n : ℤ) + i)) := by
          rw [hz]; ring
      _ = 25 * P_even r (2 * (n : ℤ) + 2 * (r : ℤ) + 1) := by rw [hn]
  · intro h
    have hm := midpoint_prod_general r m
    have hn := midpoint_prod_general r n
    have hmul :
        (2 : ℤ) ^ (2 * r) * ∏ i ∈ Finset.Icc 1 (2 * r), ((m : ℤ) + i) =
          (2 : ℤ) ^ (2 * r) * (25 * ∏ i ∈ Finset.Icc 1 (2 * r), ((n : ℤ) + i)) := by
      calc
        (2 : ℤ) ^ (2 * r) * ∏ i ∈ Finset.Icc 1 (2 * r), ((m : ℤ) + i)
            = P_even r (2 * (m : ℤ) + 2 * (r : ℤ) + 1) := hm
        _ = 25 * P_even r (2 * (n : ℤ) + 2 * (r : ℤ) + 1) := h
        _ = (2 : ℤ) ^ (2 * r) * (25 * ∏ i ∈ Finset.Icc 1 (2 * r), ((n : ℤ) + i)) := by
            rw [← hn]; ring
    have hpow_ne : (2 : ℤ) ^ (2 * r) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hz :
        (∏ i ∈ Finset.Icc 1 (2 * r), ((m : ℤ) + i)) =
          25 * ∏ i ∈ Finset.Icc 1 (2 * r), ((n : ℤ) + i) :=
      mul_left_cancel₀ hpow_ne hmul
    exact_mod_cast hz

/-- For `x ≥ 2 * r`, every factor of `P_even r x` is strictly positive, hence `0 < P_even r x`. -/
theorem P_even_pos {r : ℕ} {x : ℤ} (hx : 2 * (r : ℤ) ≤ x) : 0 < P_even r x := by
  unfold P_even
  refine Finset.prod_pos ?_
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hj_le : 2 * (j : ℤ) - 1 < x := by
    have : (j : ℤ) ≤ r := Int.ofNat_le.mpr hj.2
    linarith
  have hj_pos : 0 ≤ 2 * (j : ℤ) - 1 := by
    have : (1 : ℤ) ≤ j := Int.ofNat_le.mpr hj.1
    linarith
  nlinarith

/-- For `1 ≤ r` and `2 * r ≤ x < y`, `P_even r x < P_even r y`. -/
theorem P_even_strictMono {r : ℕ} (hr : 1 ≤ r) {x y : ℤ}
    (hx : 2 * (r : ℤ) ≤ x) (hxy : x < y) : P_even r x < P_even r y := by
  induction r, hr using Nat.le_induction with
  | base =>
    have h1 : Finset.Icc 1 1 = {1} := by decide
    simp only [P_even, h1, Finset.prod_singleton, Nat.cast_one]
    nlinarith
  | succ r hr ih =>
    have hsplit (z : ℤ) :
        P_even (r + 1) z = P_even r z * (z ^ 2 - (2 * ((r : ℤ) + 1) - 1) ^ 2) := by
      unfold P_even
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
      push_cast
      ring
    rw [hsplit x, hsplit y]
    have hx_r : 2 * (r : ℤ) ≤ x := by push_cast at hx; linarith
    have hP_pos : 0 < P_even r x := P_even_pos hx_r
    have hP_lt : P_even r x < P_even r y := ih hx_r
    have hfx_pos : 0 < x ^ 2 - (2 * ((r : ℤ) + 1) - 1) ^ 2 := by
      push_cast at hx
      have h_lin : 2 * ((r : ℤ) + 1) - 1 < x := by linarith
      have h_nonneg : 0 ≤ 2 * ((r : ℤ) + 1) - 1 := by
        have : (1 : ℤ) ≤ r := Int.ofNat_le.mpr hr
        linarith
      nlinarith
    have hfx_lt : x ^ 2 - (2 * ((r : ℤ) + 1) - 1) ^ 2 < y ^ 2 - (2 * ((r : ℤ) + 1) - 1) ^ 2 := by
      push_cast at hx
      nlinarith
    nlinarith

/-- **Gap Positivity**: From `S^2 * P_even r x = Q x ^ 2 + R x`, `0 < Q u`, `0 ≤ Q v`,
and `25 * R v < R u`, we always have `0 < 5 * Q v - Q u`. -/
theorem even_k_gap_pos {r : ℕ} {S : ℤ} {Q R : ℤ → ℤ} {u v : ℤ}
    (h_decomp : ∀ x, S ^ 2 * P_even r x = Q x ^ 2 + R x)
    (hQu : 0 < Q u) (hQv : 0 ≤ Q v)
    (heq : P_even r u = 25 * P_even r v)
    (hR_gap : 25 * R v < R u) :
    0 < 5 * Q v - Q u := by
  have h_id : (5 * Q v - Q u) * (5 * Q v + Q u) = R u - 25 * R v := by
    have hu := h_decomp u
    have hv := h_decomp v
    rw [heq] at hu
    linarith
  have hpos_rhs : 0 < R u - 25 * R v := by linarith
  have hpos_sum : 0 < 5 * Q v + Q u := by linarith
  nlinarith

/-- **Parity Step (Odd `r` / `k = 4s + 2` Upgrade)**:
When `Q` preserves oddness, any strictly positive difference `0 < 5 * Q v - Q u` between
odd inputs `u, v` is automatically at least `2`. -/
theorem even_k_odd_parity_step {Q : ℤ → ℤ} {u v : ℤ}
    (hQ_odd : ∀ z, z % 2 = 1 → Q z % 2 = 1)
    (hu_odd : u % 2 = 1) (hv_odd : v % 2 = 1)
    (hpos : 0 < 5 * Q v - Q u) :
    2 ≤ 5 * Q v - Q u := by
  have hQu := hQ_odd u hu_odd
  have hQv := hQ_odd v hv_odd
  omega

/-- **General Level-1 Polynomial Square-Completion Bound Theorem**:
Under `S^2 * P_even r x = Q x ^ 2 + R x`, once `1 ≤ f_d ≤ 5 * Q v - Q u`, `0 < Q u`,
`R u ≤ R v` (monotonicity of `-R`), and `10 * f_d * Q v + 24 * R v - f_d ^ 2 > 0`,
no solution `P_even r u = 25 * P_even r v` can exist. -/
theorem even_k_square_completion_bound {r : ℕ} {S : ℤ} {Q R : ℤ → ℤ} {f_d u v : ℤ}
    (h_decomp : ∀ x, S ^ 2 * P_even r x = Q x ^ 2 + R x)
    (hQu : 0 < Q u)
    (hR_anti : R u ≤ R v)
    (hgap : f_d ≤ 5 * Q v - Q u)
    (heq : P_even r u = 25 * P_even r v)
    (h_poly_pos : 0 < 10 * f_d * Q v + 24 * R v - f_d ^ 2) :
    False := by
  set d := 5 * Q v - Q u
  have h_id : d * (10 * Q v - d) = R u - 25 * R v := by
    have hu := h_decomp u
    have hv := h_decomp v
    rw [heq] at hu
    dsimp [d]
    linarith
  have h_mono : f_d * (10 * Q v - f_d) ≤ d * (10 * Q v - d) := by
    have hdiff : d * (10 * Q v - d) - f_d * (10 * Q v - f_d) =
        (d - f_d) * (Q u + (5 * Q v - f_d)) := by
      dsimp [d]
      ring
    have h1 : 0 ≤ d - f_d := by linarith
    have h2 : 0 ≤ Q u + (5 * Q v - f_d) := by
      have : f_d ≤ 5 * Q v - Q u := hgap
      linarith
    have hmul : 0 ≤ (d - f_d) * (Q u + (5 * Q v - f_d)) := mul_nonneg h1 h2
    linarith
  have h_upper : R u - 25 * R v ≤ -24 * R v := by linarith
  have h_quad : 10 * f_d * Q v - f_d ^ 2 = f_d * (10 * Q v - f_d) := by ring
  linarith

/-- **General Level-2 `d`-Pinching Theorem**:
Any solution `(u, v)` satisfies the exact pinching identity `10 * d * Q v - d ^ 2 = R u - 25 * R v`
with `d = 5 * Q v - Q u`. If `v` exceeds the `D0`-Level-2 threshold (`10 * D0 * Q v + 24 * R v - D0 ^ 2 > 0`),
any surviving solution MUST satisfy `f_d ≤ d < D0`, pinning `10 * d * Q v - d ^ 2` into the
remainder interval `[R_lo - 25 * R v, R_hi - 25 * R v]`. -/
theorem even_k_d_pinching_step {r : ℕ} {S : ℤ} {Q R : ℤ → ℤ} {f_d D0 u v : ℤ}
    (h_decomp : ∀ x, S ^ 2 * P_even r x = Q x ^ 2 + R x)
    (hQu : 0 < Q u)
    (hR_anti : R u ≤ R v)
    (hgap : f_d ≤ 5 * Q v - Q u)
    (heq : P_even r u = 25 * P_even r v)
    (hD0_pos : 0 < 10 * D0 * Q v + 24 * R v - D0 ^ 2) :
    ∃ d : ℤ,
      d = 5 * Q v - Q u ∧
      f_d ≤ d ∧
      d < D0 ∧
      10 * d * Q v - d ^ 2 = R u - 25 * R v := by
  refine ⟨5 * Q v - Q u, rfl, hgap, ?_, ?_⟩
  · by_contra hge
    push Not at hge
    exact even_k_square_completion_bound h_decomp hQu hR_anti hge heq hD0_pos
  · have hu := h_decomp u
    have hv := h_decomp v
    rw [heq] at hu
    linarith

/-- **Pinched Window Corollary**: If `R_lo ≤ R u ≤ R_hi`, the pinned `d` obeys
`R_lo - 25 * R v ≤ 10 * d * Q v - d ^ 2 ≤ R_hi - 25 * R v`. -/
theorem even_k_pinched_window {r : ℕ} {S : ℤ} {Q R : ℤ → ℤ} {u v R_lo R_hi : ℤ}
    (h_decomp : ∀ x, S ^ 2 * P_even r x = Q x ^ 2 + R x)
    (heq : P_even r u = 25 * P_even r v)
    (hlo : R_lo ≤ R u) (hhi : R u ≤ R_hi) :
    let d := 5 * Q v - Q u
    R_lo - 25 * R v ≤ 10 * d * Q v - d ^ 2 ∧ 10 * d * Q v - d ^ 2 ≤ R_hi - 25 * R v := by
  have hu := h_decomp u
  have hv := h_decomp v
  rw [heq] at hu
  have hid : 10 * (5 * Q v - Q u) * Q v - (5 * Q v - Q u) ^ 2 = R u - 25 * R v := by linarith
  dsimp
  constructor <;> linarith

/-- **Unified Finite-Reduction Master Theorem for Fixed Even `k = 2 * r`**:
Reduces the universal non-existence of solutions `(m, n)` with `m ≥ n + 2 * r` to:
1. A polynomial square-completion identity `S^2 * P_even r x = Q x ^ 2 + R x`,
2. Positivity/monotonicity above `2 * r + 1` and threshold `10 * f_d * Q v + 24 * R v - f_d^2 > 0`
   for `v ≥ 2 * N0 + 2 * r + 1`,
3. A finite check of the equation for `n < N0`. -/
theorem even_k_finite_reduction (r N0 : ℕ) {S f_d : ℤ} {Q R : ℤ → ℤ}
    (hr : 1 ≤ r)
    (h_decomp : ∀ x, S ^ 2 * P_even r x = Q x ^ 2 + R x)
    (hQ_pos : ∀ x, 2 * (r : ℤ) + 1 ≤ x → 0 < Q x)
    (hR_anti : ∀ x y, 2 * (r : ℤ) + 1 ≤ x → x < y → R y ≤ R x)
    (h_gap : ∀ u v, 2 * (r : ℤ) + 1 ≤ v → v < u → P_even r u = 25 * P_even r v →
      f_d ≤ 5 * Q v - Q u)
    (h_thresh : ∀ v, 2 * (N0 : ℤ) + 2 * (r : ℤ) + 1 ≤ v →
      0 < 10 * f_d * Q v + 24 * R v - f_d ^ 2)
    (h_finite : ∀ n < N0, ∀ m ≥ n + 2 * r,
      ∏ i ∈ Finset.Icc 1 (2 * r), (m + i) ≠
        25 * ∏ i ∈ Finset.Icc 1 (2 * r), (n + i)) :
    ¬ ∃ m n : ℕ, m ≥ n + 2 * r ∧
      ∏ i ∈ Finset.Icc 1 (2 * r), (m + i) =
        25 * ∏ i ∈ Finset.Icc 1 (2 * r), (n + i) := by
  rintro ⟨m, n, hmn, heq⟩
  by_cases hn : n < N0
  · exact h_finite n hn m hmn heq
  · have hn_ge : N0 ≤ n := Nat.le_of_not_lt hn
    have hP := (even_k_iff_P_even r m n).mp heq
    set u : ℤ := 2 * (m : ℤ) + 2 * (r : ℤ) + 1
    set v : ℤ := 2 * (n : ℤ) + 2 * (r : ℤ) + 1
    have hv_min : 2 * (r : ℤ) + 1 ≤ v := by dsimp [v]; omega
    have hvu : v < u := by
      dsimp [u, v]
      have : (n : ℤ) + 2 * (r : ℤ) ≤ m := by exact_mod_cast hmn
      have hr1 : (1 : ℤ) ≤ r := Int.ofNat_le.mpr hr
      linarith
    have hu_min : 2 * (r : ℤ) + 1 ≤ u := le_of_lt (lt_of_le_of_lt hv_min hvu)
    have hv0 : 2 * (N0 : ℤ) + 2 * (r : ℤ) + 1 ≤ v := by
      dsimp [v]
      have : (N0 : ℤ) ≤ n := Int.ofNat_le.mpr hn_ge
      linarith
    exact even_k_square_completion_bound h_decomp (hQ_pos u hu_min)
      (hR_anti v u hv_min hvu) (h_gap u v hv_min hvu hP) hP (h_thresh v hv0)

/-- **Instantiation Test (`k = 4`, `r = 2`)**:
Demonstrates `even_k_finite_reduction` directly on `k = 4` with `S = 1`,
`Q(x) = x^2 - 5`, `R(x) = -16`, `f_d = 1`, `N0 = 1`. -/
theorem k4_excluded_via_master :
    ¬ ∃ m n : ℕ, m ≥ n + 4 ∧
      ∏ i ∈ Finset.Icc 1 4, (m + i) = 25 * ∏ i ∈ Finset.Icc 1 4, (n + i) := by
  let Q : ℤ → ℤ := fun x => x ^ 2 - 5
  let R : ℤ → ℤ := fun _ => -16
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hdecomp : ∀ x, (1 : ℤ) ^ 2 * P_even 2 x = Q x ^ 2 + R x := by
    intro x
    dsimp [P_even, Q, R]
    simp only [hIcc2, Finset.prod_insert, Finset.mem_singleton, Finset.prod_singleton,
      OfNat.one_ne_ofNat, not_false_eq_true]
    norm_num
    ring
  refine even_k_finite_reduction 2 1 (S := 1) (f_d := 1) (Q := Q) (R := R)
    (by norm_num) hdecomp ?_ ?_ ?_ ?_ ?_
  · intro x hx
    norm_num at hx
    dsimp [Q]
    nlinarith
  · intro x y _ _
    dsimp [R]
    norm_num
  · intro u v hv hvu hP
    norm_num at hv
    have hu_pos : 0 < Q u := by dsimp [Q]; nlinarith
    have hv_nonneg : 0 ≤ Q v := by dsimp [Q]; nlinarith
    have hR_gap : 25 * R v < R u := by dsimp [R]; norm_num
    have hpos := even_k_gap_pos hdecomp hu_pos hv_nonneg hP hR_gap
    omega
  · intro v hv
    norm_num at hv
    dsimp [Q, R]
    nlinarith
  · intro n hn m hmn
    interval_cases n
    rw [hIcc4]
    intro heq
    have heq' : (m + 1) * (m + 2) * (m + 3) * (m + 4) = 600 := by
      have hlhs : ∏ x ∈ ({1, 2, 3, 4} : Finset ℕ), (m + x) =
          (m + 1) * (m + 2) * (m + 3) * (m + 4) := by
        simp; ring
      have hrhs : 25 * ∏ x ∈ ({1, 2, 3, 4} : Finset ℕ), (0 + x) = 600 := by decide
      linarith
    have hm_not_le : ¬ m ≤ 4 := by
      intro hmle
      interval_cases m; norm_num at heq'
    have hm5 : 5 ≤ m := by omega
    have hbig : 6 * 7 * 8 * 9 ≤ (m + 1) * (m + 2) * (m + 3) * (m + 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)) (by omega)
    omega

end Contribution.Erdos686GeneralEvenKTwentyFive
