import Mathlib
import FormalConjectures.ErdosProblems.«282»

/-!
Contribution: proof of `erdos_282.variants.fibonacci` from Erdős Problem 282.

Fibonacci–Sylvester: for `x ∈ (0, 1)` the greedy unit-fraction algorithm over
`A = Set.univ` terminates.  The key descent: with `n = sInf {n | 1/x ≤ n}` and
`r = x - 1/n`, minimality of `n` gives `(n - 1) < 1/x`, hence the unreduced
numerator `x.num * n - x.den` of `r` is `< x.num`; since the reduced numerator
divides the unreduced one and both are positive when `r > 0`, we get
`r.num < x.num`, and induction on the numerator finishes.
-/

open Filter Real Erdos282

namespace Contribution.Erdos282Fibonacci

/-- The greedy denominator for `x` over `A = Set.univ`. -/
noncomputable def N (x : ℚ) : ℕ :=
  sInf { n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ 1 / x ≤ (n : ℚ) }

lemma greedy_zero (A : Set ℕ) (x : ℚ) :
    greedyUnitFractionRem A x 0
      = x - 1 / (↑(sInf { n : ℕ | n ∈ A ∧ 1 / x ≤ (n : ℚ) }) : ℚ) := by
  rw [greedyUnitFractionRem]

lemma greedy_succ (A : Set ℕ) (x : ℚ) (t : ℕ) :
    greedyUnitFractionRem A x (t + 1)
      = if greedyUnitFractionRem A x t ≤ 0 then 0
        else greedyUnitFractionRem A x t
          - 1 / (↑(sInf { n : ℕ | n ∈ A ∧
              1 / greedyUnitFractionRem A x t ≤ (n : ℚ) }) : ℚ) := by
  rw [greedyUnitFractionRem]

lemma greedy_univ_zero (x : ℚ) :
    greedyUnitFractionRem Set.univ x 0 = x - 1 / (N x : ℚ) :=
  greedy_zero Set.univ x

/-- Once the remainder hits `0`, it stays `0`. -/
lemma greedy_eventually_zero (A : Set ℕ) (x : ℚ) (T : ℕ)
    (hT : greedyUnitFractionRem A x T = 0) :
    ∀ t, T ≤ t → greedyUnitFractionRem A x t = 0 := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hT
  | succ s hs ih => rw [greedy_succ, if_pos (le_of_eq ih)]

/-- If the first step lands on a positive value `y`, the tail of the algorithm
for `x` is the algorithm for `y`. -/
lemma greedy_shift (A : Set ℕ) (x y : ℚ)
    (hy : greedyUnitFractionRem A x 0 = y) (h0 : 0 < y) (t : ℕ) :
    greedyUnitFractionRem A x (t + 1) = greedyUnitFractionRem A y t := by
  induction t with
  | zero =>
    rw [greedy_succ, hy, if_neg (not_le.mpr h0), greedy_zero]
  | succ s ih =>
    rw [greedy_succ, ih, greedy_succ]

lemma N_spec (x : ℚ) : 1 / x ≤ (N x : ℚ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (1 / x)
  have h := Nat.sInf_mem (s := { n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ 1 / x ≤ (n : ℚ) })
    ⟨m, ⟨Set.mem_univ m, hm⟩⟩
  exact h.2

lemma N_min {x : ℚ} {k : ℕ} (hk : k < N x) : (k : ℚ) < 1 / x := by
  have h := Nat.notMem_of_lt_sInf
    (s := { n : ℕ | n ∈ (Set.univ : Set ℕ) ∧ 1 / x ≤ (n : ℚ) }) hk
  by_contra hcon
  push_neg at hcon
  exact h ⟨Set.mem_univ k, hcon⟩

lemma two_le_N {x : ℚ} (hx0 : 0 < x) (hx1 : x < 1) : 2 ≤ N x := by
  have hprod : x * (1 / x) = 1 := by
    rw [one_div]; exact mul_inv_cancel₀ (ne_of_gt hx0)
  have h1 : (1 : ℚ) < 1 / x := by nlinarith [hprod, hx0, hx1]
  have h2 : (1 : ℚ) < (N x : ℚ) := lt_of_lt_of_le h1 (N_spec x)
  have h3 : 1 < N x := by exact_mod_cast h2
  omega

/-- The reduced numerator after subtracting `1/n` is bounded by the unreduced one. -/
lemma num_bound {x : ℚ} {n : ℕ} (hn : (0 : ℚ) < (n : ℚ))
    (hpos : 0 < x - 1 / (n : ℚ)) :
    (x - 1 / (n : ℚ)).num ≤ x.num * n - x.den := by
  have hd : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.den_pos
  have hd0 : (x.den : ℚ) ≠ 0 := ne_of_gt hd
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt hn
  have hrep : x - 1 / (n : ℚ) = ((x.num : ℚ) * n - x.den) / ((x.den : ℚ) * n) := by
    conv_lhs => rw [← Rat.num_div_den x]
    rw [div_sub_div _ _ hd0 hn0, mul_one]
  have hn' : 0 < n := by exact_mod_cast hn
  have hb0 : ((x.den : ℤ) * (n : ℤ)) ≠ 0 := by
    have h1 : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
    have h2 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn'
    exact (mul_pos h1 h2).ne'
  have hdivInt : x - 1 / (n : ℚ)
      = Rat.divInt (x.num * n - x.den) ((x.den : ℤ) * n) := by
    rw [hrep, ← Rat.intCast_div_eq_divInt]
    push_cast
    ring
  have hdvd : (x - 1 / (n : ℚ)).num ∣ (x.num * n - x.den) := by
    rw [hdivInt]
    exact Rat.num_dvd _ hb0
  have hposQ : (0 : ℚ) < ((x.num : ℚ) * n - x.den) / ((x.den : ℚ) * n) := by
    rw [← hrep]; exact hpos
  have hBpos : (0 : ℚ) < (x.den : ℚ) * n := mul_pos hd hn
  have hcancel : ((x.num : ℚ) * n - x.den) / ((x.den : ℚ) * n) * ((x.den : ℚ) * n)
      = (x.num : ℚ) * n - x.den := div_mul_cancel₀ _ (ne_of_gt hBpos)
  have hAQ : (0 : ℚ) < (x.num : ℚ) * n - x.den := by
    nlinarith [hposQ, hBpos, hcancel]
  have hApos : (0 : ℤ) < x.num * n - x.den := by exact_mod_cast hAQ
  exact Int.le_of_dvd hApos hdvd

/-- Termination of the greedy algorithm over `Set.univ`, by strong descent on
the numerator. -/
lemma exists_terminal (p : ℕ) : ∀ x : ℚ, x.num.toNat ≤ p → x ∈ Set.Ioo (0 : ℚ) 1 →
    ∃ T : ℕ, greedyUnitFractionRem Set.univ x T = 0 := by
  induction p with
  | zero =>
    intro x hxp hx
    exfalso
    have h1 : 0 < x.num := Rat.num_pos.mpr hx.1
    omega
  | succ p ih =>
    intro x hxp hx
    obtain ⟨hx0, hx1⟩ := hx
    have h2N : 2 ≤ N x := two_le_N hx0 hx1
    have hNQ : (0 : ℚ) < (N x : ℚ) := by
      have h : 0 < N x := by omega
      exact_mod_cast h
    have hg0 : greedyUnitFractionRem Set.univ x 0 = x - 1 / (N x : ℚ) :=
      greedy_univ_zero x
    have hprod : x * (1 / x) = 1 := by
      rw [one_div]; exact mul_inv_cancel₀ (ne_of_gt hx0)
    have hprodN : (N x : ℚ) * (1 / (N x : ℚ)) = 1 := by
      rw [one_div]; exact mul_inv_cancel₀ (ne_of_gt hNQ)
    have hgeN : 1 ≤ (N x : ℚ) * x := by nlinarith [N_spec x, hprod, hx0]
    have hr_nonneg : 0 ≤ x - 1 / (N x : ℚ) := by nlinarith [hgeN, hprodN, hNQ]
    rcases eq_or_lt_of_le hr_nonneg with heq | hpos
    · exact ⟨0, by rw [hg0]; exact heq.symm⟩
    · -- strict descent on the numerator
      have hd : (0 : ℚ) < (x.den : ℚ) := by exact_mod_cast x.den_pos
      have hb1 : (x - 1 / (N x : ℚ)).num ≤ x.num * (N x) - x.den :=
        num_bound hNQ hpos
      have hmin : ((N x - 1 : ℕ) : ℚ) < 1 / x := N_min (by omega)
      have hcast : ((N x - 1 : ℕ) : ℚ) = (N x : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N x), Nat.cast_one]
      rw [hcast] at hmin
      have hstep : ((N x : ℚ) - 1) * x < 1 := by nlinarith [hmin, hprod, hx0]
      have hx_eq : (x.num : ℚ) = x * (x.den : ℚ) := by
        have h := Rat.num_div_den x
        have hd0 : (x.den : ℚ) ≠ 0 := ne_of_gt hd
        field_simp at h
        linarith [h]
      have hb2Q : (x.num : ℚ) * (N x : ℚ) - (x.den : ℚ) < (x.num : ℚ) := by
        rw [hx_eq]
        nlinarith [hstep, hd]
      have hb2 : x.num * (N x : ℤ) - (x.den : ℤ) < x.num := by exact_mod_cast hb2Q
      have hb3 : 0 < (x - 1 / (N x : ℚ)).num := Rat.num_pos.mpr hpos
      have hrx : (x - 1 / (N x : ℚ)).num < x.num := lt_of_le_of_lt hb1 hb2
      have hr_num : (x - 1 / (N x : ℚ)).num.toNat ≤ p := by omega
      have hr_lt1 : x - 1 / (N x : ℚ) < 1 := by
        have h1N : 0 < 1 / (N x : ℚ) := by positivity
        linarith [hx1]
      obtain ⟨T, hT⟩ := ih (x - 1 / (N x : ℚ)) hr_num ⟨hpos, hr_lt1⟩
      exact ⟨T + 1, by rw [greedy_shift Set.univ x _ hg0 hpos T]; exact hT⟩

/-- In 1202 Fibonacci observed that this process terminates for any $x$ when
$A=\mathbb{N}$. -/
theorem erdos_282.variants.fibonacci {x : ℚ} (hx : x ∈ Set.Ioo 0 1) :
    greedyUnitFractionRem .univ x =ᶠ[atTop] 0 := by
  obtain ⟨T, hT⟩ := exists_terminal x.num.toNat x le_rfl hx
  have hall := greedy_eventually_zero Set.univ x T hT
  have h : ∀ᶠ t in atTop, greedyUnitFractionRem Set.univ x t = (0 : ℕ → ℚ) t :=
    Filter.eventually_atTop.mpr ⟨T, fun t ht => by simpa using hall t ht⟩
  exact h

end Contribution.Erdos282Fibonacci
