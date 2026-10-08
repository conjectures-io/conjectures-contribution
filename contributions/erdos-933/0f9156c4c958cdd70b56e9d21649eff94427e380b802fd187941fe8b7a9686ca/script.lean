import Mathlib
import FormalConjectures.ErdosProblems.«933»

/-!
# Erdős 933: a valuation-free reduction to `limsup = ⊤`

`Erdos933.erdos_933` asks whether
`limsup_{n → ∞} 2^{k n} 3^{l n} / (n log n) = ⊤` (in `EReal`), where
`k n = v₂(n(n+1))` and `l n = v₃(n(n+1))`.

This file proves, with no number theory left implicit:

* `limsup_eq_top_of_frequently_ge`: if the real ratio exceeds every bound `C` for arbitrarily
  large `n`, then the `EReal` limsup in the statement is `⊤`;
* `pow_mul_pow_le_smooth`: any `2^a` and `3^b` dividing `n(n+1)` satisfy
  `2^a * 3^b ≤ 2^{k n} * 3^{l n}`;
* `limsup_eq_top_of_dvd`: it therefore suffices to find, for every `C` and `N`, some `n ≥ N`
  and exponents `a, b` with `2^a ∣ n(n+1)`, `3^b ∣ n(n+1)` and `C * (n log n) ≤ 2^a * 3^b`;
* `erdos_933_true_of_dvd`: the same criterion, stated in the `True ↔ …` shape that the
  formalized task asks for.

So a solver only has to produce the divisibility witnesses (for example `n = 2^a u` with
`3^b ∣ n + 1` and `3^b ≥ C u log n`); no `padicValNat`, `EReal` or `limsup` work remains.
-/

open Filter

namespace Contribution.Erdos933

/-- Unbounded-frequently implies that the `EReal` limsup of the ratio is `⊤`. -/
theorem limsup_eq_top_of_frequently_ge
    (h : ∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      C ≤ ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) :
    atTop.limsup (fun n : ℕ ↦
      ((((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) : EReal))
      = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  have hfreq : ∃ᶠ n in atTop, (((y + 1 : ℝ)) : EReal) ≤
      ((((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) : EReal) := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hC⟩ := h (y + 1) N
    exact ⟨n, hn, EReal.coe_le_coe_iff.mpr hC⟩
  have hle := Filter.le_limsup_of_frequently_le hfreq
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (by linarith)) hle

/-- Any powers of `2` and `3` dividing `n(n+1)` are bounded by the `{2,3}`-part `2^k 3^l`. -/
theorem pow_mul_pow_le_smooth {n a b : ℕ} (hn : 0 < n)
    (ha : 2 ^ a ∣ n * (n + 1)) (hb : 3 ^ b ∣ n * (n + 1)) :
    2 ^ a * 3 ^ b ≤ 2 ^ Erdos933.k n * 3 ^ Erdos933.l n := by
  have hne : n * (n + 1) ≠ 0 := by positivity
  have hka : a ≤ Erdos933.k n := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (padicValNat_dvd_iff_le hne).mp ha
  have hlb : b ≤ Erdos933.l n := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (padicValNat_dvd_iff_le hne).mp hb
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hka)
    (Nat.pow_le_pow_right (by norm_num) hlb)

/-- Valuation-free sufficient criterion: divisibility witnesses with
`C * (n log n) ≤ 2^a 3^b` for arbitrarily large `n` give the "frequently large" hypothesis. -/
theorem frequently_ge_of_dvd
    (h : ∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ a b : ℕ, 2 ^ a ∣ n * (n + 1) ∧ 3 ^ b ∣ n * (n + 1) ∧
      C * ((n : ℝ) * Real.log (n : ℝ)) ≤ (2 : ℝ) ^ a * (3 : ℝ) ^ b) :
    ∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N,
      C ≤ ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ)) := by
  intro C N
  obtain ⟨n, hn, a, b, ha, hb, hC⟩ := h C (max N 2)
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hden : 0 < (n : ℝ) * Real.log (n : ℝ) := mul_pos hnpos hlog
  have hS : ((2 ^ a * 3 ^ b : ℕ) : ℝ) ≤ ((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) := by
    exact_mod_cast pow_mul_pow_le_smooth (by omega) ha hb
  rw [le_div_iff₀ hden]
  calc C * ((n : ℝ) * Real.log (n : ℝ)) ≤ (2 : ℝ) ^ a * (3 : ℝ) ^ b := hC
    _ = ((2 ^ a * 3 ^ b : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := hS

/-- The valuation-free criterion gives the `EReal` limsup statement directly. -/
theorem limsup_eq_top_of_dvd
    (h : ∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ a b : ℕ, 2 ^ a ∣ n * (n + 1) ∧ 3 ^ b ∣ n * (n + 1) ∧
      C * ((n : ℝ) * Real.log (n : ℝ)) ≤ (2 : ℝ) ^ a * (3 : ℝ) ^ b) :
    atTop.limsup (fun n : ℕ ↦
      ((((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) : EReal))
      = ⊤ :=
  limsup_eq_top_of_frequently_ge (frequently_ge_of_dvd h)

/-- The same criterion in the `True ↔ …` shape of the formalized task
(the verifier instantiates the answer placeholder of `Erdos933.erdos_933` to `True`). -/
theorem erdos_933_true_of_dvd
    (h : ∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N, ∃ a b : ℕ, 2 ^ a ∣ n * (n + 1) ∧ 3 ^ b ∣ n * (n + 1) ∧
      C * ((n : ℝ) * Real.log (n : ℝ)) ≤ (2 : ℝ) ^ a * (3 : ℝ) ^ b) :
    True ↔ atTop.limsup (fun n : ℕ ↦
      ((((2 ^ Erdos933.k n * 3 ^ Erdos933.l n : ℕ) : ℝ) / ((n : ℝ) * Real.log (n : ℝ))) : EReal))
      = ⊤ :=
  ⟨fun _ => limsup_eq_top_of_dvd h, fun _ => trivial⟩

end Contribution.Erdos933
