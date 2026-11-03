import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order

/- Partial exclusions for Erdős 686. These do NOT settle either bounty target.
   All products below start at n+1, as in the pinned target. -/
namespace Contribution.Erdos686TwentyFive

lemma square_gap_twenty_five (x y : ℤ) (hx : 3 ≤ x) (hy : 0 ≤ y) :
    y ^ 2 ≠ 25 * x ^ 2 - 24 := by
  intro h
  have hlt : y < 5*x := by
    by_contra hn
    have hge : 5*x ≤ y := by omega
    nlinarith [sq_nonneg (y - 5*x)]
  have hle : y ≤ 5*x-1 := by omega
  nlinarith [mul_nonneg (show 0 ≤ 5*x-1-y by omega) (show 0 ≤ 5*x-1+y by omega)]

theorem length_two_twenty_five (m n : ℕ) :
    (m+1)*(m+2) ≠ 25*((n+1)*(n+2)) := by
  intro h
  have hz : ((m:ℤ)+1)*(m+2) = 25*((n+1)*(n+2)) := by exact_mod_cast h
  apply square_gap_twenty_five (2*n+3) (2*m+3) (by omega) (by omega)
  nlinarith

theorem length_four_twenty_five (m n : ℕ) :
    (m+1)*(m+2)*(m+3)*(m+4) ≠ 25*((n+1)*(n+2)*(n+3)*(n+4)) := by
  intro h
  have hz : ((m:ℤ)+1)*(m+2)*(m+3)*(m+4) =
      25*((n+1)*(n+2)*(n+3)*(n+4)) := by exact_mod_cast h
  apply square_gap_twenty_five (n^2+5*n+5) (m^2+5*m+5) (by nlinarith) (by nlinarith)
  nlinarith

/-- Target-shaped length-two exclusion; no disjointness hypothesis is needed. -/
theorem no_ratio_twenty_five_two (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 2, (m + i)) /
      (∏ i ∈ Finset.Icc 1 2, (n + i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 25*((n+1)*(n+2)) = (m+1)*(m+2) := by exact_mod_cast hz
  exact length_two_twenty_five m n hn.symm

/-- Target-shaped length-four exclusion; no disjointness hypothesis is needed. -/
theorem no_ratio_twenty_five_four (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 4, (m + i)) /
      (∏ i ∈ Finset.Icc 1 4, (n + i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 25*((n+1)*(n+2)*(n+3)*(n+4)) = (m+1)*(m+2)*(m+3)*(m+4) := by exact_mod_cast hz
  exact length_four_twenty_five m n hn.symm
end Contribution.Erdos686TwentyFive
