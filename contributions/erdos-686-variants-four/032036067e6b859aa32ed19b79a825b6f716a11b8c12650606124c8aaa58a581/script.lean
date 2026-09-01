import FormalConjectures.ErdosProblems.«686»

/-!
# Erdős 686: the length-2 case is impossible, and the length-3 case is a cubic curve

Two reusable pieces for the counterexample side of `Erdos686.erdos_686.variants.four`
(can `4 = ∏(m+i)/∏(n+i)` for some `k ≥ 2`, `m ≥ n + k`?).
-/

namespace Contribution.Erdos686Window

/-- **Length 2 is impossible outright.** `(m+1)(m+2) = 4(n+1)(n+2)` has no solutions in `ℕ`,
with no `m ≥ n + 2` hypothesis needed: completing the square forces
`(4n+6)² − (2m+3)² = 3`, i.e. `a * b = 3` with `b = 4n + 2m + 9 ≥ 9`. -/
theorem no_ratio_four_of_len_two (n m : ℕ) :
    (m + 1) * (m + 2) ≠ 4 * ((n + 1) * (n + 2)) := by
  intro h
  have hz : ((m : ℤ) + 1) * ((m : ℤ) + 2) = 4 * (((n : ℤ) + 1) * ((n : ℤ) + 2)) := by
    exact_mod_cast h
  have hsq : (4 * (n : ℤ) + 6) ^ 2 - (2 * (m : ℤ) + 3) ^ 2 = 3 := by
    linear_combination (-4 : ℤ) * hz
  have hfact :
      ((4 * (n : ℤ) + 6) - (2 * (m : ℤ) + 3)) * ((4 * (n : ℤ) + 6) + (2 * (m : ℤ) + 3)) = 3 := by
    linear_combination hsq
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  have hb : (9 : ℤ) ≤ (4 * (n : ℤ) + 6) + (2 * (m : ℤ) + 3) := by linarith
  by_cases ha : (4 * (n : ℤ) + 6) - (2 * (m : ℤ) + 3) ≤ 0
  · nlinarith
  · push_neg at ha
    have ha1 : (0 : ℤ) + 1 ≤ (4 * (n : ℤ) + 6) - (2 * (m : ℤ) + 3) :=
      Int.lt_iff_add_one_le.mp ha
    nlinarith

/-- **Length 3 is exactly a cubic-curve problem.** Since `(x+1)(x+2)(x+3) = (x+2)³ − (x+2)`,
the window identity for `k = 3` holds iff `u³ − u = 4(v³ − v)` with `u = m+2`, `v = n+2`.
This turns the remaining `k = 3` obligation into an integral-point question on a
genus-one curve, which a later solver can attack with elliptic-curve machinery. -/
theorem len_three_iff_cubic (n m : ℕ) :
    (m + 1) * ((m + 2) * (m + 3)) = 4 * ((n + 1) * ((n + 2) * (n + 3))) ↔
      ((m : ℤ) + 2) ^ 3 - ((m : ℤ) + 2) = 4 * (((n : ℤ) + 2) ^ 3 - ((n : ℤ) + 2)) := by
  constructor
  · intro h
    have hz : ((m : ℤ) + 1) * (((m : ℤ) + 2) * ((m : ℤ) + 3))
        = 4 * (((n : ℤ) + 1) * (((n : ℤ) + 2) * ((n : ℤ) + 3))) := by exact_mod_cast h
    linear_combination hz
  · intro h
    have hz : ((m : ℤ) + 1) * (((m : ℤ) + 2) * ((m : ℤ) + 3))
        = 4 * (((n : ℤ) + 1) * (((n : ℤ) + 2) * ((n : ℤ) + 3))) := by linear_combination h
    exact_mod_cast hz

/-- The window-overlap solution `2·3·4 = 4·(1·2·3)`, i.e. the curve point `(u,v) = (3,2)`.
It satisfies the `k = 3` equation but has `m = 1 < n + 3 = 3`, so it is excluded by the
disjointness hypothesis — which is why no congruence argument can settle `k = 3`. -/
theorem len_three_overlap_solution :
    (1 + 1) * ((1 + 2) * (1 + 3)) = 4 * ((0 + 1) * ((0 + 2) * (0 + 3))) := by norm_num

end Contribution.Erdos686Window
