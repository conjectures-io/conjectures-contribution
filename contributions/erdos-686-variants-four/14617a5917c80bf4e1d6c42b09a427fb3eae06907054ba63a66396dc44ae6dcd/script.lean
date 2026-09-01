import FormalConjectures.ErdosProblems.«686»

/-! Pell-style obstruction: the `k = 2` case of Erdős 686 has no solutions at all. -/

namespace Contribution.Erdos686PellObstruction

/-- No `m, n : ℕ` satisfy `(m+1)(m+2) = 4(n+1)(n+2)`: completing the square gives
`(4n+6)² − (2m+3)² = 3`, i.e. a factorisation `a·b = 3` with `b = 4n+2m+9 ≥ 9`,
which is impossible whether `a ≤ 0` or `a ≥ 1`. -/
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

end Contribution.Erdos686PellObstruction
