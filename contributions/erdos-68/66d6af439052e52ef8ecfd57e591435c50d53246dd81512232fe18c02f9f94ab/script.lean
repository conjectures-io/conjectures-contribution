import Mathlib

/-!
# A factorial-residue criterion for Erdős 68

The target series has factorially small positive tails. These lemmas isolate
the remaining arithmetic obligation: factorial-scaled partial sums must enter
the positive half of a unit interval arbitrarily late (possibly after one fixed
natural scaling). Under that hypothesis, a rational denominator is absorbed by
a sufficiently large factorial and an integer is forced strictly between two
consecutive integers.
-/

namespace Contribution.Erdos68

/-- If factorial-scaled tails lie strictly between `0` and `1/2`, while the
factorial-scaled partial sums enter the positive half of a unit interval
arbitrarily late, then the limit is irrational. -/
theorem irrational_of_factorial_positive_side
    (x : ℝ) (s : ℕ → ℝ)
    (htail : ∀ n ≥ 4,
      0 < (n.factorial : ℝ) * (x - s n) ∧
        (n.factorial : ℝ) * (x - s n) < (1 / 2 : ℝ))
    (hpos : ∀ B, ∃ n ≥ max B 4, ∃ z : ℤ,
      (z : ℝ) ≤ (n.factorial : ℝ) * s n ∧
        (n.factorial : ℝ) * s n < (z : ℝ) + (1 / 2 : ℝ)) :
    Irrational x := by
  rw [irrational_iff_ne_rational]
  intro a b hb hxab
  obtain ⟨n, hn, z, hzlo, hzhi⟩ := hpos b.natAbs
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hbnat : b.natAbs ∣ n.factorial :=
    Nat.dvd_factorial (Int.natAbs_pos.mpr hb) (le_trans (le_max_left _ _) hn)
  have hbint : b ∣ (n.factorial : ℤ) := Int.dvd_natCast.mpr hbnat
  obtain ⟨c, hc⟩ := hbint
  let w : ℤ := c * a
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hfactorial : (n.factorial : ℝ) = (b : ℝ) * (c : ℝ) := by
    exact_mod_cast hc
  have hscale : (n.factorial : ℝ) * x = (w : ℝ) := by
    rw [hxab, hfactorial]
    dsimp [w]
    field_simp
    norm_cast
  rcases htail n hn4 with ⟨htpos, htlt⟩
  have htail_eq :
      (n.factorial : ℝ) * (x - s n) =
        (w : ℝ) - (n.factorial : ℝ) * s n := by
    rw [mul_sub, hscale]
  have hsltw : (n.factorial : ℝ) * s n < (w : ℝ) := by
    rw [htail_eq] at htpos
    linarith
  have hwlt : (w : ℝ) < (n.factorial : ℝ) * s n + (1 / 2 : ℝ) := by
    rw [htail_eq] at htlt
    linarith
  have hzwR : (z : ℝ) < (w : ℝ) := lt_of_le_of_lt hzlo hsltw
  have hwzR : (w : ℝ) < ((z + 1 : ℤ) : ℝ) := by
    push_cast
    linarith
  have hzw : z < w := by exact_mod_cast hzwR
  have hwz : w < z + 1 := by exact_mod_cast hwzR
  omega

/-- The same criterion after one fixed natural scaling. This is useful when
the arithmetic recurrence only controls a fixed dyadic shift of the residues. -/
theorem irrational_of_scaled_factorial_positive_side
    (x : ℝ) (s : ℕ → ℝ) (m : ℕ)
    (htail : ∀ n ≥ 4,
      0 < (m : ℝ) * (n.factorial : ℝ) * (x - s n) ∧
        (m : ℝ) * (n.factorial : ℝ) * (x - s n) < (1 / 2 : ℝ))
    (hpos : ∀ B, ∃ n ≥ max B 4, ∃ z : ℤ,
      (z : ℝ) ≤ (m : ℝ) * (n.factorial : ℝ) * s n ∧
        (m : ℝ) * (n.factorial : ℝ) * s n <
          (z : ℝ) + (1 / 2 : ℝ)) :
    Irrational x := by
  have hscaled : Irrational ((m : ℝ) * x) := by
    apply irrational_of_factorial_positive_side
        ((m : ℝ) * x) (fun n ↦ (m : ℝ) * s n)
    · intro n hn
      rcases htail n hn with ⟨hlo, hhi⟩
      constructor
      · convert hlo using 1 <;> ring
      · convert hhi using 1 <;> ring
    · intro B
      obtain ⟨n, hn, z, hzlo, hzhi⟩ := hpos B
      refine ⟨n, hn, z, ?_, ?_⟩
      · convert hzlo using 1 <;> ring
      · convert hzhi using 1 <;> ring
  rw [irrational_iff_ne_rational] at hscaled ⊢
  intro a b hb hxab
  apply hscaled ((m : ℤ) * a) b hb
  rw [hxab, div_eq_mul_inv, div_eq_mul_inv]
  push_cast
  ring

end Contribution.Erdos68
