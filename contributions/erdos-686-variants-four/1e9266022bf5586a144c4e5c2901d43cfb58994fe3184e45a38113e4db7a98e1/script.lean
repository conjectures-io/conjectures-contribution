import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Contribution.Erdos686Six

def block6 (n : ℕ) : ℕ := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)
def nearSquare (n : ℤ) : ℤ := 16*n^3+168*n^2+518*n+441
def remainder (n : ℤ) : ℤ := 756*n^2+5292*n+10161

lemma square_identity (n : ℕ) :
    nearSquare n ^ 2 - 256 * (block6 n : ℤ) = remainder n := by
  simp only [nearSquare, remainder, block6, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

lemma nearSquare_pos (n : ℕ) : 0 < nearSquare n := by
  dsimp [nearSquare]
  positivity

lemma remainder_pos (n : ℕ) : 0 < remainder n := by
  dsimp [remainder]
  positivity

lemma remainder_small (n : ℕ) (hn : 247 ≤ n) :
    2 * remainder n < nearSquare n := by
  have hz : (247 : ℤ) ≤ n := by exact_mod_cast hn
  dsimp [remainder, nearSquare]
  have h1 := mul_nonneg (show (0 : ℤ) ≤ n*n by positivity) (show (0 : ℤ) ≤ n-247 by omega)
  nlinarith [sq_nonneg ((n : ℤ)-247)]

/-- Every solution is in the finite lower-block range, even without disjointness. -/
theorem solution_lower_start_le_246 (n m : ℕ) (hmn : n ≤ m)
    (h : block6 m = 4 * block6 n) : n ≤ 246 := by
  by_contra hn
  have hn' : 247 ≤ n := by omega
  have hm' : 247 ≤ m := by omega
  have hidn := square_identity n
  have hidm := square_identity m
  have hz : (block6 m : ℤ) = 4 * (block6 n : ℤ) := by exact_mod_cast h
  have hp := nearSquare_pos m
  have hq := nearSquare_pos n
  have hr := remainder_pos m
  have hs := remainder_pos n
  have hsmallm := remainder_small m hm'
  have hsmalln := remainder_small n hn'
  have hid : nearSquare m ^ 2 - (2*nearSquare n)^2 = remainder m - 4*remainder n := by
    nlinarith only [hidn, hidm, hz]
  have heq : nearSquare m = 2*nearSquare n := by
    rcases lt_trichotomy (nearSquare m) (2*nearSquare n) with hlt | heq | hgt
    · have hdiff : nearSquare m + 1 ≤ 2*nearSquare n := by omega
      have hmul := mul_nonneg (show 0 ≤ 2*nearSquare n-nearSquare m-1 by omega)
        (show 0 ≤ 2*nearSquare n+nearSquare m by omega)
      nlinarith only [hid, hp, hq, hr, hs, hsmallm, hsmalln, hmul]
    · exact heq
    · have hmul := mul_nonneg (show 0 ≤ nearSquare m-2*nearSquare n-1 by omega)
        (show 0 ≤ nearSquare m+2*nearSquare n by omega)
      nlinarith only [hid, hp, hq, hr, hs, hsmallm, hsmalln, hmul]
  have hodd : nearSquare m % 2 = 1 := by simp [nearSquare, Int.add_emod, Int.mul_emod]
  omega


/-- Certificate: the last block whose product is at most four times the lower product. -/
def cut (n : Fin 247) : ℕ :=
  ([0, 2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 19, 21, 22, 23, 24, 26, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 46, 47, 48, 50, 51, 52, 53, 55, 56, 57, 58, 60, 61, 62, 63, 65, 66, 67, 68, 70, 71, 72, 73, 75, 76, 77, 79, 80, 81, 82, 84, 85, 86, 87, 89, 90, 91, 92, 94, 95, 96, 97, 99, 100, 101, 102, 104, 105, 106, 107, 109, 110, 111, 113, 114, 115, 116, 118, 119, 120, 121, 123, 124, 125, 126, 128, 129, 130, 131, 133, 134, 135, 136, 138, 139, 140, 142, 143, 144, 145, 147, 148, 149, 150, 152, 153, 154, 155, 157, 158, 159, 160, 162, 163, 164, 165, 167, 168, 169, 170, 172, 173, 174, 176, 177, 178, 179, 181, 182, 183, 184, 186, 187, 188, 189, 191, 192, 193, 194, 196, 197, 198, 199, 201, 202, 203, 205, 206, 207, 208, 210, 211, 212, 213, 215, 216, 217, 218, 220, 221, 222, 223, 225, 226, 227, 228, 230, 231, 232, 233, 235, 236, 237, 239, 240, 241, 242, 244, 245, 246, 247, 249, 250, 251, 252, 254, 255, 256, 257, 259, 260, 261, 262, 264, 265, 266, 268, 269, 270, 271, 273, 274, 275, 276, 278, 279, 280, 281, 283, 284, 285, 286, 288, 289, 290, 291, 293, 294, 295, 296, 298, 299, 300, 302, 303, 304, 305, 307, 308, 309, 310] : List ℕ).getD n 0

lemma finite_certificate (n : Fin 247) :
    block6 (cut n) ≤ 4 * block6 n ∧
    4 * block6 n < block6 (cut n + 1) ∧
    (block6 (cut n) = 4 * block6 n → (n : ℕ) = 1 ∧ cut n = 2) := by
  revert n
  decide +kernel

lemma block6_strictMono : StrictMono block6 := by
  intro a b hab
  dsimp [block6]
  gcongr

/-- The only equality in the bounded range is the overlapping pair n=1, m=2. -/
theorem finite_check (n m : ℕ) (hn : n ≤ 246)
    (h : block6 m = 4 * block6 n) : n = 1 ∧ m = 2 := by
  let i : Fin 247 := ⟨n, by omega⟩
  obtain ⟨hlo, hhi, heq⟩ := finite_certificate i
  have hmle : m ≤ cut i := by
    by_contra hnot
    have hmge : cut i + 1 ≤ m := by omega
    have hmono := block6_strictMono.monotone hmge
    change 4 * block6 n < block6 (cut i + 1) at hhi
    omega
  have hmge : cut i ≤ m := by
    by_contra hnot
    have hmlt : m < cut i := by omega
    have hmono := block6_strictMono hmlt
    change block6 (cut i) ≤ 4 * block6 n at hlo
    omega
  have hmc : m = cut i := by omega
  have hci : block6 (cut i) = 4 * block6 i := by simpa [i, ← hmc] using h
  have hi := heq hci
  exact ⟨hi.1, hmc.trans hi.2⟩

/-- Ratio four is impossible for disjoint blocks of six consecutive positive integers. -/
theorem no_ratio_four_of_len_six (n m : ℕ) (hmn : n + 6 ≤ m) :
    block6 m ≠ 4 * block6 n := by
  intro h
  have hn := solution_lower_start_le_246 n m (by omega) h
  obtain ⟨hn1, hm2⟩ := finite_check n m hn h
  omega

/-- Direct use at the rational-product obligation in the pinned target. -/
theorem no_ratio_four_six (m n : ℕ) (hmn : n + 6 ≤ m) :
    (4 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 6, (m + i)) /
      (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 4*block6 n = block6 m := by
    dsimp [block6]
    exact_mod_cast hz
  exact no_ratio_four_of_len_six n m hmn hn.symm

end Contribution.Erdos686Six
