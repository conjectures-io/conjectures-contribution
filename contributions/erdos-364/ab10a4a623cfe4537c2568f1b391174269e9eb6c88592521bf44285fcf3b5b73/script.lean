import Mathlib
import FormalConjectures.ErdosProblems.«364»

/-!
# Erdős 364, part II: the Diophantine reformulation and the abc connection
-/

namespace Contribution.Erdos364Diophantine

open Nat Finset

/-- A product of two nonzero powerful numbers is powerful (no coprimality needed). -/
theorem Powerful.mul {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : Nat.Powerful a) (hb : Nat.Powerful b) : Nat.Powerful (a * b) := by
  intro p hp
  rw [Nat.primeFactors_mul ha0 hb0, Finset.mem_union] at hp
  rcases hp with h | h
  · exact Dvd.dvd.mul_right (ha p h) b
  · exact Dvd.dvd.mul_left (hb p h) a

/-- **Reformulation.** If `n, n+1, n+2` are powerful with `n ≠ 0`, then with `m = n+1`
the number `m^2 - 1` is powerful.  Since `m^2` is a square (hence powerful),
`(m^2 - 1, m^2)` is a pair of *consecutive* powerful numbers. -/
theorem sq_sub_one_powerful {n : ℕ} (hn : n ≠ 0)
    (h0 : Nat.Powerful n) (h2 : Nat.Powerful (n + 2)) :
    Nat.Powerful ((n + 1) ^ 2 - 1) := by
  have hEq : (n + 1) ^ 2 - 1 = n * (n + 2) := by ring_nf; omega
  rw [hEq]
  exact Powerful.mul hn (by omega) h0 h2

/-- Squares are powerful. -/
theorem powerful_sq (k : ℕ) : Nat.Powerful (k ^ 2) := by
  intro p hp
  have hk : k ≠ 0 := by rintro rfl; simp at hp
  exact pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors
    (by simpa [Nat.primeFactors_pow _ (two_ne_zero)] using hp)) 2

/-!
## The near-miss family

`(25, 27)` and `(70225, 70227)` are pairs of **odd powerful numbers differing by 2**.
They come from the Pell equation `x^2 - 27 y^2 = -2`:
`5^2 - 27·1^2 = -2` and `265^2 - 27·51^2 = -2`, with recursion
`(x,y) ↦ (26x + 135y, 5x + 26y)` from the fundamental unit `26^2 - 27·5^2 = 1`.
So the "two out of three" condition already has infinitely many solutions;
the middle term is what fails.
-/

/-- Any prime power `p ^ k` with `k ≥ 2` is powerful. -/
theorem powerful_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : Nat.Powerful (p ^ k) := by
  intro q hq
  rw [Nat.primeFactors_pow _ (by omega), hp.primeFactors, Finset.mem_singleton] at hq
  subst hq
  exact pow_dvd_pow _ hk

/-- A prime dividing `n` but whose square does not is an obstruction to powerfulness. -/
theorem not_powerful_of_mod_four {n : ℕ} (h : n % 4 = 2) : ¬ Nat.Powerful n := by
  intro hpow
  have h2 : (2:ℕ) ^ 2 ∣ n := hpow 2 (Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, by omega, by omega⟩)
  have : (4:ℕ) ∣ n := by simpa using h2
  omega

/-- The first near-miss: `25 = 5^2` and `27 = 3^3` are powerful, `26 = 2·13` is not. -/
theorem near_miss_25 :
    Nat.Powerful 25 ∧ Nat.Powerful 27 ∧ ¬ Nat.Powerful 26 :=
  ⟨by simpa using powerful_sq 5,
   by simpa using powerful_prime_pow Nat.prime_three (by norm_num : (2:ℕ) ≤ 3),
   not_powerful_of_mod_four (by norm_num)⟩

/-- The next Pell solution: `70225 = 265^2` and `70227 = 3^5 · 17^2` are powerful,
but `70226 ≡ 2 (mod 4)` is not. -/
theorem near_miss_70225 :
    Nat.Powerful 70225 ∧ Nat.Powerful 70227 ∧ ¬ Nat.Powerful 70226 := by
  refine ⟨by simpa using powerful_sq 265, ?_, not_powerful_of_mod_four (by norm_num)⟩
  have h : (70227 : ℕ) = 3 ^ 5 * 17 ^ 2 := by norm_num
  rw [h]
  exact Powerful.mul (by norm_num) (by norm_num)
    (powerful_prime_pow Nat.prime_three (by norm_num : (2:ℕ) ≤ 5))
    (powerful_prime_pow (by norm_num) (le_refl 2))

end Contribution.Erdos364Diophantine

