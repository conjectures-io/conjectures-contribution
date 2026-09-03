import FormalConjectures.ErdosProblems.«936»

/-!
# Residue obstructions for the `2 ^ n + 1` variant of Erdős 936

This contribution formalizes a reusable prime-square obstruction to powerfulness and
applies it to six explicit infinite residue classes of exponents.  The prime
`3` excludes `n ≡ 1, 5 (mod 6)`, while the prime `5` excludes
`n ≡ 2, 6, 14, 18 (mod 20)`.

These results are partial progress only: they do not prove that every
sufficiently large `2 ^ n + 1` is non-powerful.
-/

open Filter Nat

namespace Contribution.Erdos936AddResidues

/-- A prime divisor whose required power does not divide witnesses failure of fullness. -/
theorem not_full_of_prime_dvd_not_pow_dvd {m p k : ℕ} (hp : p.Prime)
    (hp_dvd : p ∣ m) (hp_pow_not_dvd : ¬ p ^ k ∣ m) : ¬ k.Full m := by
  have hm0 : m ≠ 0 := by
    intro hm
    subst m
    exact hp_pow_not_dvd (dvd_zero _)
  intro hm
  exact hp_pow_not_dvd (hm p (Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hm0⟩))

/-- Prime-square form of `not_full_of_prime_dvd_not_pow_dvd`. -/
theorem not_powerful_of_prime_dvd_not_sq_dvd {m p : ℕ} (hp : p.Prime)
    (hp_dvd : p ∣ m) (hp_sq_not_dvd : ¬ p ^ 2 ∣ m) : ¬ m.Powerful :=
  not_full_of_prime_dvd_not_pow_dvd hp hp_dvd hp_sq_not_dvd

/-- The residue class `n ≡ 1 (mod 6)` is excluded by the prime `3`. -/
theorem add_one_residue_one (k : ℕ) : ¬ (2 ^ (6 * k + 1) + 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 3) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The residue class `n ≡ 5 (mod 6)` is excluded by the prime `3`. -/
theorem add_one_residue_five (k : ℕ) : ¬ (2 ^ (6 * k + 5) + 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 3) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The residue class `n ≡ 2 (mod 20)` is excluded by the prime `5`. -/
theorem add_one_residue_two_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 2) + 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The residue class `n ≡ 6 (mod 20)` is excluded by the prime `5`. -/
theorem add_one_residue_six_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 6) + 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The residue class `n ≡ 14 (mod 20)` is excluded by the prime `5`. -/
theorem add_one_residue_fourteen_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 14) + 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The residue class `n ≡ 18 (mod 20)` is excluded by the prime `5`. -/
theorem add_one_residue_eighteen_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 18) + 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    simp [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  · rw [Nat.dvd_iff_mod_eq_zero]
    norm_num [pow_add, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- Both prime-`3` obstructions, stated directly in terms of `n % 6`. -/
theorem add_one_not_powerful_of_mod_six {n : ℕ} (hn : n % 6 = 1 ∨ n % 6 = 5) :
    ¬ (2 ^ n + 1).Powerful := by
  rcases hn with hn | hn
  · have heq : 6 * (n / 6) + 1 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 6)
    rw [← heq]
    exact add_one_residue_one (n / 6)
  · have heq : 6 * (n / 6) + 5 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 6)
    rw [← heq]
    exact add_one_residue_five (n / 6)

/-- All four prime-`5` obstructions, stated directly in terms of `n % 20`. -/
theorem add_one_not_powerful_of_mod_twenty {n : ℕ}
    (hn : n % 20 = 2 ∨ n % 20 = 6 ∨ n % 20 = 14 ∨ n % 20 = 18) :
    ¬ (2 ^ n + 1).Powerful := by
  rcases hn with hn | hn | hn | hn
  · have heq : 20 * (n / 20) + 2 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact add_one_residue_two_mod_twenty (n / 20)
  · have heq : 20 * (n / 20) + 6 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact add_one_residue_six_mod_twenty (n / 20)
  · have heq : 20 * (n / 20) + 14 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact add_one_residue_fourteen_mod_twenty (n / 20)
  · have heq : 20 * (n / 20) + 18 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact add_one_residue_eighteen_mod_twenty (n / 20)

/-- The exponents not yet eliminated by the prime-`3` and prime-`5` sieves. -/
def IsRemainingExponent (n : ℕ) : Prop :=
  n % 6 ≠ 1 ∧ n % 6 ≠ 5 ∧ n % 20 ≠ 2 ∧ n % 20 ≠ 6 ∧
    n % 20 ≠ 14 ∧ n % 20 ≠ 18

/-- A direct sieve restriction on any exponent producing a powerful value. -/
theorem powerful_add_one_residue_restrictions {n : ℕ} (h : (2 ^ n + 1).Powerful) :
    IsRemainingExponent n := by
  constructor
  · intro hn
    exact add_one_not_powerful_of_mod_six (Or.inl hn) h
  constructor
  · intro hn
    exact add_one_not_powerful_of_mod_six (Or.inr hn) h
  constructor
  · intro hn
    exact add_one_not_powerful_of_mod_twenty (Or.inl hn) h
  constructor
  · intro hn
    exact add_one_not_powerful_of_mod_twenty (Or.inr (Or.inl hn)) h
  constructor
  · intro hn
    exact add_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inl hn))) h
  · intro hn
    exact add_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inr hn))) h

/--
The original eventual-nonpowerfulness obligation is equivalent to proving it
only on the residue classes that survive the two elementary prime sieves.
-/
theorem eventually_not_powerful_iff_on_remaining :
    Erdos936.EventuallyNotPowerful (2 ^ · + 1) ↔
      ∀ᶠ n in atTop, IsRemainingExponent n → ¬ (2 ^ n + 1).Powerful := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    exact fun _ ↦ hn
  · intro h
    filter_upwards [h] with n hn
    by_cases h1 : n % 6 = 1
    · exact add_one_not_powerful_of_mod_six (Or.inl h1)
    by_cases h5 : n % 6 = 5
    · exact add_one_not_powerful_of_mod_six (Or.inr h5)
    by_cases h2 : n % 20 = 2
    · exact add_one_not_powerful_of_mod_twenty (Or.inl h2)
    by_cases h6 : n % 20 = 6
    · exact add_one_not_powerful_of_mod_twenty (Or.inr (Or.inl h6))
    by_cases h14 : n % 20 = 14
    · exact add_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inl h14)))
    by_cases h18 : n % 20 = 18
    · exact add_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inr h18)))
    exact hn ⟨h1, h5, h2, h6, h14, h18⟩

/-- In particular, infinitely many exponents produce a non-powerful value. -/
theorem infinitely_many_add_one_nonpowerful :
    Set.Infinite {n : ℕ | ¬ (2 ^ n + 1).Powerful} := by
  have hinj : Function.Injective (fun k : ℕ ↦ 6 * k + 1) := by
    intro a b hab
    change 6 * a + 1 = 6 * b + 1 at hab
    omega
  have hinf := Set.infinite_range_of_injective hinj
  exact hinf.mono (by
    rintro n ⟨k, rfl⟩
    exact add_one_residue_one k
  )

end Contribution.Erdos936AddResidues
