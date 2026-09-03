import FormalConjectures.ErdosProblems.«936»

/-!
# Residue obstructions for the `2 ^ n - 1` variant of Erdős 936

This contribution formalizes a reusable prime-square obstruction to powerfulness and
applies it to six explicit infinite residue classes of exponents.  The prime
`3` excludes `n ≡ 2, 4 (mod 6)`, while the prime `5` excludes
`n ≡ 4, 8, 12, 16 (mod 20)`.

These results are partial progress only: they do not prove that every
sufficiently large `2 ^ n - 1` is non-powerful.
-/

open Filter Nat

namespace Contribution.Erdos936SubResidues

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

/-- The residue class `n ≡ 2 (mod 6)` is excluded by the prime `3`. -/
theorem sub_one_residue_two (k : ℕ) : ¬ (2 ^ (6 * k + 2) - 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 3) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (6 * k + 2) ≡ 1 [MOD 3] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (6 * k + 2) - 1 ≡ 1 - 1 [MOD 3] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simpa [Nat.ModEq] using hs
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (6 * k + 2) ≡ 4 [MOD 9] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (6 * k + 2) - 1 ≡ 4 - 1 [MOD 9] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simp [Nat.ModEq] at hs
    omega

/-- The residue class `n ≡ 4 (mod 6)` is excluded by the prime `3`. -/
theorem sub_one_residue_four (k : ℕ) : ¬ (2 ^ (6 * k + 4) - 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 3) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (6 * k + 4) ≡ 1 [MOD 3] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (6 * k + 4) - 1 ≡ 1 - 1 [MOD 3] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simpa [Nat.ModEq] using hs
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (6 * k + 4) ≡ 7 [MOD 9] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (6 * k + 4) - 1 ≡ 7 - 1 [MOD 9] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simp [Nat.ModEq] at hs
    omega

/-- The residue class `n ≡ 4 (mod 20)` is excluded by the prime `5`. -/
theorem sub_one_residue_four_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 4) - 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 4) ≡ 1 [MOD 5] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 4) - 1 ≡ 1 - 1 [MOD 5] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simpa [Nat.ModEq] using hs
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 4) ≡ 16 [MOD 25] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 4) - 1 ≡ 16 - 1 [MOD 25] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simp [Nat.ModEq] at hs
    omega

/-- The residue class `n ≡ 8 (mod 20)` is excluded by the prime `5`. -/
theorem sub_one_residue_eight_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 8) - 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 8) ≡ 1 [MOD 5] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 8) - 1 ≡ 1 - 1 [MOD 5] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simpa [Nat.ModEq] using hs
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 8) ≡ 6 [MOD 25] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 8) - 1 ≡ 6 - 1 [MOD 25] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simp [Nat.ModEq] at hs
    omega

/-- The residue class `n ≡ 12 (mod 20)` is excluded by the prime `5`. -/
theorem sub_one_residue_twelve_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 12) - 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 12) ≡ 1 [MOD 5] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 12) - 1 ≡ 1 - 1 [MOD 5] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simpa [Nat.ModEq] using hs
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 12) ≡ 21 [MOD 25] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 12) - 1 ≡ 21 - 1 [MOD 25] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simp [Nat.ModEq] at hs
    omega

/-- The residue class `n ≡ 16 (mod 20)` is excluded by the prime `5`. -/
theorem sub_one_residue_sixteen_mod_twenty (k : ℕ) :
    ¬ (2 ^ (20 * k + 16) - 1).Powerful := by
  apply not_powerful_of_prime_dvd_not_sq_dvd (p := 5) (by norm_num)
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 16) ≡ 1 [MOD 5] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 16) - 1 ≡ 1 - 1 [MOD 5] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simpa [Nat.ModEq] using hs
  · rw [Nat.dvd_iff_mod_eq_zero]
    have h : 2 ^ (20 * k + 16) ≡ 11 [MOD 25] := by
      simp [Nat.ModEq, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have hs : 2 ^ (20 * k + 16) - 1 ≡ 11 - 1 [MOD 25] :=
      Nat.ModEq.sub (Nat.one_le_pow _ 2 (by omega)) (by omega) h (Nat.ModEq.refl 1)
    simp [Nat.ModEq] at hs
    omega

/-- Both prime-`3` obstructions, stated directly in terms of `n % 6`. -/
theorem sub_one_not_powerful_of_mod_six {n : ℕ} (hn : n % 6 = 2 ∨ n % 6 = 4) :
    ¬ (2 ^ n - 1).Powerful := by
  rcases hn with hn | hn
  · have heq : 6 * (n / 6) + 2 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 6)
    rw [← heq]
    exact sub_one_residue_two (n / 6)
  · have heq : 6 * (n / 6) + 4 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 6)
    rw [← heq]
    exact sub_one_residue_four (n / 6)

/-- All four prime-`5` obstructions, stated directly in terms of `n % 20`. -/
theorem sub_one_not_powerful_of_mod_twenty {n : ℕ}
    (hn : n % 20 = 4 ∨ n % 20 = 8 ∨ n % 20 = 12 ∨ n % 20 = 16) :
    ¬ (2 ^ n - 1).Powerful := by
  rcases hn with hn | hn | hn | hn
  · have heq : 20 * (n / 20) + 4 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact sub_one_residue_four_mod_twenty (n / 20)
  · have heq : 20 * (n / 20) + 8 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact sub_one_residue_eight_mod_twenty (n / 20)
  · have heq : 20 * (n / 20) + 12 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact sub_one_residue_twelve_mod_twenty (n / 20)
  · have heq : 20 * (n / 20) + 16 = n := by
      rw [← hn]
      simpa [Nat.mul_comm] using (Nat.div_add_mod n 20)
    rw [← heq]
    exact sub_one_residue_sixteen_mod_twenty (n / 20)

/-- The exponents not yet eliminated by the prime-`3` and prime-`5` sieves. -/
def IsRemainingExponent (n : ℕ) : Prop :=
  n % 6 ≠ 2 ∧ n % 6 ≠ 4 ∧ n % 20 ≠ 4 ∧ n % 20 ≠ 8 ∧
    n % 20 ≠ 12 ∧ n % 20 ≠ 16

/-- A direct sieve restriction on any exponent producing a powerful value. -/
theorem powerful_sub_one_residue_restrictions {n : ℕ} (h : (2 ^ n - 1).Powerful) :
    IsRemainingExponent n := by
  constructor
  · intro hn
    exact sub_one_not_powerful_of_mod_six (Or.inl hn) h
  constructor
  · intro hn
    exact sub_one_not_powerful_of_mod_six (Or.inr hn) h
  constructor
  · intro hn
    exact sub_one_not_powerful_of_mod_twenty (Or.inl hn) h
  constructor
  · intro hn
    exact sub_one_not_powerful_of_mod_twenty (Or.inr (Or.inl hn)) h
  constructor
  · intro hn
    exact sub_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inl hn))) h
  · intro hn
    exact sub_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inr hn))) h

/--
The original eventual-nonpowerfulness obligation is equivalent to proving it
only on the residue classes that survive the two elementary prime sieves.
-/
theorem eventually_not_powerful_iff_on_remaining :
    Erdos936.EventuallyNotPowerful (2 ^ · - 1) ↔
      ∀ᶠ n in atTop, IsRemainingExponent n → ¬ (2 ^ n - 1).Powerful := by
  constructor
  · intro h
    filter_upwards [h] with n hn
    exact fun _ ↦ hn
  · intro h
    filter_upwards [h] with n hn
    by_cases h2 : n % 6 = 2
    · exact sub_one_not_powerful_of_mod_six (Or.inl h2)
    by_cases h4 : n % 6 = 4
    · exact sub_one_not_powerful_of_mod_six (Or.inr h4)
    by_cases h4' : n % 20 = 4
    · exact sub_one_not_powerful_of_mod_twenty (Or.inl h4')
    by_cases h8 : n % 20 = 8
    · exact sub_one_not_powerful_of_mod_twenty (Or.inr (Or.inl h8))
    by_cases h12 : n % 20 = 12
    · exact sub_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inl h12)))
    by_cases h16 : n % 20 = 16
    · exact sub_one_not_powerful_of_mod_twenty (Or.inr (Or.inr (Or.inr h16)))
    exact hn ⟨h2, h4, h4', h8, h12, h16⟩

/-- In particular, infinitely many exponents produce a non-powerful value. -/
theorem infinitely_many_sub_one_nonpowerful :
    Set.Infinite {n : ℕ | ¬ (2 ^ n - 1).Powerful} := by
  have hinj : Function.Injective (fun k : ℕ ↦ 6 * k + 2) := by
    intro a b hab
    change 6 * a + 2 = 6 * b + 2 at hab
    omega
  have hinf := Set.infinite_range_of_injective hinj
  exact hinf.mono (by
    rintro n ⟨k, rfl⟩
    exact sub_one_residue_two k
  )

end Contribution.Erdos936SubResidues
