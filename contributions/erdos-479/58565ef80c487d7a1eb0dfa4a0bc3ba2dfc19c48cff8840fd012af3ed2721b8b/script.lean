import Mathlib
import FormalConjectures.ErdosProblems.«479»

/-!
# Erdős 479: a Fermat--CRT power-tower family

For every `t : ℕ`, put `q = 2^t` and `k = 2^q`. For every prime `p > 2`,
the denominator `n = q*p` satisfies the exact pinned congruence
`2^n ≡ k [MOD n]`. The infinitely many choices of `p` therefore give
infinitely many valid denominators for this `k`, and injectivity of
`t ↦ 2^(2^t)` gives infinitely many distinct good parameters `k`.

The proof combines divisibility modulo `q`, Fermat's little theorem modulo
`p`, and the coprime-moduli CRT lemma. The final section transports the result
to `Int.ModEq`, matching the corrected upstream integer statement while
leaving the pinned `Nat.ModEq` result unchanged.
-/

namespace Contribution.Erdos479FermatCRT

/-- Core Fermat--CRT construction. With `q = 2^t` and odd prime `p`, both
powers vanish modulo `q`; modulo `p`, their exponent difference is
`q*(p-1)`. Coprimality of `q` and `p` combines the congruences modulo `q*p`. -/
theorem nat_modEq_for_prime_multiplier
    (t p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    2 ^ (2 ^ t * p) ≡ 2 ^ (2 ^ t) [MOD 2 ^ t * p] := by
  let q := 2 ^ t
  have hpne : p ≠ 2 := by omega
  have hpnot : ¬p ∣ 2 := by
    rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
    exact hpne
  have hcop : q.Coprime p := by
    exact (hp.coprime_iff_not_dvd.mpr hpnot).symm.pow_left t
  apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
  constructor
  · have htq : t ≤ q := t.lt_two_pow_self.le
    have hqprod : q ≤ q * p := Nat.le_mul_of_pos_right q hp.pos
    have hleft : q ∣ 2 ^ (q * p) := pow_dvd_pow 2 (htq.trans hqprod)
    have hright : q ∣ 2 ^ q := pow_dvd_pow 2 htq
    exact hleft.modEq_zero_nat.trans hright.modEq_zero_nat.symm
  · have hdiv : p - 1 ∣ q * p - q := by
      refine ⟨q, ?_⟩
      calc
        q * p - q = q * p - q * 1 := by simp
        _ = q * (p - 1) := (Nat.mul_sub_left_distrib q p 1).symm
        _ = (p - 1) * q := Nat.mul_comm _ _
    have hqprod : q ≤ q * p := Nat.le_mul_of_pos_right q hp.pos
    have hz := Int.ModEq.pow_eq_pow hp hdiv hqprod (by positivity : 0 < q) (2 : ℤ)
    rw [← Int.natCast_modEq_iff]
    norm_cast at hz ⊢

/-- Exact family containment: every denominator `2^t*p` for a prime `p > 2`
belongs to the pinned target set at `k = 2^(2^t)`. -/
theorem prime_multiplier_family_subset (t : ℕ) :
    (fun p : ℕ => 2 ^ t * p) '' {p : ℕ | p.Prime ∧ 2 < p} ⊆
      {n : ℕ | 2 ^ n ≡ 2 ^ (2 ^ t) [MOD n]} := by
  rintro n ⟨p, ⟨hp, hp2⟩, rfl⟩
  exact nat_modEq_for_prime_multiplier t p hp hp2

/-- For each power-tower parameter `k = 2^(2^t)`, infinitely many
denominators satisfy the exact pinned `Nat.ModEq` target body. -/
theorem power_tower_parameter_nat (t : ℕ) :
    {n : ℕ | 2 ^ n ≡ 2 ^ (2 ^ t) [MOD n]}.Infinite := by
  let q := 2 ^ t
  have hP : {p : ℕ | p.Prime ∧ 2 < p}.Infinite := by
    rw [Set.infinite_iff_exists_gt]
    intro b
    obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (max b 2 + 1)
    exact ⟨p, ⟨hp, by omega⟩, by omega⟩
  have hImage : ((fun p : ℕ => q * p) '' {p : ℕ | p.Prime ∧ 2 < p}).Infinite :=
    hP.image (by
      intro p _ r _ hpr
      exact Nat.mul_left_cancel (by positivity : 0 < q) hpr)
  apply hImage.mono
  rintro n ⟨p, ⟨hp, hp2⟩, rfl⟩
  exact nat_modEq_for_prime_multiplier t p hp hp2

/-- Direct relevance to the pinned target body: this parameter is nontrivial
and has infinitely many valid denominators. -/
theorem pinned_target_body_at_power_tower (t : ℕ) :
    1 < 2 ^ (2 ^ t) ∧
      {n : ℕ | 2 ^ n ≡ 2 ^ (2 ^ t) [MOD n]}.Infinite := by
  refine ⟨one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by positivity), ?_⟩
  exact power_tower_parameter_nat t

/-- Infinitely many distinct natural parameters satisfy the pinned target
body, rather than merely one fixed `k`. -/
theorem infinitely_many_good_nat_parameters :
    {k : ℕ | 1 < k ∧ {n : ℕ | 2 ^ n ≡ k [MOD n]}.Infinite}.Infinite := by
  have hpow : Function.Injective (fun t : ℕ => 2 ^ (2 ^ t)) :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ 2)).comp
      (Nat.pow_right_injective (by norm_num : 2 ≤ 2))
  apply (Set.infinite_range_of_injective hpow).mono
  rintro k ⟨t, rfl⟩
  exact pinned_target_body_at_power_tower t

/- ## Compatibility with the corrected upstream integer statement -/

/-- Canonical bridge from a natural modular congruence to the corresponding
integer modular congruence. This is an explicit use of Mathlib's
`Int.natCast_modEq_iff`, not a weakening or reinterpretation of either target. -/
theorem int_modEq_of_nat_modEq {a b n : ℕ} (h : a ≡ b [MOD n]) :
    (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)] :=
  Int.natCast_modEq_iff.mpr h

/-- The same power-tower family in the exact `Int.ModEq` body used by the
corrected upstream Erdős 479 statement. -/
theorem power_tower_parameter_int (t : ℕ) :
    {n : ℕ | (2 : ℤ) ^ n ≡ (2 : ℤ) ^ (2 ^ t) [ZMOD (n : ℤ)]}.Infinite := by
  apply (power_tower_parameter_nat t).mono
  intro n hn
  simpa using int_modEq_of_nat_modEq hn

/-- Direct parameter use site for the corrected upstream integer target. -/
theorem upstream_target_body_at_power_tower (t : ℕ) :
    (2 : ℤ) ^ (2 ^ t) ≠ 1 ∧
      {n : ℕ | (2 : ℤ) ^ n ≡ (2 : ℤ) ^ (2 ^ t) [ZMOD (n : ℤ)]}.Infinite := by
  refine ⟨ne_of_gt (one_lt_pow₀ (by norm_num : (1 : ℤ) < 2) (by positivity)), ?_⟩
  exact power_tower_parameter_int t

/-- Infinitely many distinct integer parameters satisfy the corrected
upstream target body. -/
theorem infinitely_many_good_int_parameters :
    {k : ℤ | k ≠ 1 ∧
      {n : ℕ | (2 : ℤ) ^ n ≡ k [ZMOD (n : ℤ)]}.Infinite}.Infinite := by
  have hint : Function.Injective (fun t : ℕ => (2 : ℤ) ^ (2 ^ t)) :=
    (Int.pow_right_injective (a := (2 : ℤ)) (by norm_num)).comp
      (Nat.pow_right_injective (by norm_num : 2 ≤ 2))
  apply (Set.infinite_range_of_injective hint).mono
  rintro k ⟨t, rfl⟩
  exact upstream_target_body_at_power_tower t

end Contribution.Erdos479FermatCRT
