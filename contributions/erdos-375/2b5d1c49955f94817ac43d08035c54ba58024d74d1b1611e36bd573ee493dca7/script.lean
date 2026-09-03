import FormalConjectures.ErdosProblems.«375»

/-!
A proof of the `k = 3` case of Erdős problem 375 (Grimm's problem).

The pinned source already proves the range `k ≤ 2`. The marginal contribution
here is the next case, `k = 3`, together with the stronger elementary lemma that
every triple of consecutive natural numbers beginning at least at `3` admits
distinct prime divisors.
-/

namespace Contribution.Erdos375Three

open Erdos375

lemma prime_factors_of_consecutive_ne
    {a p q : ℕ} (hp : p.Prime) (hp_dvd : p ∣ a)
    (hq_dvd : q ∣ a + 1) : p ≠ q := by
  intro hpq
  have hd : p ∣ (a + 1) - a := Nat.dvd_sub (hpq ▸ hq_dvd) hp_dvd
  have : p ∣ 1 := by simpa using hd
  exact hp.not_dvd_one this

lemma prime_factors_distance_two_ne_of_two_not_dvd
    {a p q : ℕ} (hp : p.Prime) (hp_dvd : p ∣ a)
    (hq_dvd : q ∣ a + 2) (h2a : ¬ 2 ∣ a) : p ≠ q := by
  intro hpq
  have hd : p ∣ (a + 2) - a := Nat.dvd_sub (hpq ▸ hq_dvd) hp_dvd
  have hp2 : p = 2 := by
    apply Nat.le_antisymm (Nat.le_of_dvd (by omega) (by simpa using hd)) hp.two_le
  exact h2a (hp2 ▸ hp_dvd)

lemma two_not_dvd_succ_of_two_dvd {a : ℕ} (ha : 2 ∣ a) : ¬ 2 ∣ a + 1 := by
  intro h
  have : 2 ∣ (a + 1) - a := Nat.dvd_sub h ha
  norm_num at this

lemma half_dvd {a : ℕ} (h2a : 2 ∣ a) : a / 2 ∣ a := by
  exact ⟨2, by simpa [Nat.mul_comm] using (Nat.div_mul_cancel h2a).symm⟩

lemma two_not_dvd_half_of_not_four_dvd {a : ℕ}
    (h2a : 2 ∣ a) (h4a : ¬ 4 ∣ a) : ¬ 2 ∣ a / 2 := by
  intro h
  have hhalf : a / 2 ∣ a := half_dvd h2a
  rcases h with ⟨c, hc⟩
  rcases hhalf with ⟨d, hd⟩
  apply h4a
  refine ⟨c * d, ?_⟩
  omega

lemma two_not_dvd_half_add_two_of_four_dvd {a : ℕ}
    (h4a : 4 ∣ a) : ¬ 2 ∣ (a + 2) / 2 := by
  have h2a : 2 ∣ a := dvd_trans (by norm_num : 2 ∣ 4) h4a
  have h2a2 : 2 ∣ a + 2 := dvd_add h2a (by norm_num)
  intro h
  have hhalf : (a + 2) / 2 ∣ a + 2 := half_dvd h2a2
  rcases h with ⟨c, hc⟩
  rcases hhalf with ⟨d, hd⟩
  have h4a2 : 4 ∣ a + 2 := by
    refine ⟨c * d, ?_⟩
    omega
  have : 4 ∣ (a + 2) - a := Nat.dvd_sub h4a2 h4a
  norm_num at this

/-- Every triple of consecutive integers starting at least at `3` has a system
of distinct prime divisors. -/
theorem consecutive_three_distinct_prime_divisors (a : ℕ) (ha : 3 ≤ a) :
    ∃ p : Fin 3 → ℕ, p.Injective ∧ ∀ i, (p i).Prime ∧ p i ∣ a + i := by
  by_cases h2a : 2 ∣ a
  · have h2a1 : ¬ 2 ∣ a + 1 := two_not_dvd_succ_of_two_dvd h2a
    by_cases h4a : 4 ∣ a
    · have h2a2 : 2 ∣ a + 2 := dvd_add h2a (by norm_num)
      have hm : (a + 2) / 2 ≠ 1 := by
        have hfour_le : 4 ≤ a := Nat.le_of_dvd (by omega) h4a
        omega
      choose q hq using (a + 1).exists_prime_and_dvd (by omega)
      choose r hr using ((a + 2) / 2).exists_prime_and_dvd hm
      have hr_dvd : r ∣ a + 2 := dvd_trans hr.2 (half_dvd h2a2)
      have h2r : 2 ≠ r := by
        intro h
        exact two_not_dvd_half_add_two_of_four_dvd h4a (h ▸ hr.2)
      have hqr : q ≠ r := prime_factors_of_consecutive_ne hq.1 hq.2 hr_dvd
      have h2q : 2 ≠ q := by
        intro h
        exact h2a1 (h ▸ hq.2)
      refine ⟨![2, q, r], ?_, ?_⟩
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i
        fin_cases i
        · simpa using And.intro Nat.prime_two h2a
        · simpa using hq
        · simpa using And.intro hr.1 hr_dvd
    · have hhalf_ne_one : a / 2 ≠ 1 := by
        intro h
        have := Nat.div_mul_cancel h2a
        omega
      choose p hp using (a / 2).exists_prime_and_dvd hhalf_ne_one
      choose q hq using (a + 1).exists_prime_and_dvd (by omega)
      have hp_dvd : p ∣ a := dvd_trans hp.2 (half_dvd h2a)
      have hp2 : p ≠ 2 := by
        intro h
        exact two_not_dvd_half_of_not_four_dvd h2a h4a (h ▸ hp.2)
      have hpq : p ≠ q := prime_factors_of_consecutive_ne hp.1 hp_dvd hq.2
      have hq2 : q ≠ 2 := by
        intro h
        exact h2a1 (h ▸ hq.2)
      refine ⟨![p, q, 2], ?_, ?_⟩
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i
        fin_cases i
        · simpa using And.intro hp.1 hp_dvd
        · simpa using hq
        · simpa using And.intro Nat.prime_two (dvd_add h2a (by norm_num : 2 ∣ 2))
  · choose p hp using a.exists_prime_and_dvd (by omega)
    choose q hq using (a + 1).exists_prime_and_dvd (by omega)
    choose r hr using (a + 2).exists_prime_and_dvd (by omega)
    have hpq : p ≠ q := prime_factors_of_consecutive_ne hp.1 hp.2 hq.2
    have hqr : q ≠ r := prime_factors_of_consecutive_ne hq.1 hq.2 hr.2
    have hpr : p ≠ r :=
      prime_factors_distance_two_ne_of_two_not_dvd hp.1 hp.2 hr.2 h2a
    refine ⟨![p, q, r], ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i <;> simp_all

/-- The exact `k = 3` instance of `Erdos375Prop`. -/
theorem erdos_375_k_three : ∀ n ≥ 1,
    (∀ i < 3, ¬ (n + i + 1).Prime) →
      ∃ p : Fin 3 → ℕ, p.Injective ∧
        ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  intro n hn hcomp
  have hn3 : 3 ≤ n + 1 := by
    have hnot : ¬ (n + 1).Prime := hcomp 0 (by omega)
    have : n + 1 ≠ 2 := fun h => hnot (h ▸ Nat.prime_two)
    omega
  obtain ⟨p, hinj, hp⟩ := consecutive_three_distinct_prime_divisors (n + 1) hn3
  refine ⟨p, hinj, ?_⟩
  intro i
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp i

/-- The source theorem's unconditional range `k ≤ 2`, extended to `k ≤ 3`. -/
theorem erdos_375_le_three : ∀ n ≥ 1, ∀ k ≤ 3,
    (∀ i < k, ¬ (n + i + 1).Prime) →
      ∃ p : Fin k → ℕ, p.Injective ∧
        ∀ i, (p i).Prime ∧ p i ∣ n + i + 1 := by
  intro n hn k hk hcomp
  by_cases hk2 : k ≤ 2
  · exact Erdos375.erdos_375.variants.le_two n hn k hk2 hcomp
  · have : k = 3 := by omega
    subst k
    exact erdos_375_k_three n hn hcomp

end Contribution.Erdos375Three
