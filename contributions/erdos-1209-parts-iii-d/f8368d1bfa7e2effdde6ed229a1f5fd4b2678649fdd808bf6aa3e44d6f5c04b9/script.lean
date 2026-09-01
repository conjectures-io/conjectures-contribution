import Mathlib
import FormalConjectures.ErdosProblems.«1209»

-- ==== from Last_erdos1209_i.lean ====
/-!
Independent proof of `erdos_1209.parts.i`: the answer is False.

Given any lower-bound function `f`, we diagonalize: build a strictly monotone
sequence `a` of primes with `f k ≤ a k` such that for every `k ≥ 1` the number
`k + a k` is divisible by some prime `q` with `1 < q < k + a k` (choosing
`a k ≡ -k (mod q)` by Dirichlet's theorem on primes in arithmetic progressions).
Then `n = 0` gives all `n + a k` prime, but no `n ≥ 1` does (take `k = n`),
so the solution set is contained in `{0}` and is finite.
-/

namespace Contribution.Erdos1209PartsI

theorem erdos_1209.parts.i :
    answer(False) ↔
      ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
        (∃ n, ∀ k, (n + a k).Prime) →
        {n | ∀ k, (n + a k).Prime}.Infinite := by
  constructor
  · exact fun h => h.elim
  · rintro ⟨f, hf⟩
    -- Key step: for every `k` and every bound `m` there is a prime `p > m`
    -- such that `k + 1 + p` is not prime.
    have step : ∀ k m : ℕ, ∃ p : ℕ, m < p ∧ p.Prime ∧ ¬(k + 1 + p).Prime := by
      intro k m
      obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 2)
      haveI : NeZero q := ⟨hq.ne_zero⟩
      have hndvd : ¬ q ∣ (k + 1) := by
        intro hdvd
        have := Nat.le_of_dvd (Nat.succ_pos k) hdvd
        omega
      have hunit : IsUnit (-((k + 1 : ℕ) : ZMod q)) := by
        rw [IsUnit.neg_iff, ZMod.isUnit_iff_coprime]
        exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd).symm
      obtain ⟨p, hpgt, hpp, hpeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max m q)
      refine ⟨p, lt_of_le_of_lt (le_max_left m q) hpgt, hpp, ?_⟩
      have hqp : q < p := lt_of_le_of_lt (le_max_right m q) hpgt
      have hdvd : q ∣ (k + 1 + p) := by
        have h0 : ((k + 1 + p : ℕ) : ZMod q) = 0 := by
          push_cast [hpeq]
          ring
        exact (ZMod.natCast_eq_zero_iff _ _).mp h0
      intro hP
      rcases hP.eq_one_or_self_of_dvd q hdvd with h1 | h2
      · exact hq.one_lt.ne' h1
      · omega
    choose P hP1 hP2 hP3 using step
    obtain ⟨p0, hp0f, hp0p⟩ := Nat.exists_infinite_primes (f 0)
    -- The diagonal sequence.
    let a : ℕ → ℕ := fun n =>
      Nat.rec (motive := fun _ => ℕ) p0 (fun k ih => P k (max ih (f (k + 1)))) n
    have ha0 : a 0 = p0 := rfl
    have haS : ∀ k, a (k + 1) = P k (max (a k) (f (k + 1))) := fun _ => rfl
    have hmono : StrictMono a := by
      apply strictMono_nat_of_lt_succ
      intro k
      rw [haS k]
      exact lt_of_le_of_lt (le_max_left _ _) (hP1 k _)
    have hbound : ∀ k, f k ≤ a k := by
      intro k
      cases k with
      | zero => simpa [ha0] using hp0f
      | succ k =>
        rw [haS k]
        exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (hP1 k _))
    have hprime : ∀ k, (a k).Prime := by
      intro k
      cases k with
      | zero => simpa [ha0] using hp0p
      | succ k =>
        rw [haS k]
        exact hP2 k _
    have hnot : ∀ k, ¬(k + 1 + a (k + 1)).Prime := by
      intro k
      rw [haS k]
      exact hP3 k _
    have hinf := hf a hmono hbound ⟨0, fun k => by simpa using hprime k⟩
    have hsub : {n | ∀ k, (n + a k).Prime} ⊆ {0} := by
      intro n hn
      by_contra hne
      have hne' : n ≠ 0 := by simpa using hne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne'
      exact hnot m (hn (m + 1))
    exact Set.not_infinite.mpr ((Set.finite_singleton 0).subset hsub) hinf

end Contribution.Erdos1209PartsI

-- ==== from Last_erdos1209_ii.lean ====
/-
Independent proof of `erdos_1209.parts.ii`: the answer is False.

Same diagonalization as for parts.i, but with modulus `q ^ 2`: given any
lower-bound function `f`, build a strictly monotone sequence `a` of primes with
`f k ≤ a k` such that for every `k ≥ 1` the number `k + a k` is divisible by
`q ^ 2` for some prime `q` (choosing `a k ≡ -k (mod q ^ 2)` by Dirichlet's
theorem). Then `n = 0` gives all `n + a k` squarefree (they are prime), but no
`n ≥ 1` does (take `k = n`), so the solution set is contained in `{0}`.
-/

namespace Contribution.Erdos1209PartsII

theorem erdos_1209.parts.ii :
    answer(False) ↔
      ∃ f : ℕ → ℕ, ∀ a : ℕ → ℕ, StrictMono a → (∀ k, f k ≤ a k) →
        (∃ n, ∀ k, Squarefree (n + a k)) →
        {n | ∀ k, Squarefree (n + a k)}.Infinite := by
  constructor
  · exact fun h => h.elim
  · rintro ⟨f, hf⟩
    -- Key step: for every `k` and every bound `m` there is a prime `p > m`
    -- such that `k + 1 + p` is not squarefree.
    have step : ∀ k m : ℕ, ∃ p : ℕ, m < p ∧ p.Prime ∧ ¬Squarefree (k + 1 + p) := by
      intro k m
      obtain ⟨q, hqk, hq⟩ := Nat.exists_infinite_primes (k + 2)
      haveI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
      have hndvd : ¬ q ∣ (k + 1) := by
        intro hdvd
        have := Nat.le_of_dvd (Nat.succ_pos k) hdvd
        omega
      have hunit : IsUnit (-((k + 1 : ℕ) : ZMod (q ^ 2))) := by
        rw [IsUnit.neg_iff, ZMod.isUnit_iff_coprime]
        exact (((Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd).symm).pow_right 2
      obtain ⟨p, hpgt, hpp, hpeq⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (max m (q ^ 2))
      refine ⟨p, lt_of_le_of_lt (le_max_left m (q ^ 2)) hpgt, hpp, ?_⟩
      have hdvd : q ^ 2 ∣ (k + 1 + p) := by
        have h0 : ((k + 1 + p : ℕ) : ZMod (q ^ 2)) = 0 := by
          push_cast [hpeq]
          ring
        exact (ZMod.natCast_eq_zero_iff _ _).mp h0
      intro hsq
      have hdvd' : q * q ∣ (k + 1 + p) := by rwa [← sq]
      have := hsq q hdvd'
      rw [Nat.isUnit_iff] at this
      exact hq.one_lt.ne' this
    choose P hP1 hP2 hP3 using step
    obtain ⟨p0, hp0f, hp0p⟩ := Nat.exists_infinite_primes (f 0)
    -- The diagonal sequence.
    let a : ℕ → ℕ := fun n =>
      Nat.rec (motive := fun _ => ℕ) p0 (fun k ih => P k (max ih (f (k + 1)))) n
    have ha0 : a 0 = p0 := rfl
    have haS : ∀ k, a (k + 1) = P k (max (a k) (f (k + 1))) := fun _ => rfl
    have hmono : StrictMono a := by
      apply strictMono_nat_of_lt_succ
      intro k
      rw [haS k]
      exact lt_of_le_of_lt (le_max_left _ _) (hP1 k _)
    have hbound : ∀ k, f k ≤ a k := by
      intro k
      cases k with
      | zero => simpa [ha0] using hp0f
      | succ k =>
        rw [haS k]
        exact le_of_lt (lt_of_le_of_lt (le_max_right _ _) (hP1 k _))
    have hprime : ∀ k, (a k).Prime := by
      intro k
      cases k with
      | zero => simpa [ha0] using hp0p
      | succ k =>
        rw [haS k]
        exact hP2 k _
    have hnot : ∀ k, ¬Squarefree (k + 1 + a (k + 1)) := by
      intro k
      rw [haS k]
      exact hP3 k _
    have hinf := hf a hmono hbound
      ⟨0, fun k => by simpa using (hprime k).prime.squarefree⟩
    have hsub : {n | ∀ k, Squarefree (n + a k)} ⊆ {0} := by
      intro n hn
      by_contra hne
      have hne' : n ≠ 0 := by simpa using hne
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne'
      exact hnot m (hn (m + 1))
    exact Set.not_infinite.mpr ((Set.finite_singleton 0).subset hsub) hinf

end Contribution.Erdos1209PartsII
