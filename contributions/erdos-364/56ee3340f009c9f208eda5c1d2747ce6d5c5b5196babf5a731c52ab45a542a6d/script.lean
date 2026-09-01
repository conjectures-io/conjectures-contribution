import FormalConjectures.ErdosProblems.«364»

namespace Contribution.Erdos364Radical

open Nat Finset

/-- The radical (squarefree kernel) of `n`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem rad_ne_zero {n : ℕ} : rad n ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- For powerful `n`, every sub-product of squared prime factors divides `n`. -/
theorem prod_sq_dvd_of_subset {n : ℕ} (h : Nat.Powerful n) :
    ∀ S : Finset ℕ, S ⊆ n.primeFactors → (∏ p ∈ S, p ^ 2) ∣ n := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
      intro hsub
      have haS : a ∈ n.primeFactors := hsub (Finset.mem_insert_self a s)
      have hs : s ⊆ n.primeFactors := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.prod_insert ha]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h a haS) (ih hs)
      refine Nat.Coprime.pow_left 2 (Nat.Coprime.prod_right fun q hq => ?_)
      have hap : a.Prime := Nat.prime_of_mem_primeFactors haS
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (hs hq)
      have hne : a ≠ q := fun hEq => ha (hEq ▸ hq)
      exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hap hqp).mpr hne)

/-- **The radical bound.** For powerful `n`, the *square* of the radical divides `n`. -/
theorem rad_sq_dvd {n : ℕ} (h : Nat.Powerful n) : rad n ^ 2 ∣ n := by
  rw [rad, ← Finset.prod_pow]
  exact prod_sq_dvd_of_subset h _ (Finset.Subset.refl _)

/-- Hence `rad n ^ 2 ≤ n` for nonzero powerful `n`: powerful numbers have small radical. -/
theorem rad_sq_le {n : ℕ} (hn : n ≠ 0) (h : Nat.Powerful n) : rad n ^ 2 ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (rad_sq_dvd h)


/-- In a powerful triple the three numbers are pairwise coprime: `n` is odd (it is
`3 mod 4` by the congruence obstruction), so even `gcd (n) (n+2) = 1`. -/
theorem coprime_of_odd {n : ℕ} (hodd : n % 2 = 1) : Nat.Coprime n (n + 2) := by
  have h : Nat.gcd n (n + 2) ∣ 2 := by
    exact (Nat.dvd_add_right (Nat.gcd_dvd_left n (n + 2))).mp (Nat.gcd_dvd_right n (n + 2))
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact h1
  · exfalso
    have : (2 : ℕ) ∣ n := h2 ▸ Nat.gcd_dvd_left n (n + 2)
    omega

/-- **The abc bridge.** If `n, n+1, n+2` are powerful with `n` odd, then the whole product
has radical at most its own square root:
`rad (n*(n+1)*(n+2)) ^ 2 ≤ n*(n+1)*(n+2)`.
An abc-triple `(n, 2, n+2)` of this quality is exactly what the abc conjecture forbids for
large `n`; this is the precise sense in which Erdős 364 is an abc-strength statement, and why
the congruence sieve (which stalls at `n ≡ 7, 27, 35 mod 36`) cannot finish. -/
theorem triple_rad_sq_le {n : ℕ} (hn : n ≠ 0) (hodd : n % 2 = 1)
    (h0 : Nat.Powerful n) (h1 : Nat.Powerful (n + 1)) (h2 : Nat.Powerful (n + 2)) :
    rad (n * (n + 1) * (n + 2)) ^ 2 ≤ n * (n + 1) * (n + 2) := by
  have hprod : Nat.Powerful (n * (n + 1) * (n + 2)) := by
    intro p hp
    rw [Nat.primeFactors_mul (by positivity) (by omega), Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [Nat.primeFactors_mul hn (by omega), Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (h0 p hp) _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (h1 p hp) _) _
    · exact Dvd.dvd.mul_left (h2 p hp) _
  exact rad_sq_le (by positivity) hprod

end Contribution.Erdos364Radical
