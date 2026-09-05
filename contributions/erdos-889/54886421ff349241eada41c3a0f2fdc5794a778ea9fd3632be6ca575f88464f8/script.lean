import FormalConjectures.ErdosProblems.«889»

namespace Contribution.Subb

theorem new_divisor_iff_large {n k p : ℕ} (hp : 0 < p) (hd : p ∣ n + k) :
    (∀ i ∈ Finset.range k, ¬ p ∣ n + i) ↔ k < p := by
  constructor
  · intro h
    by_contra hn
    have hpk : p ≤ k := by omega
    have hdiv : p ∣ n + k - p := Nat.dvd_sub hd (dvd_refl p)
    have heq : n + k - p = n + (k - p) := by omega
    rw [heq] at hdiv
    exact h (k-p) (Finset.mem_range.mpr (by omega)) hdiv
  · intro h i hi hdi
    have hik : i < k := Finset.mem_range.mp hi
    have hdiv : p ∣ k - i := by
      have ht := Nat.dvd_sub hd hdi
      have heq : n + k - (n + i) = k - i := by omega
      simpa only [heq] using ht
    have := Nat.le_of_dvd (by omega : 0 < k-i) hdiv
    omega

theorem new_prime_factor_count (n k : ℕ) :
    Erdos889.v n k = ((n+k).primeFactors.filter (fun p => k < p)).card := by
  unfold Erdos889.v
  congr 1
  apply Finset.filter_congr
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact new_divisor_iff_large h.1.pos h.2.1

end Contribution.Subb
