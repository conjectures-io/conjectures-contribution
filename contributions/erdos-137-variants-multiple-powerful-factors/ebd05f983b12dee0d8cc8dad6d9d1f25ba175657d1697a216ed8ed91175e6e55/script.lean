import Mathlib

/-!
# erdos-137-variants-multiple-powerful-factors

Tools for producing primes that divide a block of consecutive integers **exactly once**.

The target asks, for fixed `k`, that all sufficiently long blocks `N = ∏ x ∈ Icc m (m+n), x`
admit `k` distinct primes `p` with `p ∣ N` but `p ^ 2 ∤ N`. This file supplies the
valuation machinery that turns "`p` meets the block once, simply" into exactly that
conclusion, plus an unconditional source of one such prime whenever `m ≤ n`.
-/

namespace Contribution.Erdos137VariantsMultiplePowerfulFactors

open Finset Nat

/-- The block `Icc m (m+n)` consists of positive integers when `0 < m`, so its product
is nonzero and `Nat.factorization` is available. -/
theorem prod_Icc_ne_zero {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (∏ x ∈ Icc m (m + n), x) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro x hx
  have := (Finset.mem_Icc.mp hx).1
  omega

/-- If `p ∣ i` but `p ^ 2 ∤ i` then `i` has `p`-adic valuation exactly one. -/
theorem factorization_eq_one {p i : ℕ} (hp : p.Prime) (hi : i ≠ 0)
    (hd : p ∣ i) (hnd : ¬ p ^ 2 ∣ i) : i.factorization p = 1 := by
  have h1 : 1 ≤ i.factorization p := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hi]; simpa using hd
  have h2 : ¬ (2 ≤ i.factorization p) := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hi]; exact hnd
  omega

/-- **Key reduction.** A prime meeting the block exactly once, and only to the first power,
divides the product but not its square — precisely the conclusion the target requires of
each of its `k` primes. -/
theorem simple_prime_of_unique {m n p i : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hi : i ∈ Icc m (m + n)) (hd : p ∣ i) (hnd : ¬ p ^ 2 ∣ i)
    (huniq : ∀ y ∈ Icc m (m + n), p ∣ y → y = i) :
    p ∣ (∏ x ∈ Icc m (m + n), x) ∧ ¬ p ^ 2 ∣ (∏ x ∈ Icc m (m + n), x) := by
  have hNne := prod_Icc_ne_zero hm n
  have hine : i ≠ 0 := by have := (Finset.mem_Icc.mp hi).1; omega
  have hfac : (∏ x ∈ Icc m (m + n), x).factorization p = 1 := by
    have hne : ∀ x ∈ Icc m (m + n), x ≠ 0 := by
      intro x hx; have := (Finset.mem_Icc.mp hx).1; omega
    rw [Nat.factorization_prod hne]
    simp only [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · exact factorization_eq_one hp hine hd hnd
    · intro y hy hyi
      have hpy : ¬ p ∣ y := fun h => hyi (huniq y hy h)
      simpa using Nat.factorization_eq_zero_of_not_dvd hpy
    · intro h; exact absurd hi h
  refine ⟨hd.trans (Finset.dvd_prod_of_mem _ hi), ?_⟩
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp hNne, hfac]; omega

/-- A prime exceeding the block length meets the block at most once. -/
theorem unique_of_prime_gt {m n p x y : ℕ} (hp : p.Prime) (hn : n < p)
    (hx : x ∈ Icc m (m + n)) (hy : y ∈ Icc m (m + n))
    (hdx : p ∣ x) (hdy : p ∣ y) : x = y := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  rcases le_total y x with h | h
  · have hdvd : p ∣ x - y := (Nat.dvd_sub_iff_left h hdy).mpr hdx
    have h0 : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd : p ∣ y - x := (Nat.dvd_sub_iff_left h hdx).mpr hdy
    have h0 : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

/-- **Corollary.** A prime `p > n` meeting the block simply already witnesses the target's
per-prime obligation. -/
theorem simple_prime_of_large {m n p i : ℕ} (hm : 0 < m) (hp : p.Prime) (hn : n < p)
    (hi : i ∈ Icc m (m + n)) (hd : p ∣ i) (hnd : ¬ p ^ 2 ∣ i) :
    p ∣ (∏ x ∈ Icc m (m + n), x) ∧ ¬ p ^ 2 ∣ (∏ x ∈ Icc m (m + n), x) :=
  simple_prime_of_unique hm hp hi hd hnd
    (fun y hy hdy => unique_of_prime_gt hp hn hy hi hdy hd)

/-- **Unconditional instance (the `k = 1` case for `m ≤ n`).** Bertrand supplies a prime in
`((m+n)/2, m+n]`; when `m ≤ n` that prime lies inside the block and is its own only
multiple there, so it divides the product exactly once. In particular such a product is
never powerful. -/
theorem exists_simple_prime {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ (∏ x ∈ Icc m (m + n), x) ∧
      ¬ p ^ 2 ∣ (∏ x ∈ Icc m (m + n), x) := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul ((m + n) / 2) (by omega)
  have hple : p ≤ m + n := le_trans hhi (Nat.mul_div_le (m + n) 2)
  have h2p : m + n < 2 * p := by omega
  have hmp : m ≤ p := by omega
  have hmem : p ∈ Icc m (m + n) := Finset.mem_Icc.mpr ⟨hmp, hple⟩
  refine ⟨p, hp, simple_prime_of_unique hm hp hmem dvd_rfl ?_ ?_⟩
  · intro h
    have := Nat.le_of_dvd hp.pos h
    nlinarith [hp.two_le]
  · intro y hy hdy
    obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
    obtain ⟨c, rfl⟩ := hdy
    have hc : c ≠ 0 := by rintro rfl; omega
    have : c = 1 := by nlinarith [hp.two_le]
    simp [this]

end Contribution.Erdos137VariantsMultiplePowerfulFactors
