import Mathlib
import FormalConjectures.ErdosProblems.«291»

/-!
Contribution: proof of `erdos_291.parts.ii` from Erdős Problem 291.

There are infinitely many `n` with `Nat.gcd (a n) (L n) > 1`: following
Steinerberger's observation, for `n = 2 * 3 ^ K` (leading digit `2` in base
`3`) the prime `3` divides both `a n` and `L n`.

Sketch: every `j ∈ [1, n]` that is not a multiple of `3 ^ K` satisfies
`3 * j ∣ L n` (write `j = 3 ^ v * m` with `3 ∤ m`, `v < K`), so its term
`L n / j` is a multiple of `3`.  The only multiples of `3 ^ K` in `[1, n]`
are `3 ^ K` and `n = 2 * 3 ^ K`, whose terms sum to
`2 * (L n / n) + (L n / n) = 3 * (L n / n)`.  Hence `3 ∣ a n`, and `3 ∣ L n`
since `3 ≤ n`.
-/

open Nat Finset Set Filter Erdos291

namespace Contribution.Erdos291PartsIi

/-- Every `j ∈ [1, n]` divides `L n`. -/
lemma dvd_L {j n : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : j ∣ Erdos291.L n := by
  unfold Erdos291.L
  exact Finset.dvd_lcm (f := fun x => x) (Finset.mem_Icc.mpr ⟨h1, h2⟩)

lemma L_ne_zero (n : ℕ) : Erdos291.L n ≠ 0 := by
  intro h
  unfold Erdos291.L at h
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  have hx0' : x = 0 := hx0
  rw [Finset.mem_Icc] at hx
  omega

/-- If `j ∈ [1, 2 * 3 ^ K]` is not a multiple of `3 ^ K`, then `3 ∣ L (2 * 3 ^ K) / j`. -/
lemma three_dvd_L_div (K j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ 2 * 3 ^ K)
    (hnd : ¬ 3 ^ K ∣ j) : 3 ∣ Erdos291.L (2 * 3 ^ K) / j := by
  have hj0 : j ≠ 0 := by omega
  obtain ⟨v, m, hm3, hj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj0 3 (by norm_num)
  have hvK : v < K := by
    by_contra hcon
    push_neg at hcon
    exact hnd (by rw [hj]; exact dvd_mul_of_dvd_left (pow_dvd_pow 3 hcon) m)
  have h1 : (3 : ℕ) ^ (v + 1) ∣ Erdos291.L (2 * 3 ^ K) := by
    apply dvd_L
    · exact Nat.one_le_pow _ _ (by norm_num)
    · have hle : (3 : ℕ) ^ (v + 1) ≤ 3 ^ K :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3K : 1 ≤ 3 ^ K := Nat.one_le_pow _ _ (by norm_num)
      omega
  have h2 : m ∣ Erdos291.L (2 * 3 ^ K) := by
    have hmj : m ∣ j := ⟨3 ^ v, by rw [hj]; ring⟩
    exact dvd_trans hmj (dvd_L hj1 hjn)
  have hcop : Nat.Coprime (3 ^ (v + 1)) m :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  have h4 : 3 ^ (v + 1) * m ∣ Erdos291.L (2 * 3 ^ K) :=
    hcop.mul_dvd_of_dvd_of_dvd h1 h2
  have hkey : 3 ^ (v + 1) * m = 3 * j := by
    rw [hj, pow_succ]; ring
  rw [hkey] at h4
  obtain ⟨c, hc⟩ := h4
  have hLj : Erdos291.L (2 * 3 ^ K) / j = 3 * c := by
    rw [hc, show 3 * j * c = j * (3 * c) by ring]
    exact Nat.mul_div_cancel_left _ hj1
  rw [hLj]
  exact ⟨c, rfl⟩

/-- `3` divides `a (2 * 3 ^ K)`. -/
lemma three_dvd_a (K : ℕ) : 3 ∣ Erdos291.a (2 * 3 ^ K) := by
  have h3K : 1 ≤ 3 ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hsub : ({3 ^ K, 2 * 3 ^ K} : Finset ℕ) ⊆ Finset.Icc 1 (2 * 3 ^ K) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    rcases hx with rfl | rfl <;> omega
  have hsum := Finset.sum_sdiff (f := fun j => Erdos291.L (2 * 3 ^ K) / j) hsub
  unfold Erdos291.a
  rw [← hsum]
  apply dvd_add
  · apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hj
    obtain ⟨⟨hj1, hjn⟩, hjne⟩ := hj
    push_neg at hjne
    obtain ⟨hne1, hne2⟩ := hjne
    apply three_dvd_L_div K j hj1 hjn
    rintro ⟨t, ht⟩
    have ht2 : t ≤ 2 := by
      have hle : 3 ^ K * t ≤ 3 ^ K * 2 := by
        calc 3 ^ K * t = j := ht.symm
          _ ≤ 2 * 3 ^ K := hjn
          _ = 3 ^ K * 2 := by ring
      exact Nat.le_of_mul_le_mul_left hle (by omega)
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · rw [mul_zero] at ht; omega
      · exact h
    have hcase : t = 1 ∨ t = 2 := by omega
    rcases hcase with rfl | rfl
    · exact hne1 (by rw [ht, mul_one])
    · exact hne2 (by rw [ht]; ring)
  · have hne : (3 : ℕ) ^ K ≠ 2 * 3 ^ K := by omega
    obtain ⟨M, hM⟩ : (2 * 3 ^ K) ∣ Erdos291.L (2 * 3 ^ K) := dvd_L (by omega) (le_refl _)
    have e1 : Erdos291.L (2 * 3 ^ K) / 3 ^ K = 2 * M := by
      rw [hM, show 2 * 3 ^ K * M = 3 ^ K * (2 * M) by ring]
      exact Nat.mul_div_cancel_left _ (by omega)
    have e2 : Erdos291.L (2 * 3 ^ K) / (2 * 3 ^ K) = M := by
      rw [hM]
      exact Nat.mul_div_cancel_left _ (by omega)
    rw [Finset.sum_pair hne, e1, e2]
    exact ⟨M, by ring⟩

theorem erdos_291.parts.ii :
    answer(True) ↔
      { n : ℕ | Nat.gcd (a n) (L n) > 1 }.Infinite := by
  constructor
  · intro _
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * 3 ^ (k + 1))
    · intro x y hxy
      simp only at hxy
      have h1 := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) hxy
      have h2 := Nat.pow_right_injective (by norm_num) h1
      omega
    · intro k
      simp only [Set.mem_setOf_eq]
      have h3a : 3 ∣ Erdos291.a (2 * 3 ^ (k + 1)) := three_dvd_a (k + 1)
      have h3L : 3 ∣ Erdos291.L (2 * 3 ^ (k + 1)) := by
        apply dvd_L (by norm_num)
        have h1 := Nat.le_self_pow (Nat.succ_ne_zero k) 3
        omega
      have hg : 3 ∣ Nat.gcd (Erdos291.a (2 * 3 ^ (k + 1))) (Erdos291.L (2 * 3 ^ (k + 1))) :=
        Nat.dvd_gcd h3a h3L
      have hgne : Nat.gcd (Erdos291.a (2 * 3 ^ (k + 1))) (Erdos291.L (2 * 3 ^ (k + 1))) ≠ 0 :=
        fun h => L_ne_zero _ (Nat.eq_zero_of_gcd_eq_zero_right h)
      have h3le := Nat.le_of_dvd (Nat.pos_of_ne_zero hgne) hg
      omega
  · intro _
    exact trivial

end Contribution.Erdos291PartsIi
