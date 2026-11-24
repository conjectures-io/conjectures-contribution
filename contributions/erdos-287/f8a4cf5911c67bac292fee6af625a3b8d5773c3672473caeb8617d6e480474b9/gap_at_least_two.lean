import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Erdős Problem 287: the lower bound `max_gap ≥ 2` (Erdős 1932)

Proves that `1` is never a sum of reciprocals of at least two consecutive integers `a, a+1, …`
with `a ≥ 2`, by the 2-adic "unique maximal valuation" argument, and deduces `2 ≤ max_gap`.
-/

namespace Contribution.Erdos287GapAtLeastTwo

/-- Same definition as `Erdos287.max_gap`. -/
def max_gap (k : ℕ) (s : Fin k → ℕ) : ℕ :=
   Finset.sup Finset.univ (fun i : Fin (k - 1) =>
      s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩)

/-- Between two distinct integers of equal 2-adic valuation `v` lies an integer of larger
2-adic valuation. -/
theorem two_adic_between {m n v : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m < n)
    (h1 : padicValNat 2 m = v) (h2 : padicValNat 2 n = v) :
    ∃ t, m < t ∧ t < n ∧ v < padicValNat 2 t := by
  have hd1 : 2 ^ v ∣ m := by rw [← h1]; exact pow_padicValNat_dvd
  have hd2 : 2 ^ v ∣ n := by rw [← h2]; exact pow_padicValNat_dvd
  have hnd1 : ¬ 2 ^ (v + 1) ∣ m := by rw [← h1]; exact pow_succ_padicValNat_not_dvd hm
  have hnd2 : ¬ 2 ^ (v + 1) ∣ n := by rw [← h2]; exact pow_succ_padicValNat_not_dvd hn
  obtain ⟨x, rfl⟩ := hd1
  obtain ⟨y, rfl⟩ := hd2
  have hxodd : x % 2 = 1 := by
    by_contra h
    apply hnd1
    obtain ⟨z, hz⟩ : 2 ∣ x := by omega
    exact ⟨z, by rw [hz, pow_succ]; ring⟩
  have hyodd : y % 2 = 1 := by
    by_contra h
    apply hnd2
    obtain ⟨z, hz⟩ : 2 ∣ y := by omega
    exact ⟨z, by rw [hz, pow_succ]; ring⟩
  have hp : 0 < 2 ^ v := by positivity
  have hxy : x < y := by
    by_contra h
    rw [not_lt] at h
    have := Nat.mul_le_mul_left (2 ^ v) h
    omega
  have hxy' : x + 1 < y := by omega
  obtain ⟨w, hw⟩ : 2 ∣ x + 1 := by omega
  have ht0 : 2 ^ v * (x + 1) ≠ 0 := by
    have : 0 < x + 1 := by omega
    positivity
  refine ⟨2 ^ v * (x + 1), by nlinarith, by nlinarith, ?_⟩
  have hdvd : 2 ^ (v + 1) ∣ 2 ^ v * (x + 1) :=
    ⟨w, by rw [hw, pow_succ]; ring⟩
  exact (padicValNat_dvd_iff_le ht0).mp hdvd

theorem no_consecutive_recip_sum {a k : ℕ} (ha : 2 ≤ a) (hk : 2 ≤ k) :
    ∑ i ∈ Finset.range k, (1 : ℚ) / ((a + i : ℕ) : ℚ) ≠ 1 := by
  intro hsum
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range k)
    (fun i => padicValNat 2 (a + i)) ⟨0, by simp; omega⟩
  have huniq : ∀ i ∈ Finset.range k, i ≠ j →
      padicValNat 2 (a + i) < padicValNat 2 (a + j) := by
    intro i hi hij
    have hle : padicValNat 2 (a + i) ≤ padicValNat 2 (a + j) := hjmax i hi
    by_contra hnot
    have heq : padicValNat 2 (a + i) = padicValNat 2 (a + j) :=
      le_antisymm hle (not_lt.mp hnot)
    have hik := Finset.mem_range.mp hi
    have hjk := Finset.mem_range.mp hj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · obtain ⟨t, h1, h2, h3⟩ := two_adic_between (m := a + i) (n := a + j)
        (by omega) (by omega) (by omega) heq rfl
      have ht : padicValNat 2 (a + (t - a)) ≤ padicValNat 2 (a + j) :=
        hjmax (t - a) (Finset.mem_range.mpr (by omega))
      have e : a + (t - a) = t := by omega
      rw [e] at ht
      omega
    · obtain ⟨t, h1, h2, h3⟩ := two_adic_between (m := a + j) (n := a + i)
        (by omega) (by omega) (by omega) rfl heq
      have ht : padicValNat 2 (a + (t - a)) ≤ padicValNat 2 (a + j) :=
        hjmax (t - a) (Finset.mem_range.mpr (by omega))
      have e : a + (t - a) = t := by omega
      rw [e] at ht
      omega
  have hpos : ∀ i : ℕ, (0 : ℚ) < (1 : ℚ) / ((a + i : ℕ) : ℚ) := fun i => by
    have : (0 : ℚ) < ((a + i : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < a + i)
    exact one_div_pos.mpr this
  have hval : ∀ i : ℕ, padicValRat 2 ((1 : ℚ) / ((a + i : ℕ) : ℚ)) =
      -(padicValNat 2 (a + i) : ℤ) := by
    intro i
    rw [one_div, padicValRat.inv, padicValRat.of_nat]
  have hne : ((Finset.range k).erase j).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hj]
    simp
    omega
  have hlt := padicValRat.lt_sum_of_lt (p := 2) (j := j)
    (F := fun i : ℕ => (1 : ℚ) / ((a + i : ℕ) : ℚ)) hne
    (fun i hi => by
      have hi' := Finset.mem_erase.mp hi
      have := huniq i hi'.2 hi'.1
      simp only [hval]
      omega) hpos
  have hsplit := Finset.add_sum_erase (Finset.range k)
    (fun i : ℕ => (1 : ℚ) / ((a + i : ℕ) : ℚ)) hj
  have hrest_pos : (0 : ℚ) < ∑ i ∈ (Finset.range k).erase j, (1 : ℚ) / ((a + i : ℕ) : ℚ) :=
    Finset.sum_pos (fun i _ => hpos i) hne
  have hval1 := padicValRat.add_eq_of_lt (p := 2)
    (q := (1 : ℚ) / ((a + j : ℕ) : ℚ))
    (r := ∑ i ∈ (Finset.range k).erase j, (1 : ℚ) / ((a + i : ℕ) : ℚ))
    (by have := hpos j; positivity) (hpos j).ne' hrest_pos.ne' hlt
  rw [hsplit, hsum, padicValRat.one, hval] at hval1
  have hzero : padicValNat 2 (a + j) = 0 := by omega
  obtain ⟨i0, hi0⟩ := hne
  have hi0' := Finset.mem_erase.mp hi0
  have := huniq i0 hi0'.2 hi0'.1
  omega

/-- Erdős 1932: `1` is not a sum of reciprocals of consecutive integers `> 1` (length ≥ 2),
i.e. `max_gap ≥ 2`. -/
theorem gap_at_least_two :
    ∀ (k : ℕ) (_ : 2 ≤ k) (s : Fin k → ℕ),
    StrictMono s → 1 < s ⟨0, by omega⟩ →
    ∑ i : Fin k, 1 / (s i : ℝ) = 1 →
    2 ≤ max_gap k s := by
  intro k hk s hmono h0 hsum
  by_contra hlt
  rw [not_le] at hlt
  have hgap : ∀ i : Fin (k - 1),
      s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩ ≤ 1 := by
    intro i
    have : s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩ ≤ max_gap k s :=
      Finset.le_sup (f := fun i : Fin (k - 1) =>
        s ⟨i.val + 1, by omega⟩ - s ⟨i.val, by omega⟩) (Finset.mem_univ i)
    omega
  have hstep : ∀ i (hi : i + 1 < k), s ⟨i + 1, hi⟩ = s ⟨i, by omega⟩ + 1 := by
    intro i hi
    have h1 := hgap ⟨i, by omega⟩
    have h2 : s ⟨i, by omega⟩ < s ⟨i + 1, hi⟩ := hmono (by simp [Fin.lt_def])
    simp only at h1
    omega
  have hform : ∀ i (hi : i < k), s ⟨i, hi⟩ = s ⟨0, by omega⟩ + i := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ n ih =>
      intro hi
      rw [hstep n hi, ih (by omega)]
      ring
  set a := s ⟨0, by omega⟩ with ha
  have hq : ∑ i ∈ Finset.range k, (1 : ℚ) / ((a + i : ℕ) : ℚ) = 1 := by
    have hr : ∑ i : Fin k, (1 : ℝ) / (s i : ℝ) =
        ((∑ i ∈ Finset.range k, (1 : ℚ) / ((a + i : ℕ) : ℚ) : ℚ) : ℝ) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => (1 : ℚ) / ((a + i : ℕ) : ℚ)) k]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hform i.val i.isLt]
      push_cast
      rfl
    have : ((∑ i ∈ Finset.range k, (1 : ℚ) / ((a + i : ℕ) : ℚ) : ℚ) : ℝ) = 1 := by
      rw [← hr]; exact hsum
    exact_mod_cast this
  exact no_consecutive_recip_sum (a := a) (by omega) hk hq

end Contribution.Erdos287GapAtLeastTwo
