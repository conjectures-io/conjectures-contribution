import Mathlib
import FormalConjectures.ErdosProblems.«359»

/-!
# Erdős Problem 359: the first eight terms of the greedy sequence

For `IsGoodFor A 1` we derive `A 0, …, A 7 = 1, 2, 4, 5, 8, 10, 14, 15` and hence the
image equality of `erdos_359.variants.isGoodFor_1_low_values`, sorry'd in the pool file.
Each step evaluates every consecutive-sum over the determined prefix: candidates below
the true next term are eliminated by their explicit representations, and the true term
is checked non-representable against all of them.
-/

open Erdos359

namespace Contribution.Erdos359LowValues

/-- `Finset.Icc a b ⊆ Finset.Iic j` holds iff the interval is empty or `b ≤ j`. -/
lemma icc_subset_iic {a b j : ℕ} : Finset.Icc a b ⊆ Finset.Iic j ↔ b < a ∨ b ≤ j := by
  constructor
  · intro h
    rcases Nat.lt_or_ge b a with hab | hab
    · exact Or.inl hab
    · exact Or.inr (Finset.mem_Iic.mp (h (Finset.mem_Icc.mpr ⟨hab, le_refl b⟩)))
  · intro h x hx
    rcases h with h | h
    · exact absurd (Finset.mem_Icc.mp hx) (by omega)
    · exact Finset.mem_Iic.mpr ((Finset.mem_Icc.mp hx).2.trans h)

lemma val1 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) : A 1 = 2 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 0
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have hv : A 0 < 2 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 0 → 2 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h0] at hgt
  omega

lemma val2 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) (h1 : A 1 = 2) : A 2 = 4 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 1
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have e0_1 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_0, h1]
  have e1_1 : ∑ i ∈ Finset.Icc 1 1, A i = 2 := by rw [Finset.Icc_self, Finset.sum_singleton, h1]
  have hv : A 1 < 4 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 1 → 4 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0, e0_1, e1_1] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h1] at hgt
  by_contra hlt
  push_neg at hlt
  interval_cases hAv : (A 2)
  · exact hmem.2 0 1 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e0_1])

lemma val3 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) (h1 : A 1 = 2) (h2 : A 2 = 4) : A 3 = 5 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 2
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have e0_1 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_0, h1]
  have e0_2 : ∑ i ∈ Finset.Icc 0 2, A i = 7 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_1, h2]
  have e1_1 : ∑ i ∈ Finset.Icc 1 1, A i = 2 := by rw [Finset.Icc_self, Finset.sum_singleton, h1]
  have e1_2 : ∑ i ∈ Finset.Icc 1 2, A i = 6 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_1, h2]
  have e2_2 : ∑ i ∈ Finset.Icc 2 2, A i = 4 := by rw [Finset.Icc_self, Finset.sum_singleton, h2]
  have hv : A 2 < 5 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 2 → 5 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0, e0_1, e0_2, e1_1, e1_2, e2_2] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h2] at hgt
  omega

lemma val4 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) (h1 : A 1 = 2) (h2 : A 2 = 4) (h3 : A 3 = 5) : A 4 = 8 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 3
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have e0_1 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_0, h1]
  have e0_2 : ∑ i ∈ Finset.Icc 0 2, A i = 7 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_1, h2]
  have e0_3 : ∑ i ∈ Finset.Icc 0 3, A i = 12 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_2, h3]
  have e1_1 : ∑ i ∈ Finset.Icc 1 1, A i = 2 := by rw [Finset.Icc_self, Finset.sum_singleton, h1]
  have e1_2 : ∑ i ∈ Finset.Icc 1 2, A i = 6 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_1, h2]
  have e1_3 : ∑ i ∈ Finset.Icc 1 3, A i = 11 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_2, h3]
  have e2_2 : ∑ i ∈ Finset.Icc 2 2, A i = 4 := by rw [Finset.Icc_self, Finset.sum_singleton, h2]
  have e2_3 : ∑ i ∈ Finset.Icc 2 3, A i = 9 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_2, h3]
  have e3_3 : ∑ i ∈ Finset.Icc 3 3, A i = 5 := by rw [Finset.Icc_self, Finset.sum_singleton, h3]
  have hv : A 3 < 8 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 3 → 8 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0, e0_1, e0_2, e0_3, e1_1, e1_2, e1_3, e2_2, e2_3, e3_3] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h3] at hgt
  by_contra hlt
  push_neg at hlt
  interval_cases hAv : (A 4)
  · exact hmem.2 1 2 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e1_2])
  · exact hmem.2 0 2 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e0_2])

lemma val5 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) (h1 : A 1 = 2) (h2 : A 2 = 4) (h3 : A 3 = 5) (h4 : A 4 = 8) : A 5 = 10 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 4
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have e0_1 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_0, h1]
  have e0_2 : ∑ i ∈ Finset.Icc 0 2, A i = 7 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_1, h2]
  have e0_3 : ∑ i ∈ Finset.Icc 0 3, A i = 12 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_2, h3]
  have e0_4 : ∑ i ∈ Finset.Icc 0 4, A i = 20 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_3, h4]
  have e1_1 : ∑ i ∈ Finset.Icc 1 1, A i = 2 := by rw [Finset.Icc_self, Finset.sum_singleton, h1]
  have e1_2 : ∑ i ∈ Finset.Icc 1 2, A i = 6 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_1, h2]
  have e1_3 : ∑ i ∈ Finset.Icc 1 3, A i = 11 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_2, h3]
  have e1_4 : ∑ i ∈ Finset.Icc 1 4, A i = 19 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_3, h4]
  have e2_2 : ∑ i ∈ Finset.Icc 2 2, A i = 4 := by rw [Finset.Icc_self, Finset.sum_singleton, h2]
  have e2_3 : ∑ i ∈ Finset.Icc 2 3, A i = 9 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_2, h3]
  have e2_4 : ∑ i ∈ Finset.Icc 2 4, A i = 17 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_3, h4]
  have e3_3 : ∑ i ∈ Finset.Icc 3 3, A i = 5 := by rw [Finset.Icc_self, Finset.sum_singleton, h3]
  have e3_4 : ∑ i ∈ Finset.Icc 3 4, A i = 13 := by rw [Finset.sum_Icc_succ_top (by norm_num), e3_3, h4]
  have e4_4 : ∑ i ∈ Finset.Icc 4 4, A i = 8 := by rw [Finset.Icc_self, Finset.sum_singleton, h4]
  have hv : A 4 < 10 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 4 → 10 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0, e0_1, e0_2, e0_3, e0_4, e1_1, e1_2, e1_3, e1_4, e2_2, e2_3, e2_4, e3_3, e3_4, e4_4] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h4] at hgt
  by_contra hlt
  push_neg at hlt
  interval_cases hAv : (A 5)
  · exact hmem.2 2 3 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e2_3])

lemma val6 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) (h1 : A 1 = 2) (h2 : A 2 = 4) (h3 : A 3 = 5) (h4 : A 4 = 8) (h5 : A 5 = 10) : A 6 = 14 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 5
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have e0_1 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_0, h1]
  have e0_2 : ∑ i ∈ Finset.Icc 0 2, A i = 7 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_1, h2]
  have e0_3 : ∑ i ∈ Finset.Icc 0 3, A i = 12 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_2, h3]
  have e0_4 : ∑ i ∈ Finset.Icc 0 4, A i = 20 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_3, h4]
  have e0_5 : ∑ i ∈ Finset.Icc 0 5, A i = 30 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_4, h5]
  have e1_1 : ∑ i ∈ Finset.Icc 1 1, A i = 2 := by rw [Finset.Icc_self, Finset.sum_singleton, h1]
  have e1_2 : ∑ i ∈ Finset.Icc 1 2, A i = 6 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_1, h2]
  have e1_3 : ∑ i ∈ Finset.Icc 1 3, A i = 11 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_2, h3]
  have e1_4 : ∑ i ∈ Finset.Icc 1 4, A i = 19 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_3, h4]
  have e1_5 : ∑ i ∈ Finset.Icc 1 5, A i = 29 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_4, h5]
  have e2_2 : ∑ i ∈ Finset.Icc 2 2, A i = 4 := by rw [Finset.Icc_self, Finset.sum_singleton, h2]
  have e2_3 : ∑ i ∈ Finset.Icc 2 3, A i = 9 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_2, h3]
  have e2_4 : ∑ i ∈ Finset.Icc 2 4, A i = 17 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_3, h4]
  have e2_5 : ∑ i ∈ Finset.Icc 2 5, A i = 27 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_4, h5]
  have e3_3 : ∑ i ∈ Finset.Icc 3 3, A i = 5 := by rw [Finset.Icc_self, Finset.sum_singleton, h3]
  have e3_4 : ∑ i ∈ Finset.Icc 3 4, A i = 13 := by rw [Finset.sum_Icc_succ_top (by norm_num), e3_3, h4]
  have e3_5 : ∑ i ∈ Finset.Icc 3 5, A i = 23 := by rw [Finset.sum_Icc_succ_top (by norm_num), e3_4, h5]
  have e4_4 : ∑ i ∈ Finset.Icc 4 4, A i = 8 := by rw [Finset.Icc_self, Finset.sum_singleton, h4]
  have e4_5 : ∑ i ∈ Finset.Icc 4 5, A i = 18 := by rw [Finset.sum_Icc_succ_top (by norm_num), e4_4, h5]
  have e5_5 : ∑ i ∈ Finset.Icc 5 5, A i = 10 := by rw [Finset.Icc_self, Finset.sum_singleton, h5]
  have hv : A 5 < 14 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 5 → 14 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0, e0_1, e0_2, e0_3, e0_4, e0_5, e1_1, e1_2, e1_3, e1_4, e1_5, e2_2, e2_3, e2_4, e2_5, e3_3, e3_4, e3_5, e4_4, e4_5, e5_5] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h5] at hgt
  by_contra hlt
  push_neg at hlt
  interval_cases hAv : (A 6)
  · exact hmem.2 1 3 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e1_3])
  · exact hmem.2 0 3 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e0_3])
  · exact hmem.2 3 4 (icc_subset_iic.mpr (Or.inr (by omega))) (by rw [e3_4])

lemma val7 {A : ℕ → ℕ} (hA : IsGoodFor A 1) (h0 : A 0 = 1) (h1 : A 1 = 2) (h2 : A 2 = 4) (h3 : A 3 = 5) (h4 : A 4 = 8) (h5 : A 5 = 10) (h6 : A 6 = 14) : A 7 = 15 := by
  obtain ⟨h0', hmono, hL⟩ := hA
  have hLj := hL 6
  simp only [Nat.reduceAdd] at hLj
  have hmem := hLj.1
  have e0_0 : ∑ i ∈ Finset.Icc 0 0, A i = 1 := by rw [Finset.Icc_self, Finset.sum_singleton, h0]
  have e0_1 : ∑ i ∈ Finset.Icc 0 1, A i = 3 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_0, h1]
  have e0_2 : ∑ i ∈ Finset.Icc 0 2, A i = 7 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_1, h2]
  have e0_3 : ∑ i ∈ Finset.Icc 0 3, A i = 12 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_2, h3]
  have e0_4 : ∑ i ∈ Finset.Icc 0 4, A i = 20 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_3, h4]
  have e0_5 : ∑ i ∈ Finset.Icc 0 5, A i = 30 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_4, h5]
  have e0_6 : ∑ i ∈ Finset.Icc 0 6, A i = 44 := by rw [Finset.sum_Icc_succ_top (by norm_num), e0_5, h6]
  have e1_1 : ∑ i ∈ Finset.Icc 1 1, A i = 2 := by rw [Finset.Icc_self, Finset.sum_singleton, h1]
  have e1_2 : ∑ i ∈ Finset.Icc 1 2, A i = 6 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_1, h2]
  have e1_3 : ∑ i ∈ Finset.Icc 1 3, A i = 11 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_2, h3]
  have e1_4 : ∑ i ∈ Finset.Icc 1 4, A i = 19 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_3, h4]
  have e1_5 : ∑ i ∈ Finset.Icc 1 5, A i = 29 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_4, h5]
  have e1_6 : ∑ i ∈ Finset.Icc 1 6, A i = 43 := by rw [Finset.sum_Icc_succ_top (by norm_num), e1_5, h6]
  have e2_2 : ∑ i ∈ Finset.Icc 2 2, A i = 4 := by rw [Finset.Icc_self, Finset.sum_singleton, h2]
  have e2_3 : ∑ i ∈ Finset.Icc 2 3, A i = 9 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_2, h3]
  have e2_4 : ∑ i ∈ Finset.Icc 2 4, A i = 17 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_3, h4]
  have e2_5 : ∑ i ∈ Finset.Icc 2 5, A i = 27 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_4, h5]
  have e2_6 : ∑ i ∈ Finset.Icc 2 6, A i = 41 := by rw [Finset.sum_Icc_succ_top (by norm_num), e2_5, h6]
  have e3_3 : ∑ i ∈ Finset.Icc 3 3, A i = 5 := by rw [Finset.Icc_self, Finset.sum_singleton, h3]
  have e3_4 : ∑ i ∈ Finset.Icc 3 4, A i = 13 := by rw [Finset.sum_Icc_succ_top (by norm_num), e3_3, h4]
  have e3_5 : ∑ i ∈ Finset.Icc 3 5, A i = 23 := by rw [Finset.sum_Icc_succ_top (by norm_num), e3_4, h5]
  have e3_6 : ∑ i ∈ Finset.Icc 3 6, A i = 37 := by rw [Finset.sum_Icc_succ_top (by norm_num), e3_5, h6]
  have e4_4 : ∑ i ∈ Finset.Icc 4 4, A i = 8 := by rw [Finset.Icc_self, Finset.sum_singleton, h4]
  have e4_5 : ∑ i ∈ Finset.Icc 4 5, A i = 18 := by rw [Finset.sum_Icc_succ_top (by norm_num), e4_4, h5]
  have e4_6 : ∑ i ∈ Finset.Icc 4 6, A i = 32 := by rw [Finset.sum_Icc_succ_top (by norm_num), e4_5, h6]
  have e5_5 : ∑ i ∈ Finset.Icc 5 5, A i = 10 := by rw [Finset.Icc_self, Finset.sum_singleton, h5]
  have e5_6 : ∑ i ∈ Finset.Icc 5 6, A i = 24 := by rw [Finset.sum_Icc_succ_top (by norm_num), e5_5, h6]
  have e6_6 : ∑ i ∈ Finset.Icc 6 6, A i = 14 := by rw [Finset.Icc_self, Finset.sum_singleton, h6]
  have hv : A 6 < 15 ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic 6 → 15 ≠ ∑ i ∈ Finset.Icc a b, A i := by
    refine ⟨by omega, ?_⟩
    intro a b hab
    rcases icc_subset_iic.mp hab with hcase | hcase
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
    · rcases Nat.lt_or_ge b a with hab2 | hab2
      · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; omega
      · interval_cases b <;> interval_cases a <;> simp only [e0_0, e0_1, e0_2, e0_3, e0_4, e0_5, e0_6, e1_1, e1_2, e1_3, e1_4, e1_5, e1_6, e2_2, e2_3, e2_4, e2_5, e2_6, e3_3, e3_4, e3_5, e3_6, e4_4, e4_5, e4_6, e5_5, e5_6, e6_6] <;> omega
  refine le_antisymm (hLj.2 hv) ?_
  have hgt := hmem.1
  rw [h6] at hgt
  omega

theorem isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  have h0 : A 0 = 1 := hA.1
  have h1 : A 1 = 2 := val1 hA h0
  have h2 : A 2 = 4 := val2 hA h0 h1
  have h3 : A 3 = 5 := val3 hA h0 h1 h2
  have h4 : A 4 = 8 := val4 hA h0 h1 h2 h3
  have h5 : A 5 = 10 := val5 hA h0 h1 h2 h3 h4
  have h6 : A 6 = 14 := val6 hA h0 h1 h2 h3 h4 h5
  have h7 : A 7 = 15 := val7 hA h0 h1 h2 h3 h4 h5 h6
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk7 : k ≤ 7 := hk
    interval_cases k <;> simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · intro hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> subst hx
    · exact ⟨0, by norm_num, h0⟩
    · exact ⟨1, by norm_num, h1⟩
    · exact ⟨2, by norm_num, h2⟩
    · exact ⟨3, by norm_num, h3⟩
    · exact ⟨4, by norm_num, h4⟩
    · exact ⟨5, by norm_num, h5⟩
    · exact ⟨6, by norm_num, h6⟩
    · exact ⟨7, by norm_num, h7⟩

end Contribution.Erdos359LowValues

