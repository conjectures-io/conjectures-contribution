import Mathlib
import FormalConjectures.GreensOpenProblems.«72»

/-!
# Green's Problem 72: the pigeonhole bound `AllowedSetSize k N ≤ (k − 1) · N`

A set with no `k` points on a common line has at most `k − 1` points in each of the `N`
vertical lines of the grid, hence at most `(k − 1) · N` points in total.
-/

open Finset

namespace Contribution.Green72Bound

/-- Any set of points on the vertical line `x = c` is collinear. -/
lemma collinear_vertical (c : ℝ) {S : Set (ℝ × ℝ)} (hS : ∀ p ∈ S, p.1 = c) :
    Collinear ℝ S := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨(c, 0), (0, 1), ?_⟩
  rintro ⟨x, y⟩ hp
  have hx : x = c := hS ⟨x, y⟩ hp
  subst hx
  exact ⟨y, by simp [Prod.ext_iff]⟩

theorem allowedSetSize_le {k : ℕ} {N : ℕ} (h : k ≤ N) :
    Green72.AllowedSetSize k N ≤ (k - 1) * N := by
  unfold Green72.AllowedSetSize
  apply csSup_le'
  rintro r ⟨s, rfl, hs⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: the empty subset already violates `not_collinear`
    exfalso
    refine hs.not_collinear (Finset.empty_subset s) (by simp [hk0]) ?_
    have : {r : ℝ × ℝ | ∃ i ∈ (∅ : Finset (ℕ × ℕ)), r = ((i.1 : ℝ), (i.2 : ℝ))} = ∅ := by
      simp
    rw [this]
    exact collinear_empty ℝ _
  · have hmaps : Set.MapsTo Prod.fst ↑s ↑(Finset.range N) := fun p hp =>
      Finset.mem_coe.mpr (Finset.mem_range.mpr (hs.is_bounded p hp).1)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfiber : ∀ b ∈ Finset.range N, ({a ∈ s | a.1 = b}).card ≤ k - 1 := by
      intro b _
      by_contra hgt
      push_neg at hgt
      have hk_le : k ≤ ({a ∈ s | a.1 = b}).card := by omega
      obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hk_le
      refine hs.not_collinear (htsub.trans (Finset.filter_subset _ _)) htcard ?_
      refine collinear_vertical (b : ℝ) ?_
      rintro ⟨x, y⟩ ⟨i, hit, heq⟩
      have hib : i.1 = b := (Finset.mem_filter.mp (htsub hit)).2
      have hx : x = (i.1 : ℝ) := congrArg Prod.fst heq
      simp [hx, hib]
    calc ∑ b ∈ Finset.range N, ({a ∈ s | a.1 = b}).card
        ≤ ∑ _b ∈ Finset.range N, (k - 1) := Finset.sum_le_sum hfiber
      _ = (k - 1) * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

end Contribution.Green72Bound

