import FormalConjectures.ErdosProblems.«535»

/-!
# Erdős 535: elementary structural facts about the extremal function

The open problem asks for a much sharper asymptotic upper bound.  This file
establishes the basic finite bound, monotonicity in both parameters, an
extremal-witness interface for the defining supremum, and the exact value in
the vacuous range where an `r`-element subset cannot occur.
-/

namespace Contribution.Erdos535BasicAPI

open Erdos535

/-- Every admissible family in the definition of `f r N` lies in `{1, ..., N}`,
so its cardinality is at most `N`. -/
theorem f_le (r N : ℕ) : f r N ≤ N := by
  unfold f
  apply csSup_le'
  rintro k ⟨A, hA, _havoid, rfl⟩
  calc
    A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
    _ ≤ N := by simp

/-- Enlarging the ambient interval cannot decrease the extremal value. -/
theorem f_mono_right (r : ℕ) {N M : ℕ} (hNM : N ≤ M) : f r N ≤ f r M := by
  unfold f
  apply csSup_le'
  rintro k ⟨A, hA, havoid, hcard⟩
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro j ⟨B, hB, _havoidB, rfl⟩
    calc
      B.card ≤ (Finset.Icc 1 M).card := Finset.card_le_card hB
      _ ≤ M := by simp
  · refine ⟨A, ?_, havoid, hcard⟩
    intro a ha
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hA ha)).1,
      (Finset.mem_Icc.mp (hA ha)).2.trans hNM⟩

/-- Increasing the forbidden-set size weakens the avoidance condition, so the
extremal value cannot decrease. -/
theorem f_mono_left {r s : ℕ} (hrs : r ≤ s) (N : ℕ) : f r N ≤ f s N := by
  unfold f
  apply csSup_le'
  rintro k ⟨A, hA, havoid, hcard⟩
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro j ⟨B, hB, _havoidB, rfl⟩
    calc
      B.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hB
      _ ≤ N := by simp
  · refine ⟨A, hA, ?_, hcard⟩
    intro S hSA hScard
    rintro ⟨d, hd⟩
    obtain ⟨T, hTS, hTcard⟩ :=
      Finset.exists_subset_card_eq (show r ≤ S.card by omega)
    apply havoid T (hTS.trans hSA) hTcard
    exact ⟨d, Set.Pairwise.mono (by simpa using hTS) hd⟩

/-- For `r ≥ 1`, the supremum in the definition of `f r N` is attained by an
admissible finite set. -/
theorem exists_extremal (r N : ℕ) (hr : 1 ≤ r) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ S ⊆ A, S.card = r →
        ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
      A.card = f r N := by
  let K : Set ℕ := {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = r →
      ¬ (∃ d, (S : Set ℕ).Pairwise fun a b => Nat.gcd a b = d)) ∧
    A.card = k}
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, by simp, ?_, by simp⟩
    · intro S hS hcard
      have : S = ∅ := Finset.subset_empty.mp hS
      subst S
      simp at hcard
      omega
  have hK_bdd : BddAbove K := by
    refine ⟨N, ?_⟩
    rintro k ⟨A, hA, _havoid, rfl⟩
    calc
      A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
      _ ≤ N := by simp
  simpa [f, K] using Nat.sSup_mem hK_nonempty hK_bdd

/-- The first `min N (r - 1)` positive integers are always admissible: they do
not contain enough elements to form a forbidden `r`-set. -/
theorem min_sub_one_le_f (r N : ℕ) (hr : 1 ≤ r) : min N (r - 1) ≤ f r N := by
  unfold f
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro k ⟨A, hA, _havoid, rfl⟩
    calc
      A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
      _ ≤ N := by simp
  · refine ⟨Finset.Icc 1 (min N (r - 1)), ?_, ?_, by simp⟩
    · intro a ha
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
        (Finset.mem_Icc.mp ha).2.trans (min_le_left _ _)⟩
    · intro S hS hcard _hconstant
      have hSk : S.card ≤ min N (r - 1) := by
        calc
          S.card ≤ (Finset.Icc 1 (min N (r - 1))).card := Finset.card_le_card hS
          _ ≤ min N (r - 1) := by simp
      have hkr : min N (r - 1) < r := by omega
      omega

/-- If the requested forbidden subset is larger than the entire interval,
the full interval is admissible and hence `f r N = N`. -/
theorem f_eq_of_lt (r N : ℕ) (hNr : N < r) : f r N = N := by
  apply Nat.le_antisymm (f_le r N)
  unfold f
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro k ⟨A, hA, _havoid, rfl⟩
    calc
      A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
      _ ≤ N := by simp
  · refine ⟨Finset.Icc 1 N, Finset.Subset.rfl, ?_, by simp⟩
    intro S hS hcard _hconstant
    have hSN : S.card ≤ N := by
      calc
        S.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hS
        _ ≤ N := by simp
    omega

end Contribution.Erdos535BasicAPI
