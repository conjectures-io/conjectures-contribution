import FormalConjectures.GreensOpenProblems.«40»

/-!
# Green 40 sphere-covering lower bounds

The elementary counting lower bound is the fixed half of the conjectured
equality `Green40.f 2 = 1`.  These lemmas isolate that half so a later solver
only has to construct a subsequence of covering subspaces with density at most
one.
-/

namespace Contribution.Green40FTwoEqOne

open Filter Set
open scoped ENNReal Pointwise

/-- A finite sumset that covers the ambient type has at most as many points as
the product of the two source sets.  This is the counting map used by the
sphere-covering bound. -/
theorem card_le_card_mul_of_add_eq_univ {α : Type*} [Add α] [Finite α]
    (A B : Set α) (hcover : A + B = Set.univ) :
    Nat.card α ≤ Nat.card A * Nat.card B := by
  let addMap : A × B → α := fun p => p.1.1 + p.2.1
  have hsurj : Function.Surjective addMap := by
    intro x
    have hx : x ∈ A + B := by rw [hcover]; exact Set.mem_univ x
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  simpa [Nat.card_prod] using Nat.card_le_card_of_surjective addMap hsurj

/-- Every covering subspace obeys the sphere-covering cardinality bound. -/
theorem coveringSubspace_card_bound (n r : ℕ)
    (V : Submodule (ZMod 2) (𝔽₂ n)) (hV : Green40.IsCoveringSubspace n r V) :
    2 ^ n ≤ Nat.card V * Nat.card (Green40.hammingBall n r) := by
  have h := card_le_card_mul_of_add_eq_univ
    (A := (V : Set (𝔽₂ n))) (B := Green40.hammingBall n r) hV
  simpa [Nat.card_eq_fintype_card] using h

/-- The density of each individual covering subspace is at least one. -/
theorem one_le_coveringSubspace_density (n r : ℕ)
    (V : Submodule (ZMod 2) (𝔽₂ n)) (hV : Green40.IsCoveringSubspace n r V) :
    (1 : ℝ≥0∞) ≤
      (Nat.card V : ℝ≥0∞) * (Nat.card (Green40.hammingBall n r) : ℝ≥0∞) /
        (2 ^ n : ℝ≥0∞) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  simp only [one_mul]
  exact_mod_cast coveringSubspace_card_bound n r V hV

/-- The minimum density at every finite length is at least one. -/
theorem one_le_minDensity (n r : ℕ) : (1 : ℝ≥0∞) ≤ Green40.minDensity n r := by
  rw [Green40.minDensity]
  refine le_iInf fun V => ?_
  refine le_iInf fun hV => ?_
  exact one_le_coveringSubspace_density n r V hV

/-- The sphere-covering lower bound survives the liminf defining `Green40.f`. -/
theorem one_le_f (r : ℕ) : (1 : ℝ≥0∞) ≤ Green40.f r := by
  rw [Green40.f]
  calc
    (1 : ℝ≥0∞) ≤ ⨅ n, Green40.minDensity n r := le_iInf fun n => one_le_minDensity n r
    _ ≤ liminf (fun n => Green40.minDensity n r) atTop := iInf_le_liminf

/-- Green 40 at radius two is therefore reduced to the matching upper bound. -/
theorem f_two_eq_one_iff_le_one : Green40.f 2 = 1 ↔ Green40.f 2 ≤ 1 := by
  constructor
  · intro h
    exact h.le
  · intro h
    exact le_antisymm h (one_le_f 2)

end Contribution.Green40FTwoEqOne
