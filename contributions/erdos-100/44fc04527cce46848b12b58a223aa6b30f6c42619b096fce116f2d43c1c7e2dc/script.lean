import FormalConjectures.ErdosProblems.«100»

/-!
# Counting bounds for `EuclideanGeometry.distinctDistances`

**This is a pipeline test contribution.** Its purpose is to exercise the submission and
verification pipeline end to end with a file that is correct, self-contained and free of holes.
It is offered as real (if modest) API all the same — every declaration below is proved.

Erdős problem 100 concerns how spread out a planar set must be when its distances are
`1`-separated. The counting side of that question runs through
`EuclideanGeometry.distinctDistances X`, the number of distinct values `dist p q` takes over
ordered pairs of distinct points of `X`. That definition is an image cardinality, and the three
facts one reaches for first are the trivial upper bound, monotonicity, and the degenerate case:

* `distinctDistances_le_card_offDiag` — the bound straight from `Finset.card_image_le`.
* `distinctDistances_le_card_mul_pred` — the same bound in the `n(n-1)` form the literature
  states it in, which is what an asymptotic argument actually needs.
* `distinctDistances_mono` — passing to a subset can only lose distances, so an argument may
  restrict to a convenient subconfiguration.
* `distinctDistances_eq_zero_of_card_le_one` — the base case of an induction on `#X`.

Nothing here approaches the conjecture; no statement mentions a constant or an asymptotic.
-/

open scoped EuclideanGeometry Finset

namespace Contribution.Erdos100Counting

open EuclideanGeometry

/-- Distinct distances are the image of the off-diagonal, so there are at most as many of them
as there are ordered pairs of distinct points. -/
theorem distinctDistances_le_card_offDiag (X : Finset ℝ²) :
    distinctDistances X ≤ #X.offDiag :=
  Finset.card_image_le

/-- The same bound written as `n * (n - 1)`. -/
theorem distinctDistances_le_card_mul_pred (X : Finset ℝ²) :
    distinctDistances X ≤ #X * (#X - 1) := by
  refine (distinctDistances_le_card_offDiag X).trans ?_
  rw [Finset.offDiag_card, Nat.mul_sub_one]

/-- A subset realises no more distances than the set it sits in. -/
theorem distinctDistances_mono {X Y : Finset ℝ²} (hXY : X ⊆ Y) :
    distinctDistances X ≤ distinctDistances Y :=
  Finset.card_le_card (Finset.image_subset_image (Finset.offDiag_mono hXY))

/-- Fewer than two points realise no distances at all. -/
theorem distinctDistances_eq_zero_of_card_le_one {X : Finset ℝ²} (hX : #X ≤ 1) :
    distinctDistances X = 0 := by
  refine Nat.le_zero.mp ((distinctDistances_le_card_offDiag X).trans ?_)
  rw [Finset.offDiag_card]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hX with h | h <;> simp [h]

end Contribution.Erdos100Counting
