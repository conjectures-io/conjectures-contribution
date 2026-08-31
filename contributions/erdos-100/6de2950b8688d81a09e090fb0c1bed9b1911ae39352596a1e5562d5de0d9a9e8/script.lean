import FormalConjectures.ErdosProblems.«100»

/-!
# A small API for `Erdos100.DistancesSeparated`

**This is a pipeline test contribution.** It is deliberately elementary: its purpose is to
exercise the submission and verification pipeline end to end with a file that is correct,
self-contained and free of holes. It is offered as real (if modest) API all the same — every
declaration below is proved, and none of them restate an existing Mathlib lemma.

`Erdos100.DistancesSeparated A` says that any two distances realised inside `A` are either
equal or at least `1` apart. Erdős problem 100 asks whether such a set of `n` points must have
diameter `≥ C * n`. Working with the definition directly is awkward, because it is stated as a
four-point implication whose hypothesis is a disequality. These four lemmas are the shapes one
actually wants at hand:

* `distancesSeparated_of_subset` — the property is hereditary, so an argument may pass to a
  convenient subset (an extremal configuration, a subset in general position) without losing it.
* `distancesSeparated_of_card_le_one` — the degenerate cases hold vacuously, which is what
  clears the base case of an induction on `A.card`.
* `eq_dist_of_abs_sub_lt_one` — the contrapositive. Separation is nearly always used to
  *identify* two distances that have been shown to be close, and this is that direction.
* `dist_le_diam` — the bridge to the conclusion: a lower bound on the diameter of a finite set
  is obtained by exhibiting one long distance, and this discharges the boundedness side
  condition of `Metric.dist_le_diam_of_mem` from finiteness.

Nothing here approaches the conjecture itself; no statement mentions `n`, `C`, or an
asymptotic.
-/

open scoped EuclideanGeometry

namespace Contribution.Erdos100Separated

open Erdos100

/-- Separation is hereditary: a subset of a separated set is separated. -/
theorem distancesSeparated_of_subset {A B : Finset ℝ²} (hBA : B ⊆ A)
    (hA : DistancesSeparated A) : DistancesSeparated B :=
  fun p₁ q₁ p₂ q₂ hp₁ hq₁ hp₂ hq₂ hne =>
    hA p₁ q₁ p₂ q₂ (hBA hp₁) (hBA hq₁) (hBA hp₂) (hBA hq₂) hne

/-- A set with at most one point realises only the distance `0`, so it is separated. -/
theorem distancesSeparated_of_card_le_one {A : Finset ℝ²} (hcard : A.card ≤ 1) :
    DistancesSeparated A := by
  rw [Finset.card_le_one] at hcard
  intro p₁ q₁ p₂ q₂ hp₁ hq₁ hp₂ hq₂ hne
  have h₁ : dist p₁ q₁ = 0 := dist_eq_zero.mpr (hcard p₁ hp₁ q₁ hq₁)
  have h₂ : dist p₂ q₂ = 0 := dist_eq_zero.mpr (hcard p₂ hp₂ q₂ hq₂)
  exact absurd (h₁.trans h₂.symm) hne

/-- The usable form of separation: two distances less than `1` apart are equal. -/
theorem eq_dist_of_abs_sub_lt_one {A : Finset ℝ²} (hA : DistancesSeparated A)
    {p₁ q₁ p₂ q₂ : ℝ²} (hp₁ : p₁ ∈ A) (hq₁ : q₁ ∈ A) (hp₂ : p₂ ∈ A) (hq₂ : q₂ ∈ A)
    (hclose : |dist p₁ q₁ - dist p₂ q₂| < 1) : dist p₁ q₁ = dist p₂ q₂ := by
  by_contra hne
  exact absurd (hA p₁ q₁ p₂ q₂ hp₁ hq₁ hp₂ hq₂ hne) (not_le.mpr hclose)

/-- Every distance realised in a finite set is at most its diameter; finiteness discharges
the boundedness hypothesis of `Metric.dist_le_diam_of_mem`. -/
theorem dist_le_diam {A : Finset ℝ²} {p q : ℝ²} (hp : p ∈ A) (hq : q ∈ A) :
    dist p q ≤ Metric.diam (A : Set ℝ²) :=
  Metric.dist_le_diam_of_mem A.finite_toSet.isBounded
    (Finset.mem_coe.mpr hp) (Finset.mem_coe.mpr hq)

end Contribution.Erdos100Separated
