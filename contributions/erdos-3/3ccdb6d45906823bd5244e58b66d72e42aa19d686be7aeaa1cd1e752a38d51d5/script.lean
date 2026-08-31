import Mathlib

/-!
# Sum-free sets of naturals

A small, reusable interface for the sum-free condition that recurs across the
additive Erdős problems: closure under subsets, the canonical odd-numbers
witness, and the negation form a later solver can apply directly.
-/

namespace ConjecturesContribution.SumFree

/-- `S` is sum-free when no two of its elements (not necessarily distinct) add
to an element of `S`. -/
def IsSumFree (S : Set ℕ) : Prop :=
  ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ S → a + b ∉ S

/-- Sum-freeness passes to subsets. -/
theorem isSumFree_subset {S T : Set ℕ} (hT : T ⊆ S) (hS : IsSumFree S) :
    IsSumFree T :=
  fun _ ha _ hb hab => hS (hT ha) (hT hb) (hT hab)

/-- The odd naturals are sum-free: the sum of two odds is even. -/
theorem isSumFree_setOf_odd : IsSumFree {n : ℕ | Odd n} := by
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb hab
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  obtain ⟨j, hj⟩ := hab
  omega

/-- The contrapositive, in the shape a solver usually has it: one explicit
solution to `a + b = c` refutes sum-freeness. -/
theorem not_isSumFree_of_add_mem {S : Set ℕ} {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a + b ∈ S) : ¬ IsSumFree S :=
  fun h => h ha hb hab

end ConjecturesContribution.SumFree
