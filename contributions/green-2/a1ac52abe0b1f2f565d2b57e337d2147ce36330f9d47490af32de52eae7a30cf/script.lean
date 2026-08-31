import Mathlib

/-!
# Test contribution — a CI canary, not mathematics

This is a **test submission**, made to exercise the contribution pipeline end to
end against something that satisfies every rule. Nothing here is a result; the
lemmas are elementary on purpose so that a failure in CI is a failure of the
pipeline and not of the mathematics.

It is also a worked example of the expected shape: its own namespace, a docstring
on every declaration, no `sorry`, and no imports beyond the allowlist.

`green-2` asks for `S ⊆ A` whose restricted sumset `S +̂ S` avoids `A`. These are
the book-keeping facts about a single restricted sum that any attempt discharges
on the way past.
-/

namespace Contribution.Green2Canary

/-- The sum contributed by one unordered pair of distinct elements. -/
def restrictedSum (a b : Nat) : Nat := a + b

/-- The pair is unordered, so the sum does not depend on which element is named first. -/
theorem restrictedSum_comm (a b : Nat) : restrictedSum a b = restrictedSum b a := by
  unfold restrictedSum
  omega

/-- A restricted sum overshoots each of its summands, which is why avoiding `A`
below a threshold says nothing about avoiding it above one. -/
theorem restrictedSum_gt_left {a b : Nat} (h : 0 < b) : a < restrictedSum a b := by
  unfold restrictedSum
  omega

/-- Fixing one summand, the restricted sum is strictly increasing in the other. -/
theorem restrictedSum_strictMono {a b c : Nat} (h : b < c) :
    restrictedSum a b < restrictedSum a c := by
  unfold restrictedSum
  omega

end Contribution.Green2Canary
