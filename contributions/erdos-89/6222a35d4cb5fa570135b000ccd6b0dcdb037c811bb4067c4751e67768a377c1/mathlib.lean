import Mathlib

/-!
# CI canary — Mathlib half

Separate from `script.lean` so the two failure modes are distinguishable: if this
file fails to elaborate but `script.lean` passes, the runner's Lake workspace does
not actually provide Mathlib.
-/

namespace Contribution.Canary.WithMathlib

/-- `ℕ` notation and a Mathlib-provided lemma both resolve. -/
theorem card_range (n : ℕ) : (Finset.range n).card = n := Finset.card_range n

end Contribution.Canary.WithMathlib
