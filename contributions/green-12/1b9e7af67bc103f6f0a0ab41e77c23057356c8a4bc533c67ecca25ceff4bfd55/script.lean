import Mathlib

/-!
# Sample contribution — a CI canary, not mathematics

This file is a **test submission**. It exists so maintainers can exercise the
contribution pipeline end to end against something that satisfies every rule, and
so a first-time contributor has a worked example of the expected shape. Close the
pull request that carries it; nothing here is worth merging.

What a real contribution would look like is nonetheless visible: a namespace of its
own, a docstring on every declaration, no `sorry`, and lemmas an attempt on the
target could actually cite.

The statement of `green-12` reads indices of `x_i + y_j` modulo 5. These are the
book-keeping facts that reading discharges, kept here so an attempt does not have
to restate them.
-/

namespace Contribution.Green12Canary

/-- The length of the index cycle in the statement of `green-12`. -/
def period : Nat := 5

/-- Shifting an index by a whole cycle leaves it where it was. -/
theorem shift_by_period (i : Nat) : (i + period) % period = i % period := by
  unfold period
  omega

/-- Every index the statement forms stays inside the cycle. -/
theorem offset_lt_period (i k : Nat) : (i + k) % period < period := by
  unfold period
  omega

/-- The window `{i, i+1, i+2}` names three *distinct* positions of the cycle,
which is what stops the tuple count from collapsing. -/
theorem offsets_distinct (i : Nat) :
    i % period ≠ (i + 1) % period
    ∧ (i + 1) % period ≠ (i + 2) % period
    ∧ i % period ≠ (i + 2) % period := by
  unfold period
  omega

end Contribution.Green12Canary
