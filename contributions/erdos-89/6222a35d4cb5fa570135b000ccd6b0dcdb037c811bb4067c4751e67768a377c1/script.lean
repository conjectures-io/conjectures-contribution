/-!
# CI canary — not a real contribution

Exercises the contribution pipeline end to end: the static rules, the hotkey
signature, and the Lean elaboration stage. It deliberately imports nothing, so a
failure here means the pipeline is broken rather than the toolchain being
incomplete. See `mathlib.lean` for the companion that does depend on Mathlib.

Close this pull request; do not merge it.
-/

namespace Contribution.Canary.Core

/-- Every natural number is at most its successor. -/
theorem le_succ (n : Nat) : n ≤ n + 1 := Nat.le_succ n

/-- Addition on `Nat` is monotone in its left argument. -/
theorem add_le_add_right' {m n : Nat} (h : m ≤ n) (k : Nat) : m + k ≤ n + k := by
  omega

/-- A worked special case, so the file proves something and not just a tautology. -/
theorem sub_add_cancel_of_le {m n : Nat} (h : m ≤ n) : n - m + m = n := by
  omega

end Contribution.Canary.Core
