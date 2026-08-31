import FormalConjectures.ErdosProblems.«1107»

/-!
# Introduction rules for `Erdos1107.SumOfRPowerful`

**This is a pipeline test contribution.** Its purpose is to exercise the submission and
verification pipeline end to end with a file that is correct, self-contained and free of holes.
It is offered as real (if modest) API all the same — every declaration below is proved.

Erdős problem 1107 asks whether every large integer is the sum of at most `r + 1` many
`r`-powerful numbers. `Erdos1107.SumOfRPowerful r n` states exactly that for a single `n`, and
is stated existentially over a `List ℕ`, so establishing it always means producing a witness
list and discharging its three side conditions by hand. These are the small cases, packaged:

* `sumOfRPowerful_zero` — the empty list; `0` is a sum of no summands at all.
* `sumOfRPowerful_of_full` — a singleton. An `r`-full number is trivially such a sum, and this
  is the step an argument reaches for once it has produced one large `r`-full number.
* `sumOfRPowerful_one` — the same for `1`, via `Nat.Full.one_right`.
* `sumOfRPowerful_add` — two summands, which needs `1 ≤ r` for the length bound to admit them.
  This is the base of the `r = 2` case that Heath-Brown settled.

Nothing here approaches the conjecture: every statement is about one fixed `n`, and none
mentions a filter or an eventual property.
-/

namespace Contribution.Erdos1107Sums

open Erdos1107

/-- `0` is a sum of no `r`-powerful numbers. -/
theorem sumOfRPowerful_zero (r : ℕ) : SumOfRPowerful r 0 :=
  ⟨[], by simp, by simp, by simp⟩

/-- An `r`-full number is a sum of one `r`-powerful number. -/
theorem sumOfRPowerful_of_full {r n : ℕ} (hn : Nat.Full r n) : SumOfRPowerful r n :=
  ⟨[n], by simp, by simpa using hn, by simp⟩

/-- `1` is `r`-full for every `r`, hence such a sum. -/
theorem sumOfRPowerful_one (r : ℕ) : SumOfRPowerful r 1 :=
  sumOfRPowerful_of_full (Nat.Full.one_right r)

/-- A sum of two `r`-full numbers is a sum of at most `r + 1` of them once `1 ≤ r`. -/
theorem sumOfRPowerful_add {r a b : ℕ} (hr : 1 ≤ r)
    (ha : Nat.Full r a) (hb : Nat.Full r b) : SumOfRPowerful r (a + b) :=
  ⟨[a, b], by simpa using hr, by simpa using ⟨ha, hb⟩, by simp⟩

end Contribution.Erdos1107Sums
