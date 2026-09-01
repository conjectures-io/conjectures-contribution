import FormalConjectures.ErdosProblems.«1107»

/-!
# The list introduction rule, and why Erdős 1107 asks for `r ≥ 2`

**This is a pipeline test contribution.** Its purpose is to exercise the submission and
verification pipeline end to end with a file that is correct, self-contained and free of holes.
It is offered as real (if modest) API all the same — every declaration below is proved.

`Erdos1107.SumOfRPowerful r n` is an existential over a `List ℕ` with three side conditions, so
every use of it starts by unpacking or repacking a witness. This file provides the general
packing step, and then records what the predicate degenerates to below the range the problem
asks about:

* `sumOfRPowerful_of_list` — the introduction rule in its general form: any list of `r`-full
  numbers no longer than `r + 1` witnesses the property for its own sum.
* `sumOfRPowerful_zero_left` and `sumOfRPowerful_one_left` — for `r = 0` and `r = 1` the
  predicate holds of *every* natural number, because `Nat.Full 0` and `Nat.Full 1` are
  satisfied by everything and a single summand is already within the length bound. This is the
  concrete reason `erdos_1107` is quantified over `r ≥ 2`: below that the statement is a
  triviality, so any argument that does not use `2 ≤ r` cannot be proving anything.

Nothing here approaches the conjecture. `sumOfRPowerful_of_list` is one direction of the
definition, and the other two are about the excluded range only.
-/

namespace Contribution.Erdos1107Degenerate

open Erdos1107

/-- The general introduction rule: a short enough list of `r`-full numbers witnesses the
property for its sum. -/
theorem sumOfRPowerful_of_list {r : ℕ} (s : List ℕ) (hlen : s.length ≤ r + 1)
    (hfull : ∀ x ∈ s, Nat.Full r x) : SumOfRPowerful r s.sum :=
  ⟨s, hlen, hfull, rfl⟩

/-- Every natural number is `0`-full, so for `r = 0` the property is vacuous. -/
theorem sumOfRPowerful_zero_left (n : ℕ) : SumOfRPowerful 0 n :=
  ⟨[n], by simp, by simpa using Nat.Full.zero_left n, by simp⟩

/-- Every natural number is `1`-full, so for `r = 1` the property is vacuous too. -/
theorem sumOfRPowerful_one_left (n : ℕ) : SumOfRPowerful 1 n :=
  ⟨[n], by simp, by simpa using Nat.Full.one_left n, by simp⟩

end Contribution.Erdos1107Degenerate
