import Mathlib
import FormalConjectures.ErdosProblems.«409»

/-!
Contribution: proof of `erdos_409.variants.termination` from Erdős Problem 409.

If `n > 0`, then the iteration `n ↦ φ(n) + 1` necessarily reaches a prime.
-/

open scoped Nat

namespace Contribution.Erdos409Termination

theorem erdos_409.variants.termination (n : ℕ) (hn : 0 < n) :
    ∃ i, (φ · + 1)^[i] n |>.Prime := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hp : n.Prime
    · exact ⟨0, by simpa using hp⟩
    · have h1 : n = 1 ∨ 1 < n := by omega
      rcases h1 with h1 | h1
      · subst h1
        refine ⟨1, ?_⟩
        norm_num [Function.iterate_one, Nat.totient_one]
      · have hlt : φ n < n := Nat.totient_lt n h1
        have hne : φ n ≠ n - 1 := by
          intro h
          exact hp ((Nat.totient_eq_iff_prime hn).1 h)
        have hdec : φ n + 1 < n := by omega
        have hpos : 0 < φ n + 1 := by positivity
        obtain ⟨i, hi⟩ := ih (φ n + 1) hdec hpos
        refine ⟨i + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        exact hi

end Contribution.Erdos409Termination
