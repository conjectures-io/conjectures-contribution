import Mathlib
import FormalConjectures.ErdosProblems.«364»

/-!
# Congruence obstructions for consecutive powerful triples (Erdős 364)

Target: `Erdos364.erdos_364`, i.e. `¬ ∃ n, Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2)`.

This file supplies the local (congruence) theory of a hypothetical powerful triple, plus a
proof that this approach cannot by itself finish the target.

**What a solver gets.**

* `not_powerful_of_dvd_of_not_sq_dvd` — the general "p divides n exactly once" obstruction.
  `FormalConjecturesForMathlib` already has `Nat.not_full_of_prime_mod_prime_sq`, but it requires
  the residue to be exactly `p` (`n % p ^ (k+1) = p`), so at `p = 3` it fires on `n % 9 = 3` and
  misses `n % 9 = 6`. This version covers every residue in which `p` divides `n` exactly once,
  which is what the mod-9 half of the reduction below needs.
* `triple_mod_36` — any powerful triple starts at `n ≡ 7, 27` or `35 (mod 36)`. This cuts the
  search space for a counterexample to `3/36 = 1/12` of all residues.
* `survivors_infinite` — for **every** odd `Q` infinitely many `n` pass all of these tests at once.
  Hence no finite family of congruence conditions can prove the target: the sifted set thins but
  is never empty. This is the honest negative half of the handoff, and it tells the next solver to
  spend effort elsewhere (size/abc arguments) rather than extending the sieve.
-/

namespace Contribution.Erdos364Congruence

open Nat

/-- If a prime `p` divides `n` but `p ^ 2` does not, then `n` is not powerful. -/
theorem not_powerful_of_dvd_of_not_sq_dvd {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h1 : p ∣ n) (h2 : ¬ p ^ 2 ∣ n) : ¬ Nat.Powerful n := fun hpow =>
  h2 (hpow p (Nat.mem_primeFactors.mpr ⟨hp, h1, hn⟩))

/-- A number `≡ 2 (mod 4)` is not powerful. -/
theorem not_powerful_two {n : ℕ} (h : n % 4 = 2) : ¬ Nat.Powerful n := by
  refine not_powerful_of_dvd_of_not_sq_dvd Nat.prime_two (by omega) (by omega) ?_
  have : (2:ℕ) ^ 2 = 4 := by norm_num
  rw [this]; omega

/-- A number `≡ 3` or `≡ 6 (mod 9)` is not powerful. -/
theorem not_powerful_three {n : ℕ} (h : n % 9 = 3 ∨ n % 9 = 6) : ¬ Nat.Powerful n := by
  refine not_powerful_of_dvd_of_not_sq_dvd Nat.prime_three (by omega) (by omega) ?_
  have : (3:ℕ) ^ 2 = 9 := by norm_num
  rw [this]; omega

/-- **Main reduction.** A consecutive powerful triple `n, n+1, n+2` forces
`n ≡ 7, 27` or `35 (mod 36)`: at most `1/12` of residues survive. -/
theorem triple_mod_36 {n : ℕ}
    (h0 : Nat.Powerful n) (h1 : Nat.Powerful (n + 1)) (h2 : Nat.Powerful (n + 2)) :
    n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35 := by
  have a0 : n % 4 ≠ 2 := fun h => not_powerful_two h h0
  have a1 : (n + 1) % 4 ≠ 2 := fun h => not_powerful_two h h1
  have a2 : (n + 2) % 4 ≠ 2 := fun h => not_powerful_two h h2
  have b0 : ¬ (n % 9 = 3 ∨ n % 9 = 6) := fun h => not_powerful_three h h0
  have b1 : ¬ ((n + 1) % 9 = 3 ∨ (n + 1) % 9 = 6) := fun h => not_powerful_three h h1
  have b2 : ¬ ((n + 2) % 9 = 3 ∨ (n + 2) % 9 = 6) := fun h => not_powerful_three h h2
  omega

/-- `n` is odd and `4 ∣ n + 1`: the middle term carries all the powers of two. -/
theorem triple_mod_4 {n : ℕ}
    (h0 : Nat.Powerful n) (h1 : Nat.Powerful (n + 1)) (h2 : Nat.Powerful (n + 2)) :
    n % 4 = 3 := by
  have := triple_mod_36 h0 h1 h2; omega

/-- Representative use: the residue test alone refutes a candidate triple, with no factoring. -/
example : ¬ (Nat.Powerful 100 ∧ Nat.Powerful 101 ∧ Nat.Powerful 102) := by
  rintro ⟨h0, h1, h2⟩
  have := triple_mod_36 (n := 100) h0 h1 h2
  omega

/-- For any odd `Q`, infinitely many `n` satisfy `Q ∣ n` and `n ≡ 3 (mod 4)` simultaneously.

Taking `Q = ∏ p ^ 2` over the odd primes `p ≤ N` shows that the full congruence sieve at every
prime up to `N` still leaves infinitely many candidates, for every `N`. So congruences alone can
never settle Erdős 364. -/
theorem survivors_infinite {Q : ℕ} (hQ : Odd Q) :
    {n : ℕ | Q ∣ n ∧ n % 4 = 3}.Infinite := by
  obtain ⟨a, ha⟩ := hQ
  have hQ0 : 0 < Q := by omega
  have hQQ : Q * Q % 4 = 1 := by subst ha; ring_nf; omega
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℕ => Q * (3 * Q + 4 * t)) ?_ ?_
  · intro x y hxy
    have := Nat.eq_of_mul_eq_mul_left hQ0 hxy
    omega
  · intro t
    refine ⟨⟨3 * Q + 4 * t, rfl⟩, ?_⟩
    show Q * (3 * Q + 4 * t) % 4 = 3
    have hexp : Q * (3 * Q + 4 * t) = 3 * (Q * Q) + 4 * (Q * t) := by ring
    rw [hexp]; omega

end Contribution.Erdos364Congruence
