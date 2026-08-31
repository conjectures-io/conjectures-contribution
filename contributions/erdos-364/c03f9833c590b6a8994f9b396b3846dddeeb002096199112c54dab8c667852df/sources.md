# Sources

## Target

- `Erdos364.erdos_364` in `FormalConjectures/ErdosProblems/364.lean`
  (`¬ ∃ n, Powerful n ∧ Powerful (n + 1) ∧ Powerful (n + 2)`), pinned via the
  `conjectures` submodule. Background: <https://www.erdosproblems.com/364>.

## Prior work this builds on

- `Nat.Powerful` and `Nat.Full`, with `Nat.not_full_of_prime_mod_prime_sq` and
  `Nat.full_of_le_full`, from `FormalConjecturesForMathlib/Data/Nat/Full.lean`.
  `not_powerful_of_dvd_of_not_sq_dvd` is the strengthening of
  `not_full_of_prime_mod_prime_sq` described in the module docstring: the existing
  lemma needs `n % p ^ (k+1) = p`, which at `p = 3` covers `n % 9 = 3` but not
  `n % 9 = 6`.
- `Erdos364.erdos_364.variants.weak` (the powerful-*quadruple* case, `category
  textbook`) is proved in the pool file using
  `not_full_of_prime_mod_prime_sq _ 1 Nat.prime_two`, i.e. the `p = 2` half of the
  same idea. The mod-4 argument here is that same classical observation; the
  delta in this contribution is the mod-9 extension, the combined `mod 36`
  reduction, and the sieve-limitation theorem.

## Mathlib declarations used

- `Nat.mem_primeFactors`, `Nat.prime_two`, `Nat.prime_three`
- `Nat.eq_of_mul_eq_mul_left`
- `Set.infinite_of_injective_forall_mem`
- tactics: `omega`, `ring`, `norm_num`

## Scope and honesty notes

- The `p = 2` obstruction (`n ≡ 2 mod 4` is not powerful) is classical and already
  used in the pool file; it is included only because `triple_mod_36` needs it.
- `survivors_infinite` is a limitative result, not progress toward a proof: it
  shows this congruence method **cannot** settle the target, so the residue class
  `n ≡ 7, 27, 35 (mod 36)` is the end of what sieving alone gives.
- No claim is made about the strong variant `erdos_364.variants.strong`.
