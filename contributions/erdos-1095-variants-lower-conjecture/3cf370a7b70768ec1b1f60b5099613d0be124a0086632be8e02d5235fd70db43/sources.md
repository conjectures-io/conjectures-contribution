# Sources and provenance

## Target

`Erdos1095.erdos_1095.variants.lower_conjecture` (task `erdos-1095-variants-lower-conjecture`),
Erdős Problem 1095: `∃ c > 0, ∀ᶠ k in atTop, g k ≥ exp (c * k / log k)` for the Erdős–Selfridge
function `g k = sInf {m | k + 1 < m ∧ k < (m.choose k).minFac}`. The problem is open; this
contribution does not solve it and does not prove any of the four unproved statements in the
target module.

## Obstacle addressed

The target module contains the definition of `g` and four unproved statements, and no lemma about
`g` at all. Three things stand between the definition and a lower bound.

1. `sInf (∅ : Set ℕ) = 0`, so unless the set defining `g` is shown nonempty for every `k`, the
   reward statement is *false* rather than open.
2. Membership is stated through `Nat.minFac (Nat.choose m k)`. Mathlib's general handle on prime
   factors of binomial coefficients is Kummer's theorem in carry-counting form
   (`Nat.factorization_choose`) and Lucas' theorem modulo `p` (`Choose.lucas_theorem`); the
   divisibility lemmas that exist (`Nat.Prime.dvd_choose`, `Nat.Prime.dvd_choose_add`,
   `Nat.Prime.dvd_choose_pow_iff`) all constrain `m` and `k` to a single base-`p` digit or to
   `m = p ^ n`, so none of them decides `p ∣ m.choose k` for general `m` and `k`.
3. `N ≤ sInf S` is a statement about all of `S` and has to become a finite check on the interval
   `(k + 1, N)` before any concrete or asymptotic argument can start.

## Delta: what this contribution adds

* `pow_le_mod_add_mod_iff`, `dvd_choose_iff_exists_mod_lt`, `forall_mod_le_iff_forall_digit_le`,
  `dvd_choose_iff_exists_digit_lt`: Kummer's theorem turned into a usable divisibility criterion,
  in borrow form (`p ∣ m.choose k ↔ ∃ i, m % p ^ i < k % p ^ i`) and in Lucas/digit form
  (`p ∣ m.choose k ↔ ∃ i, m / p ^ i % p < k / p ^ i % p`), with the equivalence between the two.
* `Dominates`, `dominates_iff_bounded`, `decidableDominates`, `lt_minFac_choose_iff_dominates`,
  `g_eq_sInf_dominates`: the condition defining `g` expressed as base-`p` digit domination, with
  both quantifiers cut to a finite range, hence decidable, hence a kernel computation.
* `modulus`, `dominates_congr_mod`, `dominates_add_mul_modulus`, `exists_dominates_Ico`:
  admissibility depends only on `m % modulus k`, so the admissible set is a union of residue
  classes and meets every window of `modulus k` consecutive integers.
* `g_spec`, `g_le_add_modulus`: `g` is well defined (`k + 1 < g k ∧ k < ((g k).choose k).minFac`),
  never the junk value `0`, and `g k ≤ k + 1 + modulus k`.
* `le_g_iff`, `lower_conjecture_iff_digits`: the lower bound as a finite check (an equivalence),
  and the reward statement restated with no `g`, no `sInf`, no `Nat.minFac` and no `Nat.choose`;
  two worked use sites derive the literal reward statement from it.
* `g_eq_of_check` and `g_one` … `g_thirteen`: certified values `g 1 = 3`, `g 2 = 6`, `g 3 = 7`,
  `g 4 = 7`, `g 5 = 23`, `g 6 = 62`, `g 7 = 143`, `g 8 = 44`, `g 13 = 2239`, each proved from the
  definition (the last is a kernel search over the 2224 candidates `14 < m < 2239`), and
  `not_monotone_g`, which records that `g` is not monotone.

Not provided: any lower bound on `g` growing with `k`. Deriving the target from
`lower_conjecture_iff_digits` still requires covering the whole interval
`(k + 1, exp (c * k / log k))` by the digit conditions of the primes `p ≤ k`.

## Links

* https://www.erdosproblems.com/1095
* https://github.com/google-deepmind/formal-conjectures — the pool file
  `FormalConjectures/ErdosProblems/1095.lean` whose definitions this file builds on.
* https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Factorization.html
  — `Nat.factorization_choose` (Kummer, carry-counting form).
* https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Lucas.html
  — `Choose.lucas_theorem`.
* https://en.wikipedia.org/wiki/Kummer%27s_theorem
* https://en.wikipedia.org/wiki/Lucas%27s_theorem

Cited papers (no stable open URL used, so none is given rather than guessing one):
[EES74] E. F. Ecklund Jr., P. Erdős, J. L. Selfridge, *A new function associated with the prime
factors of `n choose k`*, Math. Comp. 28 (1974), 647–649.
[ELS93] P. Erdős, C. B. Lacampagne, J. L. Selfridge, *Estimates of the least prime factor of a
binomial coefficient*, Math. Comp. 61 (1993), 215–224.
[Ko99b] S. V. Konyagin, *Estimates of the least prime factor of a binomial coefficient*,
Mathematika 46 (1999), 41–55.
[SSW20] B. Sorenson, J. Sorenson, J. Webster, *An algorithm and estimates for the Erdős–Selfridge
function* (2020), 371–385.

## AI assistance

This contribution was produced with AI assistance: Claude (Anthropic), driven interactively in a
Claude Code session, wrote the Lean statements, proofs and docstring. Every declaration was
checked by the repository's pinned Lean 4 / Mathlib toolchain — the file compiles with zero errors
and zero warnings — and `#print axioms` was run on all 30 named declarations, each depending only
on `[propext, Classical.choice, Quot.sound]`. The nine numerical values of `g` were first computed
independently with Python/sympy from the definition (least `m > k + 1` with
`min (primeFactors (m.choose k)) > k`) and only then certified in Lean from the definition itself.

## Originality

All statements and proofs in this file are original to this contribution. Nothing was copied from
another repository, from a `formal_proof` link, or from any other formalization of these facts;
the file is written against the target module's own definition of `g` and against Mathlib. Novelty
was checked before keeping each Mathlib-independent lemma: `grep` over
`.lake/packages/mathlib/Mathlib` for `dvd_choose` (only `dvd_choose`, `dvd_choose_add`,
`dvd_choose_self`, `dvd_choose_pow`, `dvd_choose_pow_iff` exist, all single-digit or prime-power
special cases), and `exact?`, `simp` and `omega` were run on the statements of
`pow_le_mod_add_mod_iff`, `dvd_choose_iff_exists_mod_lt`, `dvd_choose_iff_exists_digit_lt` and
`forall_mod_le_iff_forall_digit_le` — none is closed by a library lemma or by a single tactic
call. The remaining declarations are about the bespoke predicate `Dominates` and about
`Erdos1095.g`, neither of which exists in Mathlib.
