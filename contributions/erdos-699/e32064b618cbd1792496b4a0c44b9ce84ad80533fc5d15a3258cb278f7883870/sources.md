# Sources and provenance — partial contribution to `erdos-699`

Reward theorem: `Erdos699.erdos_699` in `FormalConjectures/ErdosProblems/699.lean`.
Contribution file: one self-contained Lean file, namespace `Contribution.Erdos699Carries`,
21 named theorems plus 4 worked examples, no `sorry`/`axiom`/`native_decide`/`set_option`.
Every named theorem was checked with `#print axioms` (temporarily) and depends only on
`propext`, `Classical.choice`, `Quot.sound`; the `#print` lines were then deleted and the file
recompiled to zero errors and zero warnings.

## The obstacle

Erdős 699 asks for a prime `p ≥ i` dividing `gcd(binom(n,i), binom(n,j))` whenever
`1 ≤ i < j ≤ n/2`. The formal obligation therefore requires *producing a prime that divides a
binomial coefficient*, and Mathlib offers no tool that applies in this regime:

* `Nat.Prime.dvd_choose` requires `k < p` **and** `n - k < p`, i.e. `p` comparable to `n`, which
  never happens for the primes relevant here;
* `Nat.Prime.dvd_choose_pow` only covers `n` a prime power;
* Kummer's theorem exists only as the valuation formula `Nat.factorization_choose`, which returns
  the cardinality of a `Finset.filter` over `Finset.Ico 1 b` whose predicate
  `p ^ t ≤ k % p ^ t + (n - k) % p ^ t` is a *carry* condition, not a divisibility statement, and
  which drags an arbitrary bound `b` through every proof.

The problem is also listed as falsifiable by a finite counterexample, yet no search can evaluate
`Nat.choose n i` for the `n` of interest, so a check that avoids the coefficient is required.

## The delta

1. **Kummer as a divisibility test.** `prime_dvd_choose_iff_exists_mod_pow_lt`:
   for `p` prime and `k ≤ n`, `p ∣ n.choose k ↔ ∃ t, 0 < t ∧ n % p ^ t < k % p ^ t`.
   The bridge `mod_lt_mod_iff_le_add_mod` (with the digit lemma `add_mod_lt_iff`) turns Mathlib's
   carry predicate into this arithmetic form; `le_log_of_mod_pow_lt` shows only the digits that
   `n` actually has can carry.
2. **A finite, `decide`-able criterion.** `prime_dvd_choose_iff_exists_le_log` bounds the search
   to `Finset.Icc 1 (Nat.log p n)`, so non-divisibility is settled without evaluating the
   coefficient. A worked example refutes `7 ∣ Nat.choose 28 14` and `13 ∣ Nat.choose 28 14` by
   `decide` on a two-element check.
3. **The target's existential, reformulated.** For `j < p`,
   `prime_dvd_gcd_choose_iff_mod_lt` reduces `p ∣ Nat.gcd (n.choose i) (n.choose j)` to `n % p < i`
   — gcd, both coefficients and all factorials vanish. `exists_prime_ge_dvd_gcd_choose_iff` then
   splits the reward obligation into an `rcases`-friendly disjunction: a bounded search over
   primes in `[i, j]`, or the purely modular condition `∃ p prime, j < p ∧ n % p < i`.
   `le_mod_of_not_exists_prime_ge_dvd` is the contrapositive a counterexample search wants
   (`i ≤ n % p` for every prime `p > j`), and `erdos_699_of_prime_dvd` disposes of every `n` with
   a prime factor above `j`.
4. **The case `i = 1`, closed.** `div_gcd_dvd_choose : 0 < n → n / Nat.gcd n k ∣ n.choose k` is
   the classical sharpening of `n ∣ k * n.choose k`; it is not in Mathlib (`exact?` finds nothing,
   and no lemma in `Mathlib/Data/Nat/Choose/` mentions `gcd`). It yields `erdos_699_index_one`:
   for `1 < j ≤ n/2` there is a prime dividing `gcd(binom(n,1), binom(n,j))`, i.e. the whole
   `i = 1` slice of the open problem is settled.
5. **Two checked exceptions.** `gcd_choose_ten` and `gcd_choose_twentyEight` verify
   `gcd(binom(10,3), binom(10,5)) = 12` and
   `gcd(binom(28,5), binom(28,14)) = 2^3 * 3^3 * 5`, the second confirming the value recorded on
   erdosproblems.com. Hence `mem_of_forall_exists_prime_gt`: every exceptional set `E` admissible
   in `Erdos699.erdos_szekeres_strengthening` must contain both `(10, 3, 5)` and `(28, 5, 14)`
   (the latter is the only exception with `i ≥ 4` known in the literature), while
   `exists_prime_ge_dvd_gcd_choose_ten` / `..._twentyEight` show the weaker bound `i ≤ p` of
   `erdos_699` does hold at both triples. So the `≤` in `i ≤ p` cannot be strengthened to `<`, and
   the two theorems in the target file are genuinely different.

The residual obligation after this contribution is exactly the third worked example: for `i ≥ 2`,
assuming `i ≤ n % p` for every prime `p > j`, find a prime `p` with `i ≤ p ≤ j` dividing the gcd.

## Links

- Problem page: https://www.erdosproblems.com/699
- Formal Conjectures repository (target file `FormalConjectures/ErdosProblems/699.lean`):
  https://github.com/google-deepmind/formal-conjectures
- Kummer's theorem (the carry description of the `p`-adic valuation of a binomial coefficient):
  https://en.wikipedia.org/wiki/Kummer%27s_theorem
- Mathlib lemmas used and checked against, at the pinned commit
  `a3a10db0e9d66acbebf76c5e6a135066525ac900`:
  - https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/Choose/Factorization.lean
  - https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/Choose/Dvd.lean
  - https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/Choose/Basic.lean
- Erdős, P. and Szekeres, G., *Some number theoretic problems on binomial coefficients*,
  Austral. Math. Soc. Gaz. 5 (1978), 97-99 (the source of the strengthening formalised as
  `Erdos699.erdos_szekeres_strengthening`); see also Guy, R. K., *Unsolved Problems in Number
  Theory*, 3rd ed., problem B31: https://link.springer.com/book/10.1007/978-0-387-26677-0

## Novelty check

Before keeping each lemma I searched the pinned Mathlib source for it and tried `exact?`:
`n / Nat.gcd n k ∣ n.choose k` is not found by `exact?` and no `gcd` statement about
`Nat.choose` exists anywhere in Mathlib; there is no `%`-form divisibility criterion for
`Nat.choose` (only the valuation formulas in `Data/Nat/Choose/Factorization.lean` and
`Data/Nat/Multiplicity.lean`, plus the restrictive `Nat.Prime.dvd_choose`); no bridge lemma
between the carry predicate `q ≤ k % q + (n - k) % q` and `n % q < k % q` exists
(`Nat.add_mod_of_add_mod_lt` in `Data/Nat/ModEq.lean` is a different statement about `(a + b) % c`
and proves no equivalence).

## AI assistance and originality

This contribution was produced with AI assistance (Claude, Anthropic), driven by the submitter.
The mathematics (the carry criterion and its finite form, the large-prime reduction of the gcd
condition, the `n / gcd(n, k) ∣ binom(n, k)` route to the `i = 1` case, and the two certified
exceptional triples) was designed and proved for this submission; nothing was copied from another
contribution, from a third-party formalisation repository, or from any `formal_proof` link in the
pool. Every statement in the file compiles in the pinned workspace and was axiom-audited as
described above.
