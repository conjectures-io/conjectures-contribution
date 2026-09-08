# sources.md — Erdős 1203 partial contribution

## Target

`Erdos1203.erdos_1203` in `FormalConjectures/ErdosProblems/1203.lean`:
does `F n = ⨆ k, ω (n + k) * (log log k / log k)` tend to infinity?

Problem page: https://www.erdosproblems.com/1203
Pool repository: https://github.com/google-deepmind/formal-conjectures

## Obstacle addressed

`Erdos1203.F` is an `iSup` of a family of reals indexed by `ℕ`. `ℝ` is only a *conditionally*
complete lattice, so `⨆` evaluates to the junk value `0` whenever the indexed family is not
bounded above. Every lower bound on `F n` therefore has to pass through `le_ciSup`, whose side
condition is

```
BddAbove (Set.range fun k => (ω (n + k) : ℝ) * (Real.log (Real.log k) / Real.log k))
```

and `Tendsto F atTop atTop` — the whole content of the target — is precisely a family of lower
bounds on `F n`. Discharging that side condition is not bookkeeping. Terms in which `n + k` is a
primorial and `k` is comparable to `n + k` have size `≍ 1`, so boundedness of the family is
equivalent to the classical *maximal order of `ω`*, `ω m ≪ log m / log log m`
(https://en.wikipedia.org/wiki/Prime_omega_function ; Hardy & Wright, *An Introduction to the
Theory of Numbers*, §22.10).

I searched the pinned Mathlib for any inequality bounding `Nat.primeFactors.card` or
`ArithmeticFunction.cardDistinctFactors` and found none (all `cardDistinctFactors_*` lemmas in
`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean` are equalities or `Iff`s), and `exact?`
fails on each of the four headline statements of this file. So the bound is built from scratch.

## Delta over the pinned environment

1. `factorial_card_succ_le_prod` — for a `Finset ℕ` whose elements are all `≥ 2`,
   `(S.card + 1)! ≤ ∏ p ∈ S, p`. Proved by `Finset.induction_on_max`: peeling the maximum `a`,
   the remaining set embeds in `Finset.Ico 2 a`, so `s.card + 2 ≤ a`. Sharp (equality at
   `S = {2, 3}`).
2. `factorial_omega_succ_le` — hence `(ω m + 1)! ≤ m` for `m ≠ 0`, via
   `Nat.prod_primeFactors_dvd`. Equality at `m = 1, 2, 6`.
3. `mul_log_div_le` — the analytic core: `2 ≤ t` and `R * log R ≤ 2 * t` imply
   `(2R + 1) * (log t / t) ≤ 12`. Case split on `R ≤ √t` (then `log t / √t ≤ 2` via
   `Real.log_le_sub_one_of_pos` and `Real.log_sqrt`) versus `R > √t` (then
   `log R > (log t)/2`, so `R < 4t / log t`).
4. `omega_mul_ratio_le` — combining 2 and 3 through `r ^ r ≤ (2r)!` (from Mathlib's
   `Nat.factorial_mul_pow_le_factorial`) with `r = ω m / 2`:
   `ω m * (log (log k) / log k) ≤ 12` whenever `8 ≤ k` and `m ≤ 2 * k`.
5. `cardDistinctFactors_mul_log_log_le` — the diagonal case: `ω m * log (log m) ≤ 12 * log m`
   for `8 ≤ m`. This is an explicit, unconditional, effective form of the maximal order of `ω`;
   the constant `12` is crude (the truth is `1 + o(1)`) and no sharpness is claimed.
6. `term_le`, `bddAbove_range`, `le_F`, `F_le` — the resulting supremum API for
   `Erdos1203.F`, with the explicit envelope `F n ≤ 2 * n + 20`.
7. `le_F_of_subset_primeFactors` — the practical lower-bound handle: exhibit a finset of primes
   dividing `n + k` (with `3 ≤ k`) and read off a lower bound on `F n`.
8. `one_le_F` — **`1 ≤ F n` for every `n`, unconditionally.** Take
   `k = 2·510510 − (n mod 510510)`, so `510510 = 2·3·5·7·11·13·17` divides `n + k` and
   `2^18 < k ≤ 2^20`; then `ω (n + k) ≥ 7`, `log log k ≥ 3 log 2`, `log k ≤ 20 log 2`, and
   `7 · 3 ≥ 20` closes it. The only numeric input is `Real.log_two_gt_d9`.
9. `variants_lower_bound` — the companion `Erdos1203.erdos_1203.variants.lower_bound`
   (`∀ ε > 0, ∀ᶠ n in atTop, F n ≥ 1 - ε`, tagged `research solved` and left unproved in the
   pool file) follows in one line, in the strictly stronger uniform form.
10. `tendsto_atTop_iff` — an **equivalence** (both directions proved) between the target
    `Tendsto Erdos1203.F atTop atTop` and a supremum-free statement
    `∀ C, ∀ᶠ n, ∃ k, C ≤ ω (n + k) * (log log k / log k)`; the `←` direction is `le_F`, the
    `→` direction is `exists_lt_of_lt_ciSup`. Nothing is lost by switching sides.
11. `tendsto_atTop_of_primeFactors` — a sufficient condition in the shape a number theorist
    would verify (find `k ≥ 3` and enough primes dividing `n + k`). Labelled as sufficient,
    not equivalent.
12. `exists_multiplied_out_of_forall` — a checked delimiting counterexample: the
    denominator-cleared condition `C * log k ≤ ω (n + k) * log (log k)` is satisfied by `k = 1`
    for *every* `C` and *every* `n` (as `log 1 = 0` and `Real.log 0 = 0`), so any reformulation
    of the target in that shape is vacuous. This is why `tendsto_atTop_of_primeFactors` carries
    the hypothesis `3 ≤ k`.

Everything elaborates with zero errors and zero warnings; `#print axioms` on all sixteen
theorems returns subsets of `[propext, Classical.choice, Quot.sound]` (checked, then the
`#print` lines were removed).

## References consulted

- Erdős problem 1203: https://www.erdosproblems.com/1203
- Prime omega function / maximal order: https://en.wikipedia.org/wiki/Prime_omega_function
- Primorial: https://en.wikipedia.org/wiki/Primorial
- Mathlib `Nat.factorial_mul_pow_le_factorial`, `Nat.prod_primeFactors_dvd`,
  `Finset.induction_on_max`, `le_ciSup` / `ciSup_le` / `exists_lt_of_lt_ciSup`,
  `Real.log_le_sub_one_of_pos`, `Real.log_sqrt`, `Real.log_two_gt_d9`, `Real.exp_one_lt_d9`:
  https://leanprover-community.github.io/mathlib4_docs/
- Mathlib source in the pinned toolchain (`leanprover/lean4:v4.27.0`) was read directly for
  `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean`, `Mathlib/Data/Nat/PrimeFin.lean`,
  `Mathlib/Data/Nat/Factorial/Basic.lean`, `Mathlib/Analysis/Complex/ExponentialBounds.lean`.

## AI assistance disclosure

This contribution was produced by Claude (Anthropic) acting as an autonomous agent, working
inside the pinned `formal-conjectures` checkout: it read the target module and the relevant
Mathlib sources, designed the proof strategy, wrote every Lean line, and iterated against the
compiler until the file elaborated with zero errors and zero warnings. A human reviewed and
directed the effort at the task level. No proof text was copied from any repository, paper, or
`formal_proof` link; no proof assistant output was accepted without recompiling it here.

## Originality

The mathematics is classical (the maximal order of `ω` and the primorial construction are
textbook), but the Lean statements and proofs in this file are original work written for this
submission. I checked with `grep` over the pinned Mathlib and with `exact?` that none of
`factorial_card_succ_le_prod`, `factorial_omega_succ_le`, `bddAbove_range` or
`cardDistinctFactors_mul_log_log_le` is available in the pinned environment. Nothing in the
file restates an existing declaration or renames a Mathlib lemma.
