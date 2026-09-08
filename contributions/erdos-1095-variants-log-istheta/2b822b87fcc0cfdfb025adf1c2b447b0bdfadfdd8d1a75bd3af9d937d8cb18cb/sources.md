# sources.md — `CW_erdos_1095_variants_log_istheta.lean`

## Target

`Erdos1095.erdos_1095.variants.log_isTheta` in `FormalConjectures/ErdosProblems/1095.lean`:

```
(fun k ↦ Real.log (Erdos1095.g k)) =Θ[atTop] (fun k ↦ (k : ℝ) / Real.log k)
```

where `Erdos1095.g k = sInf {m | k + 1 < m ∧ k < (m.choose k).minFac}` is the Erdős–Selfridge
function: the least `n > k + 1` such that every prime factor of `binom n k` exceeds `k`.

## The obstacle

The pool module offers no companion that can be proved outright. Its four `sorry`s are
`lower_solved` (Konyagin's `g(k) ≫ exp(c (log k)²)`), `upper_conjecture`
(Ecklund–Erdős–Selfridge's `g(k) ≤ exp((1+o(1))k)`), `lower_conjecture` (open) and the target
(open). Each needs a genuine analytic-number-theory argument; in particular the optimal constant
`1 + o(1)` in the upper bound requires a sieve step plus a Mertens-type product estimate that the
pinned Mathlib does not have.

What *is* tractable, and is logically prior to all four, is that nothing in the module establishes
that the set whose `sInf` defines `g` is nonempty. Until that is proved, `Erdos1095.g k` may be
`sInf ∅ = 0`, `Real.log 0 = 0`, and the target statement is *false*. Discharging it is not an
`sInf` manipulation: it is Kummer's theorem in the form "`p` does not divide `binom n k` iff every
base-`p` truncation of `k` is dominated by that of `n`", which the pinned Mathlib does not contain
— Mathlib has the carry-*counting* forms `Nat.factorization_choose` and `padicValNat_choose`, and
the digit-*sum* form `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`, neither of which can be
used to *construct* binomial coefficients free of small prime factors.

## Delta — what this file adds

34 declarations, all in `namespace Contribution.Erdos1095Carry`, zero errors and zero warnings on
the pinned toolchain, every theorem's `#print axioms` a subset of
`[propext, Classical.choice, Quot.sound]`.

1. **Base-`p` calculus.** `sub_mod_of_mod_le`, `mod_add_sub_mod_lt_iff`, `le_sub_one_mod`:
   borrow-free subtraction of remainders, the carry criterion, and "`N - 1` has large base-`p`
   digits when `p^a ∣ N`". None is closable by `exact?` in the pinned environment (checked).
2. **Kummer, digit-domination form.** `not_dvd_choose_iff`: for `p` prime and `k ≤ n`,
   `¬ p ∣ n.choose k ↔ ∀ i, k % p ^ i ≤ n % p ^ i`. `lt_minFac_choose_iff` converts the target's
   bespoke membership condition `k < (n.choose k).minFac` into that digit condition for all primes
   `p ≤ k`; `forall_mod_le_of_le_log_succ` shows only the bottom `Nat.log p k + 1` digits matter.
3. **Periodicity.** `minFac_choose_congr`: for `k < n`, `k < n'` with
   `n ≡ n' [MOD carryFreeModulus k]` the two membership conditions are equivalent. So membership is
   a union of residue classes modulo an explicit modulus — the structural fact behind every
   algorithmic and heuristic treatment of `g`, and the reason a candidate `N` can be tested by its
   residue alone.
4. **Well-definedness.** `lt_minFac_choose_sub_one`, `witness`, `lt_minFac_choose_witness`,
   `nonempty_of_g`, `g_spec`, `one_lt_g` with the explicit witness
   `witness k m = (m + k + 3) * carryFreeModulus k - 1`; `setOf_infinite` upgrades this to: for
   every `k` there are infinitely many `n` all of whose `binom n k` prime factors exceed `k`.
5. **Evaluation.** `g_eq_of` (one witness plus a finite check of the smaller candidates; its `≤`
   half is exactly `g_spec`) and the checked values `g 2 = 6`, `g 3 = 7`, `g 4 = 7`, `g 5 = 23`.
6. **Quantitative upper bounds.** `carryFreeModulus_le` (splitting the primes at `√k` and using
   Mathlib's `primorial_le_4_pow`), `g_le_pow_mul` (`g k ≤ k ^ (Nat.sqrt k + 3) * 16 ^ k`),
   `log_g_le_linear` (`log (g k) ≤ 11 * k` for `k ≥ 3`), `g_le_exp`, `log_g_isBigO`. This is an
   honest weakening of `upper_conjecture`: the order `O(k)` is right, the constant is crude, and it
   is explicitly *not* enough for the upper half of the target, which needs `O(k / log k)`.
7. **The target, unfolded.** `log_isTheta_iff` turns the `=Θ` into two explicit one-sided
   inequalities; the norms can be removed only because `log (g k) > 0`, which is available only
   after item 4.
8. **Worked use site.** `lower_conjecture_of_log_isTheta` takes the target *verbatim* as a
   hypothesis and derives the pool's other open companion
   `Erdos1095.erdos_1095.variants.lower_conjecture`. That the restated hypothesis and conclusion are
   type-identical to the pool declarations was checked in a probe file by elaborating
   `theorem checkStmt : myStmt := Erdos1095.erdos_1095.variants.log_isTheta` and
   `theorem checkLower : myLower := Erdos1095.erdos_1095.variants.lower_conjecture`.

What is **not** claimed: no lower bound on `g` beyond the trivial `g k > k + 1` is proved here, and
the upper bound is off by a factor `log k` in the exponent from what the target needs. The target
itself is untouched.

## Links

- Problem statement: https://www.erdosproblems.com/1095
- Formal Conjectures repository (source of the pool module):
  https://github.com/google-deepmind/formal-conjectures
- Mathlib 4 documentation (used to confirm what is and is not already available — Kummer's theorem
  appears only in carry-counting and digit-sum form): https://leanprover-community.github.io/mathlib4_docs/
- Erdős's own paper archive (EES74 and ELS93, cited by the pool module):
  https://users.renyi.hu/~p_erdos/Erdos.html

## Method and AI assistance

This contribution was produced by Claude (Anthropic), running as an autonomous coding agent under
human direction, in a single session. The workflow was: read the pool module and follow every
bespoke definition; check the pinned Mathlib by `grep` and by `exact?` / `simp` / `omega` probes for
each candidate lemma, dropping anything that Mathlib already had or that a single tactic call
closed; find the small values of `g` by a short brute-force Python search and then *prove* them in
Lean with `g_eq_of` and `norm_num`; iterate the Lean file to zero errors and zero warnings; append
`#print axioms` for all 34 declarations, confirm each is a subset of
`[propext, Classical.choice, Quot.sound]`, and delete those lines before the final compile.

## Originality

The mathematics is classical — Kummer's theorem, the observation that
`N ≡ -1 (mod ∏_{p ≤ k} p^{⌊log_p k⌋+1})` makes `binom (N-1) k` free of prime factors `≤ k`, and the
Chebyshev bound `∏_{p ≤ k} p ≤ 4^k` — but every Lean statement and proof in this file was written
for this contribution. No proof was copied or adapted from another repository, from a
`formal_proof` link, or from any solution to this pool target; the only external Lean input is
Mathlib itself and the pool module's definition of `Erdos1095.g`. The file contains no `sorry`,
`axiom`, `native_decide`, `partial`, or `set_option`.
