# sources.md — partial contribution to Erdős Problem 1073

## Target

`Erdos1073.erdos_1073` in `FormalConjectures/ErdosProblems/1073.lean`:

    answer(..) ↔ ∃ (o : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ x, Erdos1073.A x ≤ x ^ (o x)

where `Erdos1073.A x = {u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x}.ncard`, i.e. `A x`
counts the composite `u < x` that divide `n ! + 1` for some `n`. The question is whether
`A x ≤ x ^ o(1)`.

Contributed file: `CW_erdos_1073.lean`, namespace `Contribution.Erdos1073FactorialDivisors`
(24 declarations: 21 theorems, 2 defs, 1 `Decidable` instance).

## Sources consulted

- Problem page cited by the pool file: https://www.erdosproblems.com/1073
  Honest note: from this machine the site (and https://oeis.org) is behind a Cloudflare
  interstitial and returned HTTP 403 / a JavaScript challenge, so I did **not** read the page
  while doing this work. Everything here was derived from the Lean statement in the pool file
  and from standard facts about `n ! + 1`. No proof, and no numerical table, was copied from
  any external source or from any `formal_proof` link.
- The repository the target lives in: https://github.com/google-deepmind/formal-conjectures
- Wilson's theorem: https://en.wikipedia.org/wiki/Wilson%27s_theorem
- Wilson primes (`p ^ 2 ∣ (p - 1)! + 1` for `p = 5, 13, 563`):
  https://en.wikipedia.org/wiki/Wilson_prime
- Factorial primes (`n ! + 1`): https://en.wikipedia.org/wiki/Factorial_prime
- Mathlib declarations reused (pinned Mathlib in this repo, toolchain
  `leanprover/lean4:v4.27.0`), documentation at https://leanprover-community.github.io/mathlib4_docs/ :
  `Nat.coprime_factorial_iff` (`Mathlib/Data/Nat/Prime/Factorial.lean`),
  `Nat.minFac_sq_le_self` (`Mathlib/Data/Nat/Prime/Defs.lean`),
  `Nat.prime_iff_fac_equiv_neg_one` (`Mathlib/NumberTheory/Wilson.lean`),
  `Asymptotics.isLittleO_one_iff` (`Mathlib/Analysis/Asymptotics/Lemmas.lean`),
  `Real.rpow_def_of_pos`, `Real.log_rpow`, `Set.ncard_coe_finset`.

## The obstacle

*The counting function is opaque.* `Erdos1073.A` is a `Set.ncard` over a set defined by an
**unbounded** existential `∃ n, n ! + 1 ≡ 0 [MOD u]`. Checked in the pinned environment:
`Decidable (∃ n, n ! + 1 ≡ 0 [MOD 25])` fails to synthesize, and `decide` on
`Erdos1073.A 26 = 1` reports that reduction is stuck at `Classical.choice`. So no single
membership, let alone a value of `A`, can be obtained by computation from the statement as
given, and `exact?` closes neither of the two lemmas that would bound the witness.

*The `o(1)` exponent.* The right-hand side asks for one function `o` with `o =o[atTop] 1` and
`A x ≤ x ^ (o x)` for **all** `x` — including `x = 0`, where `(0 : ℝ) ^ (o 0)` equals `1` only
when `o 0 = 0`, and `x = 1`, where the bound reads `A 1 ≤ 1` — whereas any analytic argument
produces, for each fixed `ε > 0`, an eventual bound `A x ≤ x ^ ε`. Mathlib has
`Asymptotics.isLittleO_one_iff`, but nothing converting a family of eventual `x ^ ε` bounds
into a single `x ^ (o x)` bound.

## Delta: what this file adds over the pinned environment

1. **The search bound (the arithmetic crux).** `lt_minFac_of_dvd_factorial_add_one`: if
   `u ∣ n ! + 1` and `u ≠ 1` then `n < u.minFac`. `succ_sq_le_of_dvd_factorial_add_one`: for
   *composite* `u`, `(n + 1) ^ 2 ≤ u`. This is what turns the unbounded `∃ n` into a search
   over `n < u.sqrt`. `five_le_minFac` and `twentyFive_le` push the same computation one step:
   no such `u` has a prime factor below `5`, hence `25 ≤ u`, and `25 = 4 ! + 1` shows this is
   sharp.
2. **Decidability and a computable counting function.** `IsFactorialDivisor` is a bounded
   test with a `DecidablePred` instance; `isFactorialDivisor_iff` proves it equivalent to the
   pool's membership condition; `coe_support` and `A_eq_card` identify the noncomputable
   `Erdos1073.A x` with `(support x).card` for the concrete `Finset`
   `support x = (Finset.range x).filter IsFactorialDivisor`. `support_1000` then evaluates the
   set below `1000` **in the kernel** (`decide +kernel`, no `native_decide`) to
   `{25, 121, 169, 437, 551, 667, 721}`, giving `A_1000 : Erdos1073.A 1000 = 7`;
   `A_eq_zero_of_le` gives `A x = 0` for `x ≤ 25`. (Cross-check: the same list was produced
   independently by a short Python/sympy sweep before the Lean computation was attempted; the
   two agree. The two squares in the list, `25 = 5 ^ 2` and `169 = 13 ^ 2`, are the Wilson
   primes `5` and `13`.)
3. **Removing the `o(1)` exponent.** `exists_isLittleO_one_rpow_iff` is a general equivalence,
   for any `f : ℕ → ℝ` with `f 0 ≤ 1` and `f 1 ≤ 1`:
   `(∃ o, o =o[atTop] 1 ∧ ∀ x, f x ≤ x ^ (o x)) ↔ (∀ ε > 0, ∀ᶠ x, f x ≤ x ^ ε)`. The exponent
   is constructed as `log (max (f x) 1) / log x`, which also handles `x = 0, 1` correctly.
   `erdos_1073_rhs_iff` specialises it to the target and simultaneously swaps `A` for the
   computable `support`, so the target's right-hand side becomes one elementary estimate.
4. **Non-vacuity.** `composite_factorial_pred_add_one` proves, from Wilson's theorem, that
   `(p - 1)! + 1` is composite for every prime `p ≥ 5`; hence
   `infinite_setOf_composite_dvd_factorial_add_one` (the set is infinite) and `exists_le_A`
   (`A` is unbounded). So the conjecture is not the claim that finitely many `u` occur.
5. **Use site.** `erdos_1073_true_of_card_support_le` has as its conclusion *literally* the
   pool statement (`answer(..)` elaborates to `True`), derived from the computable estimate;
   `card_support_le_of_erdos_1073_true` is the converse, and `answer_iff_card_bound P` covers
   either answer. Because `erdos_1073_rhs_iff` is an equivalence, the reduction is not a
   one-way weakening and its hypothesis cannot be refuted for any instance of the target.

What is **not** done: no upper bound on `A x` is proved. The naive decomposition
`support x ⊆ ⋃_{n < sqrt x} divisors (n ! + 1)` cannot work, since each of the `sqrt x` terms
contributes at least one divisor; controlling the divisors of `n ! + 1` that exceed `(n + 1)^2`
is the open part and is untouched here.

## Novelty checks performed

- `exact?` was run on each headline statement — `lt_minFac_of_dvd_factorial_add_one`,
  `succ_sq_le_of_dvd_factorial_add_one`, `five_le_minFac`, `composite_factorial_pred_add_one`,
  `exists_isLittleO_one_rpow_iff`, `infinite_setOf_composite_dvd_factorial_add_one` — and
  failed on all six ("`exact?` could not close the goal"). `simp_all` / `aesop` also fail on
  the first four.
- `grep` over `.lake/packages/mathlib/Mathlib` finds no `Nat.Composite` at all (it is defined
  in `FormalConjecturesForMathlib.Data.Nat.Prime.Composite`), no lemma bounding the witness in
  `u ∣ n ! + 1`, and no characterisation of `f x = x ^ o(1)` in the `Real.rpow` asymptotics
  files.

## Verification

- The file compiles with `lake env lean CW_erdos_1073.lean` with **zero errors and zero
  warnings** (empty output, exit code 0), in about 40 s, on the pinned toolchain
  `leanprover/lean4:v4.27.0`.
- `#print axioms` was run on all 21 theorems: each depends only on
  `[propext, Classical.choice, Quot.sound]`. The `#print axioms` lines were then removed and
  the file recompiled clean.
- No `sorry`, `admit`, `axiom`, `native_decide`, `#eval`, `unsafe`, `extern`,
  `implemented_by`, no `partial` modifier, and no `set_option` anywhere in the file (grep-
  verified, including inside comments). Plain LF, no BOM, no unicode control or bidi
  characters, no line longer than 100 characters.
- `Erdos1073.erdos_1073` itself is never referenced inside any proof (its pool proof is a
  placeholder), so nothing here launders an unproved statement.

## AI assistance and originality

This contribution was produced by Claude (Anthropic) driving Lean 4 in an agentic session, at
the direction of the submitting account. Every statement and every proof in the file was
written for this contribution and machine-checked by the Lean kernel in the pinned
environment; no proof, tactic script, or numerical table was copied from another repository,
from a `formal_proof` link, or from any published solution. The mathematics used —
`gcd(u, n!) = 1` forcing all prime factors of `u ∣ n ! + 1` above `n`, `minFac(u)^2 ≤ u` for
composite `u`, and Wilson's theorem — is classical and is credited above; the Lean
formalisation, the decidable reformulation, the `x ^ o(1)` interface and the reduction of the
pool statement are original to this submission.
