# Sources and provenance — CW_erdos_1137.lean

## Target

Erdős Problem 1137, reward theorem `Erdos1137.erdos_1137`, in
`FormalConjectures/ErdosProblems/1137.lean` of the Formal Conjectures repository.

* Problem page: https://www.erdosproblems.com/1137 (the reference given in the pool file).
  Note for the reviewer: fetching this page from the build environment returned HTTP 403, so
  **nothing in the contribution depends on its content**. The only statement of the problem used
  is the Lean statement in the pool file itself.
* Formal Conjectures repository: https://github.com/google-deepmind/formal-conjectures
* The pool file contains exactly one declaration (the open reward theorem, with an unfilled
  answer) and no companion declarations, so there was no "research solved / textbook / test"
  companion available to prove outright.

## Obstacle

The obligation is
`Tendsto (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
(((range x).sup primeGap : ℕ) : ℝ) ^ 2) atTop (𝓝 0)`.

* `Finset.sup` does not commute with a product, so the numerator cannot be split into its two
  shifted factors. The one bound that is free, `maxAdjProd x ≤ maxGap x ^ 2`, is exactly the
  trivial bound the problem asks to beat (it is proved in the file, as
  `maxAdjProd_le_sq_maxGap`, so that the quotient is known to lie in `[0, 1]`).
* All the content of the problem is about a pair of *adjacent* gaps, but the statement never
  names such a pair; the truncated subtraction `n - 1` makes the `n = 0` term
  `primeGap 0 * primeGap 0` and forces a hand-derivation of `n - 1 < x` at every step.
* Every quantity is a natural number while the statement divides in `ℝ` by a square, so each
  step must cross `Nat.cast` and be guarded by positivity of the denominator.
* `primeGap` is defined in `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, whose body
  is the definition and nothing else — there is no positivity lemma, no monotonicity, no API.
  `grep -rn primeGap` over `.lake/packages/mathlib/Mathlib` returns no hits (checked in the
  pinned environment), so nothing can be imported either.

## Delta (what this file adds)

1. `primeGap_pos` — the missing base fact `0 < primeGap n`, from `Nat.nth_strictMono` and
   `Nat.infinite_setOf_prime`. Checked that `exact?` cannot close this goal in the pinned
   environment.
2. `maxGap`, `maxAdjProd`, `maxAdjMin` — names for the target's denominator, the target's
   numerator, and the new quantity `sup_{n < x} min (d_n) (d_{n-1})`, with API
   (`le_maxGap`, `one_le_maxAdjMin`, `maxGap_pos`, `maxAdjMin_le_maxGap`).
3. `sq_maxAdjMin_le_maxAdjProd` and `maxAdjProd_le_maxGap_mul_maxAdjMin` — the two-sided `ℕ`
   sandwich `maxAdjMin x ^ 2 ≤ maxAdjProd x ≤ maxGap x * maxAdjMin x`, from
   `a * b = max a b * min a b`. This is the mathematical core.
4. `tendsto_ratio_iff_tendsto_adjRatio` — the resulting **equivalence** (not a one-way
   reduction): the target limit vanishes iff `maxAdjMin x / maxGap x → 0`. The forward direction
   goes through `Real.sqrt`, since what the numerator returns is a bound on a square.
5. `tendsto_adjRatio_iff` and `nat_criterion_iff` — removal of `ℝ` and of the remaining
   `Finset.sup`, ending in a division-free arithmetic criterion.
6. `erdos_1137_tendsto_iff` — the handoff: the target obligation, stated verbatim, is equivalent
   to "for every `k > 0`, for all large `x`, every `n < x` has
   `k * min (primeGap n) (primeGap (n - 1)) < (range x).sup primeGap`".
7. `erdos_1137_true_of_isolated`, `erdos_1137_false_of_not_isolated`, and the refutation feeder
   `not_isolated_of_frequently` — worked use sites producing the reward statement with the answer
   instantiated to `True` resp. `False`.
8. `tendsto_maxGap_atTop_of_criterion` — the criterion is not vacuous: it already forces
   `maxGap x → ∞`.

Because the handoff is an `Iff`, it cannot be defeated by exhibiting a legal instance of the
target's binders that refutes a one-sided hypothesis: the criterion is equivalent to the target
obligation, for every `x`, unconditionally.

## Mathlib declarations relied on (pinned toolchain `leanprover/lean4:v4.27.0`)

* `Nat.nth_strictMono`, `Nat.infinite_setOf_prime` —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Nth.html and
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/PrimeFin.html
* `Finset.le_sup`, `Finset.sup_le`, `Finset.exists_mem_eq_sup`, `Finset.nonempty_range_iff` —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Lattice/Fold.html
* `squeeze_zero'`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`, `Filter.Tendsto.sqrt`,
  `NormedAddCommGroup.tendsto_nhds_zero`, `Filter.Tendsto.eventually_lt_const`,
  `Filter.Frequently.and_eventually`, `Filter.tendsto_add_atTop_nat`, `div_le_div_iff₀`,
  `div_lt_div_iff₀`, `exists_nat_one_div_lt` — https://leanprover-community.github.io/mathlib4_docs/

## Verification

Compiled with `lake env lean CW_erdos_1137.lean` against the pinned repository: **zero errors,
zero warnings**. Every one of the 18 theorems was checked with `#print axioms` (in a scratch copy,
removed afterwards) and depends only on `[propext, Classical.choice, Quot.sound]`. The statement
of `erdos_1137_tendsto_iff` was additionally type-checked against the target expression
copy-pasted verbatim from `FormalConjectures/ErdosProblems/1137.lean`, confirming the two are the
same term. The file contains no `sorry`-like escape, no `set_option`, no `decide`-by-compilation,
and imports only `Mathlib` and `FormalConjectures.ErdosProblems.«1137»`.

## AI assistance disclosure

This contribution was produced with AI assistance: it was written by Anthropic's Claude
(Claude Code, Opus 5) acting on my instructions. The mathematical idea (replacing the maximal
adjacent *product* by the maximal adjacent *minimum*, via `a * b = max a b * min a b`, and the
`sqrt` squeeze that makes the reduction an equivalence), the Lean statements, and all Lean proofs
were generated in that session and then verified by the Lean 4 kernel in the pinned environment;
no claim in this file is asserted on the strength of the model's word alone.

## Originality

All declarations are new and were written for this submission. No proof, statement or proof
script was copied from another repository, from a `formal_proof` link, or from any solution of
Erdős 1137 (the pool file carries no such link, and the problem is listed as open). The
supporting lemmas were checked against Mathlib by `grep` and by `exact?` before being kept.
