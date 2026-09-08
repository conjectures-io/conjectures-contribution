# Sources and provenance — erdos-158

## Target

`Erdos158.erdos_158` in `FormalConjectures/ErdosProblems/158.lean`: is it true that every
infinite `B₂[2]` set `A ⊆ ℕ` satisfies `liminf_N |A ∩ [0,N)| · N^(-1/2) = 0`?

- Problem page: https://www.erdosproblems.com/158
- Formal Conjectures repository: https://github.com/google-deepmind/formal-conjectures
- Mathlib4: https://github.com/leanprover-community/mathlib4

Background literature (consulted for the shape of the statements only, no proof was taken from
any of these):

- P. Erdős, A. Sárközy, V. T. Sós, *On sum sets of Sidon sets, I*, Journal of Number Theory 47
  (1994), 329–347. https://doi.org/10.1006/jnth.1994.1041
- The `B₂[g]` terminology and the Sidon counting bound are classical; see e.g. the survey
  K. O'Bryant, *A complete annotated bibliography of work related to Sidon sequences*,
  Electronic Journal of Combinatorics, Dynamic Survey 11 (2004).
  https://doi.org/10.37236/32

## The obstacle this contribution addresses

The pool file introduces `Erdos158.B2` and proves exactly one fact about it,
`Erdos158.b2_one : B2 1 A ↔ IsSidon A`. The identifier `B2` is declared nowhere else in the
repository, and the string `Sidon` occurs nowhere in Mathlib (checked by grep over
`.lake/packages/mathlib/Mathlib`). So nothing in the pinned environment bounds the counting
function of a `B₂[g]` set, and nothing says that the real sequence
`fun N => |A ∩ [0,N)| · N^(-1/2)`, whose `liminf` the target takes, is bounded at all.

This is a mechanical blocker, not a cosmetic one. `Filter.liminf_le_iff`,
`Filter.le_liminf_iff`, `Filter.le_liminf_of_le` and `Filter.liminf_le_of_frequently_le` all
carry `IsCoboundedUnder` / `IsBoundedUnder` side conditions supplied by a `by isBoundedDefault`
autoparam. I checked in the pinned environment that the autoparam does **not** fire for the
target's sequence: elaborating

```
example (A : Set ℕ) (x : ℝ) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop ≤ x ↔ …
  := liminf_le_iff
```

reports `could not synthesize default value for parameter 'h₁'` and `… 'h₂'`, leaving both
`IsCoboundedUnder (· ≥ ·)` and `IsBoundedUnder (· ≥ ·)` open. Coboundedness is also what makes
the target's conclusion mean what it should: Mathlib's `Real.liminf_of_not_isCoboundedUnder`
(a `@[simp]` lemma) says every real sequence that is *not* `IsCoboundedUnder (· ≥ ·)` has
`liminf` equal to `0` regardless of its values.

## Delta — what is new here

Everything is proved; nothing is assumed, and the file contains no unproved step.

1. **A counting bound for `B₂[g]` sets from scratch.** `sq_ncard_inter_Iio_le` proves
   `|A ∩ [0,N)|² ≤ 2·g·(2N−1)` by a two-step pigeonhole
   (`Finset.card_le_mul_card_image_of_maps_to` applied first to `(a,a') ↦ (min, max)` and then
   to `(a,a') ↦ a + a'`), and `ncard_inter_Iio_le` gives the real form `A(N) ≤ 2·√g·√N`. From
   it come `normalized_le`, the three boundedness lemmas
   (`isBoundedUnder_ge_normalized`, `isBoundedUnder_le_normalized`,
   `isCoboundedUnder_ge_normalized`) that discharge the autoparams above, and
   `liminf_nonneg` / `liminf_le`, which place the target's `liminf` in `[0, 2√g]`.

2. **The target's right-hand side, reformulated as an equivalence.** `liminf_eq_zero_iff`
   replaces `liminf … = 0` by the elementary "for every `ε > 0` there are infinitely many `N`
   with `A(N) < ε·√N`", with no `Real.rpow` and no `liminf` left; `liminf_ne_zero_iff` is its
   negation, in exactly the shape (`∃ c > 0, ∀ᶠ N in atTop, c ≤ …`) that the pool file's own
   proof of `Erdos158.erdos_158.variants.isSidon` derives by a hand-rolled `csSup` argument.
   `liminf_eq_zero_of_finite` shows the target's `A.Infinite` binder is redundant, and
   `erdos_158_rhs_iff` packages both improvements into a single `↔` against the target's whole
   right-hand side. Because these are equivalences they are safe to use in either direction.

3. **The Erdős–Sárközy–Sós route as a checked interface.**
   `liminf_eq_zero_of_liminf_mul_sqrt_log_lt_top` shows that for a `B₂[g]` set the bound
   `liminf ofReal (A(N)·N^(-1/2)·(log N)^(1/2)) < ⊤` implies the target's conclusion. For
   `g = 1` that hypothesis is precisely the [ESS94] theorem recorded (unproved) in the pool file
   as `erdos_158.variants.isSidon'`, so the lemma is the `B₂[g]` generalisation of the pool
   file's derivation of `erdos_158.variants.isSidon`, with the Sidon hypothesis dropped and the
   `csSup` computation replaced by `liminf_ne_zero_iff`. **Honesty note:** for `g = 2` the
   hypothesis is open; this is a *sufficient* condition, not a reformulation, and the file says
   so in the docstring. It is not vacuous (it holds for every finite `B₂[g]` set, and for `g=1`
   it is a theorem of the literature). The file never invokes `erdos_158.variants.isSidon'` or
   `erdos_158.variants.isSidon`, precisely because those are unproved in the pool; the
   hypothesis is taken as an explicit argument, and every declaration is axiom-clean.

4. **A checked counterexample delimiting the hypotheses.** `not_b2_two_squares` proves the
   perfect squares are not `B₂[2]`, via `325 = 1 + 324 = 36 + 289 = 100 + 225`;
   `ncard_squares_inter_Iio` computes `|squares ∩ [0, N+1)| = ⌊√N⌋ + 1`;
   `squares_normalized_bounds`, `tendsto_squares_normalized` and `liminf_squares_eq_one` show
   the normalised counting function of the squares is sandwiched in `[1, 1 + 1/√N]` and has
   `liminf` exactly `1`. `exists_infinite_liminf_ne_zero` concludes that the `B2 2` hypothesis
   in the target cannot be deleted: without it the statement is false. This also exhibits a
   genuinely nonzero value of the target's `liminf`, which is what a solver needs in order to
   know the `liminf` is not being computed by the `Real.sSup` junk-value route.

5. **The target is strictly more general than the solved Sidon case.**
   `doubleBlocks B = 2·B ∪ (2·B+1)` is proved `B₂[2]` whenever `B` is Sidon
   (`b2_two_doubleBlocks`), never Sidon once `B` has two elements
   (`not_isSidon_doubleBlocks`), infinite when `B` is (`infinite_doubleBlocks`), and satisfies
   `|doubleBlocks B ∩ [0,2N)| = 2·|B ∩ [0,N)|` (`ncard_doubleBlocks_inter_Iio`), i.e. it is
   denser than `B` by a factor `√2` in the target's normalisation.
   `doubleBlocks_mem_target_binders` certifies this family as a legal instance of the target's
   binders.

## Novelty checks performed

- `grep -rn "Sidon" .lake/packages/mathlib/Mathlib` returns nothing; `B2` is declared only in
  `FormalConjectures/ErdosProblems/158.lean` (Green 31 mentions "B2-Sequences" in a bibliography
  comment, not as a declaration).
- `exact?` fails on `b2_mono` and on `liminf_eq_zero_of_finite`; `simp` makes no progress on
  `normalized_eq`. None of the substantive lemmas is a one-liner from the pinned environment.
- No proof text was copied from any repository or `formal_proof` link. The only proof reused as
  a *template* is the pool file's own `Erdos158.erdos_158.variants.isSidon`, which lives in the
  target module itself; the version here is a strict generalisation (`B2 g` instead of Sidon)
  with a different and shorter middle step, and this is stated in the lemma's docstring.

## Verification

Compiled against the pinned toolchain with `lake env lean CW_erdos_158.lean`: **0 errors,
0 warnings**. `#print axioms` was run on all 31 theorems; each depends only on a subset of
`[propext, Classical.choice, Quot.sound]` (the `#print` lines were then removed and the file
recompiled clean). The file contains no `sorry`, `admit`, `axiom`, `native_decide`, `#eval`,
`unsafe`, `extern`, `implemented_by`, `partial`, or `set_option`; it is plain LF UTF-8 with no
BOM and no bidirectional/control characters; all lines are at most 100 characters. 33
declarations, all inside `namespace Contribution.Erdos158Counting`.

## AI assistance

This contribution was produced by Claude (Anthropic), an AI assistant, working under human
direction. The AI read the target module and its dependencies, chose the lemmas, wrote every
Lean proof, and iterated against the compiler until the file elaborated with zero errors and
zero warnings. Every claim in the module docstring was checked in the pinned environment before
being written (the autoparam failure, the Mathlib greps, the `exact?`/`simp` novelty probes, the
axiom audit). The human operator reviewed and submitted the result.

## Originality

This work is original to this submission. All statements and proofs were written for this
contribution. No proof was copied from Mathlib, from another contributor's submission, from a
`formal_proof` link, or from any external repository. Where a proof idea is classical (the
pigeonhole counting bound for `B₂[g]` sets) or adapted from the target module itself (the
`liminf` derivation in `Erdos158.erdos_158.variants.isSidon`), this is stated explicitly above
and in the corresponding docstring.
