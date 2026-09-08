# sources.md - Erdos 120 partial contribution (Contribution.Erdos120Steinhaus)

## Target

`Erdos120.erdos_120` in `FormalConjectures/ErdosProblems/120.lean`:
`answer(...) ↔ ∀ A : Set ℝ, A.Infinite → Erdos120For A`, where
`Erdos120For A := ∃ E, MeasurableSet E ∧ 0 < volume E ∧ ∀ a b, a ≠ 0 → ¬ ((a * · + b) '' A ⊆ E)`.
This is the Erdos similarity problem and it is open.

- https://www.erdosproblems.com/120
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/120.lean

## The obstacle

The pool file states two results and proves neither.

1. The companion `Erdos120.erdos_120.variants.finite_set` (`@[category research solved]`,
   `A.Finite → ¬ Erdos120For A`) is Steinhaus's 1920 theorem: every set of positive Lebesgue
   measure contains an affine copy of every finite set. Its proof in the pool file is a
   placeholder, so the declaration depends on the constant an incomplete proof emits (checked:
   the kernel dependency list for `Erdos120.erdos_120.variants.finite_set` contains it, while
   every declaration of this contribution lists exactly `[propext, Classical.choice,
   Quot.sound]`). Mathlib carries the Lebesgue density theorem only in ratio-of-measures form
   (`Besicovitch.ae_tendsto_measure_inter_div`), and nothing that turns it into a measure bound
   on the family of affine images `c ↦ x + c * (t - min A)`; greps of Mathlib for `affine copy`,
   `similar copy`, `homothetic`, `Steinhaus` and `density` produced no statement of this shape
   (the only `Steinhaus` hits are Banach-Steinhaus).
2. The open statement quantifies over all infinite `A ⊆ ℝ` and all measurable `E`, so a solver
   has no normal form: no boundedness, no countability, and no normalisation of the two-parameter
   affine freedom `a * A + b`.

## Delta (what this file adds)

All 14 declarations are in `namespace Contribution.Erdos120Steinhaus`; the file compiles with
zero errors and zero warnings against the pinned toolchain (`leanprover/lean4:v4.27.0`, the
repository's pinned Mathlib), and every theorem's kernel dependency list is exactly
`[propext, Classical.choice, Quot.sound]`.

* `exists_mem_measure_compl_inter_closedBall_le` - a quantitative Lebesgue density point derived
  from `Besicovitch.ae_tendsto_measure_inter_div`: for measurable `E` with `0 < volume E` and any
  `ε > 0` there are `x ∈ E` and `r₀ > 0` with
  `volume (Eᶜ ∩ closedBall x r) ≤ ENNReal.ofReal (ε * (2 * r))` for all `0 < r < r₀`. This is the
  usable, division-free form; Mathlib only provides the ratio limit.
* `volume_preimage_affine` - `volume ((fun c => x + c * s) ⁻¹' S) = ENNReal.ofReal |s⁻¹| * volume S`
  for `s ≠ 0` and an arbitrary (not necessarily measurable) `S`. Checked that `simp` does not
  close this: `simp` leaves the left-hand side untouched.
* `exists_affine_copy_subset_of_finite` - **Steinhaus's theorem, strengthened**: for measurable
  `E` with `0 < volume E`, finite `A` and any `η > 0`, there are `a, b` with `0 < a < η` and
  `(a * · + b) '' A ⊆ E`. The ratio is positive and can be prescribed arbitrarily small (so the
  admissible ratios accumulate at 0), and `volume E = ⊤` is allowed. Proof: density point +
  a union bound over the `|A| - 1` "bad ratio" sets inside `Ioc 0 δ`, each pulled back through
  `volume_preimage_affine`, with `ε := m / (4 * k * M)` chosen so the bad set has measure `≤ δ/2`.
* `not_erdos120For_of_finite` - the pool companion, proved outright. Honest note: `exact?` does
  close this goal, but only with the pool's own unproved `Erdos120.erdos_120.variants.finite_set`;
  the proof here does not use it and is placeholder-free.
* `erdos120For_mono`, `erdos120For_image_affine`, `erdos120For_image_affine_iff`,
  `bddAbove_and_bddBelow_of_image_subset_Icc`, `erdos120For_of_not_bddAbove`,
  `erdos120For_of_not_bddBelow`, `exists_countable_infinite_subset` - the structural API:
  `Erdos120For` is monotone under `⊆`, is invariant under the affine group (as an `Iff`), and
  holds outright, with the explicit witness `Set.Icc 0 1`, for every set unbounded above or below.
* `forall_infinite_iff_forall_countable_subset_unitInterval` - the resulting **normal form**, an
  equivalence (not a one-way reduction): the target's right-hand side
  `∀ A : Set ℝ, A.Infinite → Erdos120For A` is equivalent to its restriction to *countable*
  infinite subsets of `Set.Icc (0 : ℝ) 1`. Because it is an `Iff` whose right side is a special
  case of the left, there is no legal instance of the target's binders that refutes the
  hypothesis.
* `forall_infinite_iff_forall_erdos120For_iff_infinite` and `use_site_erdos_120_answer_true` -
  worked use sites: the target's right-hand side is equivalent to `∀ A, Erdos120For A ↔ A.Infinite`
  (so the `A.Infinite` hypothesis is exactly sharp), and the second theorem is the target's own
  statement with the unknown answer instantiated to `True`, derived from the normal form.

## Sources consulted

- https://www.erdosproblems.com/120 - the problem statement (Erdos similarity problem).
- https://matwbn.icm.edu.pl/ksiazki/fm/fm1/fm1111.pdf - H. Steinhaus, *Sur les distances des
  points dans les ensembles de mesure positive*, Fund. Math. 1 (1920), 93-104. Cited by the pool
  file as the source of the finite case. I did not copy any proof from it; the Lebesgue-density /
  union-bound proof formalised here was written from scratch in Lean and is the standard textbook
  argument.
- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Covering/Besicovitch.lean
  - `Besicovitch.ae_tendsto_measure_inter_div`, the density theorem used.
- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean
  - `Real.volume_preimage_mul_right`, used for the affine pullback.
- https://github.com/google-deepmind/formal-conjectures - the pool repository and its conventions.

No proof was taken from another repository, from a `formal_proof` link, or from any existing
solution of this problem.

## AI assistance

This contribution was produced by an AI assistant (Claude, Anthropic) working in a terminal
agent session, at the user's direction. The assistant read the pool file, searched Mathlib,
designed the statements, wrote every proof, and iterated against the Lean compiler until the file
compiled with zero errors and zero warnings; the kernel dependency check was run on all 14
declarations and then removed from the submitted file. No proof text was copied from a third
party.

## Originality

The Lean statements and proofs in `CW_erdos_120.lean` are original work written for this
contribution. The underlying mathematics of `exists_affine_copy_subset_of_finite` is the
classical Steinhaus argument (1920) and is not claimed as new mathematics; the strengthening to
arbitrarily small positive ratios, the normal-form equivalence
`forall_infinite_iff_forall_countable_subset_unitInterval`, and the whole formalisation are new
here.
