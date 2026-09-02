# sources.md — Erdős Problem 212 partial contribution

## Target

`Erdos212.erdos_212` in `FormalConjectures/ErdosProblems/212.lean`:

> Is there a dense subset of the plane all of whose pairwise distances are rational?
> `answer(…) ↔ ∃ u : Set ℂ, Dense u ∧ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast`

This is the Erdős–Ulam problem. It is open unconditionally; it is known to have a negative
answer conditionally on the Bombieri–Lang conjecture.

Note on the pinned environment: with `google.answer = always_true` the answer slot elaborates to
`True`, so the pinned statement reads `True ↔ ∃ u, …`. A *positive* solver therefore closes the
pinned statement by producing the existential; a *negative* solver refutes it and must replace the
answer slot by `False` first. Both directions are spelled out in the file's use sites.

## The obstacle addressed

The reward statement is a bare existential with no structure attached. Concretely:

1. `Set.Pairwise` only applies to *distinct* points, so every use of the hypothesis carries a
   `p ≠ q` side goal, including where it is irrelevant (`dist p p = 0` is rational).
2. `Set.range (Rat.cast : ℚ → ℝ)` is an opaque `Set ℝ`. It is a subfield, but none of
   `add_mem` / `sub_mem` / `mul_mem` / `div_mem` / `pow_mem` is available on it, so every one of
   the many arithmetic steps in the classical argument must `obtain` rational witnesses and
   `push_cast` them back by hand.
3. Every classical treatment starts by normalising two points of the set to `0` and `1`, using
   invariance under similarities `z ↦ a * z + b` with `‖a‖ ∈ ℚ`. Nothing in the pinned
   environment does this, and by hand it needs two distinct points of a dense set plus a check
   that an affine map preserves both density and rationality of distances.

Consequently the standard opening move of the Erdős–Ulam literature — "after normalising, every
point has rational real part and rational squared imaginary part, and all points lie in a single
imaginary quadratic field" — has never been checked in Lean.

## The delta

One self-contained file, `CW_erdos_212.lean`, 32 declarations, all in namespace
`Contribution.Erdos212RationalDistance`. It compiles with zero errors and zero warnings against
the pinned workspace (Lean 4.27.0, Mathlib `a3a10db0`), and every declaration depends only on
`[propext, Classical.choice, Quot.sound]` (checked with `#print axioms`, then removed).

**Infrastructure.** `ratField : Subfield ℝ` is the image of `ℚ` in `ℝ`; `mem_ratField_iff` is the
definitional bridge from the target's `Set.range Rat.cast`, which opens the whole `Subfield` API
on the target's own predicate. `IsRatDist` names the predicate and `isRatDist_iff_target` verifies
by `Iff.rfl` that there is no statement drift. `IsRatDist.dist_mem_ratField` kills the spurious
`p ≠ q` side condition once and for all; `IsRatDist.exists_pos_rat_dist` packages positivity.

**Normalisation.** `IsRatDist.image_affine` records invariance under rational similarities;
`exists_ne_of_dense` produces two distinct points of a dense subset of `ℂ`; and
`IsRatDist.exists_normalizing_map` combines them into an injective, density-preserving,
rational-distance-preserving affine map sending two chosen points to `0` and `1`.

**Mathematical content (the classical structure theorem, formalised).**

* `IsRatDist.re_mem_ratField` and `IsRatDist.im_sq_mem_ratField`: if `0, 1 ∈ u` then every
  `p ∈ u` has `p.re ∈ ℚ` and `p.im ^ 2 ∈ ℚ` (subtract the circle equations centred at `0`
  and at `1`).
* `IsRatDist.im_mul_im_mem_ratField`: moreover `p.im * q.im ∈ ℚ` for all `p q ∈ u` — the rigidity
  step that forces all imaginary parts onto a *single* rational line.
* `IsRatDist.exists_subset_ratSlice`: hence a normalised rational-distance set is contained in
  `RatSlice y = ℚ ⊕ ℚ·(y·i)` for a single `y` with `y ^ 2 ∈ ℚ`, i.e. in a fixed imaginary
  quadratic field — except in the degenerate collinear case `y = 0` (the branch the proof takes
  when every point of `u` is real), where `RatSlice 0` is just `ℚ ⊆ ℝ`. The degenerate case is
  what `not_dense_of_forall_im_eq_zero` rules out once density is assumed.

**Consequences.**

* `IsRatDist.countable`: **every** rational-distance set in the plane is countable, with no
  normalisation hypothesis. So any witness of the target is countable — a positive answer must be
  a countable dense set; nothing of positive measure or of second category can be a
  rational-distance set.
* `exists_dense_isRatDist_iff` and, after removing the last real scalar via the homeomorphism
  `imScale` and `dense_coord_image_iff`, the headline `exists_dense_isRatDist_iff_rat`:

  > A dense rational-distance subset of the plane exists **iff** there are a rational `d > 0` and
  > a set `S ⊆ ℚ × ℚ`, dense in the plane, such that `(a₁ - a₂) ^ 2 + d * (c₁ - c₂) ^ 2` is a
  > square in `ℚ` for every pair of points of `S`.

  Distances, normalisation and irrational numbers are all gone from the right-hand side. The `←`
  direction is `isRatDist_coord_image`, the construction interface a *positive* solver would use.

**Honesty checks (non-vacuity).** `dense_ratSlice_one` proves that `RatSlice 1` (the Gaussian
rationals) is dense, so the containment produced by the structure theorem is not by itself a
contradiction and the reduction does not silently settle the problem.
`exists_infinite_normalized_isRatDist` exhibits an infinite set satisfying
`IsRatDist u ∧ 0 ∈ u ∧ 1 ∈ u`, built through `isRatDist_coord_image`, so neither the normalised
hypotheses nor the construction interface is vacuous.

**Use sites.** Four declarations state the handoff against the reward theorem's own right-hand
side, `∃ u : Set ℂ, Dense u ∧ u.Pairwise fun c₁ c₂ => dist c₁ c₂ ∈ Set.range Rat.cast`:

1. `erdos_212_iff_diophantine` — the reduction itself, on that right-hand side.
2. `erdos_212_true_iff_of_dense_rational_family` — the positive side: from the arithmetic family
   it produces `True ↔ ∃ u, …`, which under the pinned answer setting *is* the reward statement.
3. `erdos_212_of_no_dense_rational_family` — the negative side: refuting the arithmetic family
   refutes the geometric existential. Under the pinned answer setting this *refutes* the reward
   statement rather than proving it, so a negative-answer solver must replace the answer slot by
   `False` first; the docstring says so explicitly.
4. `countable_of_erdos_212_predicate` — countability, applied straight to the target predicate.

## Novelty check

Before keeping each lemma I grepped the pinned Mathlib source
(`.lake/packages/mathlib/Mathlib`) and ran `exact?` on the goals. There is no Mathlib material on
rational distance sets, the Anning–Erdős theorem, or the Erdős–Ulam problem (`grep -r "Anning"`
and `grep -rl "rational distance"` both return nothing). `Dense.exists_ne` does not exist, so
`exists_ne_of_dense` is not a duplicate; `Dense (e '' A) ↔ Dense A` for a homeomorphism is *not*
found by `exact?`, but `Homeomorph.isDenseEmbedding` plus `IsDenseEmbedding.dense_image` does the
job, so I used Mathlib's lemmas instead of restating them. Likewise the whole subfield
membership API (`zero_mem`, `one_mem`, `add_mem`, `sub_mem`, `mul_mem`, `inv_mem`, `div_mem`,
`pow_mem`, `ofNat_mem`) and `Set.countable_range`, `Set.image_preimage_eq_of_subset`,
`Set.Countable.preimage`, `Set.infinite_of_injective_forall_mem`, `Complex.dist_eq_re_im`,
`Real.sq_sqrt`, `sq_eq_sq_iff_abs_eq_abs` and `exists_rat_near` are all used from Mathlib rather
than reproved.

Two helper lemmas that the earlier draft stated locally, `two_mem_ratField` and
`countable_ratSlice`, each turned out to be a single Mathlib lemma application (`ofNat_mem` and
`Set.countable_range` respectively). They were **deleted** after review and their two call sites
now invoke the Mathlib lemmas directly.

## Corrections made after review

The Lean statements and proofs were not changed by the review, but four docstring claims were:

* the "imaginary quadratic field" gloss (module docstring and
  `IsRatDist.exists_subset_ratSlice`) now records that it fails in the degenerate `y = 0` branch,
  where `RatSlice 0` is `ℚ ⊆ ℝ`;
* the parenthetical claiming that no measure- or Baire-category argument can build a witness
  (module docstring and `IsRatDist.countable`) was replaced by what countability actually gives:
  any witness is countable, so a positive answer must be a countable dense set and nothing of
  positive measure or of second category qualifies — a category or diagonal *construction* of a
  countable dense set is not excluded;
* the use-site describing the negative direction no longer claims to discharge the reward
  theorem; under the pinned `google.answer = always_true` setting it refutes it, and the docstring
  now says so;
* a new use site, `erdos_212_true_iff_of_dense_rational_family`, makes the positive direction
  explicit: it yields exactly the biconditional the pinned statement asks for.

## References

- Erdős Problem 212: <https://www.erdosproblems.com/212>
- J. Solymosi and F. de Zeeuw, *On a question of Erdős and Ulam*, Discrete Comput. Geom. 43
  (2010), 393–401. <https://arxiv.org/abs/0806.3095>
- J. Shaffaf, *A solution of the Erdős–Ulam problem on rational distance sets assuming the
  Bombieri–Lang conjecture*, Discrete Comput. Geom. 60 (2018), 283–293.
  <https://arxiv.org/abs/1501.00159>
- K. Ascher, L. Braune and A. Turchet, *The Erdős–Ulam problem, Lang's conjecture and
  uniformity*, Bull. London Math. Soc. 52 (2020), 1053–1063. <https://arxiv.org/abs/1901.08054>
- N. H. Anning and P. Erdős, *Integral distances*, Bull. Amer. Math. Soc. 51 (1945), 598–600.
  <https://www.ams.org/journals/bull/1945-51-08/S0002-9904-1945-08407-9/>
- Mathlib4 (pinned revision `a3a10db0e9d66acbebf76c5e6a135066525ac900`, tag `v4.27.0`):
  <https://github.com/leanprover-community/mathlib4>

The "rational real part / rational squared imaginary part after normalisation" step and the
"single quadratic field" refinement are classical folklore, stated informally in the introductions
of the Solymosi–de Zeeuw and Ascher–Braune–Turchet papers cited above; the Lean statements and
proofs here are mine.

## Originality

All statements and all proofs in `CW_erdos_212.lean` are original work written for this
submission. Nothing in the file was copied from any source: not from Mathlib, not from the
`formal-conjectures` repository, not from another contribution, and not from any paper, textbook,
website or other Lean development. The mathematical *ideas* behind the structure theorem are
classical and are credited to the references above; every Lean statement, every definition and
every proof script is new here. No proof is claimed that was not machine-checked in the pinned
environment.

## AI assistance

This contribution was produced with AI assistance: the Lean source, the module docstring and this
`sources.md` were drafted by Claude (Anthropic) working interactively against the pinned
`formal-conjectures` workspace, compiling and iterating until the file elaborated with zero errors
and zero warnings, and verifying with `#print axioms` that every declaration reduces to
`[propext, Classical.choice, Quot.sound]` only (the `#print axioms` lines were then deleted and
the file recompiled). The docstring corrections listed above were applied after an independent
review, and the file was recompiled and re-checked for axioms afterwards.
