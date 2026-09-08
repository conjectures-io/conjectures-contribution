# sources.md — Erdős problem 1085, `variants.upper_d3`

## What this contribution is

A single self-contained Lean 4 file, `CW_erdos_1085_variants_upper_d3.lean`, in namespace
`Contribution.Erdos1085UnitDistance` (42 declarations). It does **not** solve
`Erdos1085.erdos_1085.variants.upper_d3`, which is open. It supplies

1. a complete, equivalence-based interface for the extremal function `Erdos1085.f`;
2. the missing geometric input (`K₃,₃`-freeness of the unit-distance graph in dimension `< 4`),
   with a checked counterexample in `ℝ^4` showing the dimension hypothesis is necessary;
3. the resulting Kővári–Sós–Turán benchmark `f d n ≤ n + n^{5/3}` for `1 ≤ d ≤ 3`, together with
   a proof that this benchmark is strictly weaker than the conjectured `n^{4/3} log log n`.

## The obstacle

`Erdos1085.f d n = ⨆ (s : Finset (ℝ^d)) (_ : s.card = n), unitDistNum s` is an iterated
conditional supremum over *all* finite subsets of `ℝ^d`. Neither the pool file
(`FormalConjectures/ErdosProblems/1085.lean`) nor `FormalConjecturesForMathlib.Geometry.Metric`
(which contains only the definition of `unitDistNum`) records that this supremum is bounded, that
it is attained, or how it compares with a single configuration; so nothing connects "every
`n`-point configuration spans few unit distances" — the only form in which geometry can be used —
with the `IsBigO` obligation of the target, in either direction. All seven statements of the pool
file are blocked on this.

Independently, every known upper bound for `f_3` builds on the fact that three distinct points of
a space of dimension `< 4` have at most two common unit-distance neighbours. Mathlib's only
unit-distance material is `SimpleGraph.UnitDistEmbedding`
(`Mathlib/Combinatorics/SimpleGraph/UnitDistance/Basic.lean`, 78 lines), which defines
unit-distance embeddings of abstract graphs and proves nothing about how many unit distances a
finite point set can span; there is no `K₃,₃`-freeness statement in the library.

## The delta (what is new here)

* `two_mul_unitDistNum` — the handshake identity `2 * unitDistNum s = ∑ x ∈ s, deg x` for the
  unit-distance graph of a finite subset of an arbitrary metric space, via the exact count
  `card_ordered_unit_pairs` of ordered unit pairs (the `Sym2`-to-ordered-pairs fibration).
  Consequences: `unitDistNum_le_choose`, `unitDistNum_mono`, and isometry invariance
  `unitDistNum_map`.
* The `Erdos1085.f` API: `bddAbove_unitDistNum`, `unitDistNum_le_f`, `f_le_iff`,
  `exists_unitDistNum_eq_f` (**the supremum is attained**, via `Nat.sSup_mem`), `f_le_real`,
  `f_mono` (monotone in `n`), `f_le_f_of_le` (monotone in the dimension, through the explicit
  isometric embedding `embedSucc : ℝ^d → ℝ^(d+1)`), and the two **equivalences** `isBigO_f_iff`,
  `isBigO_iff_f`. Because attainment is available these are `Iff`s, not one-way reductions, so no
  hypothesis of theirs can be refuted for a legal instance of the target.
* The geometry: `inner_sub_sub_eq_zero` (perpendicular bisector identity),
  `not_three_common_unit_neighbours` and `card_le_two_of_forall_dist_eq_one` — `K₃,₃`-freeness in
  dimension `< 4`, proved by showing the two triangles span orthogonal planes.
* Sharpness: `exists_lenz_config` and `exists_card_three_forall_dist_eq_one` exhibit the Lenz
  configuration in `ℝ^4` (three points on each of two orthogonal circles of radius `√2/2`) with
  all nine cross distances equal to `1`, so the dimension hypothesis genuinely cannot be dropped
  and this route stops at `d = 3` — consistent with the quadratic behaviour asserted by the
  pool's `variants.lower_d4_lenz`. The coordinate distance formula `dist_pt` built for this is
  reusable for that companion.
* The count: `sum_choose_three_le` (`∑ₓ C(deg x, 3) ≤ 2·C(#s, 3)`) and the constant-free `ℕ`
  inequality `two_mul_unitDistNum_sub_pow_three_le`: `(2·unitDistNum s − 2·#s)^3 ≤ 2·#s^5` in any
  real inner product space of dimension `< 4`; real forms `unitDistNum_le_rpow`, `f_le_rpow`
  (`f d n ≤ n + n^{5/3}` for `1 ≤ d ≤ 3`) and `isBigO_f_three_rpow`.
* Honest measurement of the remaining gap: `isLittleO_target_rpow`
  (`n^{4/3} log log n = o(n^{5/3})`) and `not_isBigO_rpow_five_thirds` (no change of constants
  turns the benchmark into the conjectured bound), so the file states exactly what it does and
  does not settle.
* Use sites at the target: `upper_d3_isBigO_iff` (the target's obligation rewritten, norm-free,
  into a statement about arbitrary configurations of `ℝ^3`) and `isBigO_f_two_of_upper_d3`.

## Verification

* Compiles against the pinned Formal Conjectures toolchain with **zero errors and zero warnings**
  (`lake env lean CW_erdos_1085_variants_upper_d3.lean`, empty output, exit code 0).
* `#print axioms` was run on every one of the 42 declarations: each depends only on
  `[propext, Classical.choice, Quot.sound]`. The `#print` lines were then removed and the file
  recompiled clean.
* No `sorry`, `admit`, `axiom`, `native_decide`, `#eval`, `unsafe`, `extern`, `implemented_by`,
  `partial`, or `set_option` anywhere in the file; plain LF, no BOM, no bidi/zero-width
  characters, all lines ≤ 100 columns.
* Novelty was checked before keeping each lemma: `grep` over
  `.lake/packages/mathlib/Mathlib` for `unitDistNum` / `unit-distance` / `Kővári` / `K₃,₃`, and
  `Nat.choose_three_right`; and the statements at risk of being one-liners were tried against
  `simp`, `omega`, `nlinarith` and `simp [unitDistNum]` — all failed, so nothing kept here is a
  one-tactic restatement. Mathlib supplies the ingredients used (`pow_sum_le_card_mul_sum_pow`,
  `EuclideanGeometry.Cospherical.affineIndependent_of_ne`,
  `Submodule.finrank_add_finrank_orthogonal`, `isLittleO_log_rpow_atTop`) but none of the
  statements proved.

## Mathematical sources

* Problem statement and the literature it cites: <https://www.erdosproblems.com/1085>
* The pool file and definitions: Formal Conjectures repository,
  <https://github.com/google-deepmind/formal-conjectures>
  (`FormalConjectures/ErdosProblems/1085.lean`,
  `FormalConjecturesForMathlib/Geometry/Metric.lean`).
* The Kővári–Sós–Turán / Zarankiewicz argument used for the `n^{5/3}` bound is classical; for the
  standard statement see <https://en.wikipedia.org/wiki/Zarankiewicz_problem> and, for its
  application to unit distances, <https://en.wikipedia.org/wiki/Unit_distance_graph>.
* The stronger bounds mentioned in the module docstring (`O(n^{3/2})` by Kaplan, Matoušek,
  Safernová and Sharir, 2012; the improvement by Zahl, 2019) are cited by title and author only,
  from the reference list on the problem page above; none of their arguments is used or
  reproduced here.
* The `ℝ^4` sharpness example is Lenz's construction (two orthogonal circles of radius
  `1/√2`), as described on the problem page and in Erdős' work on distances in higher dimensions.

No Lean proof was copied from any repository. In particular nothing was taken from a
`formal_proof` link, from the Formal Conjectures solutions, or from any other contributor's file;
every proof in this file was written and debugged here against the pinned Mathlib, and each was
re-derived from the mathematics rather than transcribed.

## AI assistance

This contribution was produced by Claude (Anthropic), an AI assistant, working from the pool file
and the pinned Mathlib. The AI selected the decomposition, wrote every Lean proof, ran the
compiler and the axiom checks, and searched Mathlib for prior art. A human directed the work,
chose the target, and reviewed the result. All mathematical claims in the file and in this
document were checked by compiling the file; the informal remarks (attributions to
Kővári–Sós–Turán, Lenz, Kaplan–Matoušek–Safernová–Sharir and Zahl) are standard literature
citations and are not asserted as formal content.

## Originality statement

The Lean statements and proofs in `CW_erdos_1085_variants_upper_d3.lean` are original work
created for this contribution. The underlying mathematics (the handshake identity, the
perpendicular-bisector argument for `K₃,₃`-freeness in dimension `< 4`, the Kővári–Sós–Turán
double count, the Lenz configuration) is classical and is attributed above; the formalisation,
the choice of interface, the constant-free `ℕ` form of the count, and the measured gap statements
are new here and, to the best of our checking, are not present in Mathlib or in the Formal
Conjectures repository.
