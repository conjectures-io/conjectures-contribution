# Sources and provenance - partial contribution to erdos-196

## Target

`Erdos196.erdos_196` in `FormalConjectures/ErdosProblems/196.lean`:
`answer(sorry) ↔ ∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4`
("Must every permutation of ℕ contain a monotone 4-term arithmetic progression?")

This contribution does not answer the problem. It is a checked interface around the target's own
definitions, plus the case one step below the target.

## The obstacle

`HasMonotoneAP f k` is defined in `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` as

    ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

and `List.IsAPOfLength s k` is in turn

    ∃ a d, s = (List.range k).map (a + · • d) ∨ s = (List.range k).reverse.map (a + · • d).

Every use of the predicate therefore begins with the same three chores: fight a list equality
against `List.range 4` under a `reverse` / `no-reverse` disjunction; re-derive that the index list
has length `4` and destructure it; and convert `List.Pairwise (· < ·)` into index inequalities.
That is true whether one is trying to build a progression (the "yes" side of the problem) or to
verify that a candidate permutation avoids them (the "no" side, which is where the literature's
constructions live).

There is also a mismatch between the definition and its own docstring, which claims the
subsequence "forms an increasing or decreasing arithmetic progression". The definition admits
`d = 0`, so a constant list is an arithmetic progression of every length; the informal claim only
becomes true once injectivity is assumed. That step had not been checked anywhere.

## The delta

One self-contained file, `CW_erdos_196.lean`, 20 theorems, all in namespace
`Contribution.Erdos196MonotoneAP`, no `sorry`, no added axioms, no `def`s and no instances.

* `listIsAPOfLength_three_iff`, `listIsAPOfLength_four_iff` - the definition on an explicit 3- or
  4-element list as an `rcases`-friendly disjunction, over an arbitrary `AddCommMonoid`, so the
  same lemmas serve Erdős problem 195 (the analogous question over ℤ) and 197.
* `listIsAPOfLength_three_iff_nat`, `listIsAPOfLength_four_iff_nat` - over ℕ the increasing and
  the decreasing case merge into linear equations (`x₀ + x₂ = 2 * x₁`, `x₁ + x₃ = 2 * x₂`), so the
  disjunction disappears entirely and `omega` can finish. These two are ℕ-specific: over ℤ the
  disjunction survives, so they do not transfer to problem 195.
* `hasMonotoneAP_three_iff`, `hasMonotoneAP_four_iff` - the resulting index characterisations,
  which are the drop-in replacements for the target predicate.
* `not_hasMonotoneAP_four_iff` - the push-neg'd shape in which one verifies an avoiding
  permutation. It is a three-line restatement of `hasMonotoneAP_four_iff`, kept because it is the
  shape a refutation is actually written in.
* `hasMonotoneAP_four_iff_of_injective` - for injective `f` the progression really is strictly
  monotone: the common difference is positive. This is the docstring's informal claim, checked.
* `hasMonotoneAP_mono` - monotonicity in `k` (prefix of the index list in the increasing case,
  suffix in the decreasing one).
* `hasMonotoneAP_of_comp_strictMono` - a monotone AP on any increasing subsequence lifts to one
  for `f`; the standard reduction step.
* `listIsAPOfLength_two_nat`, `hasMonotoneAP_two` - degenerate cases; over ℕ every 2-element list
  is an AP, so `k ≤ 2` is automatic.
* `not_hasMonotoneAP_three_of_growth`, `not_hasMonotoneAP_four_of_growth` - an obstruction at the
  level of sequences: `∀ n, 2 * f n < f (n + 1)` rules out monotone 3-term APs, hence 4-term ones.
  That growth hypothesis is the only one asked for, because it already forces `f` to be strictly
  monotone. Caveat, stated here and in the file's docstrings: **no `f : ℕ ≃ ℕ` satisfies it**, so
  these two lemmas are a non-vacuity check about sequences and are not progress on the target.
* `no_equiv_satisfies_growth` - the proof of that caveat: no permutation of ℕ satisfies
  `∀ n, 2 * f n < f (n + 1)` (such an `f` is strictly monotone, hence `n ≤ f n`, which forces
  `f 0 = 0` and `f 1 = 1`, hence `3 ≤ f 2`, and then the value `2` has nowhere to sit). It tells a
  later solver that growth-based obstructions cannot be instantiated at the target's binder.
* `hasMonotoneAP_three_of_equiv` - **every permutation of ℕ contains a monotone 3-term arithmetic
  progression**, the case immediately below the target, stated in the pool's own vocabulary. This
  is the theorem of Davis, Entringer, Graham and Simmons; the proof given here is a short infinite
  descent (let `p` be the position of the value `0` and let `d` exceed every value occurring at a
  position `< p`; for `v ≥ d` the progression `0, v, 2v` forces the position of `2v` to lie left of
  the position of `v`, and iterating along `d, 2d, 4d, …` gives an infinite strictly decreasing
  sequence of positions). It is written entirely through `hasMonotoneAP_three_iff`, which is what
  makes it short, and it is the evidence that the interface is fit for its purpose.
* `erdos_196_iff_indices`, `hasMonotoneAP_of_le_three`, `hasMonotoneAP_four_refl` - use sites
  against the target statement itself; the first two are one-line consequences of lemmas above.
* `not_hasMonotoneAP_four_pow` - a non-vacuity witness at the level of sequences: the powers of 3
  have no monotone 4-term AP. They are not a permutation of ℕ, so this bounds no permutation; it
  only shows that `HasMonotoneAP · 4` is not automatic.

Six of the twenty theorems (`not_hasMonotoneAP_four_iff`, `not_hasMonotoneAP_four_of_growth`,
`hasMonotoneAP_of_le_three`, `erdos_196_iff_indices`, `hasMonotoneAP_four_refl`,
`not_hasMonotoneAP_four_pow`) are one- to three-line consequences of the others; they are kept as
the worked demonstrations and as the shapes a later user needs, not as independent content.

Novelty: `HasMonotoneAP` is bespoke to formal-conjectures and has no lemmas at all in the pinned
tree - its only occurrences are the definition
(`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean:248`) and the `sorry`d statements of
problems 195, 196 and 197. `List.IsAPOfLength` is bespoke too, but it is *not* lemma-free: the
pinned tree already carries the generic `List.IsAPOfLength.length`, `.zero`, `.one` and `.congr`
(AP/Basic.lean:166-181), the corresponding `List.IsAPOfLengthWith.length/.zero/.one` (lines 79-91)
and the pair lemmas `Set.isAPOfLength_pair` / `Nat.isAPOfLength_pair` (lines 185-189), and
`IsAPOfLength` is mentioned in 23 files of the tree. This file uses one of those lemmas itself
(`List.IsAPOfLength.length`, as `hap.length`). What none of them does is decide the predicate on an
explicit list of length 2, 3 or 4, which is what this file supplies. Mathlib mentions neither
definition: grepping the pinned Mathlib source for `HasMonotoneAP`, `IsAPOfLength` and
`MonotoneAP` returns nothing. Mathlib's nearest material is `ThreeAPFree` and the Roth/Behrend
AP-free machinery, which is set-level and has no monotone-index or permutation content.
(An earlier version of this paragraph claimed that `List.IsAPOfLength` had no lemmas in the pinned
tree either; that was false, and it is corrected here.)

## Corrections made after review

* The novelty paragraph above was rewritten: its previous form was factually wrong about
  `List.IsAPOfLength`, and was contradicted by the file's own use of `List.IsAPOfLength.length`.
* The redundant `Monotone f` hypothesis was dropped from `not_hasMonotoneAP_three_of_growth` and
  `not_hasMonotoneAP_four_of_growth`; the growth hypothesis alone implies it, and the file now
  derives it internally. The use site `not_hasMonotoneAP_four_pow` was simplified accordingly.
* The docstrings of both growth lemmas, and the module docstring, now disclose that no
  `f : ℕ ≃ ℕ` satisfies the growth hypothesis, so that they cannot read as target-relevant
  obstructions. `no_equiv_satisfies_growth` was added to make that disclosure a machine-checked
  theorem rather than a remark.
* The module docstring no longer lists `not_hasMonotoneAP_four_pow` among the use sites against
  the target statement; it is described as a sequence-level non-vacuity witness, which is what it
  is.

## Verification

Compiled against the pinned workspace with

    lake env lean CW_erdos_196.lean

exit code 0, zero errors and zero warnings (including the style and unused-simp-argument linters),
both before and after the corrections above. `#print axioms` was then run on all 20 theorems and
each depends only on a subset of `[propext, Classical.choice, Quot.sound]` (eight of them on
`[propext, Quot.sound]` alone); no `sorryAx`, despite the file importing the `sorry`d
`FormalConjectures.ErdosProblems.196`. The `#print` lines were deleted afterwards and the file
recompiled clean. The file contains no `sorry`, `admit`, `axiom`, `native_decide`, `#eval`,
`unsafe`, `extern`, `implemented_by`, `partial` or `set_option`.

The claim that the interface discharges the real obligation was checked mechanically, not by
reading: with `h` the arithmetic hypothesis, both `intro f; rw [hasMonotoneAP_four_iff]` and
`rw [erdos_196_iff_indices]` close a goal written literally as `∀ (f : ℕ ≃ ℕ), HasMonotoneAP (⇑f) 4`,
the right-hand side of `Erdos196.erdos_196`.

## References

- https://www.erdosproblems.com/196 - the problem page.
- J. A. Davis, R. C. Entringer, R. L. Graham, G. J. Simmons, *On permutations containing no long
  arithmetic progressions*, Acta Arithmetica 34 (1977/78), 81-90.
  https://doi.org/10.4064/aa-34-2-81-90 - every permutation of the positive integers contains a
  monotone 3-term AP, and some permutation contains no monotone 5-term AP; the 4-term case is
  problem 196.
- T. D. LeSaulnier, S. Vijay, *On permutations avoiding arithmetic progressions*, Discrete
  Mathematics 311 (2011), 205-207. https://doi.org/10.1016/j.disc.2010.10.021 - a permutation of
  the positive integers avoiding monotone 4-term APs with odd common difference.
- S. Adenwalla, *A Generalisation of a Result on Monotone Arithmetic Progressions in Permutations
  of the Positive Integers*, https://arxiv.org/abs/2302.09662 (2023).
- S. Adenwalla, *Avoiding Monotone Arithmetic Progressions in Permutations of Integers*,
  https://arxiv.org/abs/2211.04451 (2022) - the ℤ analogue, cited by the pool file for problem 195.
- Definitions used: `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean` in
  https://github.com/google-deepmind/formal-conjectures

## Originality

All statements and all proofs in `CW_erdos_196.lean` are original work produced for this
submission. Nothing in the file was copied from any source: not from the formal-conjectures
repository, not from Mathlib, not from another contribution, and not from any paper, textbook or
web page. The only inputs taken from outside are the definitions the target itself uses
(`HasMonotoneAP`, `List.IsAPOfLength`, `List.IsAPOfLengthWith`) and the standard Mathlib lemmas
invoked in the proofs.

The single piece of mathematics here that is not new is the *content* of
`hasMonotoneAP_three_of_equiv` - every permutation of ℕ contains a monotone 3-term AP - which is
the 1977 theorem of Davis, Entringer, Graham and Simmons, cited above and credited in the file's
docstring. Its Lean statement and its proof (an infinite descent along `d, 2d, 4d, …`) were written
for this submission; no formalisation of that theorem was consulted, and none is known to exist in
Mathlib or in the pinned tree.

## Disclosure

This contribution was produced with AI assistance (Claude, Anthropic): the choice of obstacle, the
statements, the proofs and the prose were drafted by the model and then compiled and iterated
against the pinned toolchain until the file elaborated with zero errors and zero warnings. Every
claim in the file is machine-checked; nothing is asserted that Lean did not accept. The file's
docstrings and this document were corrected after review - see "Corrections made after review"
above - so that every claim they make is literally true in the pinned environment.
