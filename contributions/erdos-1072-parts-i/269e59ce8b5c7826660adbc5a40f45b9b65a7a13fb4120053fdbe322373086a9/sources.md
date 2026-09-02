# Sources and provenance — `CW_erdos_1072_parts_i.lean`

## Target

Erdős Problem 1072, part (i): `Erdos1072.erdos_1072.parts.i` in
`FormalConjectures/ErdosProblems/1072.lean`, i.e. whether
`{p | p.Prime ∧ Erdos1072.f p = p - 1}` is infinite, where
`f p = sInf {n | n ! + 1 ≡ 0 [MOD p]}` is the least `n` with `n ! ≡ -1 (mod p)`.

## The obstacle this contribution removes

The pinned environment is not empty here — `f p ≤ p - 1` for prime `p`, for instance, is two
lines from `ZMod.wilsons_lemma` and `Nat.sInf_le`, and that is exactly this file's own
`f_le_sub_one`. What is missing is a usable interface: every statement about the target set has
to be re-derived from scratch, through three separate frictions.

1. `f` is an `sInf` over a set of naturals, and each `sInf` fact needs its own input.
   `Nat.sInf_mem` (membership of the value, used by `factorial_f_eq_neg_one`) needs the defining
   set to be nonempty, which here is Wilson's theorem; `Nat.sInf_le` needs an explicit member;
   only `Nat.notMem_of_lt_sInf` (minimality, used by `factorial_ne_neg_one_of_lt_f`) needs
   neither. On top of that the defining predicate is stated with `Nat.ModEq` on `n ! + 1`, while
   the usable Mathlib facts about factorials modulo `p` (`ZMod.wilsons_lemma`,
   `ZMod.cast_descFactorial`) are stated in `ZMod p`.
2. `f p = p - 1` constrains the factorials of the *large* indices `n ≤ p - 1`, i.e. numbers of
   size `p!`. The dual form replaces one index by its complement: `p - 1 - a` solves
   `n ! ≡ -1 (mod p)` if and only if `a ! ≡ (-1)^a (mod p)`, so a solution at a large index is
   certified by the single factorial `a !`, which is small exactly when `p - 1 - a` is large.
   The reflection identity behind it, `a ! · b ! ≡ (-1)^(a+1) (mod p)` for `a + b = p - 1`, is
   not in Mathlib; Mathlib has only the one-sided `ZMod.cast_descFactorial`
   (`(descFactorial (p-1) n : ZMod p) = (-1)^n * n !`).
3. The formalisation is `0`-indexed and `0! = 1`, so `0! + 1 = 2 ≡ 0 [MOD 2]` and `f 2 = 0`,
   whereas `2 - 1 = 1`. The prime `2` is therefore **not** a member of the target set even though
   Wilson's theorem holds at `2`. This is easy to miss and breaks any argument that starts at `2`.

## The delta

A small self-contained API in `namespace Contribution.Erdos1072Pillai`, all statements proved,
with `#print axioms` run on all 18 named declarations in a scratch copy: 17 report exactly
`[propext, Classical.choice, Quot.sound]` and the `private` helper reports `[propext]` alone, so
every one is a subset of the permitted three. The `#print` lines were then deleted and the file
recompiled; they are not in the submitted file.

* `factorial_add_one_modEq_zero_iff`, `factorial_add_one_mod_eq_zero_iff` — move the defining
  predicate from `Nat.ModEq` into `ZMod p`, and into a `decide`-able `%` form.
* `factorial_sub_one_modEq`, `nonempty_of_prime`, `f_le_sub_one`, `factorial_f_eq_neg_one`,
  `factorial_ne_neg_one_of_lt_f` — the `sInf` interface: Wilson's theorem in the exact shape the
  `sInf` needs, nonemptiness, the bound `f p ≤ p - 1`, membership and minimality.
* `f_eq_sub_one_iff` — the equation `f p = p - 1` as a bounded universal statement, no `sInf`.
* `factorial_mul_factorial_of_add_eq` — the reflection identity `a ! * b ! = (-1)^(a+1)` in
  `ZMod p` for `a + b = p - 1`, proved from `Nat.factorial_mul_descFactorial`,
  `ZMod.cast_descFactorial` and `ZMod.wilsons_lemma`. Wilson's theorem is the case `a = 0`.
* `factorial_eq_neg_one_iff` — the resulting duality: the index `b` solves `n ! ≡ -1` iff the
  complementary index `a = p - 1 - b` satisfies `a ! ≡ (-1)^a`.
* `f_eq_sub_one_iff_forall_small` and `setOf_prime_and_f_eq_sub_one` — the extremal condition, and
  then the target set itself, rewritten as a bounded check on the dually-indexed factorials `a !`
  for `1 ≤ a ≤ p - 1`, obtained by the relabelling `a ↔ p - 1 - a`. What this buys is the
  disappearance of the `sInf` and an unconditional set equality that plugs straight into the
  target. It is **not** a reduction in factorial size: the relabelling runs over an index range
  of the same size and reaches `(p - 1)!`, whereas the pre-reflection form `f_eq_sub_one_iff`
  reaches only `(p - 2)!`. An earlier version of the docstrings and of this file advertised it as
  a check on *small* factorials; that claim was wrong and has been corrected after review.
* `f_lt_sub_one_of_small_witness`, `notMem_of_small_witness` — the genuine small-index payoff: a
  single small `a` with `a ! ≡ (-1)^a (mod p)` certifies `f p < p - 1`, i.e. excludes `p` from the
  target set without computing any large factorial. The guard `1 ≤ a` is load-bearing: `a = 0`
  satisfies `0! = 1 = (-1)^0` for every `p`, so without it the certificate would exclude
  everything.
* `mem_iff_ball` — membership as a `decide`-able statement about natural numbers. This is the
  lemma the `decide` use sites below actually consume, and it comes from `f_eq_sub_one_iff`
  directly; the reflection identity is not on its path.
* `f_two`, `two_notMem` — the `0`-indexing trap, checked. `f_two` is a one-liner (the single
  tactic call `simp [Erdos1072.f]` also closes it); it is kept for the trap it records, not for
  its proof.

Four worked use sites are included: a target-shaped reduction of
`Answer ↔ Set.Infinite {p | p.Prime ∧ f p = p - 1}` to the dual-index form; a non-vacuity check
`{3, 5, 13, 17, 31} ⊆ {q | q.Prime ∧ f q = q - 1}` discharged by `decide` through `mem_iff_ball`;
and the exclusion certificates for `7` (via `3! ≡ (-1)^3 mod 7`) and for `23` (via
`4! ≡ (-1)^4 mod 23`, which certifies that index `18` solves `n ! ≡ -1 (mod 23)` while never
computing `18!`).

## Novelty check

Searched the pinned Mathlib source for the relevant statements before keeping each lemma:
`Mathlib/NumberTheory/Wilson.lean` (`ZMod.wilsons_lemma`, `Nat.prime_iff_fac_equiv_neg_one`),
`Mathlib/Data/ZMod/Factorial.lean` (`ZMod.cast_descFactorial`),
`Mathlib/Data/Nat/Factorial/Basic.lean` (`Nat.factorial_mul_descFactorial`) and
`Mathlib/Data/Nat/Lattice.lean` (`Nat.sInf_mem`, `Nat.notMem_of_lt_sInf`, `Nat.sInf_le`).
These are the ingredients used; none of them states the reflection identity
`a ! · b ! = (-1)^(a+1)`, the dual-index reformulation, or anything about `Erdos1072.f`. The only
helper that could overlap with Mathlib, `(-1)^a * (-1)^a = 1`, is kept `private` and is not
claimed as a contribution.

## Originality

All statements and all proofs in `CW_erdos_1072_parts_i.lean` are original work written for this
submission. Nothing in the file is copied from Mathlib, from `formal-conjectures`, from another
contribution, from a paper, or from any other source; the Mathlib lemmas listed above are used as
dependencies only, by name. The mathematics is classical (Wilson's theorem and its reflection),
but every Lean statement and every Lean proof here was written from scratch for this file and
checked by the Lean kernel. The docstrings and this document were corrected after review to
remove an overstated claim about small factorials, an overstated claim about what the pinned
environment can prove, and a dead declaration (`f_eq_sInf_zmod`, referenced nowhere).

## References

* Erdős Problem 1072: https://www.erdosproblems.com/1072
* Wilson's theorem: https://en.wikipedia.org/wiki/Wilson%27s_theorem
* G. E. Hardy and M. V. Subbarao, *A modified problem of Pillai and some related questions*,
  Amer. Math. Monthly 109 (2002), 554–559: https://doi.org/10.2307/2695445
  (cited in the pool file as [HaSu02]; the paper itself was not consulted for this submission, so
  no claim is made here about the exact form used in it)
* Mathlib source consulted, at the pinned revision in
  `.lake/packages/mathlib`: `Mathlib/NumberTheory/Wilson.lean`,
  `Mathlib/Data/ZMod/Factorial.lean`, `Mathlib/Data/Nat/Factorial/Basic.lean`,
  `Mathlib/Data/Nat/Lattice.lean`. https://github.com/leanprover-community/mathlib4

## Disclosure

This contribution was produced with AI assistance (Claude, Anthropic): the mathematics was worked
out and the Lean file was written and iterated to a zero-error, zero-warning compile in the pinned
`formal-conjectures` workspace, with a small Python script used only to check the numerical
examples (`f p` for small primes, and the members `3, 5, 13, 17, 31`) before they were proved in
Lean. Every statement in the file has been checked by the Lean kernel; nothing is asserted that
was not compiled.
