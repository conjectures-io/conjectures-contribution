# sources.md — contribution to erdos-242 (Erdos-Straus), `Contribution.Erdos242Reduction`

## What the target asks

`Erdos242.erdos_242`: for every `n > 2` there are naturals `1 <= x < y < z` (strictly increasing,
so pairwise distinct) with `(4 / n : Q) = 1/x + 1/y + 1/z`. This is the Erdos-Straus conjecture,
open since 1948.

## The obstacle this contribution attacks

The target is a single statement quantified over all `n > 2`, but every classical attack proceeds
one residue class, or one prime, at a time. Two glue steps make that possible and both are left
informal in the literature:

* "a solution for a divisor gives a solution for the multiple" — multiply all three denominators
  by `n / d`;
* "now split the last unit fraction" — pass from a two-term representation `q = 1/x + 1/m` to a
  three-term one.

In Lean both are traps, because what the target demands is the STRICT chain `x < y < z`, and that
is exactly what the naive manipulations destroy. The Sylvester (greedy) split
`1/m = 1/(m+1) + 1/(m(m+1))` only preserves the chain when `m >= 2`, and the two classical
identity families deliver their denominators in different orders: for `4 | n+1` the order is
`d < nd+1 < nd(nd+1)`, while for `3 | n+1` it is `d < n < nd` with `n` in the middle. Mathlib has
no Egyptian-fraction material to build on — grepping the pinned Mathlib source for `egyptian`,
`unitFrac` and `unit fraction` returns nothing, and `straus` returns only an unrelated
Goodman-Strauss tiling citation — so a solver currently redoes this bookkeeping by hand inside
every branch of every case split, and there is no checked version of the standard "reduce to
primes" first step to build on.

Disclosure of neighbouring work in the pool repository itself (not in Mathlib): the
formal-conjectures repo does define Egyptian-fraction notions for other problems, namely
`Erdos206.egyptianSum` and `Erdos304.unitFractionExpressible`. Neither states this target's
conclusion: `unitFractionExpressible a b` is a `Finset`-indexed, unordered predicate that in
addition forbids the denominator `1` (so it would exclude `4/3 = 1/1 + 1/4 + 1/12`, which the
target permits), whereas `IsSumOfThreeUnitFractions` is the target's own ordered conclusion,
verbatim.

## The delta (what is new here, all machine-checked)

A small coherent API around the target's own statement, in one namespace, 19 named declarations
plus 3 examples, zero `sorry`, zero warnings, every named declaration's `#print axioms` a subset
of `[propext, Classical.choice, Quot.sound]`.

* `IsSumOfThreeUnitFractions q` packages the target's conclusion; `target_iff_...` proves by
  `Iff.rfl` that at `q = 4/n` it IS the conclusion of `Erdos242.erdos_242` (no statement drift).
* `unitFrac_split` and `of_two_term`: the greedy split, and the two-term to three-term interface,
  which checks the strict chain once for the whole `a | n+1` family. This is the reusable core.
  (The `3 | n+1` family cannot be routed through it, because there the middle denominator is `n`
  itself, so `four_div_of_two_mod_three` checks its own chain.)
* `div_eq_of_mul_eq_succ`: one identity `a/n = c/n + 1/d + 1/(n*d)`, valid whenever `b*d = n+1`
  and `c + b = a`, which specialises to BOTH classical families (`c = 0` gives the `a | n+1`
  family, `c = 1` gives the `(a-1) | n+1` family). It is stated for a general numerator `a`, so
  it also applies to `Erdos242.erdos_242.variants.schinzel_generalization` — but only on the
  single residue class `n = a-1 (mod a)`, of density `1/a`, whereas that variant asks for all
  sufficiently large `n`; `of_dvd_succ` is the ready-to-apply general-numerator corollary.
* `four_div_of_even`, `four_div_of_three_mod_four`, `four_div_of_two_mod_three`: the three covered
  classes, each an unconditional theorem producing explicit witnesses.
* `IsSumOfThreeUnitFractions.div_nat` and `four_div_of_dvd`: the divisor-to-multiple step.
* `four_div_of_prime_factor_ne_one_mod_twelve`: the unconditional core — any `n > 2` with any
  prime factor outside `1 mod 12` is already solved.
* `prime_factor_one_mod_twelve_of_not` and `mod_twelve_of_not`: the contrapositive packaging — a
  counterexample has all of its prime factors `= 1 (mod 12)`, hence (by strong induction along
  the factorisation) satisfies `n % 12 = 1` itself.
* `reduce_to_primes_one_mod_twelve` and `erdos_242_of_primes_one_mod_twelve`: the reduction, and
  the same statement written in the literal syntax of the target, so a solver can `exact` it.
* `erdos_242_iff_primes_one_mod_twelve`: the reduction is an equivalence — the residual prime
  obligation is itself a special case of the target (a prime `p = 1 (mod 12)` has `p >= 13 > 2`),
  so the handoff assumes nothing stronger than what it proves.
* `mul_denom_bounds` and `four_div_denom_bounds`: a bracket on the SMALLEST denominator,
  `1 < x*q < 3` in general and `n < 4x < 3n` in N for `q = 4/n`. It is the trivial bracket that
  falls out of `x < y < z`, not a sharpened bound, and it confines only `x`: nothing here bounds
  `y` or `z`, so this alone does not reduce the remaining prime case to a finite search.

The mathematics of the covered classes and of the reduction to primes is classical (Mordell;
see the discussion in Elsholtz-Tao); nothing here claims new mathematics. What is new is that it
is now checked Lean with a usable interface, sitting directly on the pool file's statement.

## Independent cross-check (re-run and corrected after review)

Outside Lean, the three explicit constructions were evaluated with exact rational arithmetic for
every `n` in `3..3999` (3997 values), following what the Lean theorems actually do: pick a prime
factor `p` of `n` with `p % 12 != 1`, build the triple for `4/p` from the relevant unconditional
theorem, and scale it by `n/p` as `four_div_of_dvd` does.

* Against `four_div_of_prime_factor_ne_one_mod_twelve` (which fires on ANY prime factor outside
  `1 mod 12`): 3848 of the 3997 values are discharged, each with a triple checked to be strictly
  increasing and to sum to exactly `4/n`. The 149 values left are exactly those `n` all of whose
  prime factors are `= 1 (mod 12)`.
* The routing actually used inside `reduce_to_primes_one_mod_twelve` is weaker: it looks only at
  `n.minFac`. That covers 3785 values and leaves 212 — namely the `n` whose SMALLEST prime factor
  is `= 1 (mod 12)`. These 212 are not all genuinely uncovered by the contribution: 63 of them,
  starting `221 = 13*17`, `247 = 13*19`, `299 = 13*23`, are discharged by
  `four_div_of_prime_factor_ne_one_mod_twelve` through a larger prime factor.

An earlier draft of this file reported the 3785/212 split and described the 212 as "the values all
of whose prime factors are `= 1 (mod 12)`, matching what the Lean theorems assert". That was wrong
on both counts (the correct figure for that description is 149, and the theorems cover 3848), and
it has been corrected here after review; the module docstring of the Lean file was corrected in
the same pass (see "Corrections after review" below).

## Corrections after review

The Lean proofs were not touched; the file still compiles with zero errors and zero warnings, and
every named declaration is still axiom-clean. The corrections are to prose, plus one added
theorem:

* the docstring no longer calls `n < 4x < 3n` a "sharp" bracket — it is the trivial bracket
  implied by `x < y < z`;
* it no longer claims the bracket "makes the remaining prime case a finite search"; only the
  smallest denominator `x` is bounded here, `y` and `z` are not, and the docstring now says so;
* the `of_dvd_succ` docstring no longer calls itself "the tool for"
  `Erdos242.erdos_242.variants.schinzel_generalization`: it fires on the single residue class
  `n = a-1 (mod a)` (density `1/a`), while that variant asks for all sufficiently large `n`;
* the `of_two_term` docstring no longer claims to be the only place the strict chain is checked
  (`four_div_of_two_mod_three` checks its own);
* the "nothing in Mathlib" claim is now stated as the greps that back it, and the neighbouring
  formal-conjectures API (`Erdos206.egyptianSum`, `Erdos304.unitFractionExpressible`) is
  disclosed above;
* added `erdos_242_iff_primes_one_mod_twelve`, upgrading the reduction to an equivalence, so that
  the handoff is demonstrably not an assumption of anything stronger than the target.

## Sources

* Erdos problem 242: https://www.erdosproblems.com/242
* Erdos-Straus conjecture, overview and the classical residue-class reductions:
  https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture
* C. Elsholtz and T. Tao, "Counting the number of solutions to the Erdos-Straus equation on unit
  fractions", https://arxiv.org/abs/1107.1010 (Section 1 states the reduction to primes and the
  classical covered residue classes)
* W. Sierpinski, "Sur les decompositions de nombres rationnels en fractions primaires",
  Mathesis 65 (1956), 16-32 — the source cited by the pool file for the Schinzel generalisation
  (no open-access link known to me; cited as in `FormalConjectures/ErdosProblems/242.lean`)
* Pinned formal-conjectures pool file for this target:
  https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean

## Originality

All statements and all proofs in the submitted Lean file are original work written for this
submission. They were composed here from the classical mathematical ideas cited above, and were
not copied, adapted or machine-translated from any source: not from Mathlib, not from the
formal-conjectures repository or any other contribution to it, not from any other Lean or
proof-assistant development, and not from any paper, textbook, website or model output presented
as an existing formalisation. The cited references supply only the informal mathematics (the
classical covered residue classes and the reduction to primes); every Lean statement, name,
definition and tactic proof here was written for this contribution.

## Provenance and AI disclosure

This contribution was produced with AI assistance (Anthropic Claude, driven interactively): the
AI drafted the Lean statements and proofs, compiled and iterated them against the pinned
formal-conjectures workspace until zero errors and zero warnings, checked `#print axioms` for
every named declaration (all 19 print exactly `[propext, Classical.choice, Quot.sound]`; the 3
anonymous `example`s cannot be `#print axioms`-ed, and the zero-warning build rules out `sorry`
in them), grepped the pinned Mathlib source to confirm none of these lemmas already exists there
under another name, and cross-checked the constructions numerically with exact rational
arithmetic. The prose corrections listed under "Corrections after review" were applied in a
later, review-driven pass, in which the numeric cross-check was re-run from scratch rather than
carried over.
