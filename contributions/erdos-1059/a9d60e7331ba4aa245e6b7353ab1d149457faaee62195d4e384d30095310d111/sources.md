# Sources and provenance — partial contribution for `erdos-1059`

## Target

`Erdos1059.erdos_1059` in `FormalConjectures/ErdosProblems/1059.lean`:

> Are there infinitely many primes `p` such that `p - k!` is composite for each `k` with `1 ≤ k! < p`?

Problem page: https://www.erdosproblems.com/1059

Repository: https://github.com/google-deepmind/formal-conjectures (file
`FormalConjectures/ErdosProblems/1059.lean`, pinned toolchain `leanprover/lean4:v4.27.0`,
Mathlib `v4.27.0`).

## Originality

All statements and proofs in `CW_erdos_1059.lean` are original work written for this
submission. Nothing was copied from another contribution, from a solution set, from the
`formal-conjectures` repository beyond the target's own definitions, or from any other
source. Where a step is an application of an existing Mathlib lemma, that lemma is cited by
name in the dependency list below rather than restated locally.

## The obstacle this contribution addresses

The membership condition of the set whose infinitude the target asserts is
`Erdos1059.AllFactorialSubtractionsComposite p`, which unfolds to a bounded quantifier over
the *set* `Erdos1059.factorialsLessThanN p = {d | d < p ∧ d ∈ Set.range Nat.factorial}`.
Anything one wants to say about the problem — a construction, a finite search, or a
covering-congruence attempt — first has to convert a set membership together with an
existential `∃ k, k ! = d` into a statement indexed by `k`. There is also no `Decidable`
instance for the predicate: the pool file supplies only a separate `Prop` mirror
(`DecidableAllFactorialSubtractionsComposite`, which filters `Finset.range n` and scans
`Finset.Icc 0 d` for each `d`, i.e. quadratic cost) plus a bridging lemma, so `decide`
cannot be aimed at the target's own predicate.

Underneath that presentational obstacle there is a genuine mathematical one that the pool
file does not record. If `p` is prime and `k ! < p`, then a prime `q ≤ k` divides `k !`, so
`q | (p - k !)` would force `q | p`, i.e. `q = p`, contradicting `q ≤ k ≤ k ! < p`. Hence
**every prime factor of `p - k !` exceeds `k`**. Consequently a modulus fixed once and for
all is useless: it is coprime to `p - k !` for every `k` beyond it, so the standard Erdős
covering-congruence device cannot cover the whole range `k ! < p`. That does not say the
primes asked for are rare or absent — it says only that this one device cannot exhibit them
on its own. It is the first thing one reaches for on a problem of this shape, and it is
worth having it checked and recorded before a solver spends time on it.

## The delta

One self-contained file, `CW_erdos_1059.lean`, namespace
`Contribution.Erdos1059FactorialShifts`, 14 named declarations plus 3 worked `example`s.
It compiles with zero errors and zero warnings against the pinned workspace, and every
named declaration's `#print axioms` is a subset of `[propext, Classical.choice, Quot.sound]`
(three of them — `factorialsLessThanN_eq_image`, `allFactorialSubtractionsComposite_iff`,
`allFactorialSubtractionsComposite_of_certificates` — are choice-free). The `#print axioms`
lines were removed from the submitted file after the check, and the file recompiled clean.

Reshaping the predicate:

* `factorialsLessThanN_eq_image` — `Erdos1059.factorialsLessThanN n = Nat.factorial '' {k | k ! < n}`.
* `allFactorialSubtractionsComposite_iff` — the workhorse: the set-indexed predicate is
  equivalent to the `rcases`-friendly `∀ k : ℕ, k ! < n → (n - k !).Composite`.
* `lt_of_factorial_lt`, `allFactorialSubtractionsComposite_iff_range` — the quantifier
  restricts to `Finset.range B` for any `B` with `n ≤ B !`; a minimal such `B` has size
  `O(log n / log log n)`, and rewriting with it is the cheap way to settle membership.
* `decidableAllFactorialSubtractionsComposite` — the `Decidable` instance obtained from the
  same lemma, so `decide` applies to the target's own predicate with no rewriting first.
  This is a capability the pool file does not provide (measured: with only `import Mathlib`
  and the pool file, `example : Erdos1059.AllFactorialSubtractionsComposite 101 := by decide`
  fails with "failed to synthesize `Decidable …`"; with this instance in scope the identical
  `by decide` succeeds). Its cost is **not** the `O(log n / log log n)` one: the instance
  instantiates `B := n` via `Nat.self_le_factorial`, so it runs an `O(n)`-step check, and
  `decide` through it already exceeds the default `maxRecDepth` at `n = 211` (measured in
  the pinned workspace: `n = 101` succeeds at the default; `n = 211` fails at the default and
  succeeds with `maxRecDepth` around 20000; the demand grows with `n`). Beyond small `n` the route
  to use is `allFactorialSubtractionsComposite_iff_range` at a minimal `B`. The file's module
  docstring and the instance's own docstring state this cost explicitly.

The obstruction:

* `lt_of_prime_dvd_sub_factorial` — every prime divisor of `p - k !` exceeds `k`.
* `coprime_sub_factorial`, `not_dvd_sub_factorial_of_le` — a modulus whose prime factors are
  all `≤ k` is coprime to `p - k !`; in particular `M ∤ (p - k !)` whenever `M ≤ k`. So no
  prime factor of a fixed modulus `M` can certify compositeness of `p - k !` once `k ≥ M`,
  and a covering system with a fixed modulus cannot cover the whole range `k ! < p`.
* `sq_succ_le_sub_factorial` — for a prime `p` in the target set, `(k + 1) ^ 2 ≤ p - k !` for
  every `k` with `k ! < p`.
* `not_allFactorialSubtractionsComposite_of_lt` — hence no prime in the window
  `(k !, k ! + (k+1)^2)` lies in the target set, for any `k`, and no primality test or
  factorisation of `p - k !` is needed to see it. These windows are thin: together they cover
  `O((log n / log log n)^3)` of the integers below `n`, so this settles the primes sitting
  just above a factorial and is not a material speedup for a search over all primes.

Handoff:

* `infinite_setOf_of_unbounded`, `allFactorialSubtractionsComposite_of_certificates`,
  `infinite_setOf_of_certificates`, `erdos_1059_answer_true_of_unbounded` — the chain from
  "unboundedly many primes, each carrying a proper prime factor of every `p - k !`" to the
  literal statement `True ↔ Set.Infinite {p | p.Prime ∧ Erdos1059.AllFactorialSubtractionsComposite p}`
  of the reward theorem.
* Three `example`s: `101` is in the set via the five-element `iff_range` check, `101` again
  straight through the `Decidable` instance with no rewriting (so the instance is exercised
  in-file), and `127` is out of the set by the window bound alone.

## Novelty check (G4)

`Nat.Composite` is not a Mathlib notion — it is a *reducible* abbreviation in
`FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean`
(`abbrev Nat.Composite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime`) with no lemmas attached.
Being reducible, it is transparent to Mathlib's results about `¬ n.Prime`, so the absence of
`Nat.Composite` from Mathlib is **not** an argument that statements mentioning it are new.
Concretely, the compositeness obligation in
`allFactorialSubtractionsComposite_of_certificates` is discharged in one term by Mathlib's
`Nat.not_prime_of_dvd_of_lt`. An earlier draft of this file carried a local introduction
rule `composite_of_prime_dvd` for that step; it was **deleted after review** as a
repackaging of that Mathlib lemma, and the Mathlib term is now used inline at its single use
site.

What is genuinely absent from Mathlib and from the pool file: I grepped the pinned Mathlib
source under `.lake/packages/mathlib/Mathlib` for `sub_factorial` / `factorial_sub`, for
factorial–`minFac` interactions, and for `Coprime`–factorial results. The closest existing
statements are `Nat.Prime.dvd_factorial`, `Nat.coprime_factorial_iff` and
`Nat.Prime.coprime_factorial_of_lt` (`Mathlib/Data/Nat/Prime/Factorial.lean`); none says
anything about `p - k !`, so `lt_of_prime_dvd_sub_factorial`, `coprime_sub_factorial` and
`not_dvd_sub_factorial_of_le` are new. `exact?` fails on all of
`lt_of_factorial_lt`, `lt_of_prime_dvd_sub_factorial`, `coprime_sub_factorial` and
`factorialsLessThanN_eq_image`. In the interest of full disclosure: the headline
`allFactorialSubtractionsComposite_iff` *is* reachable by automation — unfolding the three
definitions and calling `grind` closes it — so its value is in being stated and named for
reuse, not in the difficulty of its proof. I also grepped the pinned repository for any other
file mentioning `AllFactorialSubtractionsComposite` or `factorialsLessThanN`: only
`FormalConjectures/ErdosProblems/1059.lean` itself does.

Pre-existing results used as dependencies rather than restated: `Nat.not_prime_of_dvd_of_lt`
(`Mathlib/Data/Nat/Prime/Basic.lean`), `Nat.dvd_factorial`, `Nat.self_le_factorial`,
`Nat.factorial_le`, `Nat.prime_dvd_prime_iff_eq`, `Nat.exists_prime_and_dvd`,
`Nat.minFac_prime`, `Nat.minFac_dvd`, `Nat.minFac_sq_le_self`, `Nat.eq_one_of_dvd_coprimes`,
`Nat.pow_le_pow_left`, `Nat.le_of_dvd`, `Nat.sub_add_cancel` and
`Set.infinite_of_forall_exists_gt`.

## Corrections made after review

This file was revised in response to a second review. The mathematics and the proofs were
not weakened; the changes are deletions and honesty repairs:

1. `composite_of_prime_dvd` was **deleted** as a near-duplicate of Mathlib's
   `Nat.not_prime_of_dvd_of_lt` (which applies through the reducible `Nat.Composite`
   abbreviation), and its single use site now uses that Mathlib lemma directly. The
   dependency list above now cites it.
2. The G4 claim that "`Nat.Composite` does not exist in Mathlib, so none of the statements
   can be Mathlib restatements" was **removed**: it is a non-sequitur, because the
   abbreviation is reducible.
3. The description of `decidableAllFactorialSubtractionsComposite` — in the module
   docstring, in the instance's docstring and here — now states that it instantiates
   `B := n` and is therefore an `O(n)`-step check, not the `O(log n / log log n)` one, and
   that `decide` through it already needs `maxRecDepth` above the default at `n = 211`.
4. A third `example` was added so that the instance is actually exercised inside the file
   (`example : Erdos1059.AllFactorialSubtractionsComposite 101 := by decide`, which compiles
   at the default `maxRecDepth`); as submitted before, neither example used the instance.
5. The docstring of `not_dvd_sub_factorial_of_le` no longer says a fixed-modulus covering
   system "cannot produce primes in the target set" (which does not follow, and such primes
   are in fact plentiful); it now says what is proved — no prime factor of a fixed `M` can
   certify compositeness of `p - k !` once `k ≥ M`, so such a system cannot cover the whole
   range `k ! < p`.
6. The "search pruning" claim for `not_allFactorialSubtractionsComposite_of_lt` is now
   qualified with the measure of the pruned region, `O((log n / log log n)^3)`, so it is not
   read as a material speedup.

## References

* Erdős problem 1059: https://www.erdosproblems.com/1059
* Formal Conjectures repository: https://github.com/google-deepmind/formal-conjectures
* Mathlib 4: https://github.com/leanprover-community/mathlib4
* Background on the covering-congruence technique whose failure is certified here (Erdős's
  original covering-system paper): P. Erdős, "On integers of the form 2^k + p and some
  related problems", Summa Brasil. Math. 2 (1950), 113–123 —
  https://users.renyi.hu/~p_erdos/1950-07.pdf

## AI assistance disclosure (G6)

This contribution was produced with AI assistance (Anthropic's Claude, used as a coding and
proof-search assistant inside a terminal agent session on 2026-09-02, including the
post-review corrections listed above). The choice of obstacle, the statement of every lemma,
the proofs and the prose were developed in that session and checked by compiling the file
against the pinned workspace; nothing was copied from another contribution, from a solution
set, or from any other submission. Every claim in the file's module docstring and in this
document corresponds either to a declaration that elaborates in the pinned environment or to
a behaviour measured in it, and the compile is warning-free.
