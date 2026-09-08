# sources.md — erdos-1106-parts-ii

## Target

`Erdos1106.erdos_1106.parts.ii` in `FormalConjectures/ErdosProblems/1106.lean`:
`answer(sorry) ↔ ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n`, where
`Erdos1106.p n = Fintype.card (Nat.Partition n)`. Write `F n` for
`#(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors`. This is an open research problem; nothing here
claims to solve it.

Problem page: https://www.erdosproblems.com/1106 (the site returned HTTP 403 to my fetch, so
nothing on that page is quoted or relied on here; the statement used is the one formalised in
the pool file). Repository of the formalisation:
https://github.com/google-deepmind/formal-conjectures

## The obstacle

Two walls, one infrastructural and one mathematical.

1. Infrastructural. Mathlib defines `Nat.Partition n` and gives it a `Fintype` instance
   (https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Enumerative/Partition/Basic.lean)
   but proves nothing about the size of that type: there is no evaluation, no monotonicity and
   no bound for `Fintype.card (Nat.Partition n)` anywhere in the library. Kernel evaluation is
   not available either: I checked that both `by decide` and `by decide +kernel` fail on
   `Erdos1106.p 2 = 2` (reduction gets stuck on the `Fintype.ofSurjective` instance). The only
   evaluations of this function in the pinned environment are `OeisA41.a_0 … OeisA41.a_5` in
   `FormalConjectures/OEIS/41.lean`, and from `a_2` on they are compiler-evaluated; I checked
   with `#print axioms` that they rest on `Lean.ofReduceBool` and `Lean.trustCompiler`. So any
   statement about `F` — even `F 3 ≤ 3` — needs a kernel-checked partition-function API first.

2. Mathematical. `F n > n` needs one brand new prime per step on average. The unconditional
   lower bounds available for `F` come from smooth-number counting: `p 1, …, p n` are `n`
   distinct integers `≤ p n` whose prime factors all divide the product, so
   `n ≤ (log₂ (p n) + 1) ^ F n`. Since `p n = exp(Θ(√n))` (Hardy–Ramanujan, informal here), this
   inequality can be exploited with `k = 1` (giving `2 ≤ F n` for `n ≥ 3`) but never with
   `k = 2`, so the counting route reaches neither `F n → ∞` (part (i)) nor `F n > n` (part
   (ii)). The genuinely missing input is arithmetic: a mechanism producing a prime that divides
   `p (n + 1)` but no earlier `p i`. Nothing in Mathlib does that. The contribution isolates
   that missing input as an explicit hypothesis rather than pretending to supply it.

## Delta (what this file adds, all proved outright)

Namespace `Contribution.Erdos1106PartitionPrimeFactors`, one file, 24 named declarations plus 4
worked use sites, no `sorry`, and every declaration checked with `#print axioms` to rest only on
`propext`, `Classical.choice`, `Quot.sound`.

* Partition-function API, none of which exists in Mathlib:
  `p_pos`, `p_one`, `p_le_two_pow` (`p n ≤ 2 ^ (n-1)`, via `Nat.Partition.ofComposition_surj`
  and `composition_card`), `p_lt_two_pow` (`p n < 2 ^ (n-1)` for `3 ≤ n`, by exhibiting the
  colliding compositions `[1, n-1]` and `[n-1, 1]`), `consOne` / `consOne_injective` /
  `p_lt_p_succ` (strict monotonicity from `1` on, by the injection that adds a part `1` and
  misses `Nat.Partition.indiscrete (n+1)`), `p_lt_p`, `p_le_p`, and the exact values
  `p_two : p 2 = 2`, `p_three : p 3 = 3` obtained by squeezing the strict bounds — kernel-checked,
  unlike the compiler-evaluated values in `FormalConjectures/OEIS/41.lean`.
* General number theory: `card_le_pow_log`, the box bound for smooth numbers (a finset of
  nonzero integers `≤ X` with prime factors inside a finset `S` has at most
  `(Nat.log 2 X + 1) ^ #S` elements, by injecting into the `S`-indexed exponent vectors);
  `card_primeFactors_le_log` (`#N.primeFactors ≤ Nat.log 2 N`); `primeFactors_prod`
  (prime factors of a finset product = `biUnion` of the prime factors). Mathlib's nearest
  relatives are in
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/SmoothNumbers.lean
  which bounds `#(smoothNumbersUpTo N k)` by `2 ^ #k.primesBelow * √N`, indexed by a smoothness
  bound rather than by an arbitrary finset of primes, and gives nothing usable here; I grepped
  Mathlib for `card_primeFactors`, `primeFactors_prod` and `Fintype.card (Nat.Partition` before
  keeping each statement.
* Target-facing results: `n_le_pow_log_p`
  (`1 ≤ n → n ≤ (Nat.log 2 (p n) + 1) ^ F n`); `lt_card_primeFactors_prod`, its contrapositive
  handoff form turning any upper bound `p n ≤ B` with `(Nat.log 2 B + 1) ^ k < n` into `k < F n`;
  the unconditional `two_le_card_primeFactors_prod : 3 ≤ n → 2 ≤ F n` (sharp at `n = 3`, where
  `F 3 = 2`); the upper bound `card_primeFactors_prod_le_sum`; the small-case computation
  `card_primeFactors_prod_le_of_le_four : 1 ≤ n → n ≤ 4 → F n ≤ n`; and `five_le_of_lt_card`,
  which turns that into the statement that any threshold witnessing the target's
  `Filter.Eventually` is `≥ 5`.
* Step form: `card_primeFactors_prod_succ`, the exact recursion
  `F (n+1) = #((p (n+1)).primeFactors \ (∏ i ∈ Icc 1 n, p i).primeFactors) + F n`, and
  `eventually_gt_of_new_primes`, which converts a starting point plus "one new prime at every
  step" into the target's right-hand side verbatim.

Honesty about strength: `eventually_gt_of_new_primes` is a *sufficient* criterion, strictly
stronger than the target (the target tolerates steps with no new prime once `F n - n` has
slack); this is stated in the docstring and the exact identity `card_primeFactors_prod_succ` is
supplied for solvers who need to track that slack. `lt_card_primeFactors_prod` is an implication
whose hypothesis is an upper bound on the partition function, i.e. a statement about the fixed
object of the target, not about a universally quantified instance, so it cannot be refuted by
choosing a bad instance; but I state plainly in the file that its hypothesis is satisfiable only
for `k = 1`, so it cannot by itself prove either part of 1106.

## Background references (used for orientation, not copied)

* G. H. Hardy and S. Ramanujan, *Asymptotic formulae in combinatory analysis*, Proc. London
  Math. Soc. (1918): https://doi.org/10.1112/plms/s2-17.1.75 — the `p n = exp(Θ(√n))` growth
  that pins down where the counting route stops. Not formalised here and not in Mathlib.
* P. Erdős, *On an elementary proof of some asymptotic formulas in the theory of partitions*,
  Ann. of Math. 43 (1942): https://doi.org/10.2307/1968802 — elementary route to the same
  growth, the plausible source of a future `p n ≤ 2 ^ (c * Nat.sqrt n)` in Lean.
* Mathlib files relied on:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Combinatorics/Enumerative/Composition.lean
  (`composition_card`),
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Factorization/Defs.lean
  (`Nat.factorization_inj`, `Nat.support_factorization`),
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Factorization/Basic.lean
  (`Nat.prod_primeFactors_dvd`).

## AI assistance and originality

This contribution was produced by Claude (Anthropic), an AI assistant, driven by the author.
The AI read the pool file and the relevant Mathlib sources, chose the statements, wrote every
proof, and iterated them to a clean compile; the author reviewed the result. No proof, proof
sketch or Lean code was copied from another repository, from a `formal_proof` link, or from any
other solution to Erdős problem 1106: no such solution is known. The mathematical ideas used
(counting smooth numbers by exponent vectors, bounding partitions by compositions, adding a part
`1` to get strict monotonicity) are standard textbook arguments; their Lean formalisation here
is original to this contribution. Every claim in the module docstring was checked in the pinned
environment: the failure of `decide` and `decide +kernel` on `Erdos1106.p 2 = 2`, the axiom
dependencies of `OeisA41.a_2`, the absence of any `Fintype.card (Nat.Partition …)` result in
Mathlib, and `#print axioms` for all 24 named declarations.
