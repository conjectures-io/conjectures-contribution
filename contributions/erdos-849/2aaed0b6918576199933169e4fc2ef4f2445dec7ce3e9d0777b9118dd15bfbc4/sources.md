# sources.md — contribution to erdos-849 (`Erdos849.erdos_849`)

## What the target asks

`Erdos849.erdos_849` asks whether for every integer `t ≥ 1` there is an `a` such that
`{n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t`, i.e. whether every multiplicity `t`
is attained by the number of rows of Pascal's triangle in which `a` occurs at a position
`1 ≤ k ≤ n/2`. This is Erdős problem 849 and is open; this contribution does not attempt to
solve it.

## The obstacle addressed

The counted object is an unbounded `Set ℕ` with an existential over `k` inside it, and the
count is taken with `Set.ncard`, which is junk-valued (`0`) on infinite sets. Consequently:

1. nothing at all can be proved about the count before finiteness of the set is established,
   and finiteness is not apparent from the statement: `2 * k ≤ n` bounds `k` in terms of `n`,
   but nothing bounds `n`;
2. the membership predicate is not visibly decidable, so the naive `Finset` reformulation
   would have to range over all of `ℕ`;
3. even once a bound on `n` is available, a concrete witness cannot be checked by `decide`,
   because the kernel evaluates `Nat.choose n k` through Pascal's recurrence, at a cost of
   about `n.choose k` additions. Every interesting witness (`a = 3003` needs the range
   `[4, 78]`, which contains `Nat.choose 78 39`) is therefore unverifiable as stated.

## The delta

A single self-contained file, `CW_erdos_849.lean`, 28 declarations in the namespace
`Contribution.Erdos849Counting`, compiling with zero errors and zero warnings against the
pinned workspace; every declaration's `#print axioms` is a subset of
`[propext, Classical.choice, Quot.sound]`.

* **Left-half monotonicity of binomial coefficients.** `choose_le_choose_of_le_half`:
  `i ≤ j` and `2 * j ≤ n` imply `n.choose i ≤ n.choose j`. Mathlib has only the single-step
  version `Nat.choose_le_succ_of_lt_half_left` and the comparison with the middle coefficient
  `Nat.choose_le_middle`; its two-index lemma `choose_le_middle_of_le_half_left` is `private`
  and compares with the middle coefficient only. `exact?` fails on the statement in the pinned
  environment. Corollaries `self_le_choose` (`n ≤ n.choose k`) and `self_lt_choose`
  (`n < n.choose k` for `k ≥ 2`) supply the missing bound `n ≤ a` and pin the trivial solution.
* **`n.choose k` is never prime for `2 ≤ k` and `2 * k ≤ n`** (`not_prime_choose`), proved
  from `Nat.add_one_mul_choose_eq` plus the strict bound `n < n.choose k`: a prime value would
  have to divide `(n-1).choose (k-1)`, which forces `n ∣ k`, impossible for `0 < k < n`. Also
  absent from Mathlib (`exact?` fails). Consequence: `sols_of_prime : p.Prime → sols p = {p}`,
  so `t = 1` in the target is realised by an infinite family, not by a sporadic example.
* **The counted set and its degenerate cases.** `sols` is definitionally the target's set
  (`sols_eq_target` is `rfl`), with `sols_finite`, `le_of_mem_sols`, `self_mem_sols`,
  `sols_eq_empty_of_lt_two` (no `a < 2` is ever a witness) and `one_le_ncard_sols`
  (so `t = 0` is unattainable).
* **A kernel-checkable finite search.** `HasProperRep a n` is the `k ≥ 2` part of membership,
  phrased through `Nat.descFactorial k / k !` rather than `Nat.choose` — equal by
  `Nat.choose_eq_descFactorial_div_factorial` (`hasProperRep_iff`), but evaluated by the kernel
  in `2k` multiplications and one division instead of `n.choose k` additions. With
  `mul_pred_le_of_hasProperRep` (`n * (n-1) ≤ 2 * a`, so nontrivial solutions are only
  `O(√a)` large), `sols_eq_insert_properSols` and `ncard_sols_eq` turn the target's `ncard`
  into a `Finset.card` that `decide` actually evaluates, for any user-supplied bound `B` with
  `2 * a < (B + 1) * B` and `B < a`.
* **Worked use site.** `erdos_849_of_le_four` proves the right-hand side of the reward
  statement, verbatim in its own syntax, for every `t ≤ 4` (witnesses `3`, `6`, `120`, `3003`),
  and a closing `example` reruns the whole recipe on a fresh value (`a = 210`, `B = 21`).

Checked byproducts that were not previously verified in this workspace:
`(sols 6).ncard = 2`, `(sols 120).ncard = 3`, `(sols 3003).ncard = 4`, `(sols 210).ncard = 3`,
and `(sols p).ncard = 1` for every prime `p`.

## Citations

* Erdős problem 849 statement: https://www.erdosproblems.com/849
* Singmaster's conjecture and the multiplicity of entries of Pascal's triangle (background for
  `a = 3003`, which occurs eight times in the triangle, i.e. in four rows at `k ≤ n/2`):
  https://en.wikipedia.org/wiki/Singmaster%27s_conjecture
* OEIS A003015, numbers occurring five or more times in Pascal's triangle:
  https://oeis.org/A003015
* D. Singmaster, *How often does an integer occur as a binomial coefficient?*, American
  Mathematical Monthly 78 (1971), 385–386. (Bibliographic reference only; no DOI/JSTOR link is
  asserted here because it was not verified in this session.)
* Mathlib lemmas relied on, in the pinned `Mathlib/Data/Nat/Choose/Basic.lean`:
  `Nat.choose_le_succ_of_lt_half_left`, `Nat.choose_le_middle`, `Nat.choose_two_right`,
  `Nat.add_one_mul_choose_eq`, `Nat.choose_eq_descFactorial_div_factorial`:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Nat/Choose/Basic.lean

## Provenance and disclosure

This contribution was produced with AI assistance (Anthropic Claude, driven interactively by
the submitter): the statements, proofs and documentation in `CW_erdos_849.lean` were drafted
and iterated by the model and compiled against the pinned `formal-conjectures` workspace until
they elaborated with zero errors and zero warnings. Every claimed lemma was machine-checked in
that workspace; the axiom check (`#print axioms`) was run on all 28 declarations and then the
`#print` lines were removed. Novelty was checked by grepping the pinned Mathlib source and by
running `exact?` on the four load-bearing statements, all of which fail to be closed by the
library. The work is original to this submission and was not copied from another contribution;
no other contributor's file was consulted beyond reading two previously merged contribution
files in the same workspace for house style (`CW_erdos_617.lean`, `CW_erdos_1003.lean`).
