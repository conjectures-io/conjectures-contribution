# sources.md — partial contribution to erdos-677

## Target

`Erdos677.erdos_677` in `FormalConjectures/ErdosProblems/677.lean`:

```
∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k
```

with `Finset.lcmInterval n k = (Finset.Ioc n (n + k)).lcm id`, i.e. Erdős's
`M(n, k) = lcm{n+1, …, n+k}` (definition in
`FormalConjecturesForMathlib/Algebra/GCDMonoid/Finset.lean`).

## The obstacle this contribution removes

Two concrete blockers sit in front of any attempt on this statement.

1. **`lcmInterval` has no unfolding lemma.** `simp [Finset.lcmInterval]` does not stop at
   `(Finset.Ioc n (n + k)).lcm id`; on `ℕ` it continues through the `LocallyFiniteOrder`
   instance and leaves goals about
   `List.foldr GCDMonoid.lcm 1 (List.map id (List.range' (n+1) (n+k-n)))`, on which none of
   the `Finset.lcm` API applies. (Observed directly: a probe using
   `simp only [Finset.lcmInterval, Finset.lcm_eq_zero_iff]` reported `Finset.lcm_eq_zero_iff`
   as an *unused* simp argument and then failed with a dependent-elimination error on the
   `List.foldr`/`List.range'` term.)

2. **There is no "prime power divides an lcm" lemma in Mathlib.** `Finset.lcm_dvd_iff`
   characterises what an lcm *divides*, which is the wrong direction for proving two lcms are
   different. `Nat.Prime.dvd_lcm`
   (`Mathlib/Data/Nat/GCD/Prime.lean`) covers only a bare prime and only two arguments, and
   there is no `Finset`-indexed analogue; `exact?` on
   `p ^ e ∣ Nat.lcm b c ↔ p ^ e ∣ b ∨ p ^ e ∣ c` fails in the pinned environment. As a result
   the standard elementary argument for this problem — "a prime `p ∈ (m, m+k]` satisfies
   `p > m ≥ n + k`, hence `p ∣ M(m,k)` but `p ∤ M(n,k)`" — cannot even be started in Lean.

## The delta

One self-contained file, 17 theorems, all in namespace
`Contribution.Erdos677LcmInterval`, no `sorry`/`axiom`/`native_decide`, every theorem checked
to depend only on `[propext, Classical.choice, Quot.sound]`.

* **Entry point.** `lcmInterval_eq_lcm_Ioc` (the missing unfolding lemma), plus the basic
  facts a solver needs at every `Nat.le_of_dvd` step: `dvd_lcmInterval`, `lcmInterval_pos`,
  `le_lcmInterval` (`n + k ≤ M(n,k)`), and the hereditary lemma
  `lcmInterval_dvd_lcmInterval` (`M(n,k) ∣ M(n',k')` for nested intervals).
* **Degenerate and base cases.** `lcmInterval_zero_eq_one` (`M(n,0) = 1`),
  `not_forall_lcmInterval_ne` (the reward statement with `k > 0` deleted is *false*, so the
  hypothesis is sharp), `lcmInterval_one_eq` (`M(n,1) = n+1`) and `lcmInterval_two_eq`
  (`M(n,2) = (n+1)(n+2)`, by coprimality of consecutive integers).
* **New machinery.** `primePow_dvd_lcm_iff` (`p ^ e ∣ Nat.lcm b c ↔ p ^ e ∣ b ∨ p ^ e ∣ c`,
  proved through `Nat.factorization_lcm`), its `Finset ℕ` version
  `primePow_dvd_finset_lcm_iff`, and the specialisation to the target's own definition,
  `primePow_dvd_lcmInterval_iff` : for `p` prime and `e > 0`,
  `p ^ e ∣ M(n,k) ↔ ∃ a, n < a ∧ a ≤ n + k ∧ p ^ e ∣ a`. This is the reformulation that turns
  the bespoke `Finset.lcm` into a statement about one integer of the interval.
* **Separation criteria.** `lcmInterval_ne_of_primePow` (exhibit a prime power dividing an
  element of one interval and no element of the other) and its prime special case
  `lcmInterval_ne_of_prime_mem_Ioc`.
* **Reduction of the target.** `erdos_677_of_primeFree`: the conclusion is *syntactically the
  reward statement*, and the hypothesis is the same statement restricted to `m, k` for which
  `(m, m + k]` contains no prime. A solver applies it as the first line of the proof and is
  left with the prime-gap case, which is the genuine core of the problem.
* **Worked use sites.** `erdos_677_of_k_le_two` proves the reward statement outright for all
  `k ≤ 2`; `erdos_677_zero_left` proves the first case `M(k,k) ≠ M(0,k)` for every `k > 0` by
  feeding Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`) into the prime witness,
  demonstrating how an external prime-existence input plugs into the API.

Nothing here claims to solve the problem: after the reduction, the open content is exactly the
prime-free case, which is untouched.

## Novelty check performed

* `grep` over the pinned Mathlib source for `lcmInterval`, `factorization_lcm`,
  `coprime_succ`, and prime-vs-lcm lemmas; `Finset.lcmInterval` occurs only in its defining
  file and in problems 677/678, with no lemmas attached to it.
* `exact?` on the two-argument prime-power statement
  (`p ^ e ∣ Nat.lcm b c ↔ p ^ e ∣ b ∨ p ^ e ∣ c`) fails, so it is not in Mathlib under another
  name; the `Finset` version a fortiori is not.
* Numerical sanity checks against the pool file's own example
  (`lcmInterval 4 3 = 210 = lcm(5,6,7)`, `lcmInterval 3 2 = 20 = 4·5`, and `M(k,k) ≠ M(0,k)`
  for `k ≤ 7`) were run in a scratch file to make sure the lemmas say what is intended; those
  `#eval`s are **not** part of the submitted file.

## References

* Erdős Problem 677: https://www.erdosproblems.com/677
* Erdős Problem 678 (the neighbouring `M(n,k) > M(m,k+1)` question, same `lcmInterval`
  definition): https://www.erdosproblems.com/678
* S. Cambie, *Resolution of an Erdős problem on least common multiples*, arXiv:2410.09138
  (2024): https://arxiv.org/abs/2410.09138 — cited for context on problem 678; it is not used
  in any proof here.
* P. Erdős, *Some unconventional problems in number theory*, Math. Mag. 52 (1979), 67–70:
  https://doi.org/10.1080/0025570X.1979.11976756
* Mathlib ingredients used: `Nat.factorization_lcm`
  (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factorization/Basic.html),
  `Nat.Prime.pow_dvd_iff_le_factorization`, `Finset.lcm_dvd_iff`/`Finset.dvd_lcm`
  (https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GCDMonoid/Finset.html),
  and Bertrand's postulate `Nat.exists_prime_lt_and_le_two_mul`
  (https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html).

## Provenance and AI disclosure

This contribution was produced with AI assistance (Anthropic Claude, used as a coding and
proof-search assistant) and reviewed by the submitter. It is original to this submission: it
was written from the pool file and the pinned Mathlib source, and is not copied or adapted
from another contribution, from an external repository, or from a published formalisation.
Every statement in the file was compiled against the pinned workspace with zero errors and
zero warnings, and each theorem's axiom footprint was checked with `#print axioms` to be a
subset of `[propext, Classical.choice, Quot.sound]` (those `#print` lines were removed before
submission and the file recompiled clean).
