# Sources, scope, and use

This is one partial contribution for `CarmichaelTotient.charmichaelTotient`. The standalone Lean module provides prime-square forcing, descent for hypothetical singleton totient inputs, globally quantified sufficient uniqueness certificates, and exact obstructions to several incomplete collision constructions. It does not prove or refute the target.

All names below are relative to `Contribution.CarmichaelTotient`, including the `InverseTotient` subnamespace. A singleton means a positive `n` for which every natural number with totient `φ(n)` equals `n`; this is the explicit predicate `UniqueTotient`.

## Concrete obstacles and reusable interfaces

### Prime-square forcing

- `Klee.carmichael_klee` formalizes the full Carmichael--Klee lemma in quotient/radical form. Given a unitary divisor `d` of a hypothetical singleton, the required prime-support condition on `φ(d)`, and a permitted multiplier `e`, primality of `p = 1 + e * φ(d)` supplies `p^2 ∣ n`. `carmichael_klee_support` exposes a factored version.
- `GlobalStrongerForcing.thirteen_or_nineteen_sq_dvd` gives the classical `13^2 ∣ n ∨ 19^2 ∣ n` branch after the initial `2,3,7,43` forcing.
- `PrimeReplacement.prime_sq_dvd_of_pred_support_except_five` strengthens the predecessor-support interface: if `p ∣ n`, every prime factor of `p-1` need only divide `n` **or equal 5** to force `p^2 ∣ n`. It does not require `5 ∣ n`. The companion theorem `carmichael_klee_support_except_five` propagates this relaxation to the full factored Klee argument.
- `PrimeReplacement.eleven_sq_dvd_of_unique` is a checked use of the replacement idea: `11 ∣ n` forces `121 ∣ n`, including the previously uncovered case `5 ∤ n`. `two_five_prime_sq_dvd_of_unique` treats all prime predecessors `2^(s+1) * 5^k`. The block-collision lemmas expose the actual replacement witnesses used in the proofs.

These interfaces let a later solver discharge prime-square obligations without redoing the totient calculations. They do not assert that any prime not already forced by the explicit hypotheses must occur, or that the resulting generation process continues indefinitely.

### Minimal-counterexample descent

- `MinimalDescent.exists_reduced_counterexample` constructs a singleton divisor congruent to `4 mod 8` from any singleton input. `carmichael_iff_four_mod_eight` connects this directly to the full target: proving the conjecture throughout that residue class suffices.
- `FermatDescent.unique_cofactor_of_fermat_prime` and `exists_fermat_prime_descent` remove an entire Fermat-prime power, for a Fermat prime greater than 3, from a singleton not divisible by 8. The resulting cofactor is a smaller singleton. `fermat_prime_not_dvd_of_minimal_unique` gives the corresponding exclusion for a least counterexample.
- `OddDescent.unique_cofactor_of_predecessor_not_dvd` generalizes actual cofactor descent to any prime `p` under the explicit condition `(p-1) ∤ φ(c)`, where `n = p^(a+1)c` and `p ∤ c`.
- `OddDescent.predecessor_sq_dvd_totient_of_minimal_unique` is a concrete use of that descent: every prime divisor `p` of a least singleton must satisfy `(p-1)^2 ∣ φ(n)`. The stronger cofactor statement `predecessor_dvd_cofactor_totient_of_minimal_unique` retains where the second predecessor factor comes from.

The last statements supply necessary constraints on a hypothetical least counterexample. They are not claimed to make such an integer impossible.

### Sound counterexample certificates and search restrictions

- `PomeranceCriterion.singleton_of_divisor_certificate` proves global uniqueness from a positive candidate satisfying the complete divisor checklist: for every `d ∣ φ(n)`, if `d+1` is prime then `(d+1)^2 ∣ n`. `refutes_carmichael_of_divisor_certificate` is a checked use site deriving the negation of the full target from such a candidate and certificate. No candidate is supplied.
- `SquareKernelCriterion.exists_criterion_iff_squareKernel` reduces existence **within that sufficient criterion's witness class** to squares of products of distinct primes.
- `FermatDescent.minimal_unique_fails_criterion` proves that a least singleton cannot satisfy that sufficient criterion. `exists_unique_outside_criterion` therefore shows that, if any counterexample exists, some counterexample lies outside this certificate class. This prevents treating the sufficient criterion as a complete search characterization. It does not rule out a nonminimal witness satisfying the criterion.
- `InverseTotient.totient_injective_on_powerful` proves that two positive powerful integers with equal totients must be equal. Here powerful means every prime divisor occurs squared. In particular, restricting **both** the candidates and their possible companions to powerful integers would miss every distinct companion of a powerful input. This theorem is an injectivity statement, not a companion-existence theorem, and it does not assert that every Carmichael counterexample is powerful.

### Collision constructions and verified limitations

- The original collision transport, `prime_scaling_totient_iff`, and `prime_power_scaling_collision` describe exactly when prime scaling preserves a collision and extend it through every exponent.
- `InverseTotient.FiniteRatios.finite_menu_misses_four_mod_eight` proves that any finite list of fixed nonidentity ratios misses an entire arithmetic progression `n = 4*M^2*(2*k+1)` within the reduced class. The theorem explicitly assumes each denominator divides the input; for a ratio in lowest terms this exactly captures an integral rational move. `ratio_obstruction_of_prime_squares` exposes the local support condition, and `finite_menu_misses_progression` gives a simpler all-input version. These statements rule out completeness of a finite menu of actual fixed ratios, not a finite set of formulas with unbounded parameters.
- `OddDoubling.no_odd_preimage_two_pow_thirty_two` and `odd_doubling_not_universal` provide an exact obstruction to unrestricted odd-preimage doubling: `φ(4294967295)=2^31`, but no odd input has totient `2^32`. The supporting eligible-prime classification is checked by Lean. This auxiliary obstruction is **not** a Carmichael counterexample and makes no claim that `2^32` has a unique unrestricted preimage.
- `OddDescent.five_not_dvd_of_totient_four_times_three_power` exhibits an unbounded family of attained totients whose preimages cannot contain 5, although 4 divides the totient. The canonical boundary collision/lift lemmas show that even a companion containing every predecessor prime can lift back to the original input. These results identify the missing normalization and distinctness hypotheses in a proposed global descent.
- `ClosureAudit.predecessor_square_fixed_point` retains the exact fixed point `{2,3,7,43}` of the weaker predecessor-square rule, so that rule alone cannot be mistaken for an infinite-chain proof.

The initial bound `3261636 ∣ n` and the proof of companion existence for **every** `0 < n < 13046544` are retained. These are formal consequences of divisibility and explicit checked collisions; no new interval scan or larger search bound is claimed.

## Scope and provenance

No global solution, globally certified singleton witness, or infinite forced-prime theorem is supplied. The historical Klee/Ford enormous lower bounds are not formalized here. Paper-only research notes and speculative first-layer existence arguments are not presented as verified artifacts.

The Carmichael--Klee and Pomerance arguments follow the primary references below. The remaining elementary deductions, collision identities, and structural interfaces were developed and assembled during this investigation, using Mathlib identities and AI assistance. No claim of mathematical priority or a new resolution is made. The intended contribution is the explicit checked Lean handoff and the strengthened interfaces, rather than ownership of classical mathematics.

## Lineage and formalization delta

This is an expanded replacement of the same pending, unmerged [pull request #139](https://github.com/conjectures-io/conjectures-contribution/pull/139). It supersedes unmerged record `a6afad0b69d6f395164f56bbebc290b35431109d553f95b752a701fd02a96fd3`, which previously superseded `c5b0a9baba06891baad13582f2d541b445a93066fe90b522074549262cbb3abd`. The old pending records are not claimed as separate contributions. No accepted contribution is changed.

The canonical target index contains no published contribution at base `be220ff2519ecfd61b28ba9e477321e4287ef6b4`, so there are no published parent records to list. The module retains all 60 declarations of the prior pending submission and adds 49: 48 proved statements, including six private helpers, and one definition. The complete source has 105 proved lemmas/theorems and four definitions, of which 99 proved statements and four definitions are public. All 109 declarations are audited. Counts describe the inventory; they do not establish recognition value or a reward share.

The material additions since that pending submission are the minimal/Fermat/general conditional descent, predecessor duplication at a least counterexample, missing-5 prime-square forcing, powerful-input injectivity, and the exact construction obstructions described above. All declarations now use the same contribution namespace convention. Namespace organization and comments are not claimed as mathematical progress.

## Primary references

- [Kevin Ford, The distribution of totients, Section 7.3, Lemma 7.2](https://arxiv.org/abs/1104.3264), for the full Carmichael--Klee forcing statement.
- [Kevin Ford, Sieving very thin sets of primes, and Pratt trees with missing primes, introduction](https://arxiv.org/abs/1212.3498), for the classical 13/19 branch, the conditional infinite-prime route, and discussion of Pomerance's criterion.
- [Carl Pomerance, On Carmichael's conjecture, Proc. Amer. Math. Soc. 43 (1974), 297--298](https://math.dartmouth.edu/~carlp/PDF/carmichaelconjecture.pdf), for the sufficient global uniqueness criterion.
- [Mathlib, Nat.Totient at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Totient.lean), for multiplicativity, prime-power formulas, divisibility, and Euler's product identities.
- [Target problem](https://conjectures.io/problems/carmichaeltotient-charmichaeltotient).

## Verification and dependencies

`script.lean` imports only Mathlib and is elaborated independently. It has no proof holes, custom axioms, native evaluation, sibling imports, private services, or dependency on a local mathematical patch. The exact source SHA-256 is `d9fe53bdef512638fa2edd1c2d2348c211166448f1b7276eb083800714db0d8c`.

The pinned environment is Formal Conjectures `6a786f997e18e8f095762a2830d191b7e25e505e`, Lean `4.33.1`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The complete source and all 109 axiom reports compile with warnings treated as errors and a 400000-heartbeat limit. The audit dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. The local macOS checker cannot supply Linux user-namespace network isolation; remote sandbox elaboration remains a separate gate.
