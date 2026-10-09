# Sources, scope, and reusable results

This is one expanded partial contribution to
[Erdős Problem 11](https://conjectures.io/problems/erdos11-erdos-11). The exact
target is
`∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l`.
The contribution does not prove or refute that target. It provides checked
certificate interfaces, obstruction-counting arguments, order-lifting and
periodic-cover results, cofactor bounds, and explicit examples identifying
limits of proposed proof strategies.

## Lineage and the expanded submission

The published parent is
[`9912bf43713402fa030c83358b48a3fe22041358846f121c30389f4e1775d74a`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-11/9912bf43713402fa030c83358b48a3fe22041358846f121c30389f4e1775d74a).
Its ten structural results remain available in that published contribution.
Only its witness-elimination equivalence is reproduced here, because it is
needed by the standalone certificate API. Its original proof is credited to
the parent. The other nine inherited results are linked rather than submitted
again, and none of the parent's work is claimed as new mathematical work.

This package expands the author's existing, unmerged
[pull request 140](https://github.com/conjectures-io/conjectures-contribution/pull/140).
The earlier proposed record
`45bc0230584c6702fe2d89234672a6c6d179f001a2d3fb8270a0d5de0d24e0a1` is superseded
by a newly promoted and signed record in the same pull request. Its earlier
certificate, CRT-prefix, finite-capacity, and short-gap results are retained.
The old signed record is not edited in place, and no contribution already
accepted on the canonical main branch is changed. Because that earlier record
has not been merged, it is documented here as the previous submission rather
than listed as an already-published parent in metadata.

The marginal additions are the results developed in the following 17 research
modules: `WindowObstructionBudget`, `ObstructionEscape`, `SharpFiniteCapacity`,
`GlobalCapacityCriterion`, `NonWieferichSeparation`, `NonWieferichOrderBound`,
`PrimeSquareOrderLifting`, `KnownWieferichPeriods`, `OrdinaryCoverEscape`,
`KnownExceptionCoverEscape`, `PrefixHeightRegression`, `SmallWindowSharpness`,
`CofactorMultiplicity`, `CofactorBudget`, `LateCofactorBudget`,
`WindowBudgetSharpness`, and `MiddlePrimeNecessity`. The submitted standalone
source assembles these results with their required earlier proofs. It retains
the earlier 25 public declarations, including the one credited parent lemma,
and adds 61 public declarations, including supporting definitions, for a total
of 86. It does not depend on those development modules being available as
sibling imports. Twenty one-use private primality helpers are placed as local
proofs in their consumers to meet the repository declaration limit. Their proof
bodies and all public results are retained; the final file has 197 top-level
declarations, comprising 86 public declarations and 111 private helpers.

These results are offered as one coherent, reusable unit. Credit is requested
for the checked delta and its use in the target, not for inherited lemmas,
generated helper count, repeated packaging, computational search volume, or
time spent. The author and reward destination are the same as in the prior
submission. Recognition and any eventual payment remain subject to the
repository's [contribution contract](https://github.com/conjectures-io/conjectures-contribution/blob/main/contribution-contract.md).

## Concrete handoff

Declaration names below are relative to
`Contribution.Erdos11Certificates`. `Cofactors`, `ShortCollisions`,
`HeightRegression`, and `WindowSharpness` identify the corresponding groups.

### Finite certificates and failed prefixes

`not_representation_iff_prime_square_cover` turns absence of a representation
into a finite prime-square-divisibility obligation after supplying a bound
`n ≤ 2^L`. `not_representation_of_square_divisors` accepts arbitrary explicitly
nontrivial square divisors. `refute_of_three_mod_four_certificate` connects a
complete certificate in the requested residue class to negation of the exact
universal target. No complete counterexample certificate is supplied.

`arbitrarily_long_obstruction_prefix` and `no_uniform_exponent_bound` show that
no fixed initial exponent cutoff proves the conjecture, even in the class
`n % 4 = 3`. The constructed integer depends on the prefix length. Exchanging
these quantifiers would not produce a counterexample.

The retained regression gives twelve failed initial exponents for
`40448892456331339`, followed by a kernel-checked squarefree representation at
exponent 12. It is a positive use example for the certificate machinery.

### Sharp finite capacities and the 110-exponent window

`blocking_exponents_card_le_sharp` bounds the number of obstructions from one
modulus by `(L - 1) / t + 1`, where `t` is the relevant positive multiplicative
order. `finite_cover_capacity_sharp` sums this bound for a supplied complete
covering pool. `representation_of_capacity_deficit` turns a strict deficit
into a squarefree representation for any odd integer, accounting separately
for the possible factor 4 at exponent zero. The uniform deficit required for a
global proof is not established.

`ShortCollisions.prime_square_mersenne_lt_110` classifies all prime squares
dividing `2^d - 1` for `0 < d < 110`: only prime bases 3, 5, and 7 occur.
Consequently, primes at least 11 cannot repeat as blockers within the first
110 exponents. `small_blockers_card_le_31` shows that the three smaller prime
squares obstruct at most 31 exponents there, and
`at_least_79_distinct_large_blockers` requires at least 79 distinct assigned
primes at least 11 in a complete failed prefix. The escape theorem
`representation_of_small_large_prime_pool` supplies a useful converse when
every large blocker belongs to a pool of cardinality at most 78.

`small_blockers_bound_attained` verifies that the bound 31 is attained.
`WindowSharpness.large_blocker_bound_attained` constructs a complete
110-exponent failed prefix using exactly 79 distinct assigned large primes.
`WindowSharpness.cannot_replace_79_by_80` therefore rules out raising the
general lower bound without additional hypotheses. The large integer in that
example has 1155 admissible exponents, so the certified failed prefix does not
constitute an Erdős counterexample. A later positive witness was independently
checked numerically; that numerical witness is not presented as a Lean theorem.

### Prime-square orders and the limits of periodic covers

`square_order_eq_of_nonwieferich` proves the standard identity
`ord_(p²)(2) = p * ord_p(2)` for an ordinary odd prime. The exceptional identity
`square_order_eq_of_wieferich` proves that the order does not grow when
`p² ∣ 2^(p-1) - 1`. Supporting lemmas transfer these identities to finite
obstruction counts and repeated exponent gaps.

`wieferich_blocker_is_simultaneous` shows that a Wieferich prime actually
obstructing a remainder for `n` also satisfies `p² ∣ n^(p-1) - 1`.
`order_1093_square` and `order_3511_square` verify the precise periods 364 and
1755. The accompanying repeated-blocker example checks why the ordinary-prime
gap bound cannot be applied to exceptional primes.

`exists_avoids_ordinary_periods` uses CRT to escape any finite collection of
ordinary-prime exponent classes, with an explicit product bound on the escape
exponent. `periodic_cover_contains_other_wieferich` proves that a finite pool
covering every natural exponent must contain a Wieferich prime other than
1093 and 3511. Its quantifier over every exponent is essential: a hypothetical
individual counterexample only obstructs its finite admissible prefix, so this
theorem does not impose that exceptional-prime requirement on every individual
counterexample.

`HeightRegression.initial_prime_product_exceeds_n` rules out a tempting but
invalid size argument. For `n = 118811`, an irredundant initial four-exponent
certificate uses distinct ordinary primes 109, 3, 13, and 199, whose product
845949 exceeds `n`. `HeightRegression.candidate_has_representation` also checks
the positive witness `118811 = 118795 + 2^4`. Thus this is a counterexample to
the auxiliary prime-product bound, not to Erdős 11.

### Cofactor multiplicity and finite splitting

`Cofactors.no_three_exponents` proves that for fixed odd `n` and fixed natural
`c`, at most two positive exponents can appear in representations
`n = c*u² + 2^l`. Neither `c` nor `u` is assumed squarefree or prime. The proof
gives explicit adjacent-root inequalities through
`Cofactors.adjacent_root_bounds`. `Cofactors.cofactor_mod_eight` restricts the
cofactor to the residue class of `n` modulo 8 when `l ≥ 3`, and
`Cofactors.repetition_height_bound` controls where a cofactor can repeat.

`Cofactors.representation_of_mixed_budget` gives a reusable finite counting
interface: if exceptional failed exponents lie in `T`, all remaining failures
are covered by a cofactor pool `Q`, and `#T + 2*#Q < #S` for an admissible
exponent set `S`, then a representation exists.
`Cofactors.representation_of_prime_cofactor_split` obtains a concrete pool
`Q = {c < C : c % 8 = n % 8}` from the cutoff `C*p² ≥ n` for large square
divisors. The complementary prime obstructions still require a bound.

In a sufficiently late exponent window, each cofactor occurs at most once.
`Cofactors.late_cofactor_exponents_card_le_one` and
`Cofactors.representation_of_late_prime_cofactor_split` improve the cofactor
contribution from `2*#Q` to `#Q`. `Cofactors.late_window_height` provides an
explicit threshold from a binary-length bound. These are conditional finite
criteria, not a uniform solution of the target.

### Explicit remaining quantitative obligation

For `L = n.log2 + 1`, `middleObstructions n L L` consists of exponents
`3 ≤ a < L` for which some prime `p ≥ 11` satisfies both `L*p² < n` and
`p² ∣ n - 2^a`. It counts exponents, not distinct primes.

`middle_prime_budget_of_no_representation` combines the small-prime ceilings
and cofactor argument without discarding finite rounding terms.
`middle_prime_linear_necessity` proves that a hypothetical counterexample
must satisfy `17*L ≤ 35*#M + 253`, where `M` is this middle obstruction set.
`middle_prime_two_fifths_necessity` gives `2*L ≤ 5*#M` for `L ≥ 85`.

The sufficient theorem `representation_of_middle_third` proves a
representation when `L ≥ 48` and `3*#M ≤ L`. Finally,
`global_of_finite_base_and_middle_bound` connects that estimate to the exact
original target, assuming both a complete base certificate below `2^47` and
the uniform middle-prime estimate for every odd integer at least `2^47`.
Neither closing hypothesis has been proved in this contribution. The theorem
requires the estimate on both odd residue classes; the inherited parent does
not already prove the original target for `n % 4 = 1`.

## Mathematical and software provenance

- The inherited structural framework comes from the published parent linked
  above. Its not-four-divides reduction assumes the original conjecture; that
  assumption is not used to prove any unconditional new target result.
- The failed-prefix CRT construction follows the standard argument in Remark 4
  of Christian Hercher's
  [On the Sum of Squarefree Integers and a Power of Two](https://arxiv.org/html/2411.01964v1).
  The formalized interface adds the requested residue constraint and arbitrary
  lower bounds. The underlying CRT construction is not claimed as new.
- The multiplicative-order and Wieferich framework is classical; see Andrew
  Granville and K. Soundararajan,
  [A Binary Additive Problem of Erdős and the Order of 2 mod p²](https://dms.umontreal.ca/~andrew/PDF/wieferich.pdf),
  and Keith Conrad's
  [Wieferich primes](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/wieferich-primes.pdf).
  This submission supplies checked target-specific interfaces and finite
  arithmetic certificates. No density result is promoted to a pointwise theorem.
- The adjacent-factorization approach to cofactor multiplicity is discussed in
  [Kalinin's note on Erdős 11](https://kilin-math.github.io/assets/numbers/erdos11.pdf).
  The present proof establishes its factor inequalities explicitly, avoids the
  extra positive-sign assertion in that note's Lemma 2, and works for arbitrary
  natural cofactors. The at-most-two principle itself is not claimed as new.
- The proof implementations and their integration were prepared during this
  task with OpenAI Codex assistance. Standard APIs come from
  [Mathlib](https://github.com/leanprover-community/mathlib4), including finite
  sets, Chinese remaindering, squarefreeness, multiplicative order, natural
  logarithms, and proof-producing arithmetic tactics.
- Sage/PARI generated arithmetic candidates with primality proofs enabled.
  The short-gap proof includes explicit factorizations and Lucas primality
  certificates, and the 110-exponent sharpness construction has an explicit
  divisor certificate. Generation is untrusted: the claimed Lean results are
  checked again from ordinary proof terms. Numerical search records and the
  modular-root filter explored during research are not submitted as
  kernel-certified universal bounds.

## Verification scope

The development baseline records 26 verified source modules in
`formal-verification.json`, with source hashes and axiom closures for 91 named
public results and definitions. Those counts include credited inherited work
and development interface material; they are provenance and audit counts, not
an independent measure of mathematical contribution value.

The development proofs were checked against the original task pin: Lean
4.35.0-rc2, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, and Formal
Conjectures `4b69a7dca3e731dd1f28cb523b9ebd2ea32527f4`. Axiom audits allow only
`propext`, `Classical.choice`, and `Quot.sound`.

The exact standalone source also compiled cleanly with warnings treated as errors
under Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`,
the contribution repository pin. It also compiled under the original Lean 4.35.0-rc2
pin. All 86 public declaration closures were audited under Lean 4.33.1 and use
only `propext`, `Classical.choice`, and `Quot.sound`. The accompanying
`verification.json` records the exact source digest, compiler versions, dependency
revisions, and axiom audit. Remote isolated CI remains authoritative. No claim of completion follows merely from
successful compilation of the conditional theorems.

The contribution does not invoke the unproved `Erdos11.erdos_11` declaration,
add an axiom, use a native decision oracle, or rely on a private local service
during elaboration. Exploratory searches restricted to `n % 4 = 3` do not
establish a universal statement over all odd integers.
