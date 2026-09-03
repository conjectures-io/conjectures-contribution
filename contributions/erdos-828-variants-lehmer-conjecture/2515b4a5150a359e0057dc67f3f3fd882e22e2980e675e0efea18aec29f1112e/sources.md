# Erdős 828, Lehmer variant: sources and scope

## Intended submission metadata

- Target: `erdos-828-variants-lehmer-conjecture`
- Kind: `partial-proof`
- Mode: `formalized`
- Proposed title: `Lehmer candidates: five-factor, Carmichael, and normal-support API`
- Parents: none

## Exact target and use

- Pinned Formal Conjectures source:
  [`ErdosProblems/828.lean` at `379fc0298dc146df549e7061c3ede0353a5bb51f`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/828.lean).
- Open declaration: `Erdos828.erdos_828.variants.lehmer_conjecture`.
- Exact open body: `∀ n > 1, φ n ∣ n - 1 ↔ Prime n`.
- Contribution target: `erdos-828-variants-lehmer-conjecture`.

The unresolved implication would have to rule out a composite `n > 1` with
`φ n ∣ n - 1`. The script defines that obstruction as
`IsCompositeCandidate`, proves an exact equivalence between the target body and
the absence of such candidates, and provides checked facts a later proof can
invoke without reproving the elementary layer.

## Checked mathematical result

Every hypothetical composite candidate is proved to be odd and squarefree; it
satisfies `p - 1 ∣ n - 1` for each prime divisor `p`, Euler's congruence
`a^(n-1) ≡ 1 (mod n)` for every coprime base, and Mathlib's `IsCarmichael`
predicate. It is coprime to its own totient. For prime divisors `p,q ∣ n`, the
script proves `¬ p ∣ q - 1`, exposing Lehmer's normal-prime-support condition.

The factor-counting part proves that no product of two, three, or four pairwise
distinct primes satisfies Lehmer's divisibility; prime powers and repeated
factors are already excluded by squarefreeness. Consequently it exports the
checked interfaces

```text
5 ≤ n.primeFactors.card
32 ∣ φ n
32 ∣ n - 1.
```

The four-prime exclusion is elementary but nontrivial: ordering the primes and
bounding `n / φ(n)` forces the quotient `(n-1)/φ(n)` to equal `2`, then forces
the two least primes to be `3` and either `5` or `7`. The `5` branch reduces to
`(r-16)(s-16)=239`, whose divisor cases are composite; the `7` branch
contradicts divisibility modulo `3`. The script also retains explicit two- and
three-prime exclusions as reusable intermediate theorems.

It also proves the exact bridge
`IsCompositeCandidate n ↔ IsCarmichael n ∧ φ n ∣ n - 1`. The main downstream
interfaces are `strengthened_structure_of_composite_candidate`,
`isCompositeCandidate_iff_isCarmichael_and_totient_dvd`, and
`target_body_iff_no_composite_candidate`. The open target theorem itself is
neither assumed nor invoked.

## Prior mathematics and novelty boundary

This is a formalization of classical elementary consequences, not new number
theory. Lehmer's original paper proves much more: any composite solution would
be odd, squarefree, and have at least seven prime factors.

- D. H. Lehmer, “On Euler's totient function,” *Bulletin of the American
  Mathematical Society* **38** (1932), 745–751,
  [doi:10.1090/S0002-9904-1932-05521-5](https://doi.org/10.1090/S0002-9904-1932-05521-5).

Later published work reports still stronger lower bounds, so the checked
five-factor interface must not be presented as the best mathematical result:

- C. Pomerance, “On composite n for which φ(n) divides n−1, II,” *Pacific
  Journal of Mathematics* **69** (1977), 177–186,
  [journal PDF](https://msp.org/pjm/1977/69-1/pjm-v69-n1-p16-p.pdf).

Pomerance reports Lieuwens's proved eleven-factor bound and Kishore's then-
announced thirteen-factor bound. A later peer-reviewed article reports Pinch's
computational bounds of at least fifteen prime factors and `n > 10^30`:

- C. Ji and H. Qin, “On composite numbers `n` for which `φ(n) | n - 1`, II,”
  *Comptes Rendus Mathématique* **355** (2017), 370–377,
  [journal PDF](https://www.numdam.org/item/10.1016/j.crma.2017.03.007.pdf).

The pinned Formal Conjectures tree also has semantic predecessors in
[`Wikipedia/AgohGiuga.lean`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/Wikipedia/AgohGiuga.lean):
`AgohGiuga.squarefree_of_isCarmichael` and
`AgohGiuga.korselts_criterion`. Mathlib supplies the general totient and modular
arithmetic lemmas used by this script.

Accordingly, the only possible recognition claim is the missing target-specific
Lean handoff: a self-contained derivation from the exact totient premise,
explicit exclusions through four prime factors, a five-factor lower bound,
Carmichael and normal-support bridges, a concrete 2-adic sieve, and an exact
target-body reduction. Maintainers may reasonably judge this routine or
superseded by the stronger classical theory. No claim is made for the
underlying mathematics.

## Limitation

This package does **not** rule out composite candidates with five or more prime
factors, does not reach Lehmer's published seven-factor theorem, and does not
prove the target equivalence. Its congruence and support sieves are necessary
conditions, not an existence or nonexistence result. It is a partial-proof
portfolio, not a validator solution.

## Assistance and provenance disclosure

No Lean code was copied from a paper, another contribution, or a third-party
formalization. The proof and documentation were developed locally with OpenAI
Codex assistance. The eventual signer remains responsible for checking the
code, attribution, novelty, metadata, and recognition case before promotion.
