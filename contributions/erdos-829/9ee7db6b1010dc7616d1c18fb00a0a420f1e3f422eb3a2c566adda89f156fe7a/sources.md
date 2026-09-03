# Sources and provenance

## Declared target

- Contribution target: `erdos-829`; site slug: `erdos829-erdos-829`.
- Proposed kind/mode: `lemma` / `formalized`.
- Proposed title: `Erdős 829: discriminant and primitive-factor filters for two-cube representations`.
- Reward target: `fc-target:Erdos829.erdos_829`.
- Formalized task: `fc-379fc029-erdos829-erdos-829-683570d245-formalized-v1`.
- Exact source: [`FormalConjectures/ErdosProblems/829.lean`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/829.lean)
  at commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.
- Problem reference: [erdosproblems.com/829](https://www.erdosproblems.com/829).

The exact target asks for one fixed `C : ℕ` such that the ordered representation
count `sumRep Erdos829.cubes n` is `O((Real.log n) ^ C)`. This file does not
produce such a `C` and therefore does not solve Erdős 829.

## Mathematical provenance

The source problem is attributed to Paul Erdős and Underwood Dudley,
[*Some Remarks and Problems in Number Theory Related to the Work of Euler*](https://doi.org/10.1080/0025570X.1983.11977060),
*Mathematics Magazine* 56 (1983), 292–298.

For a representation `n = x^3 + y^3`, put

```text
d = x + y,
k = |x - y|.
```

Then `d ∣ n`, `k ≤ d`, `d + k` is even, and

```text
4n = d (d^2 + 3k^2).
```

Conversely, these finite arithmetic conditions reconstruct the nonnegative
roots `(d + k) / 2` and `(d - k) / 2`. Kevin A. Broughan,
[*Characterizing the Sum of Two Cubes*](https://cs.uwaterloo.ca/journals/JIS/VOL6/Broughan/broughan25.html),
*Journal of Integer Sequences* 6 (2003), Article 03.4.6, Theorem 2.1, gives the
equivalent characterization for **positive** roots. This Lean file translates
the criterion to the exact Formal Conjectures definition using nonnegative
natural cubes and separately handles the zero-root boundary. Michael Nyblom,
[*A Closed Form for Representing Integers as Sums and Differences of Cubes*](https://cs.uwaterloo.ca/journals/JIS/VOL25/Nyblom/nyblom8.html),
*Journal of Integer Sequences* 25 (2022), Article 22.4.4, restates and develops
Broughan's characterization.

The second filter starts from the classical factorization

```text
n = (x + y) (x^2 - xy + y^2).
```

For coprime roots, the two displayed factors have gcd dividing `3`. Hence, if
`3 ∤ x + y`, the root sum is a unitary divisor of `n`: it divides `n` and is
coprime to its cofactor. These are elementary consequences of the factorization;
this file claims their checked Lean formalization, not a new informal theorem.

James Maynard's survey
[*Sums of three positive cubes*](https://doi.org/10.1112/jlms.70554), section 2.1,
uses the coarser fact that there are at most two two-cube representations per
divisor. That is the content of the earlier local v1 divisor-count bound.

## Exact theorem delta from v1

The earlier draft proved only

```lean
sumRep Erdos829.cubes n ≤ 2 * n.divisors.card
```

and its corresponding big-O statement. This v2 file contains 40 declarations
and adds the following checked API:

1. the forward discriminant identity and constructive converse;
2. the exact positive-`n` characterization
   `d ∈ admissibleRootSums n ↔ ∃ x y, x + y = d ∧ x^3 + y^3 = n`;
3. the necessary interval `n ≤ d^3 ≤ 4n` and the finite
   `cubicWindowDivisors n` sieve;
4. the sharper bounds by the exact admissible set and by the cubic-window set;
5. an injection proof showing the admissible bound is never weaker than the
   full-divisor bound;
6. a target-facing big-O interface and an implication from a fixed-polylog
   estimate for the **exact admissible set**;
7. the primitive-factor identities, gcd-divides-three theorem, and unitary-
   divisor conclusion for coprime roots with `3 ∤ x + y`;
8. the concrete boundary/strict-filter certificate
   `admissibleRootSums 8 = {2}`.

No polylogarithmic estimate for `cubicWindowDivisors` is asserted. Its full
cardinality can be much larger than the exact admissible set. Likewise, the
fixed-polylog hypothesis on `admissibleRootSums` is the remaining asymptotic
obligation, not evidence that the obligation has already been discharged.

## Lean/library ingredients

The file uses the pinned `Erdos829.cubes`, `AdditiveCombinatorics.sumRep`,
`sumRep_def`, natural antidiagonals and divisors, `Odd.nat_add_dvd_pow_add_pow`,
finite-cardinality injections, and Mathlib's asymptotics API. `Classical.choose`
selects the natural cube root associated with a cube value.

## Authorship disclosure

The Lean proof and these notes were developed with OpenAI Codex assistance. A
future signer must independently inspect the mathematics, target relevance,
provenance, metadata, and recognition risk.
