# Sources and intended use

## Checked contribution

This contribution formalizes a structured equal-totient construction and connects it directly to
`Erdos1004.IsDistinctTotientRun`.

Its main reusable arithmetic theorem is Schinzel's even-shift construction:

```lean
Even k → p.Prime → q.Prime → q + 1 = 2 * p →
  p.Coprime k → q.Coprime k →
  Nat.totient (q * k) = Nat.totient (q * k + k)
```

The file then supplies all of the following checked interfaces:

- a generic lemma turning any equal-totient pair inside `[n + 1, n + K]` into failure of
  `Erdos1004.IsDistinctTotientRun n K`;
- a run-level obstruction for the full Schinzel even-shift family;
- the concrete prime-pair specialization
  `p, 2 * p - 1 prime → φ(4 * p - 2) = φ(4 * p)`;
- the target-specific predicate `MinusPrimePairCovers n K p` and its finite obstruction API;
- the consequence that every run supplied by the positive Erdős 1004 assertion must avoid all such
  prime-pair coverage certificates;
- an eventual-filter theorem reducing a counterexample to one explicit local-coverage hypothesis;
- a concrete checked example proving that the run `[9, 12]` is not totient-distinct.

A later solver can use the general Schinzel theorem for additional even shifts, or use the
`MinusPrimePairCovers` interface to work solely on the remaining analytic question about local
coverage by the prime-pair collision locations. The arithmetic identities, interval bookkeeping,
and `Filter.atTop` contradiction need not be rebuilt.

This contribution does **not** claim an unconditional proof or refutation of Erdős 1004. In
particular, it does not assume or prove a maximal-gap or local-density theorem for primes `p` for
which `2 * p - 1` is prime. That unresolved requirement occurs only as an explicit hypothesis of the
conditional target theorem.

## Mathematical sources

- The pinned Formal Conjectures definition and statement for Erdős 1004:
  https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/1004.lean
- The Erdős Problems reference page:
  https://www.erdosproblems.com/1004
- Sidney W. Graham, Jeffrey J. Holt, and Carl Pomerance, *On the solutions to
  φ(n) = φ(n + k)*, Number Theory in Progress, Vol. 2, pp. 867–882. The construction attributed
  there to Schinzel states that for even `k`, primes `p, q` satisfying `q + 1 = 2p` and
  `pq ∤ k` give `φ(qk) = φ(qk + k)`; the Lean theorem uses the equivalent separate coprimality
  hypotheses needed by Mathlib:
  https://math.dartmouth.edu/~carlp/ghp.pdf
- Mathlib's pinned Euler-totient API, including `Nat.totient_mul`, `Nat.totient_prime`, and
  `Nat.totient_two_mul_of_even`:
  https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/Totient.lean

## Provenance and original delta

The Schinzel construction and its `k = 2` prime-pair specialization are attributed to the cited
literature. Their Lean proofs were reconstructed from Mathlib's multiplicativity and prime formulas.
The target-specific collision API, interval-coverage predicate, run obstruction, eventual-filter
handoff, normalized-target bridge, and checked use example are original Lean integration written for
this contribution.

ChatGPT assisted with proof development, testing, and documentation. The submitting author remains
responsible for the checked statements and this attribution. No code was copied from an earlier
Erdős 1004 contribution; the target index contained no published contribution when this package was
prepared. The artifact has no private data, sibling-file dependency, external executable, or
unpublished assumption.

## Minimal downstream uses

A future counterexample argument can prove the following analytic statement and apply
`not_normalized_target_of_eventual_minusPrimePair_coverage` directly:

```lean
∀ᶠ x : ℕ in Filter.atTop, ∀ n ≤ x, ∃ p,
  MinusPrimePairCovers n ⌊(Real.log (x : ℝ)) ^ c⌋₊ p
```

A future positive argument can apply
`assertion_implies_eventually_minusPrimePair_free_run` to extract the exact prime-pair avoidance
obligation forced by its claimed distinct-totient runs. For other even shifts, downstream work can
apply `totient_schinzel_even_shift` together with
`not_isDistinctTotientRun_of_schinzel_even_shift`.
