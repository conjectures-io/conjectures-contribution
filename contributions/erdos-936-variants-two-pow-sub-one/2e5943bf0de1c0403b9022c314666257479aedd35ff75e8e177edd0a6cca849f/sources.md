# Sources and provenance

## Declared target

- Target slug: `erdos-936-variants-two-pow-sub-one`
- Proposed kind/mode: `partial-proof` / `formalized`
- Proposed title: `Erdős 936 sub-one: prime-square residue sieves modulo 60`
- Parents: `c03f9833c590b6a8994f9b396b3846dddeeb002096199112c54dab8c667852df` (cross-target semantic predecessor; mandatory)
- Reward target: `fc-target:Erdos936.erdos_936.variants.two_pow_sub_one`
- Formal Conjectures source: `FormalConjectures/ErdosProblems/936.lean` at commit
  `379fc0298dc146df549e7061c3ede0353a5bb51f`
- Exact source statement:

  ```lean
  theorem erdos_936.variants.two_pow_sub_one :
     answer(sorry) ↔ EventuallyNotPowerful (2 ^ · - 1) := by
    sorry
  ```

- Generated formalized task type: `True ↔ Erdos936.EventuallyNotPowerful fun x => 2 ^ x - 1`
- Problem reference: <https://www.erdosproblems.com/936>

## Mathematical and library sources

- The mathematical argument is the elementary prime-square obstruction: if a prime `p`
  divides `m` but `p ^ 2` does not divide `m`, then `m` is not powerful.
- The residue calculations use the cycles of `2` modulo `9` and `25`.
- `Nat.Full`, `Nat.Powerful`, and `Nat.mem_primeFactors` come from the pinned Formal
  Conjectures/Mathlib environment, in particular
  `FormalConjecturesForMathlib/Data/Nat/Full.lean`.
- That pinned file already proves `Nat.not_full_of_prime_mod_prime_sq`, which
  applies when the value is congruent to exactly `p` modulo `p^(k+1)`. The
  general obstruction here is not claimed as a wholly new idea: it exposes the
  more flexible hypotheses `p ∣ m` and `p^k ∤ m`. The sub-one residue values
  modulo `9` and `25` are often non-`p` multiples of `p`, so the exact-`p`
  predecessor does not directly cover the six families packaged here.
- No proof text was copied from another contribution. The pinned contribution index showed
  zero prior contributions for this target when checked at `2026-09-02T22:38:02Z`.

## Existing contribution lineage

The published Erdős 364 contribution
[`c03f9833c590b6a8994f9b396b3846dddeeb002096199112c54dab8c667852df`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-364/c03f9833c590b6a8994f9b396b3846dddeeb002096199112c54dab8c667852df)
already exports
`Contribution.Erdos364Congruence.not_powerful_of_dvd_of_not_sq_dvd`,
which is semantically the same prime-square obstruction as this draft's
`not_powerful_of_prime_dvd_not_sq_dvd` (its explicit `n ≠ 0` assumption
follows here from the non-square-divisibility hypothesis). It is therefore an
intended parent even though it belongs to another target.

The general obstruction is repeated only so this target artifact elaborates
independently, and **no recognition or credit is claimed for it**. The marginal
claim is restricted to the six sub-one residue families, their arbitrary-`n`
interfaces, the exact remaining-class reduction, and the infinitude theorem.

## Authorship disclosure

The Lean formalization and its documentation were developed for this local draft with
OpenAI Codex assistance. The eventual signer must inspect the statements, proof scope,
provenance, and submission metadata before publishing. This draft claims only the checked
partial sieve described in `READINESS.md`.

The add-one and sub-one variants were developed as a disclosed paired investigation, but
they are distinct reward targets and prove different residue families. Both scripts repeat
the two elementary `Nat.Full` obstruction lemmas because the contribution policy requires
each Lean artifact to elaborate independently; no separate recognition is claimed for that
duplicated support code.
