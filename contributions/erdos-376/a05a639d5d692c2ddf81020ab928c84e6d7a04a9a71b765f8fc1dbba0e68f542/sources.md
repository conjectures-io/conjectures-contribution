# Sources and intended use

This contribution addresses [Erdős problem 376](https://www.erdosproblems.com/376) and its exact
[Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/376.lean).

The carry count uses Mathlib's formalization of Kummer's theorem,
[`Nat.Prime.emultiplicity_choose`](https://github.com/leanprover-community/mathlib4/blob/a3a10db0e9d66acbebf76c5e6a135066525ac900/Mathlib/Data/Nat/Choose/Factorization.lean).
`centralBinom_coprime_105_iff_no_carries` specializes it to the primes `3`, `5`, and `7`.
`digitGood357_implies_coprime_105` then proves that simultaneous digitwise smallness in those
three bases prevents every carry. The final two declarations let a later solver finish the
target from either infinitely many such values or an eventually positive checked counting
function with explicit witness semantics.

The specialization, prefix argument, and Lean integration were developed in a private Daryxx
investigation with [OpenAI Codex](https://openai.com/codex/) assistance. They were not copied
from another contribution; the signer takes responsibility for the submitted proof and
provenance.
