# Sources and intended use

This contribution addresses [Erdős problem 1094](https://www.erdosproblems.com/1094) and its
exact [Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/1094.lean).

The quotient-transfer idea is attributed to P. Erdős, C. B. Lacampagne, and J. L. Selfridge,
“Estimates of the least prime factor of a binomial coefficient,” *Mathematics of Computation*
61 (1993), 215–224, [DOI 10.1090/S0025-5718-1993-1199990-6](https://doi.org/10.1090/S0025-5718-1993-1199990-6).
`Quotient.quotient_transfer_of_large_minFac` is a target-facing Lean formalization of this known
descent: an exceptional pair forces `n / k` to divide a smaller binomial product.

`Compression.whole_multiplicand_compression` is the subsequent checked strengthening developed in
our investigation. Given the quotient-supported divisor and the absence of small prime divisors,
it forces the complete multiplicand `d*k`, rather than only `d`, to divide `lcm(1,…,k)`. This
reduces the remaining finiteness problem to an explicit lcm-compressed family.

The Lean integration and compression argument were developed in a private Daryxx investigation
with [OpenAI Codex](https://openai.com/codex/) assistance. No code was copied from another
contribution; the signer takes responsibility for the submitted proofs and provenance.
