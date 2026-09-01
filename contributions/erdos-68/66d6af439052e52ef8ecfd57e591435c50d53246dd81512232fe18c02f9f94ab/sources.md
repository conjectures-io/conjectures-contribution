# Sources and intended use

This contribution addresses [Erdős problem 68](https://www.erdosproblems.com/68) and the exact
Lean target in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/68.lean).

`irrational_of_factorial_positive_side` turns two explicit facts about a sequence of partial
sums into irrationality: a positive factorial-scaled tail below `1/2`, and arbitrarily late
visits of the scaled partial sums to the lower half of a unit interval. A solver can instantiate
`x` with the Erdős 68 series and `s` with its finite partial sums, leaving only the arithmetic
positive-side recurrence. `irrational_of_scaled_factorial_positive_side` permits one fixed
natural multiplier, including a fixed dyadic shift.

The argument and Lean formalization were developed in a private Daryxx investigation with
[OpenAI Codex](https://openai.com/codex/) assistance. They were not copied from another
contribution; the signer takes responsibility for the proof and its provenance.
