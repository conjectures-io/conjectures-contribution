# Sources and scope

Original Lean formalization developed with OpenAI Codex assistance. No claim of new mathematics or a full solution is made.

Definitions: [FormalConjectures, Erdős 889](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/889.lean).

Original problem reference: P. Erdős and J. L. Selfridge, [Some problems on the prime factors of consecutive integers](https://users.renyi.hu/~p_erdos/1967-21.pdf), Illinois Journal of Mathematics 11 (1967), 428–430.

For a positive divisor p of n+k, the no-earlier-divisibility condition is equivalent to p>k. If p≤k, take i=k-p. Conversely, divisibility of both n+k and n+i forces p to divide the positive difference k-i<p, a contradiction. Applying this criterion to prime factors proves the cardinality identity for Erdos889.v.

This is an elementary reduction, not the conjectured divergence of the extremal count. No Lean proof was copied from another contribution, and no unproved research theorem in the imported module is used.
