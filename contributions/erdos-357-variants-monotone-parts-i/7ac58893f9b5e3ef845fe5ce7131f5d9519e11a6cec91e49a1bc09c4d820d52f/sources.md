# Sources and scope

Original Lean formalization developed with OpenAI Codex assistance. No claim of new mathematics or a full solution is made.

The source definitions are from [FormalConjectures, Erdős 357](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/357.lean). The proof shows that HasDistinctSums implies injectivity using singleton sums; monotonicity then implies strict monotonicity, establishing h(n) = f(n).

No external mathematical proof is used beyond those definitions and standard Mathlib order/finite-set facts. The observation is elementary. This contribution reduces the monotone variant to the strict-monotone problem; it does not prove the requested little-o bound. The proof uses neither the unproved research declarations in the imported module nor sibling contribution files.
