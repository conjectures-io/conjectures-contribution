# Sources for `erdos-770-parts-i`

- Erdős Problem 770 problem statement and background (`h(n) = n + 1 ↔ Prime (n + 1)`, unboundedness of `h(n)` on odd `n`): [erdosproblems.com/770](https://www.erdosproblems.com/770)
- Pinned `FormalConjectures` specification: [FormalConjectures/ErdosProblems/770.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/770.lean)
- Polynomial root count bound (`Polynomial.card_le_degree_of_subset_roots`) and Fermat's Little Theorem (`ZMod.pow_card_sub_one_eq_one`) in Mathlib: [mathlib4/Mathlib/Algebra/Polynomial/Roots.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Polynomial/Roots.lean)
- Dirichlet's theorem on primes in arithmetic progressions (`Nat.forall_exists_prime_gt_and_modEq`), CRT (`Nat.chineseRemainderOfList`), and Quadratic Reciprocity (`legendreSym`) in Mathlib: [mathlib4/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean)
