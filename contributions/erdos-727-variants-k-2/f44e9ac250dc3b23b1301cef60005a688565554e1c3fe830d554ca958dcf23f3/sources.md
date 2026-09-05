# Sources and scope

Four structural results for the k=2 case of Erdős 727:

1. factorial_square_iff_choose: reduces (n+2)!² | (2n)! to (n+1)²(n+2)² | C(2n,n).
2. central_choose_valuation_le_one: Kummer's theorem gives v_p(C(2n,n)) ≤ 1 when 2n < p².
3. prime_factor_square_bound: if n is a solution and p divides n+1 or n+2, then p² ≤ 2n.
4. arbitrarily_large_failures_in_every_residue: every residue class modulo a positive integer contains arbitrarily large non-solutions, via Dirichlet's theorem on primes in arithmetic progressions.

The fourth result rules out proving infinitude by exhibiting a fixed arithmetic progression consisting entirely of solutions, even after discarding an initial segment. It does not rule out infinitely many solutions within a residue class and does not prove or refute the full conjecture.

## References

- P. Erdős, R. L. Graham, I. Z. Ruzsa, E. G. Straus, [On the prime factors of the central binomial coefficient](https://users.renyi.hu/~p_erdos/1975-27.pdf), Math. Comp. 29 (1975), 83–92.
- [OEIS A389396](https://oeis.org/A389396), solutions for k=2; [OEIS A343507](https://oeis.org/A343507), smallest solution by k. These were consulted for context, not used as proof assumptions.
- Mathlib: padicValNat_choose (Kummer), Nat.forall_exists_prime_gt_and_modEq (Dirichlet), and standard factorial, divisibility, gcd and congruence lemmas.

Original Lean formalization developed with OpenAI Codex assistance. No claim of new versions of Kummer's or Dirichlet's theorems is made. The mathematical novelty of these structural consequences is not asserted here. No code was copied from a sibling contribution, and the proof imports only Mathlib.
