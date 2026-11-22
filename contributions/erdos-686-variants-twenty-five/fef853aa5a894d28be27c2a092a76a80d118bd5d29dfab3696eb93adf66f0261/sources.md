# Provenance and intended use

Original, self-contained Lean 4 formalizations advancing the `N = 25` variant of [Erdős Problem 686](https://www.erdosproblems.com/686) in [`erdos-686-variants-twenty-five-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample).

These two artifacts establish universal structural theorems valid for **all** large or even block lengths `k`:

1. **`even_k_leading_neg.lean` (`Contribution.Erdos686EvenKLeadingNegTwentyFive`)**:
   - Unconditional universal proof that for **every** integer `r ≥ 1` (`k = 2 * r`), the unique monic degree-`r` polynomial `Q_r` truncating the square root of `P_{2r}(X) = ∏_{j=1}^r (X^2 - (2j - 1)^2)` above degree `degR r := 2 * ((r - 1) / 2)` satisfies `(P_{2r} - Q_r^2).natDegree = degR r` and **`(P_{2r} - Q_r^2).leadingCoeff < 0`**.
   - Proof via an explicit upper half-plane square-root branch `F_uhp`, Cauchy–Goursat rectangle contour integration (`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`) on `[-R, R] × [0, R]` as `R → ∞` (`upperRect3_inv_z`, `remainder_asymptotic_O_inv_sq`, `contour_identity_im`), reflection symmetry (`g_int_neg`), the exact shift identity `P(x + 4) * (x - (2r - 3)) * (x - (2r - 1)) = P(x) * (x + 2r + 1) * (x + 2r + 3)` (`P_even_real_shift4_id`), and alternating-sum positivity (`alt_sum_pos`, `integral_g_int_pos`).
   - Exports `exists_unique_square_root_truncation`, `even_k_remainder_coeff_neg_real`, `even_k_remainder_natDegree_eq_real`, `even_k_remainder_leadingCoeff_neg_real`, `even_k_remainder_leadingCoeff_neg_rat_of_spec`, `even_k_remainder_natDegree_eq_rat`, and `even_k_remainder_leadingCoeff_neg_rat`.

2. **`super_quadratic_bound.lean` (`Contribution.Erdos686SuperQuadraticBoundTwentyFive`)**:
   - Unconditional explicit `Ω(k^2 log₂ k)` lower bound on `n` for **all** `k ≥ 11` solving `∏_{i=1}^k (m + i) = 25 * ∏_{i=1}^k (n + i)` (`m ≥ n + k`): `super_quadratic_bound_master` proves `k ^ 2 * Nat.log 2 k < 32 * n + 10 * k ^ 2 + 24 * k`, together with explicit linear-constant corollaries `super_quadratic_bound_k_ge_4096` (`< 384 * n`), `super_quadratic_bound_k_ge_8192` (`< 192 * n`), and `super_quadratic_bound_k_ge_2_pow_21` (`< 64 * n`).
   - Combines standalone general bounds (`ratio_upper_pow_nat`, `prime_upper_bound`), Erdős's prime-removal divisibility theorem (`erdos_prime_removal_dvd_factorial`, `prime_count_gt_half_k`), the sharp binomial gap bound `k * (m - n) < 4 * (n + k)` for `k ≥ 11` (`twentyfive_mul_pow_le_add_four_pow`, `gap_upper_bound_sharp`), and Chebyshev's primorial bound `primorial X ≤ 4 ^ X` (`primorial_le_four_pow`) after splitting prime factors at `k / 4`.

## Lineage, external sources, and novelty boundary

- Problem statement and classical prime-removal technique: [Erdős Problem 686](https://www.erdosproblems.com/686) (Erdős, *Some unconventional problems in number theory*, Acta Math. Acad. Sci. Hungar. 1979, 71–80).
- The analytic proof of `lc(P_{2r} - Q_r^2) < 0` uses standard contour integration of the exterior square-root branch of `∏_{j=1}^r (z^2 - (2j - 1)^2)` along the branch cuts `[-2r + 1, 2r - 1]`.
- Checked existing published contributions on `main` under `contributions/erdos-686-variants-twenty-five/`:
  - [`e1fb33970c1f...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/e1fb33970c1f18dde8fb7d314a9fc2344ec6ad84a7009552171c99e3e8b37f38) (`k = 2, 4`),
  - [`73960d1dcffd...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/73960d1dcffd211bfc8aefc30cb90554345de31430aff9a7bd42713f7c69df31) (`k = 8, 12`),
  - [`13a0386bac98...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/13a0386bac98d3986cbfeb59c11011589b7add613d108eb802201d61d9b91f48) (`k = 10`).
  Both files here are new, 100% self-contained (`parents: []`), depend only on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard axioms `[propext, Classical.choice, Quot.sound]`, and compile independently well below `--memory=8192`.
