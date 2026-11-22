# Provenance and intended use

Original, standalone Lean 4 formalizations advancing the `N = 25` variant of [Erdős Problem 686](https://www.erdosproblems.com/686) in [`erdos-686-variants-twenty-five-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample).

Together, these five self-contained artifacts provide:
1. Universal structural bounds (`general_bounds.lean`), Erdős's combinatorial prime-removal theorem (`prime_removal.lean`), and a reusable midpoint / square-completion / `d`-pinching master framework (`general_even_k.lean`) valid for arbitrary block length `k ≥ 2` or `k = 2 * r`.
2. Full unconditional length-18 and length-20 exclusions (`k18.lean`, `k20.lean`) for **all** `m, n : ℕ`, with both natural-product statements (`no_sol_twenty_five_*`, `length_*`) and exact rational-quotient bridges matching `Erdos686.erdos_686.variants.twenty_five` (`no_ratio_twenty_five_*`, `erdos_686_variants_twenty_five_k*_bridge`).

Every `.lean` file elaborates independently using only targeted Mathlib imports (peak RSS well below `--memory=8192`), zero `sorry`, zero `native_decide`, and only `[propext, Classical.choice, Quot.sound]`.

## File-by-file mathematical arguments

1. **`general_bounds.lean` (`Contribution.Erdos686GeneralBoundsTwentyFive`)**:
   - Exact ratio sandwich for any solution `(m, n, k)` (`k ≥ 2`, `n < m`): `(m + k)^k < 25 * (n + k)^k` and `25 * (n + 1)^k < (m + 1)^k` (`ratio_upper_pow_nat`, `ratio_lower_pow_nat`, `ratio_sandwich_rat`).
   - Explicit quadratic lower bounds on `n` in terms of `k` via binomial truncation (`gap_upper_bound`, `quadratic_lower_bound`, `quadratic_lower_bound_k_ge_8`, `quadratic_lower_bound_k_ge_16`).
   - Prime-divisor transfer (`prime_dvd_transfer`), block uniqueness (`prime_unique_in_block`), upper bound `p ≤ (m - n) + k - 1` for primes `p ≠ 5` (`prime_upper_bound`), and exact 5-adic shift `padicValNat 5 (∏_{i=1}^k (m + i)) = 2 + padicValNat 5 (∏_{i=1}^k (n + i))` (`padicValNat_five_shift`).

2. **`prime_removal.lean` (`Contribution.Erdos686PrimeRemovalTwentyFive`)**:
   - Standalone proof of Erdős's prime-removal divisibility lemma (`erdos_prime_removal_dvd_factorial`): choosing one maximizing index per prime divisor in `P = (∏_{i=1}^k (m + i)).primeFactors` yields a surviving subset `S ⊆ Finset.Icc 1 k` with `k ≤ S.card + P.card` whose product divides `(k - 1)!`.
   - Master super-quadratic / prime-count inequalities (`erdos_prime_removal_master_bound`, `prime_count_ratio_lower_bound`, `prime_count_gt_third_k`: `51 ≤ k → k < 3 * P.card`), plus an elementary binomial proof of `(k + 1)^k ≥ 7 * (k - 1)^k` for `k ≥ 4` yielding `prime_count_gt_half_k` (`11 ≤ k → k < 2 * P.card`).

3. **`general_even_k.lean` (`Contribution.Erdos686GeneralEvenKTwentyFive`)**:
   - Unified symmetric midpoint identity (`midpoint_prod_general`, `even_k_iff_P_even`): `2^(2r) * ∏_{i=1}^{2r} (m + i) = P_even r (2m + 2r + 1)` where `P_even r x = ∏_{j=1}^r (x^2 - (2j - 1)^2)`.
   - General positivity, strict monotonicity (`P_even_pos`, `P_even_strictMono`), odd-parity congruence (`even_k_gap_pos`, `even_k_odd_parity_step`), Level-1 square-completion bound (`even_k_square_completion_bound`), Level-2 `d`-pinching reduction (`even_k_d_pinching_step`, `even_k_pinched_window`, `even_k_finite_reduction`), and an end-to-end instantiation (`k4_excluded_via_master`).

4. **`k18.lean` (`Contribution.Erdos686EighteenTwentyFive`)**:
   - Proves `16384 * P_18(x) = Q_18(x)^2 + R_18(x)` (`S = 128`) and modular divisibility `162 ∣ 5 * Q_18(v) - Q_18(u)` for odd `u, v`.
   - Combines 4-zone `d`-pinching (`Base`, `Zone 2`, `Zone 1B`, `Zone 1A`), Taylor-shift positivity (`Q18_s10`, `negR18_s10`), and kernel-verified bracketing (`cert18_ok` via `decide +kernel`), plus overlapping monotonicity (`11^18 < 10^18 * 25`), to prove `no_sol_twenty_five_eighteen_Icc`, `no_sol_twenty_five_eighteen`, `length_eighteen`, `no_ratio_twenty_five_eighteen`, and `erdos_686_variants_twenty_five_k18_bridge`.

5. **`k20.lean` (`Contribution.Erdos686TwentyTwentyFive`)**:
   - Proves exact degree-10 square completion `P_20(x) = Q_20(x)^2 + R_20(x)` (`S = 1`) and modular congruence `3200 ∣ Q_20(2k + 1)` (`Q20Z_3200_dvd`).
   - Combines Taylor-shift positivity above `n = 25000` (`asymp20_excl`), kernel-verified bracketing over `0 ≤ n < 25000` (`base20_ok` via `decide +kernel`), and overlapping monotonicity (`11^20 < 10^20 * 25`), to prove `no_sol_twenty_five_twenty_Icc`, `no_sol_twenty_five_twenty`, `length_twenty`, `no_ratio_twenty_five_twenty`, and `erdos_686_variants_twenty_five_k20_bridge`.

## Lineage, external sources, and novelty boundary

- Problem statement and historical context: [Erdős Problem 686](https://www.erdosproblems.com/686) (Erdős, *Some unconventional problems in number theory*, Acta Math. Acad. Sci. Hungar. 1979, 71–80).
- The prime-removal divisibility argument adapts Erdős's classical binomial/factorial factor-bounding technique to `∏ (m + i) = 25 * ∏ (n + i)` in elementary Finset arithmetic.
- Checked existing published contributions on `main` under `contributions/erdos-686-variants-twenty-five/`:
  - [`e1fb33970c1f...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/e1fb33970c1f18dde8fb7d314a9fc2344ec6ad84a7009552171c99e3e8b37f38) (`k = 2, 4`),
  - [`73960d1dcffd...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/73960d1dcffd211bfc8aefc30cb90554345de31430aff9a7bd42713f7c69df31) (`k = 8, 12`),
  - [`13a0386bac98...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/13a0386bac98d3986cbfeb59c11011589b7add613d108eb802201d61d9b91f48) (`k = 10`).
  None of `general_bounds.lean`, `prime_removal.lean`, `general_even_k.lean`, `k18.lean`, or `k20.lean` is published on `main`, and each file is self-contained (`parents: []`).
- Offline Python/SymPy calculations explored polynomial square completions and bracketing intervals; neither is a proof dependency. All Lean proofs depend solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard axioms `[propext, Classical.choice, Quot.sound]`.
