# Provenance and intended use

Original, standalone Lean 4 formalization unconditionally excluding multiplier `25` at block length `k = 3` in [Erdős Problem 686](https://www.erdosproblems.com/686), targeting the rational-product conjecture in [`erdos-686-variants-twenty-five-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample).

Unlike the even-length (`k = 2r`) square-completion exclusions already published for `k ∈ {2, 4, 8, 10, 12}`, the odd-length case `k = 3` leads to a genus-1 Thue / Mordell problem (`x^3 - x = 25 * (y^3 - y)`). The file `k3.lean` resolves `k = 3` **100% unconditionally inside the Lean 4 kernel** with zero `sorry`, zero `native_decide`, targeted Mathlib imports keeping elaboration under `--memory=8192`, and only `[propext, Classical.choice, Quot.sound]`.

Exported interfaces in `Contribution.Erdos686ThreeTwentyFive`:
- `no_k3_solution_y1_le_10_pow_276`: pure-integer convergent exclusion for `(n + 2) / gcd(m + 2, n + 2) ≤ 10 ^ 276`.
- `no_sol_twenty_five_three`: `¬ ∃ m n : ℕ, m ≥ n + 3 ∧ (m + 1) * (m + 2) * (m + 3) = 25 * ((n + 1) * (n + 2) * (n + 3))`.
- `no_sol_twenty_five_three_unrestricted` and `no_sol_twenty_five_three_Icc`: unrestricted exclusions for all `m, n : ℕ` (dropping `m ≥ n + 3`).
- `no_ratio_twenty_five_three` and `erdos_686_variants_twenty_five_k3_bridge`: exact rational-quotient interfaces matching the `k = 3` branch of `Erdos686.erdos_686.variants.twenty_five`.

## Mathematical arguments

1. **Thue–Mordell descent and mod-27 local filter (`Contribution.Erdos686ThreeTwentyFive.Reduction`)**:
   - Substituting `x = m + 2`, `y = n + 2` transforms `(m + 1)(m + 2)(m + 3) = 25 (n + 1)(n + 2)(n + 3)` into `x^3 - x = 25 (y^3 - y)`.
   - Extracting `D = gcd(x, y)`, `x = D * x1`, `y = D * y1` with `Nat.Coprime x1 y1` reduces any solution with `m ≥ n + 3` to the cubic Thue family `25 * y1^3 - x1^3 = d` where `d ∣ 15600` and `22 * y1 < d * D^2 < 24 * y1` (`k3_thue_reduction`).
   - Exact modular admissibility modulo `27` (`locallyAdmissible3_of_solution`, `locallyAdmissible3_filters_15600`) filters the `60` positive divisors of `15600` to `24` surviving values (`surv24`).
   - A kernel-verified cube-root check (`decide +kernel` in `low_y1_1_to_2000_ok` → `no_k3_solution_y1_le_2000`) eliminates all `y1 ≤ 2000` uniformly for arbitrary `D ≥ 1`, forcing `29 * y1 ≤ 10 * x1`.
2. **Pure-integer continued-fraction convergent chain (`y1 ≤ 10^276`)**:
   - Eight upper continued-fraction convergents of `25^(1/3)` (`idx = 8, 9, 14, 20, 24, 40, 74, 138`) close `2001 ≤ y1 ≤ 10^73` via elementary cross-multiplication lemmas (`upper_cubic_approx_excludes_window`).
   - Two additional convergents (`excl_conv_275` for `10^73 ≤ y1 ≤ 10^140` and `excl_conv_511` for `10^140 ≤ y1 ≤ (10^138)^2 = 10^276`) extend the exclusion continuously up to `y1 ≤ 10^276` (`no_k3_solution_y1_le_10_pow_276`).
3. **First-principles Padé / Euler-integral tail (`y1 > 10^276`, `Contribution.Erdos686ThreeTwentyFive.Pade`)**:
   - Constructs the Padé / hypergeometric approximants `(Ppoly n z, Qpoly n z)` to `(1 - z)^(1/3)` evaluated at the 21st convergent `(a21, b21) = (700728535, 239645788)` of `25^(1/3)` (`A0 = 5 * a1^3`, `B0 = b21^3`, `C0 = A0 - B0 = 402657`, `z = C0 / A0`).
   - Discrete Zeilberger creative telescoping (`Xtilde_rec`) proves the shared 3-term Gauss recurrence and non-vanishing Wronskian determinant (`Ppoly_Qpoly_det_ne_zero`), guaranteeing `(x1 * v_k - y1 * u_k) ≠ 0` for `k ∈ {n, n + 1}`.
   - Continuous creative telescoping and the Fundamental Theorem of Calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) establish the exact Euler integral representation and exponential remainder bound (`Erem_eq_Ppoly_sub_Qpoly`, `Erem_bounds`, `Ppoly_abs_le`).
   - Elementary 3-adic denominator clearing (`2 * padicValNat 3 n! ≤ n`) yields integer linear forms `(uSeq n, vSeq n)` with explicit constants `M0 = 48 * 10^7`, `M = 955 * 10^23`, `E0 = 702 / 10^14`, `E = 511 / 10^17`, satisfying `M * E^2 ≤ 1/400` and `4992 * M0 * E0^2 * M^2 * (1/400)^17 < 1`. This forces `n ≥ 17` and `|x1 * v_k - y1 * u_k| < 1` against `1 ≤ |x1 * v_k - y1 * u_k|` whenever `y1 > 10^276` (`pade_no_thue_solution_gt_10_pow_276`).

## Lineage, external sources, and novelty boundary

- Problem statement and context: [Erdős Problem 686](https://www.erdosproblems.com/686) (original formulation in Erdős, *Some unconventional problems in number theory*, Acta Math. Acad. Sci. Hungar. 1979, 71–80).
- Classical Thue–Siegel–Bennett Padé/hypergeometric method for effective rational approximation to cube roots is adapted from first principles directly into elementary Lean 4 real-analysis and 3-adic proofs (no Baker's theorem or transcendence results required).
- Checked existing published contributions on `main` under `contributions/erdos-686-variants-twenty-five/`:
  - [`e1fb33970c1f...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/e1fb33970c1f18dde8fb7d314a9fc2344ec6ad84a7009552171c99e3e8b37f38) (`k = 2, 4`),
  - [`73960d1dcffd...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/73960d1dcffd211bfc8aefc30cb90554345de31430aff9a7bd42713f7c69df31) (`k = 8, 12`),
  - [`13a0386bac98...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/13a0386bac98d3986cbfeb59c11011589b7add613d108eb802201d61d9b91f48) (`k = 10`).
  None covers `k = 3`, and `k3.lean` imports no sibling or prior contribution (`parents: []`).
- Continued-fraction convergents and Padé constants were discovered offline with Python and PARI/GP (neither is a proof dependency). All Lean proofs depend solely on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard axioms `[propext, Classical.choice, Quot.sound]`.
