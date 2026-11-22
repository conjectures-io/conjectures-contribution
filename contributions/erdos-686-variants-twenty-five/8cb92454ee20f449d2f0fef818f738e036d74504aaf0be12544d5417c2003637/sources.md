# Provenance and intended use

Original Lean 4 formalizations excluding multiplier `25` at block lengths `k = 6`, `k = 14`, and `k = 16` in [Erdős Problem 686](https://www.erdosproblems.com/686), targeting the rational-product conjecture in [`erdos-686-variants-twenty-five-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample).

Each file (`k6.lean`, `k14.lean`, `k16.lean`) elaborates independently and proves the full unconditional exclusion for **all** `m, n : ℕ` (even without the disjointness hypothesis `m ≥ n + k`), exposing both natural-product statements (`length_six`, `length_fourteen`, `length_sixteen`, `erdos686_n25_k*_Icc`, `erdos686_n25_k*_range`) and the exact rational-quotient interfaces matching `FormalConjectures.ErdosProblems.«686»` (`no_ratio_twenty_five_six`, `no_ratio_twenty_five_fourteen`, `no_ratio_twenty_five_sixteen`, and `no_sol_twenty_five_*`). A future counterexample proof of `¬ Erdos686.erdos_686.variants.twenty_five` can import these files to discharge the `k = 6`, `k = 14`, and `k = 16` cases directly.

## Mathematical arguments

All three proofs rewrite `2^k * ∏_{i=1}^k (m + i) = P_k(2m + k + 1)` via the midpoint substitution `u = 2m + k + 1`, `v = 2n + k + 1` where `P_{2r}(x) = ∏_{j=1}^r (x^2 - (2j-1)^2)`, and use scaled polynomial square-completion together with Taylor-shifted positivity identities verified by `ring` and `positivity`, plus kernel-checked finite bracketing certificates via `decide +kernel`:

1. **`k = 6` (`Contribution.Erdos686SixTwentyFive` in `k6.lean`)**:
   Uses `4 * P_6(x) = (2x^3 - 35x)^2 - (189x^2 + 900)`. Setting `Q_6(x) = 2x^3 - 35x` (always odd for odd `x`) forces `d = (5 Q_6(v) - Q_6(u)) / 2 ≥ 1`, which leads to `20 Q_6(v) + 24 R_6(v) - 4 < 0`, contradicting positivity for `n ≥ 54` (`v ≥ 115`). The remaining `0 ≤ n ≤ 53` are excluded by kernel-checked bracketing (`base6_ok`).

2. **`k = 14` (`Contribution.Erdos686FourteenTwentyFive` in `k14.lean`)**:
   Uses `256 * P_14(x) = Q_14(x)^2 + R_14(x)` with homogenized integer polynomials `P14Z_hom`, `Q14Z_hom`, `R14Z_hom` so all monotonicity and pinching estimates remain over `ℤ`. For `n ≥ 9883` (`v ≥ 19779`), quadratic pinching on `d = (5 Q_14(v) - Q_14(u)) / 2` restricts `1 ≤ d ≤ 5000`, pinches `12584989/10^7 < u/v < 12584990/10^7`, and traps odd `v` into an explicit integer window `[v_lo, v_hi]` per `d`. Every window for `1 ≤ d ≤ 5000` and the base range `0 ≤ n ≤ 9882` are discharged by kernel-checked bracketing certificates.

3. **`k = 16` (`Contribution.Erdos686SixteenTwentyFive` in `k16.lean`)**:
   Uses the degree-8 substitution `X = x^2` with `P_16(x) = Q_8(X)^2 + R_6(X)` and homogenized `Q8Z_hom`, `R6Z_hom`. For `n ≥ 1089` (`v ≥ 2193`, `V ≥ 4809249`), parity-free `d = 5 Q_8(V) - Q_8(U)` satisfies `1 ≤ d ≤ 1069`, pinches `149534/10^5 < U/V < 149535/10^5`, and restricts odd `v` to a tiny quadratic window `V_lo < v^2 < V_hi` per `d`. All windows for `1 ≤ d ≤ 1069` and the base range `0 ≤ n ≤ 1088` are discharged by kernel-checked bracketing certificates.

## Lineage, external sources, and novelty boundary

- The general even-length midpoint expansion and square-completion strategy originates in public discussion of Erdős #686 on [erdosproblems.com](https://www.erdosproblems.com/686), notably Vjeko Kovač's length-6 comment and [IRAMBONA's post 9291](https://www.erdosproblems.com/forum/thread/686#post-9291). We claim no priority for the general method; the contribution here is the self-contained Lean 4 formalization of the `k = 6`, `k = 14`, and `k = 16` exclusions with homogenized integer pinching lemmas and kernel-verified certificates.
- Checked existing published contributions under `contributions/erdos-686-variants-twenty-five/`:
  - [`e1fb33970c1f...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/e1fb33970c1f18dde8fb7d314a9fc2344ec6ad84a7009552171c99e3e8b37f38) (`k = 2, 4`),
  - [`73960d1dcffd...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/73960d1dcffd211bfc8aefc30cb90554345de31430aff9a7bd42713f7c69df31) (`k = 8, 12`),
  - [`13a0386bac98...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/13a0386bac98d3986cbfeb59c11011589b7add613d108eb802201d61d9b91f48) (`k = 10`).
  None of `k = 6`, `k = 14`, or `k = 16` is published in `contributions/erdos-686-variants-twenty-five/`. Published records also note unmerged [open PR #141](https://github.com/conjectures-io/conjectures-contribution/pull/141) addressing `k = 6` among other helpers; our Lean files were developed independently prior to cloning this repository and import no sibling or prior contribution (`parents: []`).
- Symbolic polynomial identities and finite bounds were explored with Python and SymPy, which are not proof premises. All Lean theorems rely exclusively on [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard axioms `[propext, Classical.choice, Quot.sound]` with zero `sorry` or `native_decide`.
