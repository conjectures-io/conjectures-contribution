# Provenance and intended use

Original, self-contained Lean 4 formalization advancing the `N = 25` variant of [Erdős Problem 686](https://www.erdosproblems.com/686) in [`erdos-686-variants-twenty-five-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample).

**`k24.lean` (`Contribution.Erdos686TwentyFourTwentyFive`)** unconditionally rules out block length `k = 24` for `N = 25`, discharging the `k = 24` case of `Erdos686.erdos_686.variants.twenty_five` (`¬ ∃ n, ∃ m ≥ n + 24, (25 : ℚ) = (∏ i ∈ Finset.Icc 1 24, (m + i)) / (∏ i ∈ Finset.Icc 1 24, (n + i))`):

- **Symmetric midpoint & exact integer square-completion (`S = 1`)**: Transforms `∏_{i=1}^{24} (m + i) = 25 * ∏_{i=1}^{24} (n + i)` into `P24Z u = 25 * P24Z v` in odd midpoint coordinates `u = 2*m + 25`, `v = 2*n + 25`, where `P24Z x = ∏_{j=1}^{12} (x^2 - (2j - 1)^2)`, and proves the exact polynomial identity `P24Z x = Q24Z x ^ 2 + R24Z x` (`deg Q24Z = 12`, `deg R24Z = 10`, `lc R24Z = -7057203580108800`).
- **Modular congruence (`21233664 ∣ 5 * Q24Z v - Q24Z u`)**: Proves `Q24Z (2*a + 1) ≡ 131072 (mod 262144)` across the 4 residue classes of `a % 4` (`Q24Z_2pow18_mod`), `81 ∣ Q24Z x` across the 3 residue classes of `x % 3` (`Q24Z_81_dvd`), and combines them via the Bézout identity `(-26) * 262144 + 84145 * 81 = 1` (`Q24Z_diff_21233664_dvd`), eliminating any need for `d`-pinching.
- **Level-1 asymptotic exclusion (`n ≥ 15000`)**: Establishes `5 * u < 6 * v` (`P24Z_hom65_gt`), `25 * R24Z v < R24Z u` (`negR24_s5_upper65`), and strict positivity of `21233664 * (10 * Q24Z v - 21233664) + 24 * R24Z v` (`thresh_24_pos`) by explicit positive Taylor expansions shifted to `v_0 = 30025` (`asymp24_excl`).
- **Finite kernel-checked exhaustion (`0 ≤ n ≤ 15000`)**: Excludes `1 ≤ n ≤ 15000` via `15` kernel-evaluated `1000`-blocks (`base24_ok : checkGrid stepBase24 1 1000 15 = true := by decide +kernel`), and excludes `n = 0` directly from `m ≥ 24` (`25 * P24 25 < P24 73 ≤ P24 (2 * m + 25)`), separating it cleanly from the overlapping identity `25! = 25 * 24!`.
- **Exported theorems**: `no_sol_twenty_five_twenty_four_Icc`, `no_sol_twenty_five_twenty_four`, `no_ratio_twenty_five_twenty_four`, and `erdos_686_variants_twenty_five_k24_bridge`.

## Lineage, external sources, and novelty boundary

- Problem statement and classical even-length square-completion method: [Erdős Problem 686](https://www.erdosproblems.com/686) (Erdős, *Some unconventional problems in number theory*, Acta Math. Acad. Sci. Hungar. 1979, 71–80).
- Checked existing published contributions on `main` under `contributions/erdos-686-variants-twenty-five/`:
  - [`e1fb33970c1f...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/e1fb33970c1f18dde8fb7d314a9fc2344ec6ad84a7009552171c99e3e8b37f38) (`k = 2, 4`),
  - [`73960d1dcffd...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/73960d1dcffd211bfc8aefc30cb90554345de31430aff9a7bd42713f7c69df31) (`k = 8, 12`),
  - [`13a0386bac98...`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-twenty-five/13a0386bac98d3986cbfeb59c11011589b7add613d108eb802201d61d9b91f48) (`k = 10`).
- `k24.lean` is completely self-contained (`parents: []`), depends only on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`, and compiles independently well below `--memory=8192`.
