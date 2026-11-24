# Provenance and intended use

Original, standalone Lean 4 formalizations advancing [Erdős Problem 672](https://www.erdosproblems.com/672) across both [`erdos-672-formalized`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-672-formalized) and [`erdos-672-counterexample`](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-672-counterexample).

Together, these four self-contained artifacts discharge the `sorry` variants `Erdos672.erdos_672.variants.euler` (`k = 4, l = 2`), the `Erdos672With 5 2` and `Erdos672With 3 4` conjuncts of `Erdos672.erdos_672.variants.oblath`, and their full infinite exponent families `l = 2 * m` (`k = 4, 5`) and `l = 4 * m` (`k = 3`), while supplying the general coprime arithmetic-progression `p`-adic factor-splitting reduction for arbitrary `(k, l)`. Each `.lean` file uses targeted Mathlib imports only, compiles independently below the memory and heartbeat caps, and relies solely on the three standard axioms `[propext, Classical.choice, Quot.sound]`.

## File-by-file mathematical summary

1. **`ap_reduction.lean` (`Contribution.Erdos672APReduction`)**:
   - Proves pairwise GCD divisibility (`ap_pairwise_gcd_dvd`: `Nat.gcd (n + i * d) (n + j * d) ∣ j - i` for `Nat.Coprime n d` and `i < j`), unique-term prime divisibility for `p ≥ k` (`ap_prime_unique_term`), exact `p`-adic exponent divisibility (`ap_padicValNat_dvd_of_prod_eq_pow`: `l ∣ padicValNat p (n + i * d)`), and canonical factor splitting (`ap_canonical_factor_splitting`: `n + i * d = a * x ^ l` with all prime factors of `a` strictly `< k` and `padicValNat p a < l`).
   - Bridges directly to `Set.IsAPOfLengthWith` and `Erdos672.Erdos672With` via `erdos_672_reduction_bridge` and the exponent-monotonicity principle `erdos_672_pow_mul_monotone`, narrowing either proof search or counterexample search for any `(k, l)`.

2. **`euler_k4_l2.lean` (`Contribution.Erdos672EulerK4L2`)**:
   - Proves Fermat-style infinite descent on simultaneous Pythagorean equations (`no_sim_pyth`: no positive coprime integers satisfy `x^2 + y^2 = z^2` and `x^2 + 4 * y^2 = w^2`), the biquadratic corollary `no_biquad_sub` (`p^4 + q^4 = c^2 + p^2 * q^2`), and Euler's four-squares-in-AP impossibility theorem `no_four_sq_ap`.
   - Deduces `no_prod_four_ap_sq` (`n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2`) and exports `euler_k4_l2_bridge` (`Erdos672.Erdos672With 4 2`, discharging `Erdos672.erdos_672.variants.euler`) and `euler_k4_even_l_bridge` (`Erdos672.Erdos672With 4 (2 * m)` for `0 < m`).

3. **`oblath_k5_l2.lean` (`Contribution.Erdos672OblathK5L2`)**:
   - Uses `ap5_sq_splitting` (`n + i * d = a_i * x_i^2` with `a_i ∈ {1, 2, 3, 6}`) together with a kernel-decidable mod-`8` and mod-`9` congruence filter (`checkAll5_true`) reducing all `4^5 = 1,024` tuples to three survivors `(1, 1, 1, 1, 1)`, `(6, 1, 2, 3, 1)`, and `(1, 3, 2, 1, 6)`.
   - Closes each survivor by embedded four-term square-product exclusion, proving `no_prod_five_ap_sq` and exporting `oblath_k5_l2_bridge` (`Erdos672.Erdos672With 5 2`) and `oblath_k5_even_l_bridge` (`Erdos672.Erdos672With 5 (2 * m)` for `0 < m`).

4. **`oblath_k3_l4.lean` (`Contribution.Erdos672OblathK3L4`)**:
   - Proves Fermat descent on `V^4 + W^2 = U^4` (`no_fourth_sub_fourth_eq_sq`), deducing `no_odd_coprime_fourth_add_four_fourth` (`x^4 + 4 * z^4 = y^4`) and `no_three_fourth_ap` (`x_0^4 + x_2^4 = 2 * x_1^4`).
   - Combines canonical `{1, 2, 4, 8}` splitting (`ap3_fourth_splitting`) with a kernel-decidable mod-`16` filter (`checkAll3Fourths_true`) leaving only `(1, 1, 1)`, `(2, 1, 8)`, and `(8, 1, 2)` to prove `no_prod_three_ap_fourth`, `oblath_k3_l4_bridge` (`Erdos672.Erdos672With 3 4`), and `oblath_k3_mult4_l_bridge` (`Erdos672.Erdos672With 3 (4 * m)` for `0 < m`).

## Minimal Lean usage

A downstream proof importing `FormalConjectures.ErdosProblems.«672»` together with these declarations immediately obtains:

```lean
example : Erdos672.Erdos672With 4 2 := Contribution.Erdos672EulerK4L2.euler_k4_l2_bridge
example : Erdos672.Erdos672With 5 2 := Contribution.Erdos672OblathK5L2.oblath_k5_l2_bridge
example : Erdos672.Erdos672With 3 4 := Contribution.Erdos672OblathK3L4.oblath_k3_l4_bridge
```

## Lineage and external references

- Problem statement and history: [Erdős Problem 672](https://www.erdosproblems.com/672); L. Euler (impossibility of four squares in arithmetic progression); R. Obláth (1951), *Über das Produkt fünf aufeinander folgender Zahlen in einer arithmetischen Reihe*, Publicationes Mathematicae Debrecen 2, 222–229.
- Checked `main` at commit `d45062d` (`contrib ls contributions --target erdos-672`: `0` published contributions); therefore `parents` is `[]` and all declarations are original work under distinct `Contribution.Erdos672*` namespaces.
- Local Python experiments guided modular congruence table design (`mod 8`, `mod 9`, `mod 16`) and are not proof dependencies. All proofs rely strictly on pinned [Mathlib (`v4.33.1`)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and the three standard Lean axioms `[propext, Classical.choice, Quot.sound]`.
