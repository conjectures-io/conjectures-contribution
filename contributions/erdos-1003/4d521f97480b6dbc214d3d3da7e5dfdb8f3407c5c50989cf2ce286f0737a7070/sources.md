## Sources

* Problem statement: Erdős Problem 1003, https://www.erdosproblems.com/1003 — "Are there infinitely many solutions to φ(n) = φ(n+1)?"
* Formal target: `FormalConjectures/ErdosProblems/1003.lean` in the Formal Conjectures repository, https://github.com/google-deepmind/formal-conjectures — theorems `Erdos1003.erdos_1003`, `Erdos1003.erdos_1003.variants.Icc`, `Erdos1003.erdos_1003.variants.eps87`.
* `answer(..)` elaboration: `FormalConjecturesUtil/Answer.lean` in the same repository; under the default `google.answer := .alwaysTrue` setting `answer(sorry)` at `Prop` type elaborates to `True`, which is why the use sites are stated as `True ↔ …`. I re-read this file and re-checked the elaborated types with `#check @Erdos1003.erdos_1003` etc. (printed `True ↔ {n | n.totient = (n + 1).totient}.Infinite`).
* Solution data: the values 1, 3, 15, 104 below 106 are OEIS A001274 ("Numbers k such that φ(k) = φ(k+1)"), https://oeis.org/A001274 . They are not taken on trust: `filter_range_106` is an exhaustive kernel check over `Finset.range 106`.
* The witness 5186, 5187, 5188 with φ = 2592 is the smallest known triple for k = 2 (also visible in OEIS A001274 as consecutive terms); the factorisations 5186 = 2·2593, 5187 = 3·7·13·19, 5188 = 2²·1297 are verified inside the Lean proof, not assumed.
* Erdős, P., *Some problems and results in number theory*, Number theory and combinatorics, Japan 1984 (1985), 65–87 — source of the `Icc` variant (φ(n) = ⋯ = φ(n+k) presumably has infinitely many solutions for every k).
* Erdős, Pomerance, Sárközy, *On locally repeated values of certain arithmetic functions II*, Proc. Amer. Math. Soc. (1987), 1–7 — source of the `eps87` upper bound x/exp((log x)^{1/3}).
* Mathlib (pinned in this repo, Lean 4.27.0): `Mathlib/Data/Nat/Totient.lean` for `Nat.totient_le`, `Nat.totient_lt`, `Nat.totient_prime`, `Nat.totient_prime_pow`, `Nat.totient_mul`; `Nat.ordProj_mul_ordCompl_eq_self` and `Nat.coprime_ordCompl` for the 2-adic split; `tendsto_atTop_atTop_of_monotone` and `Set.Infinite.exists_subset_card_eq` for the counting equivalence. Novelty was checked by grepping `Mathlib/Data/Nat/Totient.lean` and every Mathlib file mentioning `totient`, and by running `exact?` in a clean Mathlib-only scope on `Even n → 2 * φ n ≤ n`, `φ n = φ (n+1) → 2 * φ n ≤ n + 1`, `4 ≤ n → φ n = φ (n+1) → ¬ n.Prime`, the chain reformulation, and the `Finset` description of the counted set — all five failed, so none of these is in Mathlib under another name.

## AI assistance

This contribution was produced with AI assistance (Anthropic Claude, running as an agent with a local Lean 4 / Mathlib checkout). The AI drafted the statements and proof scripts and iterated against the compiler; every declaration in the shipped file was compiled with `lake env lean` (zero errors, zero warnings) and every declaration's axiom set was checked with `#print axioms` in a scratch copy, printing exactly `[propext, Classical.choice, Quot.sound]` for all 16 named declarations. No proof was accepted without compiling. Nothing here is claimed to solve the problem.

## Note on this revision

This is a repair of an earlier version that used `set_option maxRecDepth 40000 in` to make a `decide` go through. The option is gone: the exhaustive search is now run by the kernel (`decide +kernel`), which is not subject to the elaborator's recursion limit and, as the axiom check confirms, adds no axiom and no additional trust (unlike `native_decide`, which is banned and is not used). Seven declarations flagged as inline-trivial in review were deleted outright, and the misleading claim that the `Icc` variant is progress towards the reward theorem was replaced by an explicit statement that the implication goes the wrong way.

## Originality

All Lean statements and proofs in this file are original work produced for this submission and were not copied from any existing formalisation (Mathlib, FormalConjectures, another contribution, or elsewhere). Mathlib lemmas are used only as named dependencies. The docstrings and this file were corrected after adversarial review.
