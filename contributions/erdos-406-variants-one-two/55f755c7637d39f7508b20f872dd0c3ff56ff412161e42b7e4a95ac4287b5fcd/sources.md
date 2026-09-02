## Sources

- Target statement: `FormalConjectures/ErdosProblems/406.lean` in the Formal Conjectures repository — https://github.com/google-deepmind/formal-conjectures
- Problem statement and background: https://www.erdosproblems.com/406
- Mathlib 4 (pinned in this repo's lakefile), used for every imported lemma — https://github.com/leanprover-community/mathlib4
  - `Nat.getD_digits`, `Nat.lt_digits_length_iff`, `Nat.digits_lt_base`, `Nat.digits_def'` — Mathlib/Data/Nat/Digits/*
  - `Nat.pow_totient_mod` — Mathlib/NumberTheory/PowModTotient.lean (`x ^ k % n = x ^ (k % Nat.totient n) % n` for `1 < n`, `x` coprime to `n`); the Euler periodicity of `2 ^ k mod 3 ^ m` is taken directly from this lemma rather than re-derived. This replaces the earlier `two_pow_mod_pow_three`, which reviewer feedback correctly identified as a re-derivation of existing Mathlib work; it is now a single `rw` inlined at its only use site in `zero_mem_digits_two_pow_of_check`.
  - `Nat.totient_prime_pow`, `Nat.prime_three`, `Nat.Coprime.pow_right`, `Nat.one_lt_pow` — Mathlib/NumberTheory/Totient and Mathlib/Algebra/Order/*
- Novelty checks: `exact?` was run on `mem_digits_iff`, `digits_subset_one_two_iff_zero_notMem`, `digit_eq_of_mod_pow_eq`, `digits_subset_one_two_succ_iff`, `digits_div_pow_subset` and `digits_three_mul_add_subset` (all fail), and the Mathlib source tree was grepped for `mem_digits`, `digits_subset` and `digit_eq_of_mod` (no lemma of this shape; the only `mem_digits` hit is `Nat.lt_of_mem_digitsAppend`, which is unrelated). `mem_digits_iff` is not in Mathlib under any name I could find.
- The survivor counts asserted by `card_sieve_survivors` (2, 4, 8, 16, 32 for m = 1..5) were first found by an independent Python brute force over the residue classes, then proved in Lean by `decide` — the Lean `decide` is the authority, the Python was only a guide.

## AI assistance

This file was written with AI assistance (Anthropic Claude, acting as a Lean 4/Mathlib agent) under human direction, and repaired by the same means after a reviewer verdict of FIX. Every declaration was elaborated by `lake env lean` with zero errors and zero warnings, and every named declaration's axiom dependencies were checked with `#print axioms` to be a subset of `[propext, Classical.choice, Quot.sound]`. No `sorry`, `axiom`, `native_decide` or trust-raising `set_option` appears anywhere in the file.

## Originality
All Lean statements and proofs in this file are original work produced for this submission and were not copied from any source (Mathlib, FormalConjectures, another contribution, or elsewhere). The docstring was corrected after review to state that the membership half of the target is already closed by `by norm_num`; the contribution's value is for symbolic exponents.
