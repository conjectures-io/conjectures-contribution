# Sources

## Target and statement

`FormalConjectures/ErdosProblems/9.lean` declares `erdos_9.variants.infinite`
(`Erdos9A.Infinite`) under `@[category research solved]` with a `sorry` proof. This
contribution supplies a checked proof of exactly that statement (restated under the
`Contribution` namespace). Background: https://www.erdosproblems.com/9.

## Mathematical content

Crocker-style construction (R. Crocker, On the sum of a prime and two powers of two,
Pacific J. Math. 36 (1971) 103-107): explicit witnesses `N k = w * (2^(2^(12k)) - 1) / G`
with `G = (2^1024 + 1) / 45592577` the F_10 cofactor and `w` an explicit 746-bit CRT
multiplier. If `N k = p + 2^a + 2^b` with `a ≠ b`, a Fermat number `F_(v2(a-b))` (or the
prime 45592577 at r = 10) divides `p`, excluded mod 16; if `a = b`, an explicit 21-prime
covering system mod 720 produces a small prime divisor of `p`, contradicting the size
bound. The covering design was validated numerically before formalization.

## Mathlib declarations used

Fermat-number and 2-adic valuation API (`Nat.factorization`, `padicValNat`), `Nat.ModEq`,
`ZMod` casts, `decide`-free `norm_num` arithmetic, `omega`. Self-contained on Mathlib plus
the pool module import. Axiom closure of the final theorem is exactly `propext`,
`Classical.choice`, `Quot.sound` on the pinned toolchain (Lean 4.27.0 / Mathlib `a3a10db0`).
