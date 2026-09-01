# Sources

## Target and statements

`FormalConjectures/ErdosProblems/1209.lean` declares `erdos_1209.parts.i` and
`erdos_1209.parts.ii` under research-solved categories with `sorry` proofs. This
contribution proves exactly those statements (restated under the `Contribution`
namespace), both with `answer(False)`.

## Method

Diagonalization against an arbitrary candidate function f: by Dirichlet
(`Nat.forall_exists_prime_gt_and_eq_mod`) choose primes a_k ≡ −k (mod q_k) — modulus
q_k for parts.i, q_k² for parts.ii — with a_k exceeding max(a_(k−1), f k, q_k). Then
n = 0 gives all-prime (resp. squarefree, via `Prime.squarefree`) values, while any
n ≥ 1 fails at index k = n because q_n (resp. q_n²) properly divides n + a_n. So the
solution set is contained in {0}, refuting infinitude.

Both proofs were produced independently from the statements alone; the external
`formal_proof` link on the file's separate declaration `parts.iii.a` (another author's
public repository) was not consulted or adapted.

## Verification

Axiom closure exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned
toolchain (Lean 4.27.0 / Mathlib `a3a10db0`); no sorry/native_decide/set_option.
