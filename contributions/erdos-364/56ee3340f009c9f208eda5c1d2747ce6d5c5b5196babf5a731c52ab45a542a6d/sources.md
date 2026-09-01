# Sources

## Target

- `Erdos364.erdos_364` in `FormalConjectures/ErdosProblems/364.lean`
  (`¬ ∃ n, Powerful n ∧ Powerful (n+1) ∧ Powerful (n+2)`), pinned via the `conjectures`
  submodule. Background: <https://www.erdosproblems.com/364>.

## Relation to the two existing contributions on this target

Checked `contributions/erdos-364/index.json` before writing. The published work is:

- `c03f9833…` — the congruence layer: `triple_mod_4`, `triple_mod_36`, and
  `survivors_infinite` (the surviving classes `n ≡ 7, 27, 35 mod 36` are infinite, so the
  sieve cannot finish). Its `sources.md` says to "spend effort elsewhere (size/abc
  arguments)".
- `ab10a4a6…` — the Diophantine layer: `Powerful.mul`, `sq_sub_one_powerful`
  (`(n+1)² − 1` is powerful), `powerful_sq`, `powerful_prime_pow`, and two near-misses.
  Its module docstring is titled "the abc connection".

**Both point at the abc/size obstruction; neither formalises a radical bound.** No published
declaration on this target mentions `rad`, `radical`, or a product over `primeFactors`. That
gap is what this contribution fills, so it is disjoint from both parents and is filed with
no `parents` link (it uses neither).

## What is proved here

- `rad` — the radical (squarefree kernel) `∏ p ∈ n.primeFactors, p`, with `rad_ne_zero`.
- `prod_sq_dvd_of_subset` — for powerful `n`, *every* sub-product `∏_{p ∈ S} p²` over
  `S ⊆ n.primeFactors` divides `n`. Proved by induction on `S` using
  `Nat.Coprime.mul_dvd_of_dvd_of_dvd` and `Nat.coprime_primes`.
- **`rad_sq_dvd`** — hence `rad n ^ 2 ∣ n` for powerful `n`.
- **`rad_sq_le`** — hence `rad n ^ 2 ≤ n`: *powerful numbers have small radical*. This is
  the quantitative content that congruences cannot see.
- `coprime_of_odd` — `gcd n (n+2) = 1` for odd `n` (the triple is pairwise coprime, since
  `n ≡ 3 mod 4` is odd by the published congruence result).
- **`triple_rad_sq_le`** — for a powerful triple with `n` odd,
  `rad (n(n+1)(n+2))² ≤ n(n+1)(n+2)`.

## Why this is the right next interface

`triple_rad_sq_le` says a powerful triple yields an abc-triple `(n, 2, n+2)` whose radical is
at most the square root of the product — precisely the quality the abc conjecture forbids for
large `n`. It makes explicit, as a checked Lean statement, *why* Erdős 364 is an abc-strength
problem: the congruence sieve stalls at `n ≡ 7, 27, 35 (mod 36)` with infinitely many
survivors, and what actually rules those out is a size/radical bound, not a divisibility one.

A later solver can take `rad_sq_le` as the bridge from `Nat.Powerful` to any radical- or
abc-based argument without redoing the factorisation bookkeeping.

## Mathlib declarations used

`Nat.primeFactors`, `Nat.prime_of_mem_primeFactors`, `Nat.primeFactors_mul`,
`Nat.Coprime.mul_dvd_of_dvd_of_dvd`, `Nat.Coprime.pow_left`, `Nat.Coprime.pow_right`,
`Nat.Coprime.prod_right`, `Nat.coprime_primes`, `Nat.dvd_add_right`, `Nat.gcd_dvd_left`,
`Nat.gcd_dvd_right`, `Nat.dvd_prime`, `Nat.le_of_dvd`, `Finset.prod_ne_zero_iff`,
`Finset.prod_insert`, `Finset.induction_on`.
