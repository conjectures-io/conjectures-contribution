# Sources

## Target

- Erdős Problem 137, https://www.erdosproblems.com/137
- The pinned declaration `Erdos137.erdos_137.variants.multiple_powerful_factors`, which asks
  that for fixed `k`, every sufficiently long block of consecutive integers admits `k`
  distinct primes dividing the block product exactly once.
- Erdős, P., "Miscellaneous problems in number theory", Congressus Numerantium (1982), 25-45.
  (the source of the `k`-primes conjecture)

## Context

- Erdős, P. and Selfridge, J. L., "The product of consecutive integers is never a power",
  Illinois Journal of Mathematics 19(2) (1975), 292-301,
  https://doi.org/10.1215/ijm/1256050816
  Context only: this file does not use or restate that theorem.

## Mathlib declarations used

- `Nat.factorization_prod` — valuation of a product is the sum of valuations.
- `Nat.Prime.pow_dvd_iff_le_factorization` — `p ^ j ∣ N ↔ j ≤ N.factorization p`.
- `Nat.factorization_eq_zero_of_not_dvd` — non-divisors contribute nothing to the sum.
- `Nat.exists_prime_lt_and_le_two_mul` — Bertrand's postulate, used to place a prime in
  `((m+n)/2, m+n]`.
- `Nat.dvd_sub_iff_left`, `Nat.eq_zero_of_dvd_of_lt` — the two-multiples-are-equal step.

## Relation to prior contributions

The `p ∣ i`, `p ^ 2 ∤ i` valuation idea is the same device used in the author's earlier
merged contribution on target `erdos-364` (`Contribution.Erdos364Congruence`). That file
applied it to a fixed three-term window to derive congruence obstructions; the delta here is
different and new: the argument is carried out over a block of arbitrary length `Icc m (m+n)`,
the uniqueness hypothesis is isolated as a reusable interface, and Bertrand is used to
discharge it unconditionally in the regime `m ≤ n`. No statement is copied from that file.

## What a later solver gets

- `simple_prime_of_unique` reduces the target's per-prime obligation
  (`p ∣ N ∧ ¬ p ^ 2 ∣ N`) to the purely combinatorial claim that `p` meets the block once,
  simply. This is the shape the target needs for each of its `k` primes.
- `simple_prime_of_large` discharges that hypothesis automatically for any prime `p > n`.
- `exists_simple_prime` gives one such prime unconditionally whenever `1 ≤ m ≤ n`, which is
  the `k = 1` case of the target in that regime, and in particular shows those block
  products are not powerful.
