# Sources

## Target and statement

`FormalConjectures/ErdosProblems/141.lean` declares
`erdos_141.variants.first_cases` (`∀ k ≥ 3, k ≤ 10 → ∃ s, s.IsAPAndPrimeProgressionOfLength k`)
under `@[category research solved]` with a `sorry` proof. This contribution supplies a checked
proof of exactly that statement (restated under the `Contribution` namespace).

## Mathematical content and witnesses

- The k = 3..10 cases all follow from one witness: the known CPAP-10, ten consecutive primes in
  arithmetic progression with common difference 210 starting at
  100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719
  (Toplic 1998; see https://www.erdosproblems.com/141 and the CPAP records page
  https://www.pzktupel.de/JensKruseAndersen/CPAP.htm).
- Primality of each term is proved by explicit Lucas certificates (`prime_of_lucas`, with a
  recursion into certified prime factors of p − 1); compositeness of every number in the gaps by
  Fermat tests (`not_prime_of_fermat`, base-2 via fast modular exponentiation `pw`) or explicit
  factors; consecutiveness by exhaustive gap chains. No `native_decide` and no `decide`
  kernel-reduction on large numbers: every certificate elaborates through `norm_num`.

## Mathlib declarations used

`Nat.Prime` API, `Nat.ModEq`-free elementary arithmetic, `List.forall_mem_cons`, `norm_num`,
`omega`. Self-contained on Mathlib plus the pool module import. Axiom closure of the final
theorem is exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned toolchain
(Lean 4.27.0 / Mathlib `a3a10db0`).
