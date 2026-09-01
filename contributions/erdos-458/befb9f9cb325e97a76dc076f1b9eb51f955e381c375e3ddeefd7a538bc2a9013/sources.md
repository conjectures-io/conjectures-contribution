# Sources

## Target

`Erdos458.erdos_458` in `FormalConjectures/ErdosProblems/458.lean`
(`lcm(1,…,p_{k+1}-1) < p_k · lcm(1,…,p_k)` for all `k`), via the pinned `conjectures`
submodule. Background: https://www.erdosproblems.com/458 ("open, but could be disproved
with a finite counterexample"; Erdős–Graham judged it "almost certainly true").

## What this contributes (checked counterexample work)

The ratio `lcm(1,…,p_{k+1}-1)/lcm(1,…,p_k)` picks up exactly the primes `q` with a power
`q^a` (`a ≥ 2`) strictly inside the gap `(p_k, p_{k+1})` — no first powers, since the gap
contains no primes. As `q^a < p_{k+1}` with `a ≥ 2` gives `q < √p_{k+1}`, one such prime
power cannot reach `p_k`: any counterexample needs two prime squares inside one prime
gap. The two theorems here prove the resulting barrier: that configuration forces
`q - p ≥ 4a + 4` and `(q - p)² > 16 p`, i.e. a prime gap longer than `4√p`. Known gaps
grow like `log² p` (maximal known gap below 10¹⁸ is 1476, vs 4√p = 4·10⁹ there), and even
RH yields only `O(√p · log p)` — the wrong side of the barrier. Hence no finite search
can produce a counterexample; effort on this target should go to the formalized
direction. An exhaustive computation over all 80070 prime powers `q^a ≤ 10¹²` (a ≥ 2)
confirms no prime gap below 10¹² contains two prime squares; only five gaps contain even
two prime powers, the largest ratio being `6/7` at `p = 7`.

## Mathlib declarations used

`Nat.Prime.odd_of_ne_two`, `Nat.Prime.two_le`, `Nat.pow_le_pow_left`; tactics `omega`,
`nlinarith`. Self-contained; axiom closure of both theorems is exactly `propext`,
`Classical.choice`, `Quot.sound` on the pinned toolchain (Lean 4.27.0 / Mathlib `a3a10db0`).
