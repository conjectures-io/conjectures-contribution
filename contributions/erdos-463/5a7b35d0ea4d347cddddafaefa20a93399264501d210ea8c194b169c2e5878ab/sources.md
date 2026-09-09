# Sources

## Target

- `Erdos463.erdos_463` in `FormalConjectures/ErdosProblems/463.lean`, pinned via the
  `conjectures` submodule: is there `f → ∞` such that every large `n` has a composite `m` with
  `n + f(n) < m < n + minFac(m)`? Background: <https://www.erdosproblems.com/463>.
- Checked before writing: `contributions/erdos-463/` had no prior contributions.

## What is proved here (all kernel-checked)

- `offsets n` — admissible offsets `{d > 0 : n + d composite ∧ d < minFac (n + d)}`;
  `offsets_le` (`d ≤ n`), `offsets_sq_lt` (`d² < n + d`), `offsets_bddAbove`.
- `reach n := sSup (offsets n)` — the largest admissible offset (`0` if none);
  `le_reach`, `reach_mem`.
- **`erdos_463_iff_tendsto_reach`** — the pinned statement is *equivalent* to
  `Tendsto reach atTop atTop`. Given `f`, the witness `m` gives `reach n ≥ m − n > f n`;
  given `reach → ∞`, take `f n := reach n − 1`, `m := n + reach n`. Erdős 463 is exactly
  the growth of one explicit, computable function.
- **`reach_unbounded`** — `∀ B, ∃ n, B ≤ reach n`, unconditionally: just below a prime
  square `q²` the offset `q − 1` is admissible because `minFac (q²) = q`. So
  `limsup reach = ∞` is a theorem; Erdős 463 is the statement `liminf reach = ∞`.
- **`reach_267380 = 3`** — the *deepest hole* found by computation, **certified**: the offset
  `3` works since `267383 = 47 · 5689`; every `d ∈ [4, 517]` fails because `267380 + d` is
  prime or has a prime factor `≤ d` (514 cases, `interval_cases` + `norm_num`); larger `d`
  is excluded by `offsets_sq_lt`.
- `reach_sixteen = 0` — a certified hole with no admissible offset at all.

## Supporting computation (not part of the Lean artifact)

Exact computation of `reach` for `n ≤ 6·10⁶`, then a vectorised least-prime-factor sieve
testing `reach n ≤ 25` for all `n ≤ 2·10⁸` (a composite `m` with least prime `p ≥ 27` serves
exactly `n ∈ (m − p, m − 26]`).

- Holes `reach n ≤ 25` occur only in clusters near `n ≈ 101068, 108828, 121966,
  267358–267448`. **The last hole below `2·10⁸` is at `n = 267448`** — no `n` in
  `[10⁶, 2·10⁸]` has `reach n ≤ 25`.
- Minima of `reach` over dyadic ranges above `2¹⁸` (exact, to `6·10⁶`):
  `73, 227, 539, 539, 871`. Empirically the pinned statement is true.

## Why holes cannot persist, and why a proof is still out of reach

A hole of depth `D` can be engineered by CRT (`n ≡ −d (mod p_d)`, `p_d ≤ d`), but that
forces `n ≳ e^{θ(D)}`, so the danger zone `√n ≈ e^{D/2}` vastly exceeds the depth `D`
controlled. Structured large holes therefore do not exist; only accidental small ones, which
is what the data shows.

Proving `reach → ∞` needs, for *every* large `n`, a `d`-rough composite in
`(n + C, n + √n]`. Sifting an interval of length `√n` by the primes up to `√n` is the
linear sieve at parameter `s = 1`, where no lower bound exists — the same barrier that
keeps Legendre's conjecture open. Sieve methods give "almost all `n`", never "every `n`".
Alternative witnesses (balanced semiprimes, prime squares) run into the parity barrier
instead. This is the precise obstruction, not a heuristic.

**Caveats, stated explicitly:** the hole data is exact but finite; the CRT argument is
informal. The Lean artifact claims exactly the listed theorems.

## Mathlib declarations used

`Nat.minFac_sq_le_self`, `Nat.Prime.pow_minFac`, `Nat.prime_dvd_prime_iff_eq`,
`Nat.exists_infinite_primes`, `Nat.le_self_pow`, `Nat.sSup_mem`, `le_csSup`, `csSup_le`,
`Filter.tendsto_atTop_atTop`, `Filter.eventually_atTop`, `interval_cases`, `norm_num`.

## Toolchain

Validated against the pool pin `8432eac9` (upstream Formal Conjectures `7d1a8c99`): Lean `v4.33.1`, Mathlib `0df444a`. Compiles with no warnings; axioms `propext`, `Classical.choice`, `Quot.sound` only.
