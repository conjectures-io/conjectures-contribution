# Sources

## Target

- [Erdős Problem 686](https://www.erdosproblems.com/686) — can `4` be written as
  `∏_{1≤i≤k}(m+i) / ∏_{1≤i≤k}(n+i)` for some `k ≥ 2` and `m ≥ n + k`?
- Pinned statement `Erdos686.erdos_686.variants.four` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  at commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.

## Relation to the parent contribution

This supersedes and extends parent
`14617a5917c80bf4e1d6c42b09a427fb3eae06907054ba63a66396dc44ae6dcd`, which contained
only the length-2 obstruction. That theorem is reproved here unchanged
(`no_ratio_four_of_len_two`); everything else is new.

## What is proved here

1. **`no_ratio_four_of_len_two`** (from the parent). `(m+1)(m+2) = 4(n+1)(n+2)` has no
   solutions in `ℕ` at all — no `m ≥ n + 2` hypothesis needed. Completing the square
   forces `(4n+6)² − (2m+3)² = 3`, a factorisation `a·b = 3` with `b = 4n+2m+9 ≥ 9`,
   impossible whether `a ≤ 0` or `a ≥ 1`. Technique is classical Pell/square-difference
   descent, e.g. Mordell, *Diophantine Equations* (Academic Press, 1969); the statement
   and Lean proof are original to this work.

2. **`len_three_iff_cubic`** (new). Because `(x+1)(x+2)(x+3) = (x+2)³ − (x+2)`, the
   length-3 window identity holds **iff** `u³ − u = 4(v³ − v)` with `u = m+2`, `v = n+2`.
   This converts the remaining `k = 3` obligation from a product identity into an
   integral-point question on a genus-one curve — a checked interface a later solver can
   attack with elliptic-curve machinery.

3. **`len_three_overlap_solution`** (new). The curve point `(u,v) = (3,2)`, i.e.
   `2·3·4 = 4·(1·2·3)` with `m = 1, n = 0`, is a genuine solution of the `k = 3`
   equation, excluded only by the disjointness hypothesis `m ≥ n + 3`. Recording it in
   Lean documents why **no congruence argument can settle `k = 3`**: any such argument
   must admit this point.

## Supporting analysis (not part of the Lean artifact)

Computed 2026-09-01 with PARI/GP 2.15.4. Via `ellfromeqn`, the curve of item 2 is
`y² = x³ − 48x + 272`, minimal model `y² + y = x³ − 3x + 4` — **Cremona 135a1**,
conductor 135, trivial torsion, analytic rank 1 with `L′(1) ≈ 0.6703`. So `E(ℚ) ≅ ℤ`
and no finite-descent shortcut exists.

Two independent searches for integral points agree on
`{(0,0), (±1,0), (0,±1), (±1,±1), (±3,±2)}`: an exact-rational chord–tangent enumeration
on the plane cubic to height `10⁶⁰`, and a direct sweep over `2 ≤ v ≤ 10⁷`. The only
non-trivial pair is `±(3,2)`, which is the excluded overlap solution of item 3.

**Caveat, stated explicitly:** these searches are strong evidence, not a certified
complete integral-point list. Establishing completeness requires a standard
integral-points algorithm (elliptic logarithms / Baker bounds), e.g. via Magma or
Sage on 135a1. The Lean artifact above claims none of this — it claims only the two
theorems and the recorded solution point.

## Consequence for the target

The counterexample side needs "no `(k, n, m)` witness exists". Item 1 closes `k = 2`
unconditionally. Item 2 reduces `k = 3` to a named curve, and the analysis above
indicates `k = 3` has no admissible witness. The frontier is therefore `k ≥ 4`, where
any prime in `(m, m+k]` contradicts the identity, so a witness would need `k`
consecutive `(n+k)`-smooth numbers at height `m` — beyond current prime-gap technology.
