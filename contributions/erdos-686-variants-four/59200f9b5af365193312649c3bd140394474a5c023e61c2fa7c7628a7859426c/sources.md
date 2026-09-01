# Sources

## Target

- [Erdős Problem 686](https://www.erdosproblems.com/686) — can `4` be written as
  `∏_{1≤i≤k}(m+i) / ∏_{1≤i≤k}(n+i)` for some `k ≥ 2` and `m ≥ n + k`?
- Pinned statement `Erdos686.erdos_686.variants.four` in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  at commit `379fc0298dc146df549e7061c3ede0353a5bb51f`.

## Relation to the parent

Extends parent `032036067e6b859aa32ed19b79a825b6f716a11b8c12650606124c8aaa58a581`
(which itself extended `14617a5917c8…`). The parent's three results are reproved
here unchanged — each `.lean` must be self-contained, so they cannot be imported.
**The new delta is item 4 below**, plus the search in the analysis section.

## What is proved here

1. `no_ratio_four_of_len_two` — from the parent chain. `k = 2` impossible in `ℕ`.
2. `len_three_iff_cubic` — from the parent. `k = 3` ⟺ `u³ − u = 4(v³ − v)`.
3. `len_three_overlap_solution` — from the parent. The curve point `(3,2)`.
4. **`no_ratio_four_of_len_four` (NEW).** `k = 4` is impossible outright, by the same
   square-difference method as `k = 2`. The identity
   `(x+1)(x+2)(x+3)(x+4) = (x²+5x+5)² − 1`
   turns the window equation into `A² − 4B² = −3`, i.e. `(A−2B)(A+2B) = −3`, with
   `A = m²+5m+5 ≥ 5` and `B = n²+5n+5 ≥ 5`, hence `A + 2B ≥ 15 > 3`. Contradiction in
   every sign case. As with `k = 2`, no `m ≥ n + 4` hypothesis is needed.

   This is not an accident of small numbers: for even `k = 2j` the window product is
   `∏_{i=1..j}(s + i(2j+1−i))` with `s = x² + (2j+1)x`, which is a *perfect square minus
   one* exactly when `j ≤ 2`. So `k ∈ {2,4}` are precisely the cases this elementary
   method reaches; `k = 3` and `k = 6` already give curves of positive genus.

## Supporting analysis (not part of the Lean artifact)

**Curve data for `k = 3`** (PARI/GP 2.15.4). The curve of item 2 is `y² = x³ − 48x + 272`,
minimal model `y² + y = x³ − 3x + 4` — **Cremona 135a1**, conductor 135, trivial torsion,
analytic rank 1 with `L′(1) ≈ 0.6703`, so `E(ℚ) ≅ ℤ`. An exact-rational chord–tangent
enumeration to height `10⁶⁰` and a direct sweep over `2 ≤ v ≤ 10⁷` both give integral
points `{(0,0), (±1,0), (0,±1), (±1,±1), (±3,±2)}`; the only non-trivial pair `±(3,2)` is
the excluded overlap solution of item 3.

**Two necessary conditions for any witness.** (a) The ratio is minimised at `m = n + k`,
and `∏(n+k+i)/∏(n+i) ≤ 4` forces `n ≳ k²/log 4 ≈ 0.72 k²`. (b) Any prime `p ∈ [m+1, m+k]`
divides the left side but, being `> n + k`, cannot divide `4∏(n+i)` — so `[m+1, m+k]` must
be **prime-free**. Together: a witness needs a prime gap of length `k` near `m ≈ 0.72k²`,
i.e. a gap of size `≈ 1.18√m` at `m`. Since maximal gaps near `x` are empirically
`≈ log²x`, witnesses are possible only for `k ≲ 70`, and ruling them out for all `k`
unconditionally is Legendre-strength (note even RH gives only `O(√x log x)`).

**Exhaustive bounded search.** Using (a) and (b) as filters over all prime gaps below
`2 × 10⁶`, **16 363 283** admissible `(k, m)` pairs were tested for an exact solution of
`∏(m+i) = 4∏(n+i)`; **none** was found, and no solution violating `m ≥ n + k` appeared
either. Combined with items 1–4 this leaves `k ≥ 5, k ≠ 6` as the open frontier.

**Caveat, stated explicitly:** the curve and search results above are computational
evidence, not certified proofs — a complete integral-point determination needs a standard
algorithm (elliptic logarithms / Baker bounds) on 135a1. The Lean artifact claims none of
it: it claims exactly the four theorems.
