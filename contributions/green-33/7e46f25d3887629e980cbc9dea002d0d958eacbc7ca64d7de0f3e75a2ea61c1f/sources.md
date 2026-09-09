# Sources

## Target

- `Green33.green_33` in `FormalConjectures/GreensOpenProblems/33.lean`, pinned via the
  `conjectures` submodule: are there infinitely many `q` with `A ⊆ ℤ/qℤ`, `A + A = ℤ/qℤ`, and
  `|A| = (√2 + o(1))√q`? Background: Ben Green, "100 open problems", Problem 33
  (<https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.33>).
- Checked before writing: `contributions/green-33/` had no prior contributions.

## The gap this fills

The pinned file's only quantitative lemma, `green_33.sanity_sq_bound`, gives `q ≤ |A|²`, i.e.
`|A| ≥ √q` — constant `1`. But the constant in Green's question is `√2`, and it comes from
counting *unordered* sums: `A + A` has at most `binom(|A|+1, 2) = |A|(|A|+1)/2` elements, so
`A + A = ℤ/qℤ` forces `|A|(|A|+1) ≥ 2q`, hence `|A| ≥ (√2 − o(1))√q`. This sharp bound — the
reason `√2` is the constant in the problem — was absent from the pool file. This contribution
supplies it, and shows it is optimal.

## What is proved here (all kernel-checked; axioms: propext, Classical.choice, Quot.sound only)

### Part I — the sharp lower bound

- `card_add_self_le_choose` — for any `A ⊆ ℤ/qℤ`, `|A + A| ≤ binom(|A|+1, 2)`. Proof: the
  symmetric sum map factors through `Finset.sym2 A` (the `binom(|A|+1,2)` unordered pairs) via
  `Sym2.lift ⟨(· + ·), add_comm⟩`.
- `two_mul_le_card_mul` — if `A + A = ℤ/qℤ` then `2q ≤ |A|(|A|+1)`.
- **`sqrt_two_mul_sqrt_le`** — the sharp bound: `A + A = ℤ/qℤ ⟹ √2·√q ≤ |A| + 1`.
- **`sqrt_two_sub_le_ratio`** — ratio form: `√2 − 1/√q ≤ |A|/√q`, so `liminf |A|/√q ≥ √2`.
- **`abs_lt_iff_upper`** — target simplification: once `1/√q < ε`, the two-sided closeness in
  `green_33` is *equivalent* to the one-sided `|A|/√q − √2 < ε`.
- **`exists_tight`** — the counting bound is attained (`q = 3`, `A = {0,1}`).

### Part II — equality is classified (`|A| ≤ 2`)

- `sum_injOn_sym2_of_tight` — if `2q = |A|(|A|+1)` and `A + A = ℤ/qℤ`, the unordered sum map is
  injective on `A.sym2`: a perfect basis is a Sidon set.
- `sub_injOn_offDiag_of_tight` — hence all `|A|(|A|−1)` ordered nonzero differences are distinct.
- **`card_le_two_of_tight`** — so `|A|(|A|−1) ≤ q − 1`; with `2q = |A|(|A|+1)` this gives
  `(|A|−1)(|A|−2) ≤ 0`, i.e. `|A| ≤ 2`.
- **`two_mul_succ_le_card_mul`** — for `q ≥ 4` the bound strengthens to `2(q+1) ≤ |A|(|A|+1)`.
- **`tight_iff`** — complete classification: `ℤ/qℤ` has a perfect basis iff `q = 1` or `q = 3`.
  (This turns the earlier finite computation "no perfect basis for `3 ≤ k ≤ 12`" into a theorem
  for all `k`.)

### Part III — additive energy and the spike theorem

Definitions: `rep A x = #{(a,b) ∈ A² : a + b = x}`, `dif A y = #{(a,b) ∈ A² : a − b = y}`.

- `rep_eq_card_filter` — `rep A x = |A ∩ (x − A)|`, the symmetry defect of `A` about `x/2`.
- `sum_sq_card_filter_eq` — fibre identity `∑_x #{p : f p = x}² = #{(p,p') : f p = f p'}`.
- **`sum_sq_rep_eq_sum_sq_dif`** — the energy identity `∑_x rep² = ∑_y dif²`, via the bijection
  `(a,b,c,d) ↦ (a,d,c,b)` turning `a + b = c + d` into `a − d = c − b`.
- `sum_rep`, `sum_dif`, `dif_zero`, `sum_dif_erase_zero` — `∑ rep = ∑ dif = |A|²`,
  `dif 0 = |A|`, `∑_{y≠0} dif y = |A|² − |A|`.
- `sq_sum_dif_le`, **`energy_lower`** — Cauchy–Schwarz over the `q − 1` nonzero differences:
  `(q−1)·∑_x rep(x)² ≥ (|A|² − |A|)² + (q−1)|A|²`.
- `one_le_rep`, `two_le_rep_of_not_mem_double` — covering gives `rep ≥ 1`, and `rep ≥ 2` off
  the at most `|A|` doubles `a + a`.
- **`exists_rep_spike`** — exact form: with `k = |A|` and `M = max_x rep A x`,
  `k²(k−1)² ≤ (q−1)·(M·(k² + k − 2q) + k² − k)`. Proof: the pointwise bound
  `rep² + 2M ≤ M·rep + 2·rep + (M−1)·[x is a double]` (valid for `1 ≤ rep ≤ M`), summed and
  combined with `energy_lower`.
- **`exists_spike`** — symmetry-defect form, free of `q − 1`: for some `x`,
  `(k+1) · |A ∩ (x − A)| · (k² + k − 2q) ≥ k(k−1)(k−3)`.
- **`exists_spike_of_le_sqrt`** — asymptotic form: if `|A| ≤ √2·√q + t` (`t ≥ 0`) then for some
  `x`, `k(k−1)(k−3) ≤ (k+1) · |A ∩ (x − A)| · ((2t+1)k + t² + 2t)`, i.e.
  `|A ∩ (x − A)| ≳ k/(2t+1)`.

### Part IV — the refined universal bound `2q ≤ |A|² + 2`

- **`two_mul_add_rep_le`** — wasted pairs: all unordered pairs summing to `x` collapse to the
  single element `x`, so `2q + rep A x ≤ |A|(|A|+1) + 2` for every `x` (the `⌈rep/2⌉` pairs are
  counted via `Finset.card_le_mul_card_image` with fibres of size `≤ 2`).
- **`two_mul_le_sq_add_two`** — for every basis, `2q ≤ |A|² + 2`. Proof: write
  `D = k² + k − 2q ≥ 0`; the waste bound gives `rep A x ≤ D + 2` at the spike `x`, the exact
  spike inequality gives `k²(k−1)² ≤ (q−1)(rep·D + k² − k)`; if `D ≤ k − 3` these contradict:
  with `k = e + 3 + t`, `D = t` (`e, t ∈ ℕ`) the difference of the two sides is the polynomial
  `12 + 14t + 6t² + t³ + 28e + 37et + 15et² + 2et³ + 23e² + 23e²t + 5e²t² + 8e³ + 4e³t + e⁴`,
  all of whose coefficients are positive (checked by `ring` + `positivity`). Hence `D ≥ k − 2`.
  This removes the linear term of the sharp bound `2q ≤ |A|(|A|+1)`: the bound symmetric sets
  satisfy trivially (`S = −S` wastes the pairs `{s, −s}`) holds for *all* bases.
- **`sqrt_two_mul_sub_two_le`** — real form `√(2q − 2) ≤ |A|` (vs. `√(2q) − 1 ≤ |A|` before).
- **`exists_rep_ge_of_eq`** — equality `2q = |A|² + 2` (with `|A| ≥ 3`) forces some `x` with
  `|A ∩ (x − A)| ≥ |A| − 1`: an extremal basis is symmetric up to one element.

**Why this matters for Green 33.** The spike theorem says every basis within an additive
constant of the sharp bound `√(2q)` is symmetric about some point on a positive proportion of
its elements. Exact symmetry `A = x − A` with `A + A = ℤ/qℤ` means `A − A = ℤ/qℤ` with each
nonzero difference hit `≈ 2` times — a `(q, k, 2)` difference set (a *biplane*) up to the spike.
Conversely a symmetric cyclic biplane gives a basis of ratio `k/√q → √2`. Only three cyclic
biplanes are known (`(7,4,2)`, `(11,5,2)`, `(37,9,2)`), and whether infinitely many biplanes
exist is a well-known open problem; the spike theorem shows this rigidity is *forced* on any
near-`√2` basis, not merely a feature of one construction. Green 33 therefore sits between
"infinitely many approximate biplanes" and the coupon-collector obstruction to random-like sets.

## Supporting computation (not part of the Lean artifact)

- **Exact minimal basis sizes.** Exhaustive search (bitmask sumsets, `0 ∈ A` w.l.o.g.) gives
  `k(q) = min{|A| : A + A = ℤ/qℤ}` for all `q ≤ 42`. In every case `k(q)² ≥ 2q − 2`, confirming
  `two_mul_le_sq_add_two`, with **equality exactly at `q = 3, 9, 19`** (`k = 2, 4, 6`). Sample:
  `k(13) = 5`, `k(19) = 6`, `k(29) = 8`, `k(30) = 8`, `k(33) = 9`, `k(42) = 10`.
- **Symmetric perfect bases.** By Part IV a basis attaining `|A|² = 2q − 2` is symmetric up to one
  element; a fully symmetric one is `S = B ∪ (−B)` with `q = 2n² + 1`, `|B| = n`, all nonzero
  differences of multiplicity `≤ 2` (a `(2n²+1, 2n, λ ∈ {1,2})` almost difference set). Exhaustive
  search: such `B` exist **only for `n ≤ 3`** (`q = 3, 9, 19`; e.g. `S ⊆ 𝔽₁₉` is the multiplicative
  subgroup of order 6) and for **no `4 ≤ n ≤ 8`** (`q ≤ 129`). The variant with `0 ∈ S`
  (`q = 2n² + 2n + 1`) exists only for `n ≤ 2` (`q = 5, 13`; `S = {0} ∪ H₄ ⊆ 𝔽₁₃`) and for no
  `3 ≤ n ≤ 7`. So the exact extremal objects are sporadic, exactly like biplanes.
- **Product (CRT) constructions are excluded.** A "graph" basis `{(x, f(x))} ⊆ ℤ_{2n+1} × ℤ_n`
  (ratio `→ √2`) would have `rep ≤ 4` everywhere; the energy lower bound `≈ 12n²` versus the
  graph's `≈ 8n²` forbids it — an instance of the spike theorem. Symmetrised graphs (`f` odd)
  regain the spike but need `x ↦ f(x) + f(s−x)` to be a near-bijection on pairs for every `s`;
  for the natural algebraic choices (`f` = discrete log, quadratics, norms from `𝔽_{p²}`) the
  sign ambiguity `u² + v² = c` produces `≈ p/8` collisions per fibre (about 25% of each fibre
  uncovered), so no such family exists.

- Direct numerical check of `exists_rep_spike` / `exists_spike` on the minimal bases of
  `ℤ/qℤ` for `q ≤ 30` and on the Fano-complement basis `{0,3,5,6} ⊆ ℤ/7ℤ` (`k = 4`,
  `D = k² + k − 2q = 6`, spike `M = 3`: exact form `144 ≤ 180`, `q`-free form `12 ≤ 90`).
  Equality in the exact form occurs precisely at `q = 1` and `q = 3` (`4 ≤ 4`), matching
  `tight_iff`.
- Exhaustive search over `ℤ/qℤ` (now superseded by `tight_iff`): perfect bases only for `k ≤ 2`.
- Largest coverable modulus `Q(k)` gives ratios `k/√Q(k)` of `1.33`–`1.48` for `k ≤ 8`,
  straddling `√2 ≈ 1.414`.
- Sumsets of the three known cyclic biplanes: `(7,4,2)` covers `ℤ/7ℤ` exactly; the quartic
  residues mod 37 miss exactly one residue; the QR set mod 11 misses one. Only the `q ≡ 3 (mod 4)`
  Fano complement is exactly symmetric.

**Caveats, stated explicitly:** the computational claims are exact but finite; the biplane
remarks are context, not theorems; the coupon-collector remark is heuristic. The Lean file
claims exactly the theorems listed above (29 theorems, 2 definitions).

## Mathlib declarations used

`Finset.card_sym2`, `Finset.mk_mem_sym2_iff`, `Sym2.lift`, `Sym2.eq_iff`, `Finset.card_image_le`,
`Finset.card_image_iff`, `Finset.card_image_of_injOn`, `Finset.card_le_card`, `Finset.mem_add`,
`Finset.offDiag_card`, `Finset.mem_offDiag`, `Finset.diag_card`, `Finset.mem_diag`,
`Finset.card_erase_of_mem`, `Finset.card_eq_sum_card_fiberwise`, `Finset.filter_product`,
`Finset.filter_filter`, `Finset.card_product`, `Finset.card_nbij'`, `Finset.add_sum_erase`,
`Finset.sum_le_sum`, `Finset.sum_add_distrib`, `Finset.mul_sum`, `Finset.sum_const`,
`Finset.sum_boole`, `Finset.exists_max_image`, `Finset.one_lt_card`, `Finset.card_pos`,
`Finset.card_le_mul_card_image`, `Finset.card_le_two`, `Finset.card_sdiff_of_subset`,
`Finset.card_union_le`, `Int.eq_ofNat_of_zero_le`,
`sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz), `ZMod.card`, `Nat.choose_two_right`,
`Nat.even_mul_succ_self`, `Nat.mul_div_cancel'`, `PNat.eq`, `Real.sqrt_mul`, `Real.sqrt_le_sqrt`,
`Real.sqrt_sq`, `Real.sq_sqrt`, `Real.sqrt_pos`, `pow_le_pow_left₀`, `le_div_iff₀`, `abs_lt`.

## Toolchain

Validated against the pool pin `8432eac9` (upstream Formal Conjectures `7d1a8c99`): Lean `v4.33.1`, Mathlib `0df444a`. Compiles with no warnings; axioms `propext`, `Classical.choice`, `Quot.sound` only.
