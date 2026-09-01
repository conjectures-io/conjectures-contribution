# Sources

## Target and statement

`FormalConjectures/GreensOpenProblems/24.lean` declares `lower_HL` under a
research-solved category with a `sorry` proof. This contribution proves exactly that
statement (restated under the `Contribution` namespace): the lower bound γ ≥ 1/12 for
the limsup density of 3-term affine translates, complementing the file's proven
`upper_trivial`.

## Method

Explicit witness family A = {0,…,n−1}: the pairs (x, x+j) with j ≥ 1 and x+3j ≤ n−1
inject into the counted set (`Finset.card_le_card_of_injOn` over a sigma set), giving
count ≥ Σ_{s<n} ⌊s/3⌋ ≥ n²/12 for n ≥ 10 (Gauss sum + `nlinarith`); `le_csSup` lifts to
`max013AffineTranslates`, and `le_limsup_of_frequently_le` (bounded via `upper_trivial`)
concludes.

## Verification

Axiom closure exactly `propext`, `Classical.choice`, `Quot.sound` on the pinned
toolchain (Lean 4.27.0 / Mathlib `a3a10db0`); no sorry/native_decide/set_option.
