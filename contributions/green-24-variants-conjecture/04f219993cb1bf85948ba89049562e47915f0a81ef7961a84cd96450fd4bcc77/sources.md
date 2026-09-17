# Sources

## Target

- Lean target: `Green24.variants.conjecture : Green24.variants.gamma = 1/3`, reward target
  `fc-target:Green24.variants.conjecture`, in `FormalConjectures/GreensOpenProblems/24.lean`
  of the pinned Formal Conjectures release
  (<https://github.com/google-deepmind/formal-conjectures/blob/7d1a8c9912747679d0093f6d1216420c33ee5ffa/FormalConjectures/GreensOpenProblems/24.lean>).
  There `Green24.max013AffineTranslates n` is the supremum, over all `A : Finset ℤ` with
  `A.card = n`, of the number of ordered pairs `(x, y) ∈ A × A` with `x ≠ y` and
  `x + 3 * (y - x) ∈ A`, and `gamma` is `limsup (max013AffineTranslates n / n ^ 2)` as `n → ∞`.
- Informal problem: Green's Open Problem 24
  (<https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.24>): how many affine
  copies of `{0, 1, 3}` can a set of `n` integers contain? The conjectured answer
  `(1/3 + o(1)) n^2` is due to Aaronson, *Maximising the number of solutions to a linear equation
  in a set of integers*, Bull. London Math. Soc. 51 (2019), p. 579
  (<https://arxiv.org/abs/1801.07135>), where the interval `{0, …, n-1}` is shown to realise the
  constant `1/3`.
- The target is the statement `gamma = 1/3`. It splits into the lower bound `gamma ≥ 1/3`, which
  is elementary, and the upper bound `gamma ≤ 1/3`, which is the open part. This contribution
  settles the lower bound in Lean and reduces the whole target to a finite-`n` upper bound; it
  does **not** prove the conjecture.

## Relation to existing contributions

Parent: `10e86c934afdeeb8cb74f4b0ae90e14953920084c1118c6d6a5ede4ad19411a3`
(<https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/green-24-variants-conjecture/10e86c934afdeeb8cb74f4b0ae90e14953920084c1118c6d6a5ede4ad19411a3>),
"Lower bound gamma >= 1/12 for 3-term affine translates" (`Contribution.LowerHL`). It uses the
same interval witness but counts only the increasing pairs `(x, x + j)` and bounds their number
by `∑_{s < n} ⌊s/3⌋ ≥ n^2/12`, obtaining `gamma ≥ 1/12`.

Delta of this contribution (all declarations are new and independently written; nothing is
copied from the parent):

- the constant is improved from `1/12` to the sharp value `1/3` conjectured to be optimal;
- both orientations of every copy `{x, x + d, x + 3d}` are counted — the increasing pair
  `(x, x + d)` and the decreasing pair `(x + 3d, x + 2d)` — with an explicit index set, two
  injections and a disjointness argument, giving the exact count `2 m n - 3 m (m + 1)`,
  `m = ⌊(n-1)/3⌋`, hence `3 · pairCount ≥ n^2 - 5 n`;
- a reusable two-sided limsup interface for `gamma`: an eventual bound
  `c n^2 - C n ≤ max013AffineTranslates n` yields `c ≤ gamma`, and an eventual bound
  `max013AffineTranslates n ≤ c n^2 + C n` yields `gamma ≤ c`, with the boundedness and
  coboundedness side conditions discharged once and for all;
- a reduction theorem: `conjecture_of_upper_bound` shows that an eventual inequality
  `max013AffineTranslates n ≤ n^2/3 + C n` implies the target `gamma = 1/3`. A later solver can
  use it to discharge the limsup and lower-bound halves of `Green24.variants.conjecture`,
  leaving exactly the combinatorial upper bound.

## What is proved here

Namespace `Contribution.Green24VariantsConjecture`. Everything is elementary; the value of the
file is that these steps are checked once and exposed with usable statements.

- `pairCount A` — the pair count of a single set, written with the same filter predicate as
  `max013AffineTranslates`; `pairCount_le_max (hA : A.card = n) : pairCount A ≤ max013AffineTranslates n`
  (via `le_csSup` and the `n^2` bound `bddAbove_pairCounts`).
- `interval n = {0, …, n-1}` with `card_interval`, `mem_interval : z ∈ interval n ↔ 0 ≤ z ∧ z < n`,
  `natCast_mem_interval`.
- `copyIndex n`, `card_copyIndex`, `two_mul_sum_copies` — index of the copies inside the interval
  and the closed form `2 ∑_{i<m} (n - 3(i+1)) + 3 m (m+1) = 2 m n` for `3 m ≤ n`.
- `upPair`, `downPair`, `upPair_mem`, `downPair_mem`, `upPair_injOn`, `downPair_injOn`,
  `disjoint_upPair_downPair`, `two_mul_card_copyIndex_le` — both orientations inject disjointly
  into the counted pairs of the interval.
- `pairCount_interval_ge : n ^ 2 ≤ 3 * pairCount (interval n) + 5 * n` and
  `max_ge : n ^ 2 ≤ 3 * max013AffineTranslates n + 5 * n` — the finite-`n` lower bound.
- `ratio_le_one`, `ratio_nonneg`, `ratio_isBoundedUnder` — the sequence
  `max013AffineTranslates n / n ^ 2` lies in `[0, 1]` (using the proved `upper_trivial`).
- `gamma_ge_of_eventually {c C} : (∀ᶠ n, c n^2 - C n ≤ max013AffineTranslates n) → c ≤ gamma` and
  `gamma_le_of_eventually {c C} : (∀ᶠ n, max013AffineTranslates n ≤ c n^2 + C n) → gamma ≤ c`,
  proved by comparing limsups with the sequences `c ∓ C/n`.
- `gamma_ge_one_third : Green24.variants.gamma ≥ 1 / 3`.
- `conjecture_of_upper_bound {C} : (∀ᶠ n, max013AffineTranslates n ≤ n^2/3 + C n) → gamma = 1/3`.

## Verification

- Toolchain: Lean `leanprover/lean4:v4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`
  (tag v4.33.1); Formal Conjectures at the pool's pinned commit
  `8432eac998110a563e03df65a28c117e97c8c142` (upstream base
  `7d1a8c9912747679d0093f6d1216420c33ee5ffa`,
  <https://github.com/google-deepmind/formal-conjectures>).
- The file elaborates with the default budget (`maxHeartbeats` 400000) with no errors or
  warnings.
- Axiom closure of every declaration, including `gamma_ge_one_third` and
  `conjecture_of_upper_bound`: exactly `propext`, `Classical.choice`, `Quot.sound`.
- No forbidden dependencies: the only imports are `Mathlib` and
  `FormalConjectures.GreensOpenProblems.«24»`; the source file's `lower_HL` and `upper_HL`, whose
  proofs are not supplied there, are not used; only the proved `upper_trivial` is. No
  `native_decide`, no `set_option`, no metaprogramming.
- Sanity check performed outside the file: `pairCount (interval 10) = 24` by kernel `decide`,
  matching the closed form `2 m n - 3 m (m+1)` with `m = 3`.
