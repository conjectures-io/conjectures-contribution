# Sources and provenance

**Target.** `erdos-153`, reward theorem `Erdos153.erdos_153`
(`FormalConjectures/ErdosProblems/153.lean`).

Statement: let `A` be a finite Sidon set and `A + A = {s_1 < ... < s_t}`; is it true that
`(1/t) * sum_{1 <= i < t} (s_{i+1} - s_i)^2 -> infinity` as `|A| -> infinity`?

## The obstacle this contribution addresses

The target module has exactly two declarations, the definition `Erdos153.f` and the
`research open` theorem `Erdos153.erdos_153`. There is no `research solved` / `textbook` /
`test` companion carrying a `sorry`, so no complete special case was available to prove
outright; the problem is genuinely open.

`Erdos153.f n` is an infimum over the subtype
`{A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)}` of a quantity built from
`Finset.orderIsoOfFin` and summed over the coerced sort `↥(Set.Ico 1 (A + A).card)` with a
`Nat`-subtracted index carrying its own inequality proof. Before anything can be said about the
target:

* the quantity attached to a single Sidon set has to be re-indexed over `Finset.range`;
* lower bounds need `le_ciInf`, hence a `Nonempty` instance for that subtype, and upper bounds
  need `ciInf_le`, hence `BddBelow` of the range — neither is recorded anywhere in the repo;
* the infimum is not a priori attained, so strict bounds cannot be transferred to competitors;
* the competitor set is infinite, so no exact value is computable without a diameter cut-off;
* Mathlib in the pinned toolchain (`leanprover/lean4:v4.27.0`) contains no Sidon material at
  all — a case-insensitive grep of the `Mathlib` tree for `sidon` returns 0 files — so every
  Sidon counting fact had to be proved from scratch.

## What is delivered (delta over the pinned environment)

One self-contained file, 59 declarations, all in namespace `Contribution.Erdos153Gaps`,
compiling with 0 errors and 0 warnings, every declaration axiom-clean (each `#print axioms`
returns a subset of `[propext, Classical.choice, Quot.sound]`; the check was run and then the
`#print` lines removed).

1. **An infimum-free interface for the target's own definition.** `gapEnergy` (the minimised
   quantity as a plain `Finset.range` sum) together with
   `f_eq : Erdos153.f n = ⨅ A : …, gapEnergy A.1`, the `Nonempty` instance
   (`exists_isSidon_card`), `bddBelow_range_gapEnergy`, the two one-sided rules
   `f_le_gapEnergy` / `le_f`, and `tendsto_f_atTop_iff`, which is an **equivalence** between the
   target's right-hand side and a statement with no infimum in it.
2. **Attainment.** `exists_gapEnergy_eq_f`: the infimum defining `Erdos153.f n` is a minimum.
   This is what makes `lt_f_iff` (`c < f n ↔ ∀ competitors, c < gapEnergy`) true; the `←`
   direction is false for a general infimum.
3. **The Erdős–Turán window inequality for Sidon sets, formalised.** For Sidon `A ⊆ [0, N]` and
   `l ≥ 1`, `erdos_turan_ineq : |A|^2 * l ≤ (N + l) * (|A| + l - 1)`. The proof double counts
   `sum_x |A ∩ (x-l, x]|` (`sum_windowCount`) and its square (`sum_windowCount_sq`), bounds the
   second moment using injectivity of `(a,b) ↦ a - b` on ordered pairs of a Sidon set
   (`two_mul_sum_lower_le`, the only place the Sidon hypothesis is used) against the triangular
   sum `two_mul_sum_Ico`, and finishes with Cauchy–Schwarz. Specialising `l = m * |A|` gives
   `diam_ge_of_isSidon : m * n^2 ≤ (diam A + m * n) * (m + 1)`.
4. **The resulting improvement for the target, with both ceilings proved.** The elementary route
   is also formalised, so the improvement is checked rather than asserted:
   `card_sq_le_two_mul_diam` (elementary `n^2 ≤ n + 2 diam A`) feeds `real_gap_bound` and gives
   `f_lower_bound : 4n(n-1)/((n+1)(n+2)) ≤ Erdos153.f n`, whose ceiling is `lower_bound_lt_four`
   (always `< 4`). The Erdős–Turán route gives `f_lower_bound_param` and hence
   `eventually_le_f : c < 16 → ∀ᶠ n in atTop, c ≤ Erdos153.f n`, whose ceiling is
   `param_lt_sixteen` (always `< 16`). Both ceilings are stated explicitly and honestly: this
   family of arguments cannot decide the conjecture, which asks for *every* constant.
5. **A reusable finite-search principle and three exact values.** `f_eq_of_search` packages the
   cut-off argument (a competitor of energy below `v` must have diameter at most `D`, via
   `four_mul_diam_sq_le` and `exists_translate`) so that any exact value can be certified from a
   `decide` classification plus one gap-energy computation. Instantiated three times:
   `f_two : Erdos153.f 2 = 2/3`, `f_three : Erdos153.f 3 = 4/3`, `f_four : Erdos153.f 4 = 9/5`.
   These are exact values of the target's own function and also serve as non-vacuity witnesses
   for the whole interface.
6. **Honest identification with the standard library.** `nth_eq_natNth` proves that the
   auxiliary enumeration `nth A` used throughout *is* Mathlib's `Nat.nth (· ∈ A)`, so nothing
   here is a hidden re-definition and every result transfers to the `Nat.nth` API and back.

## What is *not* delivered

The conjecture is untouched: `Erdos153.erdos_153` is still open, and nothing here decides the
`answer(sorry)` slot. The best asymptotic bound obtained is `f n ≥ 16 - o(1)`, and
`param_lt_sixteen` proves that this particular route can never do better than 16, so a solver
will need a genuinely different idea (some control on the *variance* of the gaps of `A + A`,
not only on their sum) to push the bound to infinity. No claim is made in either direction
about the truth of the conjecture.

## References

- https://www.erdosproblems.com/153
- https://github.com/google-deepmind/formal-conjectures — the task pool file
  `FormalConjectures/ErdosProblems/153.lean` (definition `Erdos153.f`, theorem
  `Erdos153.erdos_153`) and `FormalConjecturesForMathlib/Combinatorics/Basic.lean`
  (definition `IsSidon`, `Finset.IsSidon.insert_ge_max'`, the `Decidable` instance for
  `IsSidon` on a `Finset`).
- https://leanprover-community.github.io/mathlib4_docs/ — Mathlib API used
  (`Finset.orderEmbOfFin`, `Nat.nth`, `sq_sum_le_card_mul_sum_sq`, `Finset.sum_equiv`,
  `Finset.sum_image`, `Nat.cast_choose_two`, `Finset.diag_union_offDiag`).
- https://en.wikipedia.org/wiki/Sidon_sequence — background on the Erdős–Turán bound
  `|A| ≤ N^{1/2} + N^{1/4} + 1` for a Sidon set `A ⊆ [1, N]`, whose window/second-moment proof
  is the argument formalised here as `erdos_turan_ineq`. The Lean proof was written from the
  standard double-counting argument, not transcribed from any source text.
- [ESS94] P. Erdős, A. Sárközy, V. T. Sós, *On sum sets of Sidon sets, I*, Journal of Number
  Theory 47 (1994), 329–347 — the reference cited by the pool file. Consulted only through the
  pool file's own citation; no material from it is reproduced here.

## Originality and AI assistance

All Lean code in this contribution is original work written for this submission. No proof,
statement, or proof script was copied from another repository, from a `formal_proof` link, or
from any third party's formalisation; in particular no `formal_proof` URL attached to this
target was opened or used. The mathematics is classical and in the public domain (Cauchy–Schwarz
on telescoped gaps; the Erdős–Turán window/second-moment count for Sidon sets); the
formalisation — the statements, the definitions `gapEnergy`, `nth`, `windowCount`, the
finite-search principle `f_eq_of_search`, and every proof — is ours.

This contribution was produced with AI assistance: the author used Anthropic's Claude (via
Claude Code) to draft, iterate and repair the Lean proofs. Every declaration was compiled and
checked in the pinned environment before submission (0 errors, 0 warnings), and every
declaration was audited with `#print axioms`, each returning a subset of
`[propext, Classical.choice, Quot.sound]`; the `#print axioms` lines were removed from the
submitted file afterwards. No `sorry`, `admit`, `native_decide`, `set_option`, `partial` or
`unsafe` appears in the file. Numeric claims in the module docstring (the values 2/3, 4/3, 9/5,
the constants 4 and 16 and their ceilings) are each backed by a compiled declaration in the same
file rather than by prose.
