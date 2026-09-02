# Sources — Erdős 1135 (the 3x+1 problem), `Contribution.Erdos1135CollatzDescent`

## Target

- Reward theorem `Erdos1135.erdos_1135` in `FormalConjectures/ErdosProblems/1135.lean`; its type is
  `type_of% CollatzConjecture.collatz_conjecture`, defined in
  `FormalConjectures/Wikipedia/CollatzConjecture.lean`, i.e.
  `∀ (n : ℕ), n > 0 → ∃ m, collatzStep^[m] n = 1` with
  `collatzStep n = if Even n then n / 2 else 3 * n + 1`.
  (`#check @Erdos1135.erdos_1135` prints `∀ n > 0, ∃ m, collatzStep^[m] n = 1`.)
- Problem page: https://www.erdosproblems.com/1135

## Originality

All statements and all proofs in `CW_erdos_1135.lean` are original work written for this
submission. Nothing was copied, transcribed or machine-translated from any source: not from the
papers cited below, not from Mathlib, not from any other Lean project, blog post, GitHub
repository or AI-generated corpus. The references below supply the *mathematical ideas* — the
shortcut map, its affine behaviour on residue classes mod a power of two, the descent reduction —
which are classical and are credited as such; the Lean statements (`Reaches1`, `collatzShortcut`,
`oddCount`, `reachesOneIn`, `reaches1_of_descent_above`, `exists_descent_of_mod`, …), their
formulations, and every tactic proof are mine.

## Mathematical sources

- Terras, R., *A stopping time problem on the positive integers*, Acta Arithmetica 30 (1976),
  241-252. https://doi.org/10.4064/aa-30-3-241-252
  Source of the shortcut map `T(n) = n/2` (even), `(3n+1)/2` (odd) and of the structural fact
  formalised here as `iterate_collatzShortcut_add_two_pow_mul`: `T^[k]` is affine on each residue
  class mod `2^k`, with slope `3^(number of odd steps)`. The classical statement is usually phrased
  via parity vectors; the `oddCount` formulation and every Lean proof in the file are my own.
  No proof text was transcribed from the paper.
- Lagarias, J. C., *The 3x+1 problem and its generalizations*, Amer. Math. Monthly 92 (1985), 3-23.
  https://doi.org/10.1080/00029890.1985.11971528
  Survey (it treats both the `3n+1` map and the shortcut map); background for the folklore "most
  residue classes mod a power of two descend", which `erdos_1135_of_descent_mod_sixteen` makes
  precise at modulus 16 (13 of 16 classes settled).
- https://en.wikipedia.org/wiki/Collatz_conjecture
  Statement; the `1 → 4 → 2 → 1` cycle used in the backwards direction of `reaches1_step_iff`;
  the orbit of 27, whose length motivated the fuel bound 120 in the `Reaches1 27` example.

## Novelty check (G4)

- `grep -ril collatz` over the pinned Mathlib source tree
  (`.lake/packages/mathlib/Mathlib`) returns no files (exit status 1, zero hits). Mathlib has no
  Collatz content, so nothing stated about `collatzStep`, `collatzShortcut`, `oddCount` or
  `Reaches1` can be a renamed Mathlib lemma.
- I looked for the one genuine overlap and removed it. My first draft carried a generic lemma
  "the orbit of a positive number under a positivity-preserving map is positive"; that is exactly
  `Set.MapsTo.iterate` (`Mathlib/Data/Set/Function.lean:156`, confirmed at that line in the pinned
  tree). I deleted my version, and `reaches1_of_descent_above` now calls Mathlib's lemma instead.
  Only the bespoke one-step facts `collatzStep_pos` / `collatzShortcut_pos` remain.

## Verification performed

- Compiled with the pinned toolchain (`leanprover/lean4:v4.27.0`):
  `lake env lean CW_erdos_1135.lean` exits 0 with **zero** output — no errors, no warnings, no
  linter hits. 443 lines, 30 declarations (26 named plus 4 `example`s), all inside the single
  namespace `Contribution.Erdos1135CollatzDescent`.
- Axiom audit: I appended `#print axioms` for all 26 named declarations and recompiled; every one
  reports exactly `[propext, Classical.choice, Quot.sound]`. The four anonymous `example`s were
  audited in a throwaway copy in which they are given names — all four report exactly those three
  axioms as well. No `sorryAx` (so nothing leaks in from the sorried target — `type_of%` takes
  only the type) and no `Lean.ofReduceBool`, which confirms that every `decide` in the file is
  real kernel evaluation rather than compiled evaluation. The `#print axioms` lines were then
  removed and the file recompiled to zero output.
- G1 checked by execution, not by reading: in a probe I wrote the reward obligation out longhand,
  `∀ (n : ℕ), n > 0 → ∃ m, CollatzConjecture.collatzStep^[m] n = 1`, and closed it with
  `erdos_1135_of_descent_mod_sixteen h`. It elaborates, and the resulting declaration is itself
  axiom-clean.
- Non-vacuity of the residual obligation: `∃ m, 0 < m ∧ collatzStep^[m] 7 < 7` discharged
  concretely (m = 11, `decide`), so the hypothesis of the headline is satisfiable class by class,
  not empty.
- Reusability of `exists_descent_of_mod` checked at a modulus used nowhere in the file:
  `n % 32 = 11` (k = 5), closed by the same pattern (`decide` for `hpow`, `decide` for the value
  `collatzShortcut^[5] 11 = 10`, then `omega`).
- Banned-token scan (`sorry`, `admit`, `axiom`, `native_decide`, `#eval`, `unsafe`, `partial`,
  `extern`, `implemented_by`, `set_option`): clean, including inside prose. Plain LF, UTF-8, no
  BOM, no control or bidi characters.

## Changes made in the repair passes

**First pass.** The version before it was returned FIX for two `set_option maxRecDepth 8000 in`
lines (a banned token) and for a set of one-tactic wrapper lemmas presented as content. Both were
addressed: the `set_option` lines are gone (the examples compile without them), and the file was
rebuilt around the Terras affine theorem so that the hand-written per-class rewrite chains
(`iterate_collatzStep_four_mul_add_one`, `iterate_collatzStep_sixteen_mul_add_three`, the three
`exists_descent_of_*` class lemmas), the `reaches1_one` wrapper and the
`dropsBelowIn` / `exists_iterate_lt_of_dropsBelowIn` thin specialisation were all deleted and
subsumed.

**Second pass (this one) — the docstring was corrected after review.** The reviewer found one
sentence in the module docstring that was false in the pinned environment, and it has been
rewritten to say what actually happens:

- The docstring claimed that *both* hypotheses of `exists_descent_of_mod` "are closed by `decide`
  in the kernel for any concrete `k` and `r`". Only `hpow` is. `hrep` is
  `collatzShortcut^[k] r < r + n / 2 ^ k`, which still mentions the universally quantified `n`, so
  `decide` fails on it with `Expected type must not contain free variables`. The docstring now
  states that `hpow` is closed outright by `decide`, while `hrep` is closed by a `decide` for the
  *value* `collatzShortcut^[k] r` followed by `omega` — which is exactly what all four use sites
  in the file have always done. The same false claim appeared a second time, in the declaration
  docstring of `exists_descent_of_mod`; it is corrected there too, and the matching phrase "each
  one costs two `decide` calls" on the headline theorem now reads "two `decide` calls and an
  `omega`".
- Unsupportable universal claims about the world were softened to claims that are checkable:
  "All of the literature (Terras, Lagarias) works with the shortcut map" became "the literature
  this file follows (Terras 1976, and the shortcut-map half of Lagarias' 1985 survey) …, and
  nothing in Mathlib or in this repository connects the two maps" (Lagarias' survey treats both
  maps); "the usually-asserted, never-checked equivalence" became "an equivalence that is
  routinely taken for granted, and that appears neither in Mathlib nor elsewhere in this
  repository"; "what *every* known result about the 3x+1 problem does" and "the reduction every
  attack on the problem uses" were narrowed to the classical results this file actually follows.
- The four branch lemmas (`collatzStep_two_mul`, `collatzStep_two_mul_add_one`,
  `collatzShortcut_two_mul`, `collatzShortcut_two_mul_add_one`) were exporting **global** `@[simp]`
  attributes about `CollatzConjecture.collatzStep` from a contribution file. They are now
  `@[local simp]`, so importing this file no longer changes the ambient `simp` set; they are
  load-bearing internally (the affine-theorem proof rewrites with them) and were therefore kept,
  as both reviewers advised.
- The dead `0 < m` conjunct in the `hhigh` hypothesis of `reaches1_of_descent_above` was removed.
  It was never used in the proof (a descent with `m = 0` is impossible anyway, since `f^[0] n = n`
  is not `< n`), so dropping it strictly strengthens the engine; the two call sites and the two
  worked-assembly examples were adjusted accordingly.

No declaration was deleted in this pass: the reviewer reported no Mathlib duplicates and nothing
unsound or unusable.

## AI assistance

This contribution was produced with AI assistance: I am Claude (Anthropic), and I wrote the Lean
statements, the proofs, the documentation and this file. Nothing here rests on my say-so — every
claim above was checked by running the Lean compiler and the axiom probe described in the
Verification section. The mathematics (Terras' affine structure of the shortcut map; the census of
residue classes mod 16) is classical and credited above; the Lean formalisation, as stated under
Originality, is original work written for this submission.
