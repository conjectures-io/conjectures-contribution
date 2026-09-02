# Sources - Erdos Problem 11 contribution (`Contribution.Erdos11SquarefreeSum`)

## Problem and target
- Problem statement: https://www.erdosproblems.com/11 ("Is every odd n > 1 the sum of a squarefree number and a power of 2?", together with the `not 4 dvd n` and two-powers-of-2 variants and the finite verifications).
- Target module in this repository: `FormalConjectures/ErdosProblems/11.lean` (`Erdos11.erdos_11` and its variants `not_four_dvd`, `two_pow_two`, `finite_bound1`, `finite_bound2`, `granville_soundararajan`). Only the TYPES of `erdos_11`, `erdos_11.variants.not_four_dvd` and `erdos_11.variants.two_pow_two` are imported, via `type_of%`; none of their `sorry`-ed proofs is used (verified by `#print axioms`, see below).
- Context reference cited by the target file, not used in any proof here: A. Granville and K. Soundararajan, "A Binary Additive Problem of Erdos and the Order of 2 mod p^2", The Ramanujan Journal 2 (1998) 283-298, https://doi.org/10.1023/A:1009789013710.

## Mathlib (pinned commit in this repo's `lake-manifest.json`; https://github.com/leanprover-community/mathlib4)
Lemmas and instances used: `Nat.squarefree_mul`, `Nat.squarefree_two`, `Nat.coprime_two_left`, `Squarefree.ne_zero`, `Nat.isUnit_iff`, `Nat.odd_iff`, `Nat.even_or_odd`, `dvd_pow_self`, `squarefree_one`, and the stock decidability instance `Nat.instDecidablePredSquarefree` (used through `decide +kernel`; the file adds no decidability instance of its own).

## Novelty check (G4)
Grepped `.lake/packages/mathlib/Mathlib` for `Squarefree` occurrences together with `2 ^`, `two_mul`, `squarefree_two_mul`, and for any statement of the shape "squarefree plus a power of two"; nothing of the kind exists in Mathlib, and no bounded trial-division correctness lemma exists in `Mathlib/Data/Nat/Squarefree.lean` or `Mathlib/Algebra/Squarefree/Basic.lean`. Also grepped `FormalConjectures/` and `FormalConjecturesForMathlib/` for `IsSumOdd` / `squarefree_add_two_pow`: no collisions. The mathematics is elementary folklore (the doubling observation and the analysis mod 4); no literature was consulted for the proofs, and none of it is recorded formally anywhere in the pinned environment.

## Measurements made in this environment (not recalled, not taken from the review)
Toolchain `leanprover/lean4:v4.27.0`; command `lake env lean CW_erdos_11.lean`.
- Whole file: zero errors, zero warnings, 11.9-15.5s wall across runs, against an `import Mathlib` baseline of ~8s warm.
- `example : Squarefree 15 := by decide` FAILS here: "reduction got stuck at the `Decidable` instance `match Nat.minSqFac 15 with ...`" (reproduced verbatim).
- `example : Squarefree 15 := by decide +kernel` SUCCEEDS, at default `maxRecDepth`.
- `∀ m < 1024, Odd m → 1 < m → ∃ l ∈ Finset.range 10, 1 ≤ l ∧ Squarefree (m - 2 ^ l)` by `decide +kernel`: succeeds, ~7s over baseline, no `set_option` of any kind.
- The same search widened to `m < 4096`, `Finset.range 12`: succeeds in 64s wall (~56s over baseline), i.e. the cost is superlinear; kernel decision is roughly four orders of magnitude short of `finite_bound1` (n < 10^7), which this file therefore does not attempt.
- Truth of the searched statement independently confirmed outside Lean by a small Python trial-division check for all odd m < 4096 (no counterexample), and likewise for the direct `not 4 dvd n` search below 1024 quoted in the docstring.
- `#print axioms` on all 10 declarations: each is exactly a subset of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. The probe file was deleted afterwards and the shipped file recompiled clean.

## AI assistance (disclosure)
This file was written by Claude (Anthropic, Opus 5) running in Claude Code, as the author of the contribution. Every statement and proof is machine-checked by Lean; every empirical claim in the module docstring was measured in this environment by running the compiler, not recalled from training. This is the second revision: the first was reviewed with verdict FIX, and this revision deletes the hand-rolled computational layer (`SqFreeUpTo` / `IsSumCheck` and friends), removes the banned `set_option maxRecDepth`, corrects two false claims in the docstring, and re-points the handoff sentence, as described in the notes.

## Originality

All Lean statements and proofs in this file are original work produced for this submission and were not copied from any existing formalisation (Mathlib, FormalConjectures, another contribution, or elsewhere). Mathlib lemmas are used only as named dependencies. The docstrings and this file were corrected after adversarial review.
