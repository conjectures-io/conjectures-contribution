# Sources and handoff

## Target and provenance

- Ben Green, [100 open problems, Problem 12](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.12).
- The exact Lean target is [`Green12.green_12`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/12.lean), pinned by the Conjectures task pool.
- This contribution is original, tool-assisted work by the submitting author. No prior Green 12
  contribution was present in `contributions/green-12/index.md` at the base commit. The Lean
  implementation uses only standard Mathlib finite-cardinality and ordered-field lemmas.

## Kernel-checked result submitted here

Write `N = |G|`, `a = |A|`, and let `validTuples A` be exactly the finite set in the right-hand
side of `Green12.green_12`. The file constructs two families:

1. choose `u : Fin 5 → A` and `g : G`, then set `xᵢ = uᵢ - g` and every `yⱼ = g`;
2. choose a nonconstant `u : Fin 5 → A` and `g : G`, then set every `xᵢ = g` and
   `yⱼ = uⱼ - g`.

Every resulting tuple is valid. Both parametrizations are injective, and equality between a
constant-right tuple and a constant-left tuple forces both `A`-valued words to be constant.
Omitting constant words from the second family therefore makes the union disjoint and proves

```text
|validTuples A| ≥ N (2a^5 - a).
```

The final theorem `green12_of_card_condition` converts this integer count to the exact real
normalization in the target and proves Green 12 whenever

```text
a^15 ≤ N^6 (2a^5 - a).
```

The file is self-contained and imports the pinned Green 12 module. It contains no `sorry`,
custom axiom, `native_decide`, or unsafe declaration. An explicit axiom audit of the final theorem
reported only `propext`, `Classical.choice`, and `Quot.sound`.

## Related exact research and limits

The inequality above is the analytic tail used in a separate exact-computation campaign. That
campaign found and independently replayed the following stronger special-case evidence:

- the full Green 12 inequality for every finite abelian group when `|A| ≤ 9`, combining this
  analytic tail with exhaustive finite-prefix enumeration;
- the full inequality whenever `|G \ A| ≤ 4`, and the analytic dense regime
  `|G| ≥ |G \ A|^2 + 12|G \ A|`;
- an unconditional density frontier approximately `0.6290672` from exact rational Fourier and
  graph certificates;
- exact weighted fixed-group inequalities through several abelian groups of order at most seven;
- exact obstruction examples showing that naive termwise positivity, unrestricted PSD-kernel
  relaxation, and monotone translation smoothing do not by themselves prove the target.

Those computer-assisted claims are disclosed as research context only: their Python/C++
certificates and enumeration logs are not part of this immutable contribution, so this PR does
not ask Lean or the contribution reviewer to recognize them as kernel-checked declarations.
Nothing here claims the unrestricted Green 12 conjecture is solved.

## Intended use

`card_validTuples_ge_card_mul` is a reusable lower bound for every finite abelian group and every
subset. `green12_of_card_condition` lets a later solver discharge the original target immediately
after proving the single natural-number condition above for the class under study. The explicit
embeddings and overlap lemma can also be extended with additional disjoint structured families.
