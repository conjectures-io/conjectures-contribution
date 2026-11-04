# Greedy Sidon difference counts and density interfaces

This is a partial contribution to
[`Erdos340.erdos_340.variants.sub_hasPosDensity`](https://conjectures.io/problems/erdos340-erdos-340-variants-sub-hasposdensity).
It does not prove positive density, prove a counterexample, or assert a new growth
bound for the infinite greedy Sidon sequence.

## Concrete use for the target

The standalone `script.lean` supplies 71 named public theorems and seven supporting
definitions, grouped as one contribution. All names below start with `Contribution.`.

- `Erdos340.greedyPrefix_difference_card` gives the exact natural-number difference
  count `choose (n + 1) 2 + 1` for the first `n + 1` greedy terms. The supporting
  lemmas prove monotonicity, the Sidon invariant, minimality of the next term,
  positive-difference uniqueness, and the collision criterion for rejecting a term.
- `Erdos340.greedyPrefix_window_increment_tail` converts a new difference-window
  contribution into an exact count of old sequence entries in a short interval
  below the appended term. The insertion and disjointness lemmas justify the
  recurrence, with no double counting. `greedyPrefix_window_unchanged_below_gap`
  records a sufficient condition for no new differences below a cutoff.
- `Erdos340Asymptotics.prefix_density_lower_bound` applies the finite prefix count
  to the actual infinite difference set. `eventually_prefix_window_eq` proves that
  every fixed finite window is eventually exhausted by the prefixes. Its threshold
  depends on that window; no uniform rate is asserted.
- `DensityInterface.hasPosDensity_iff_limit_exists_and_lowerDensity_pos` separates
  the two outstanding analytic obligations. The uniform counting-bound interface
  yields the target only after convergence and a positive uniform tail bound have
  both been supplied. An anonymous example specializes this to the actual greedy
  difference set, keeping both assumptions explicit.
- `FixedPrefixLimit.fixedPrefix_density_tendsto_zero` and
  `fixedPrefix_density_liminf_eq_zero` establish the zero limit when the prefix is
  fixed and the cutoff grows. They identify a quantifier error to avoid when using
  finite-prefix computations. They are not statements about the density of the
  full infinite difference set.

The finite windows are `[0, N)` in the natural numbers, with truncated natural
subtraction and a single zero difference, matching the pinned target. The prefix
index `n` counts `n + 1` terms; it is not a value cutoff. The source also includes
an anonymous example applying the finite-prefix lower bound to the infinite set.

## Provenance and formalization delta

The canonical definitions of `Finset.greedySidon`, `IsSidon`, and set density are
imported from the pinned Formal Conjectures environment. Their development and the
problem statement are upstream work, not claimed as new here:

- [Formal Conjectures problem 340 at the upstream base](https://github.com/google-deepmind/formal-conjectures/blob/7d1a8c9912747679d0093f6d1216420c33ee5ffa/FormalConjectures/ErdosProblems/340.lean).
- [The pinned task and exact challenge](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-340-variants-sub-hasposdensity-formalized).
- [Mathlib at the contribution toolchain pin](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).

In particular, the pinned density library already proves
`Nat.hasDensity_zero_of_finite`. The two fixed-prefix limit results here are
specializations to the contribution's finite-window density expression and are
integration checks, not new asymptotic mathematics. The upstream combinatorics
library also supplies Sidon insertion and three-term progression results, used
as foundations for the concrete rejection and difference-count interfaces. Those
upstream facts are not claimed as new contributions.

The contribution's proofs and interfaces were developed with AI assistance using
standard Sidon counting, finite-set identities, and elementary filter-limit
arguments. No originality claim is made for those underlying mathematical facts.
The submitted delta is their explicit, checked integration with the canonical
greedy construction: exact insertion/window recurrences, finite-window exhaustion,
and clearly separated sufficient hypotheses for the density target.

At contribution repository base
`be220ff2519ecfd61b28ba9e477321e4287ef6b4`, the
[target index lists no published contributions](https://github.com/conjectures-io/conjectures-contribution/blob/be220ff2519ecfd61b28ba9e477321e4287ef6b4/contributions/erdos-340-variants-sub-hasposdensity/index.md).
There are no parent contributions. The previously local source modules are
consolidated without duplicating their shared structural declarations. The
submission contains the 59 structural and finite-window theorems, ten exhaustion
and density-interface theorems, and two fixed-prefix limit theorems. Counts are an
inventory, not a claim of 71 independent mathematical advances or reward units.

## Verification and remaining gap

The repository pins Lean `4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and audited Formal Conjectures
`6a786f997e18e8f095762a2830d191b7e25e505e`. The script has no sibling imports;
it uses the actual imported greedy sequence rather than a replacement definition.
The public-declaration axiom audit must contain only `propext`, `Classical.choice`,
and `Quot.sound`. The open target theorem is not a proof dependency.

No numerical experiments are submitted as kernel-certified statements. In
particular, a finite observed density is not offered as an asymptotic bound. The
uniform positive count bound and convergence for the full difference set remain
unproved. Recognition and any eventual reward are governed by the repository's
[contribution contract](https://github.com/conjectures-io/conjectures-contribution/blob/main/contribution-contract.md).
