# Complete-factor stencil extension to the pending Erdős686 contribution

This revision adds a focused, AI-assisted formalization from research sessions20
and21. The exact statements, complete factorization hypotheses, concrete use sites
and limitations are in [stencil-guide.md](stencil-guide.md). The standalone Lean
file preserves the earlier contribution and adds the dense reduction,
complementary divisor, coefficient-dependent bound and unscaled special-case
exclusion. Only their necessary supporting lemmas are added.

These results were not present in the previous PR head
[4a236cb](https://github.com/Dom1W1ns/conjectures-contribution/commit/4a236cb9e9bfbcdf79bba42df5c00657fb5b8d0e).
The target's canonical index still has no published contribution at base
`4ed0217e9791408469af21821d37e3a0aa31bef1`. This replaces the previous **unmerged**
record `3bc3477f5593f193b2fe64a4f9d838bffe30f7841dcedebe1a35f1420eeb072f` in the
same [PR141](https://github.com/conjectures-io/conjectures-contribution/pull/141).
That record and the earlier record remain in Git history. No published record is
modified, no duplicate PR is opened, and no separate credit is sought for retained
proofs. `parents` remains empty because there is no published parent to name.

The new proofs use polynomial arithmetic, order and coprimality from the pinned
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474).
The formalization and local elimination were developed in this research; no
worldwide mathematical novelty or literature-priority determination is claimed.
The session20 exclusion now reuses the session21 dense reduction, instead of
repeating the same elimination. Three implementation lemmas and the elementary
contradiction are private. The selected source mapping is in source_manifest.json.

**The full target remains unresolved.** `T=2*d^2*e*c` retains unbounded factors.
The external restricted exclusion does not add remaining k5 coverage, and no
external finite search is a Lean premise. Recognition or payment is not claimed.

## Earlier contribution provenance (retained)

# Expanded contribution: verified length-five square-pair exclusions

This revision adds two completed proof modules to the six research modules and the ratio bridge already collected here. The new proofs were developed with AI assistance in this research session. They use elementary polynomial identities, integer order, rational-square arithmetic, and a kernel-checked finite bracketing certificate; they do not use the missing class-group or rank certificates.

The key new declaration is `Contribution.Erdos686TwentyFive.SquarePair.cross_ratios_nonsquare`. Given a hypothetical admissible length-five multiplier-25 witness, it proves that every one of the 25 cross-block term ratios is a nonsquare in Q. Equivalently, `k5_square_pair_exclusion` excludes any witness with `n+i=d*a^2` and `m+j=d*b^2` for positive integers d,a,b and 1<=i,j<=5. The quantifiers are unbounded in n,m,d,a,b. A later solver may use this to discard a square-pair branch before performing arithmetic geometry. `SquareCenter.common_square_factor_exclusion` retains the shorter direct proof for the middle terms. No completeness statement covering all other squareclasses is claimed.

`SquarePair.finite_five_exclusion` proves that there is no length-five witness with 0<=n<16384, for any natural m, using strict brackets and monotonicity. This interval was already inside the research's computationally excluded region; its new role is a kernel-checked small-case component of the unbounded square-pair theorem. It is not advertised as a larger numerical search.

The underlying ingredients are standard algebra and the pinned [Mathlib library](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The new target-specific argument and its formalization are supplied here; no claim of a worldwide literature-priority determination is made.

## Revision lineage

This is the expanded pending package for [PR #141](https://github.com/conjectures-io/conjectures-contribution/pull/141). Its earlier unmerged record had ID `f300f0b627040a577cd014051efb359d150817aa2ac6e225a1e2b6eee3a286f9`, at [commit 52f2c70](https://github.com/Dom1W1ns/conjectures-contribution/tree/52f2c70c4abc31b60222f0f02b3dcb0333424a5e/contributions/erdos-686-variants-twenty-five/f300f0b627040a577cd014051efb359d150817aa2ac6e225a1e2b6eee3a286f9). That record is preserved in Git history and the local archive. It was not merged or in the target's published index when this revision was prepared. The current PR replaces that pending package with this newly promoted record, leaving one contribution directory in its diff against canonical main. No second reward or duplicate credit is sought for the earlier modules. There are no published parent contributions at the checked base.

The full k=5 problem, all 16 covering cases, and the all-length bounty remain unresolved. A square product does not by itself force a square cross-pair. The optional isogeny screen only rejects small-prime-isogeny shortcuts; it is not a rank bound or a Lean premise.

## Earlier modules and sources (preserved)

# Provenance, use, and limits

This is one combined partial contribution for the [multiplier-25 target](https://conjectures.io/problems/erdos686-erdos-686-variants-twenty-five), prepared by GitHub user Dom1W1ns with AI assistance. It is not a solution of the existential statement over all lengths. The earlier formal contribution collected its completed original Lean modules; this revision adds only the selected stencil API, without importing diagnostic copies.

## Concrete use by a later solver

All names are under `Contribution.Erdos686TwentyFive` unless qualified further.

- `k6_exclusion` and `k6_ratio_exclusion` rule out length six for every admissible pair of natural numbers. It is a complete fixed-length result, with an elementary polynomial and congruence argument followed by a kernel-checked finite decision. A solver may remove this length from a case split; this does not remove the other lengths.
- `lower_prime_le_width` and `upper_prime_le_width` constrain prime divisors of the two blocks by their total width, with the necessary exception for the multiplier's prime5. The compositeness corollaries make the additional span hypotheses explicit.
- `square_dvd_transport_of_coprime_complement` supplies a squared divisibility step when its coprimality hypothesis is established. It does not assert that hypothesis for every prime allocation.
- The three `higherContact_*` lemmas check the algebraic divisibility mechanism of a supplied contact certificate. The accompanying obstruction note explains why uniform full-support polynomial contact does not close the k=5 problem. These supporting lemmas are retained for reproducibility, with no separate reward claim for generic wrappers.
- `centeredFive_to_quotient` maps a nonzero centered rational solution to the explicit sextic equation. It supplies the algebraic step needed before the covering-curve analysis. It does not prove completeness of that analysis.
- `NormRelationBridge.relation_injective` and `relation_finrank_le` prove the abstract F2-linear consequence of a coefficient-five relation. The exact permutation certificate is supplied separately; its arithmetic class-group instantiation is not formalized in Lean and no numerical rank bound is claimed.

## Mathematical and software sources

- The target and bibliographic context are from [Erdős Problem686](https://www.erdosproblems.com/686) and the [pinned task repository](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-formalized).
- The formal proofs use [Mathlib at0df444a360eaa60ab8c11dca51a86af692955474](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474), with Lean4.33.1. The project source pin is [Formal Conjectures6a786f997e18e8f095762a2830d191b7e25e505e](https://github.com/google-deepmind/formal-conjectures/tree/6a786f997e18e8f095762a2830d191b7e25e505e).
- Related background includes [Bennett–van Luijk, Squares from blocks of consecutive integers](https://doi.org/10.1016/j.indag.2011.11.002) and [Erdős–Straus, On Products of Consecutive Integers](https://www.renyi.hu/~p_erdos/1977-18.pdf). Their theorems are not imported as unproved hypotheses.
- The written class-group correspondence interpretation uses [Etienne, Computing class groups by induction with generalised norm relations](https://arxiv.org/html/2411.13124v2), and the certification limitations are informed by [Biasse–Fieker–Hofmann–Page](https://www.normalesup.org/~page/Recherche/Documents/articles/brauer.pdf). Our explicit finite-group matrices, field specializations and accompanying checkers were developed during this work. These computational results are not presented as Lean theorems.
- The Cayley-resolvent construction uses the classical quintic-invariant setting discussed by [Dummit](https://site.uvm.edu/ddummit/files/2021/04/Solving_Solvable_Quintics__Math_Comp_57_no195_1991__pp_387_401.pdf). The included symbolic program derives its coefficients anew and checks polynomial identities. The quartic pair-product resolvent is classical.

No claim of priority is made for the underlying elementary arguments or classical constructions. The submitted delta is the target-specific formalization, its interfaces, and the explicitly scoped computational handoff. No source from the friend's erdos790 repository is incorporated. All new proof bodies were generated with AI assistance and checked against the stated environment.

At upstream base `be220ff2519ecfd61b28ba9e477321e4287ef6b4`, the official contribution listing contains no published records for this target. Therefore `parents` is empty. Recognition and payment remain decisions of the project under its [contribution contract](https://github.com/conjectures-io/conjectures-contribution/blob/main/contribution-contract.md).
