# Finite reduction and maximal-index multiplicity for Erdős 274

## Target and reusable results

The target is `Erdos274.herzog_schonheim`: a nontrivial finite exact coset partition of an arbitrary group must have repeated subgroup indices. The contribution uses the exact official `Erdos274.Group.ExactCovering` structure.

All declarations are in `Contribution.Erdos274Finite`.

- `finiteQuotientCover`, `finite_quotient`, and `finiteQuotientCover_index` construct a finite quotient of the actual input covering, preserving every index. `finite_counterexample` transports pairwise distinct indices. `herzog_schonheim_iff_finite` proves the full target equivalent to its restriction to finite groups.
- `sum_inv_index` proves the exact identity `sum_i 1/[G:H_i] = 1` without assuming the original ambient group finite.
- `maximal_prime_power_multiplicity` proves that if the numerically largest index is `p^a`, with `p` prime and `a > 0`, its multiplicity is divisible by `p` and at least `p`. Smaller indices are unrestricted. `herzog_schonheim_maximal_prime_power` gives the literal repeated-index conclusion.
- `common_base_multiplicity` proves the corresponding divisibility by an arbitrary integer base `b >= 2` when all indices are powers of `b`. `herzog_schonheim_common_base` gives the target conclusion, and `herzog_schonheim_prime_power_order` specializes it to all finite prime-power order groups.

The final checked example shows how a solver gets at least three maximal-index parts when the largest index is nine. The general arithmetic lemmas are exposed for use with other reciprocal identities.

## Why this is one contribution

The same finite-quotient construction produces the mass identity used by both multiplicity arguments. The package removes the infinite-ambient-group reduction and prime-power-maximum branch from subsequent work. Supporting facts are bundled, not submitted as separate claims.

## Proof and limitations

Neumann's finite-index-subcover theorem plus disjointness forces every part to have finite index. The normal core of their intersection has finite index and lies in every part. A surjective homomorphism whose kernel lies in each part preserves the partition and all indices. Counting in the finite quotient proves the reciprocal identity.

For a largest index `p^a`, clear denominators using their least common multiple `L`. Its `p`-adic exponent is exactly `a`. Terms from smaller indices are divisible by `p`; maximal terms equal `L/p^a`, which is not divisible by `p`. Thus the number of maximal terms is divisible by `p`. For common-base powers, multiplication by the largest power gives the analogous argument modulo the base.

This does **not** prove the general Herzog–Schönheim conjecture. In particular it does not settle general mixed-index partitions whose largest index is not a prime power. No commutativity, conjectural analytic hypothesis, bounded search result, or unresolved upstream theorem is used in the proofs.

## Sources, overlap, and attribution

1. [Official pinned target bundle](https://github.com/conjectures-io/conjectures-tasks/tree/275ef4824c41d41f97ac4e9fff95ca471de9341d/pool/tier-1/erdos-274-herzog-schonheim-formalized) and [problem page](https://conjectures.io/problems/erdos274-herzog-schonheim).
2. Leo Margolis and Ofir Schnabel, [The Herzog-Schönheim Conjecture for small groups and harmonic subgroups](https://arxiv.org/html/1803.03569v1), introduction and Lemma 2.3: classical finite reduction and reciprocal-index context. No result about groups of order below 1440 is claimed or used here.
3. Pinned Mathlib [CosetCover](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/CosetCover.lean), especially `Subgroup.leftCoset_cover_filter_FiniteIndex`; [Index](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/GroupTheory/Index.lean), for finite intersections, normal cores, quotient finiteness, and index preservation; and [FinsetLemmas](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/GCDMonoid/FinsetLemmas.lean), for the valuation of a finite least common multiple.
4. Murali Menon's [finite-abelian formalization](https://github.com/Jostamon/erdos274-hs-abelian/tree/2ab8a2e39e7dd7836adf577b52555f069244466f), including `ExactCovering.lean`, was inspected for overlap. It already has quotient transport under a supplied common kernel. That construction is not claimed as a new mathematical idea here. Our map is reproved against the official structure, and the submitted delta includes automatic finite-index/core construction, the full target equivalence, and arbitrary-group arithmetic multiplicity results. No abelian theorem or proof from that repository is imported or assumed.

At contribution base `22019a3051609bca40902de7ac3c9764ac0326d7`, this target has no prior published mathematical contribution. No contribution parents are used. The established Mathlib lemmas above are dependencies, not claimed discoveries.

The mathematics is classical or elementary; no worldwide priority is asserted. The offered novelty is the checked, standalone, target-compatible development and reusable combination of these results, not a claim to have discovered the finite-group reduction. Reviewers determine material novelty under the contribution contract.

Development was AI-assisted with ChatGPT GPT-6 Astra Pro, using Lean and exact-integer exploratory checks. Those exploratory checks are not proof dependencies and are not submitted as certificates. The source has been freshly elaborated, and all 28 named declarations have a transitive axiom audit restricted to `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduction and license

The file stands alone; it imports only Mathlib and the official Erdős 274 module. It has no sibling-file imports or private-project dependencies.

Pinned environment: Lean `4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; audited Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`; task submodule `275ef4824c41d41f97ac4e9fff95ca471de9341d`.

Run the official `contrib check` and `contrib elaborate --workspace <pinned-workspace>` on the promoted directory. Audit commands and local research records are intentionally not included in the public source.

The contributed source is released under Apache-2.0; `license.txt` contains the license. Imported dependencies retain their respective upstream notices.
