# Provenance and intended use

This is an AI-assisted Lean formalization of previously published length-eight and length-twelve exclusions for Erdős 686, multiplier 25. The mathematical exclusions and explicit bounds were posted by **IRAMBONA**, 5 October 2026, in [forum post 9291](https://www.erdosproblems.com/forum/thread/686#post-9291), following Vjeko Kovač's earlier even-length expansion argument. That post discloses Claude assistance. We do not claim these mathematical cases as new discoveries.

The new contribution is a standalone, kernel-checked handoff in the exact pinned environment. `no_ratio_eight` and `no_ratio_twelve` use the rational `Finset.Icc` product notation of the [target](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample). `bound8` and `bound12` expose the finite starting-point bounds 67 and 1660. The finite-check declarations discharge the entire remaining ranges, not just a fixed box of both starting points.

The length-eight theorem needs no disjointness hypothesis. The length-twelve theorem also needs no disjointness hypothesis: there is no product equality for any natural m,n.

## Adaptation and lineage

The integer-square gap argument and bracketing-certificate method adapt our published [length-six contribution](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-686-variants-four/1e9266022bf5586a144c4e5c2901d43cfb58994fe3184e45a38113e4db7a98e1). It is declared in `parents`, including for the ratio-25 contribution, because the verification framework is reused across targets. The new module is self-contained and does not import that file. No credit is requested again for its length-six result.

For length twelve, this formalization uses a positive-coefficient identity to prove that G(u)r(v)-G(v)r(u)>0 for u>v>=169, where G(w)=w^3-143w^2+4147w-24453 and r(w)=429w^2-14274w+94501. This avoids the source argument's cube-root estimates. Integer-square gaps would force G(u)=tG(v) and r(u)=t^2 r(v), contradicting that inequality. The polynomial identity is checked by `ring`; the resulting numerical bounds are the same as the published ones.

The bracketing tables were generated with exact Python integer arithmetic. A recursive Boolean checker visits each length-twelve row once, and an induction theorem proves its soundness. `decide +kernel` verifies the concrete tables. SymPy assisted expansion of the cross-multiplication identity. Neither Python nor SymPy is a Lean premise; no native-computation axiom is used.

The Lean code and adaptation were developed with OpenAI Codex assistance. The signer remains responsible for correctness and provenance. [Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474), with Lean 4.33.1, supplies the arithmetic tactics and finite-product API.

## Novelty boundary

We checked canonical main at `62786ab273dc804593a741d6900224497f323a64`: the ratio-4 contributions cover lengths 2,3,4,6 and bounded search; the ratio-25 contribution covers lengths 2,4. Neither directory contains the all-starting-points length-eight or length-twelve results. The pinned source `6a786f997e18e8f095762a2830d191b7e25e505e` also contains neither proof.

We inspected related open [PR #141](https://github.com/conjectures-io/conjectures-contribution/pull/141) at `8ab9a0460eea0cf90d844499e005fd9e35744bd9`. It supplies ratio-25 length-six and length-five/transport/stencil results, not these cases. No result or implementation from that PR is used here.

Lengths eight and twelve are bundled as one contribution for this target. This is partial progress only; other lengths remain open. Recognition and payment are separate decisions under the contribution contract.
