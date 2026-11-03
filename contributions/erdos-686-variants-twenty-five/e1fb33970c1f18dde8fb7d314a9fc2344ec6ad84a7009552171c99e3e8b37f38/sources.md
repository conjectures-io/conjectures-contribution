# Provenance and intended use

Original Lean formalization developed in this research chat with OpenAI Codex assistance. The signer remains responsible for the work. The elementary square-gap argument is not claimed to be a new number-theory result.

Target: [Erdős 686, ratio 25](https://www.erdosproblems.com/686), with its exact rational-product formulation in the [pinned task](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-counterexample).

The theorems `no_ratio_twenty_five_two` and `no_ratio_twenty_five_four` directly discharge the k=2 and k=4 cases of the rational-product equation. They hold for every natural m,n, even without disjointness. The integer product lemmas are available separately.

The identities are (2m+3)^2-1 = 4(m+1)(m+2), and (m^2+5m+5)^2-1 = (m+1)(m+2)(m+3)(m+4). A solution would put a square strictly between consecutive squares below 25x^2.

We checked the [published target directory](https://github.com/conjectures-io/conjectures-contribution/tree/4ed0217e9791408469af21821d37e3a0aa31bef1/contributions/erdos-686-variants-twenty-five) on 2026-11-03: no contributions were listed. Related ratio-4 contributions exist, but this implementation was developed independently in the same chat before this preparation and imports none of them. No parent contribution was used.

A final check of open pull requests found [PR #141](https://github.com/conjectures-io/conjectures-contribution/pull/141), inspected at commit `8ab9a0460eea0cf90d844499e005fd9e35744bd9`. Its submitted module supplies a ratio-25 length-six exclusion and length-five/prime-transport/stencil interfaces; it does not state the length-two or length-four exclusions supplied here. That unmerged work is acknowledged as related prior public work, not used as a dependency. Our contribution makes no claim to its results or to a complete ratio-25 refutation.

[Mathlib](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) supplies the arithmetic tactics and finite-product API. The proof does not invoke an open target theorem. These are partial exclusions, not a solution of the unrestricted problem.
