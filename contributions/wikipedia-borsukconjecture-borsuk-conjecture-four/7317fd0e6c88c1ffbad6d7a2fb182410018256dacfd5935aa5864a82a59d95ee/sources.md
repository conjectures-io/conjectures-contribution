# Five smaller-diameter pieces from a small planar projection

For a diameter-one set K in Euclidean four-space, this proves the five-piece conclusion if K fits in the origin-centered ball of squared radius 1/3 and its last two coordinates fit in some disk of squared radius strictly below 3/16. The conclusion uses strict extended diameters and each of the five sets lies in K. Orthogonal coordinates may be chosen before applying the theorem.

A later solver can apply Contribution.BorsukFiveSectors.five_cover_of_small_planar_projection after verifying those two geometric bounds. For a different enclosing radius R and an upper bound D on the projected diameter, sector_cover_of_projected_diameter only needs 12 R²/5 < 1 and 2 R D < 1. The construction splits the first coordinate plane into five angular sectors. The coupled_radial estimate keeps track of how much of the squared radius is available in the second plane for two points in the same sector. It gives the squared distance bound max(12 R²/5, 2 R D).

This is an AI-assisted proof developed in this Borsuk investigation with OpenAI Codex. The angular sectors and the underlying Euclidean distance identities are elementary. The contribution is the quantitative normalized covering theorem and its Lean proof. The repository target index at commit a4a026e7f77ce991d0bdd1fd33e3a206d39106a3 listed zero contributions. No prior contribution was used as a parent. We make no claim of priority in the mathematical literature.

- [Pinned contribution target](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/wikipedia-borsukconjecture-borsuk-conjecture-four-formalized)
- [Mathlib's Euclidean coordinate distance identity](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/PiL2.html)
- [Mathlib's complex argument and polar identities](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Complex/Arg.html)
- [Conjectures.io contribution index](https://github.com/conjectures-io/conjectures-contribution/blob/a4a026e7f77ce991d0bdd1fd33e3a206d39106a3/contributions/wikipedia-borsukconjecture-borsuk-conjecture-four/index.md)
