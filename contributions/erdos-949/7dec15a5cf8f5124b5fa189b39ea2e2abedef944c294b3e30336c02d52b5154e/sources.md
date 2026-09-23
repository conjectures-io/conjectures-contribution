# Sources

**What this is for.** The #S = 𝔠 case is the whole open content of Erdős 949. This contribution
isolates the reusable engine of the existing proof and settles every "structured" subclass. A later
solver only has to handle sum-free `S` with `#S = 𝔠`, `S` unbounded above and below, and
`span_ℚ S = ⊤`.

**Declarations (namespace `Contribution.Erdos949Partial`).**
- `exists_of_small_traces` — general Zorn criterion: if `#X = 𝔠`, `#(S ∩ X) < 𝔠` and
  `#(S ∩ (X + X)) < 𝔠` for some `X`, the target's conclusion holds for `S`. No hypothesis on `S`.
  Intended use: pick any `X` adapted to the hard case (a subgroup, a coset, a translate of a
  subset of `S`) and reduce the problem to bounding two traces.
- `exists_of_mk_lt` — case `#S < 𝔠` (`X = univ`).
- `exists_of_bddAbove`, `exists_of_bddBelow` — half-lines `(max M 0, ∞)` / `(-∞, min M 0)`.
- `exists_of_span_ne_top` — coset `c + span_ℚ S` with `c ∉ span_ℚ S`.
- `erdos_949_of_cases` — the target conclusion for every `S` in any of these classes.

**Provenance.**
- The Zorn/cardinality argument generalizes the `#S < 𝔠` branch of the Sidon-variant proof
  already in `FormalConjectures/ErdosProblems/949.lean` (AlphaProof / Dillies). That branch is
  inlined in a proof there and not exported; here it is stated for an arbitrary `X`, which is
  what makes it reusable for the open case.
- The bounded and non-spanning cases, and the general `X` form, are original to this
  contribution.
- Written with AI assistance (Claude); every declaration compiles against the pinned pool
  (Lean 4.33.1, Formal Conjectures `6a786f99`) with only `propext`, `Classical.choice`,
  `Quot.sound`.
