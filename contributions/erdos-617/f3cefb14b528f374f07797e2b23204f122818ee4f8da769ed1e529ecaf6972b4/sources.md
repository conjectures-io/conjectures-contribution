## Sources

Problem statement and target module
- Erdős Problem 617: https://www.erdosproblems.com/617
- Target module in this repository: `FormalConjectures/ErdosProblems/617.lean` (declarations `Erdos617.erdos_617`, `Erdos617.erdos_617.variants.r_eq_3`, `Erdos617.erdos_617.variants.r_eq_4`, `Erdos617.erdos_617.variants.r2`, all `sorry`).
- The bibliographic pointer P. Erdős and A. Gyárfás, *Split and balanced colorings of complete graphs*, Discrete Math. 200 (1999), 79-86, is copied from the target module's own reference list. I did not obtain or read that paper; no claim in this file depends on it, and no DOI is asserted because I could not verify one.

Originality
- All statements and all proofs in `CW_erdos_617.lean` are original work written for this submission. Nothing in the file was copied, translated, or adapted from any existing Lean file, repository, formalisation, blueprint, or proof assistant library: no source other than the pinned Mathlib (used only through the public lemmas listed below) and the target module's own statement of the obligations was consulted while writing it. In particular the definitions `MissesColor`, `IsBalanced`, `slopeColoring` and `pentagonColoring`, and every lemma about them, were written from scratch here.
- The *mathematics* behind item 1 is not original: the affine-plane construction is the standard one (see below), and the file's docstring says so. What is original is the Lean rendering and every proof term in it.

Mathematics
- The construction proving `variants.r2` is the standard affine-plane one and I re-derived it from scratch: the `q + 1` parallel classes of AG(2, q) partition the edges of K_(q^2); merging two classes leaves `q` colours, each colour class containing a full parallel class (a spanning set of `q` disjoint `q`-cliques), so each colour class has independence number `q` and no `q + 1` vertices can miss a colour. In Lean this is implemented without ever mentioning lines: the edge {P, Q} is coloured by the slope `(P.2 - Q.2) / (P.1 - Q.1)` (vertical edges get `0`, which is the merge of the vertical class with the slope-`0` class), and balancedness reduces to a single pigeonhole on the linear form `y - m * x` (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`).
- The `r = 2` counterexample is the pentagon/pentagram 2-colouring of K_5: both colour classes are 5-cycles, which have independence number 2. Checked in Lean by `decide`.
- Independent cross-check outside Lean: a Python brute force verified (a) the slope colouring of (ZMod p)^2 is symmetric and every `(p+1)`-subset realises all `p` colours, for p = 2, 3, 5, and (b) no 3-subset of the pentagon colouring misses a colour, and (c) the colour-0 link data used in use sites 4 and 5 — including that vertex `0` and vertex `2` are both witnesses for use site 5.

Mathlib (pinned `leanprover-community/mathlib4` rev `a3a10db0e9d66acbebf76c5e6a135066525ac900`, tag `v4.27.0`, toolchain `leanprover/lean4:v4.27.0`)
- `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` (`Mathlib/Data/Finset/Card.lean`, line 442): https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Data/Finset/Card.lean
- `Sym2.lift` (`Mathlib/Data/Sym/Sym2.lean`, line 196): https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Data/Sym/Sym2.lean
- `ZMod.card` (`Mathlib/Data/ZMod/Defs.lean`, line 171): https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Data/ZMod/Defs.lean
- the `Field (ZMod p)` instance for `[Fact p.Prime]` (`Mathlib/Algebra/Field/ZMod.lean`, line 30 — an anonymous `instance`, so it is used here only through instance resolution): https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Algebra/Field/ZMod.lean
- `Nat.infinite_setOf_prime` (`Mathlib/Data/Nat/PrimeFin.lean`, line 27): https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Data/Nat/PrimeFin.lean
- `Set.Infinite.mono` (`Mathlib/Data/Set/Finite/Basic.lean`, line 517): https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Data/Set/Finite/Basic.lean
- `Finset.exists_card_fiber_le_of_card_le_mul` (`Mathlib/Combinatorics/Pigeonhole.lean`, line 286) — the lemma the *previous* version of this file duplicated; the offending declarations `sum_card_colorNbhd` and `exists_colorNbhd_card_le` have been deleted, and nothing here restates it: https://github.com/leanprover-community/mathlib4/blob/v4.27.0/Mathlib/Combinatorics/Pigeonhole.lean

Novelty checks performed
- Grepped the pinned Mathlib source for `Ramsey` (only `Mathlib/Combinatorics/HalesJewett.lean` and `Mathlib/Combinatorics/Hindman.lean`, plus unrelated coalgebra files — there is no Ramsey-number machinery), for `IsBalanced` under `Mathlib/Combinatorics` (nothing), and for affine-plane edge colourings (nothing). Mathlib does define `slope` for difference quotients on a field (`Mathlib/LinearAlgebra/AffineSpace/Slope.lean`), a different object, which is why the definition here is named `slopeColoring`.
- `exists_missesColor_iff_exists_link` was tested against `simp [MissesColor]` (unsolved goals) and `simp [MissesColor]; aesop` (deterministic timeout), so it is not a one-tactic restatement. `MissesColor.insert` is not closed by `aesop` either.
- `not_exists_missesColor_iff_isBalanced` *is* a one-tactic lemma — it is proved by a single `simp [IsBalanced]`, and its docstring says exactly that. It is included because it is the bridge that makes the `IsBalanced` API reachable from the reward theorem's own goal by `by_contra` (use site 6), not because it has content of its own.

Corrections made after review
- The "Worked use sites" header sentence previously claimed that *each* example is stated with the binders of `Erdos617.erdos_617` or of `Erdos617.erdos_617.variants.r2`. That was false: it holds for use sites 1, 2 and 6 only, while use site 3 derives `False` from a hypothetical hypothesis-free form of the theorem and use sites 4 and 5 are concrete `Fin 5` statements. The sentence now says which example is which.
- Use site 5's docstring said "namely the vertex `0`", implying a unique witness; vertex `2` is an equally good witness (it carries colour-0 edges to `1` and to `3`). The docstring now says "e.g." and names both.
- The two Mathlib citations `ZMod.card` and the `Field (ZMod p)` instance were previously both attributed to `Mathlib/Data/ZMod/Basic.lean`. Both file paths were wrong and are corrected above.
- This originality section was added; the previous version asserted provenance of the mathematics only and never stated that the Lean formalisation itself is original.
- The bridge lemma `not_exists_missesColor_iff_isBalanced` and use site 6 were added on the reviewer's suggestion; no existing declaration was changed, deleted, or reproved.

AI assistance
- This file was written by Claude (Anthropic), an AI assistant, running as an automated contributor. Every statement and proof was elaborated and checked by Lean 4 / Mathlib at the pinned versions above. `lake env lean CW_erdos_617.lean` exits 0 with zero bytes of output: no errors and no warnings. The axiom footprint was checked by appending `#print axioms` for all 20 named declarations, recompiling, and confirming every one is a subset of `[propext, Classical.choice, Quot.sound]`; the six anonymous `example` use sites were given names in a throwaway probe copy and checked the same way, with the same result. The `#print axioms` lines were then deleted and the file recompiled clean. The combinatorial content was additionally cross-checked by an independent Python brute force as described above.
