ations of `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Connectivity.lean`
  (43 lines; verified with `wc -l` and by reading the file). There is not one lemma about
  either. `grep -rn "InfinitelyConnected" .lake/packages/mathlib/Mathlib/` returns nothing.
* Unfolded, `InfinitelyConnected G` requires, for each pair `u ≠ v`, an **infinite**
  `P : Set (G.Walk u v)` of pairwise internally disjoint paths. One cannot build such a set
  incrementally, the type `G.Walk u v` depends on the endpoints (so transporting the property
  along an isomorphism needs an endpoint-substitution dance), and in the target the walks live
  over the subtype `↥s`.
* `SimpleGraph.chromaticCardinal` is an `sInf` of a set of cardinals. Grepping the repository,
  the identifier occurs only in its own definition and inside the *statements* of Erdős problems
  75, 593, 740, 918, 1067, 1068, 1175 and 1176 (`ThreeUniformHypergraph.chromaticCardinal` is a
  different function). Nothing records that the infimum is attained; nothing relates it to the
  existence of a colouring by a given type.
* The pool file for 1068 contains exactly one declaration — the open reward theorem — so there is
  no `research solved` / `textbook` / `test` companion with a `sorry` proof to close outright.

## The delta

**Headline (`infinitelyConnected_iff`).** `InfinitelyConnected G ↔ Nontrivial V ∧
FinitelyUnseparated G`, where `FinitelyUnseparated G` says: for all `u ≠ v` and every *finite*
`S : Set V` there is a `u`-`v` path of length at least 2 whose interior misses `S`. One infinite
object is replaced by a family of finite obligations. The reverse direction is the substantial
one: the infinite family of pairwise internally disjoint paths is constructed greedily
(`blockedSet`, `pathAt` — structural recursion on ℕ over a `{S : Set V // S.Finite}`
accumulator), each new path avoiding all interior vertices used so far; the length condition is
exactly what forces the constructed paths to be pairwise *distinct*.

**Sharpness (`finitelyUnseparated_length_condition_necessary`).** A checked delimiter: dropping
`2 ≤ p.length` yields a criterion that holds for `⊤ : SimpleGraph (Fin 2)` — whose only path
between the two vertices is the edge, with empty interior — while that graph is *not* infinitely
connected. Both halves are proved, so the criterion is sharp as stated.

**The bespoke definition means what it says (`mem_innerSupport_iff`,
`internallyDisjoint_iff_of_isPath`).** `p.support.tail.dropLast` is exactly the set of
non-endpoint vertices of a path, hence two paths with the same endpoints are internally disjoint
iff every vertex they share is an endpoint. This validates the FCFM docstring of
`InternallyDisjoint` against its actual definition.

**Necessary conditions on any witness.** `infinite_neighborSet_of_infinitelyConnected`:
infinitely connected graphs have infinite minimum degree.
`infinite_neighborSet_of_infinitelyConnected_induce` transfers this to the target: every vertex
of a witness set `s` has infinite degree *in `G`*. Also `exists_isPath_avoiding` (the pigeonhole
form used when refuting), `infinite_of_infinitelyConnected`, and
`connected_of_infinitelyConnected`, a bridge into Mathlib's standard connectivity API.

**The missing `chromaticCardinal` API.** `chromaticCardinal_attained` (the `sInf` is attained,
via `csInf_mem`), `chromaticCardinal_le_iff`, `chromaticCardinal_le_aleph0_iff`,
`chromaticCardinal_top`, and `exists_adj_eq_of_chromaticCardinal_eq_aleph_one`, which converts
the target's hypothesis into: no `f : V → ℕ` is a proper colouring.

**Non-vacuity, both sides.** `exists_chromaticCardinal_eq_aleph_one` exhibits a `V : Type` and a
`G` satisfying the target's hypothesis; `exists_countable_infinitelyConnected_of_infinite_clique`
proves the target's conclusion for every graph containing an infinite clique. The latter is a
*sufficient condition only* and is flagged as such in the file: a graph of chromatic number ℵ₁
need not contain an infinite clique (there are triangle-free graphs of uncountable chromatic
number), so it does not solve 1068.

**Use site.** `erdos_1068_rhs_iff` restates the reward statement's right-hand side verbatim and
proves it equivalent to: for every `G` with `chromaticCardinal = ℵ_ 1` there is `H : SimpleGraph ℕ`
with `FinitelyUnseparated H` and `Nonempty (H ↪g G)`. Both rewrites used are equivalences, so
nothing is lost in either direction — this is a reformulation, not a strengthening, and it cannot
be refuted by instantiating the target's own binders.

## Verification

* Compiled with the pinned toolchain (`leanprover/lean4:v4.27.0`, repository Mathlib) via
  `lake env lean CW_erdos_1068.lean`: **zero errors, zero warnings**.
* `#print axioms` was run on all 39 declarations: every one depends only on a subset of
  `[propext, Classical.choice, Quot.sound]` — in particular nothing depends on `sorryAx`, so
  nothing leaks from the `sorry`-proved target. Those `#print` lines were then deleted and the
  file recompiled clean.
* No `sorry`, `admit`, `axiom`, `native_decide`, `#eval`, `unsafe`, `extern`, `implemented_by`,
  `partial`, or `set_option` anywhere in the file (checked by grep). Plain LF, no BOM, no
  control or bidi characters.
* Novelty spot-checks: `exact?` fails on `not_mem_support_dropLast`, `eq_of_length_le_one`,
  `mem_support_of_mem_innerSupport` and `mem_innerSupport_of_mem_support` stated over raw
  `p.support.tail.dropLast`; `simp` makes no progress on `innerSupport_eq_nil_iff`. Neither
  `InfinitelyConnected` nor `chromaticCardinal` exists anywhere in the pinned Mathlib.

## Sources consulted

* https://www.erdosproblems.com/1068 — the target problem.
* https://www.erdosproblems.com/1067 — the sibling problem (answer: no), consulted only to
  confirm that its counterexamples do not settle 1068: 1067 demands an infinitely connected
  subgraph *of chromatic number ℵ₁*, whereas 1068 allows any countable one.
* The references listed in the repository's own `FormalConjectures/ErdosProblems/1067.lean`
  header (Erdős–Hajnal 1966; Komjáth 2013; Soukup 2015; Thomassen 2017; Bowler–Pitz,
  arXiv:2402.05984, https://arxiv.org/abs/2402.05984) were read as context for why 1068 is hard.
  No proof, statement or Lean code was taken from any of them, nor from any `formal_proof`
  link in the repository.
* Mathlib source read directly in `.lake/packages/mathlib` for lemma names and signatures
  (`Combinatorics/SimpleGraph/Walks/Basic.lean`, `Paths.lean`, `Clique.lean`,
  `Data/Set/Finite/Basic.lean`, `Data/List/Basic.lean`).

## AI assistance

This contribution was produced by Claude (Anthropic) acting as an autonomous Lean 4 agent: the
mathematical design (the finite-cut criterion, the greedy construction, the sharpness
counterexample, the choice of API), the Lean source, and all proofs were written by the model and
iterated against the compiler until the file elaborated with zero errors and zero warnings. Every
statement in this document and in the file's module docstring was checked against the pinned
environment (compilation, `#print axioms`, `exact?`/`simp` probes, and greps quoted above) rather
than asserted from memory.

## Originality

All Lean code in `CW_erdos_1068.lean` is original to this contribution. No proof or statement was
copied from another repository, from a `formal_proof` link, or from any paper; the results are
not present in the pinned Mathlib or elsewhere in the Formal Conjectures repository. The greedy
construction behind `infinitelyConnected_iff` is a standard argument in infinite graph theory,
but its formalisation here — including the `blockedSet`/`pathAt` recursion, the
length-≥-2 device that forces distinctness, and the `Fin 2` delimiter showing that device is
necessary — was worked out from scratch for this file.
