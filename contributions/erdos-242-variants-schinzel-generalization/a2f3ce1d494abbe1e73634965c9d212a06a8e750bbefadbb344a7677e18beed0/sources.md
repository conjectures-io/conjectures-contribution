# Sources and provenance — Schinzel small numerators and multiples

## Intended submission metadata

- Target: `erdos-242-variants-schinzel-generalization`
- Kind: `partial-proof`
- Mode: `formalized`
- Proposed title: `Schinzel: complete positive numerators below 4 and a multiples family for every numerator`
- Cross-target parent:
  [`6862728fa0017d77cc6e4e19fe2d84df35c94abb79d5188fccc7ae7674c0f859`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-242/6862728fa0017d77cc6e4e19fe2d84df35c94abb79d5188fccc7ae7674c0f859)

The parent is declared because it already contains supporting
general-numerator machinery and explicitly discusses this variant. Current
repository rule `C010` accepts any published contribution id as a parent and
does not impose a same-target restriction. This must be rechecked against the
current policy immediately before any promotion. The parent is lineage and
overlap disclosure, not a Lean import.

## Exact checked result

The target asks, for every fixed positive numerator `a`, for the ordered
three-unit-fraction conclusion eventually in `n`. This contribution proves two
proper partial results:

1. **Complete small numerators.** For every `0 < a < 4`, the conclusion holds
   for every `n ≥ 2`, hence with one common explicit eventual threshold.
   `numerator_three` supplies the main new construction, splitting on the
   parity of `n`. The final theorem is stated in the literal syntax of the
   target body.
2. **A positive-density family for arbitrary numerator.** For every `a > 0`,
   all `n` with `a ∣ n` and `n ≥ 2a` are covered. This is the tail of the
   multiples of `a`, an arithmetic progression with natural density `1/a`.
   The Lean file proves both the divisor-facing theorem and set containment,
   as well as infinitude; it does not introduce a separate asymptotic-density
   definition.

This does not prove the Schinzel target for arbitrary `a`, because the
multiples family is not cofinite when `a > 1`.

## Delta and overlap with the parent

The published parent proves an elementary general-numerator identity and the
family `a ∣ n+1`, i.e. one residue class `n ≡ -1 (mod a)`. In particular,
that parent already implies the complete `a=1` case. No originality credit is
claimed here for that observation, for the local `Decomp` wrapper, or for the
classical unit-fraction splitting idea.

The marginal claims are:

- completion of all denominators for `a=2` and `a=3`, rather than one residue
  class; the parity construction in `numerator_three` is the principal result;
- consolidation into the exact target-body theorem for all positive `a<4`;
- the distinct arbitrary-`a` family `a ∣ n` with `n ≥ 2a`, including a
  checked set-containment and infinitude handoff.

To minimize overlap, this file does not copy or redeclare the parent's named
split, master-identity, or `a ∣ n+1` API. The elementary rational identities
needed for the new constructions are proved directly inside their theorems.

## Sources

- Exact pinned target:
  [`FormalConjectures/ErdosProblems/242.lean`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/242.lean).
- Historical statement and bibliography:
  [Erdős Problems 242](https://www.erdosproblems.com/242).
- The pool file cites Wacław Sierpiński, *Sur les décompositions de nombres
  rationnels en fractions primaires*, Mathesis 65 (1956), 16–32, for
  Schinzel's generalization.
- The local verified starting point was
  `/tmp/formal-new28-b/Scratch242Schinzel.lean`. The submission-shaped file was
  refined from it to remove named support lemmas overlapping the parent, expose
  literal target-body use sites, and state the multiples tail directly.

## Originality and assistance disclosure

The unit-fraction identities are elementary and no claim of new mathematics is
made. The claimed deliverable is their focused Lean formalization and the
specific checked parameter/family results above. No Lean code was copied from
the published parent.

The proof and documentation were developed locally with OpenAI Codex
assistance. The eventual signer remains responsible for reviewing correctness,
provenance, novelty, lineage, and reward metadata before promotion.
