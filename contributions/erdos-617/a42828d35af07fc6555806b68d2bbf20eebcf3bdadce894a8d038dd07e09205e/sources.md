# Partition stability, minimum-hole transfer, and surplus bounds

## What is contributed

This is a separate partition-based route to Erdős 617. The main development
constructs a labelled partition under an independence cap, pays for missing
internal edges using the exact edge surplus, and establishes transfer inequalities
for one globally minimum-hole partition. Empty parts are explicitly permitted.
The stability proof uses a minimum-degree induction and exact integer balancing;
its factor-of-two passage from ordered pairs to unordered edges is proved.

## Reusable interfaces and explicit use

Under namespace `Contribution.Erdos617Partitions`:

- `Stability.partition_stability` and `Consequences.exists_partHoles_le_surplus`
  give the actual partition and its hole budget.
- `Optimality.minimum_partition_package` provides minimality, nonnegative holes,
  the crossing-edge bound, and every vertex-transfer inequality on the SAME partition.
- `Consequences.palette_edges` supplies the hereditary full-palette lower bound.
- `Consequences.local_surplus_bound`, `Consequences.surplus_ge_pred`, and
  `Consequences.surplus_of_isolated` provide explicit partial surplus estimates.
- `ColourBounds.sum_surplus` and `ColourBounds.partSurplus_eq` give exact accounting.
- `Target.aggregate_iff_literal` and `Target.statement_iff_literal` identify the
  sufficient surplus goal with the literal missing-colour statement; they prove
  equivalences, not either open proposition.

A later solver working by contradiction can apply `Consequences.independenceBound_of_caps`
to each actual colour graph, then use `Optimality.minimum_partition_package` to
obtain a single partition with all necessary bounds and transfer inequalities.
This removes the partition-existence and vertex-move proof obligations without
assuming any unproved strict aggregate inequality. The checked example at the
end of the file instantiates precisely this route for an actual colour graph.

The sparse minimal-core package is neither imported nor duplicated. Two adapters
to the separate certificate/minimal-core library were deliberately omitted to
avoid dragging that independent development into this logical unit.

## Provenance

The source is the submitter's signed-surplus and partition-stability development,
including the elementary stability/optimality formalization recorded on
14 September 2026. Namespace cleanup and source packaging do not constitute the
mathematical contribution; the included checked construction and inequalities do.
Original source digests and the old-to-new declaration mapping are retained in
the private preparation audit. The mathematical formulas use signed integer
subtraction where required; no count silently changes from ordered to unordered.
The development used AI assistance. Required third-party notices are preserved.

## What is not claimed

The uniform bound proved here is t_j >= r-1, not the much stronger per-colour
target bound choose(r,2)+1. The latter is obtained only under the explicit
isolated-vertex hypothesis in `surplus_of_isolated`. Such a vertex is not
asserted to exist. The identity sum_j t_j = r*choose(r,2) is a conservation law,
not the missing strict contradiction. No all-r solution is claimed.

## Target and pinned environment

Target: `erdos-617`; reward target: `fc-target:Erdos617.erdos_617`.
This is partial work for the full all-parameter problem, not a submission of a full solution.
The checked environment is Lean 4.33.1, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and the audited Formal Conjectures
commit `8432eac998110a563e03df65a28c117e97c8c142` reconstructed from its public base and patch.

- Official pinned task: https://github.com/conjectures-io/conjectures-tasks/tree/275ef4824c41d41f97ac4e9fff95ca471de9341d/pool/tier-1/erdos-617-formalized
- Problem and bibliography: https://www.erdosproblems.com/617
- Mathlib dependency: https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474
- Formal Conjectures source: https://github.com/google-deepmind/formal-conjectures
- Contribution format and review contract: https://github.com/conjectures-io/conjectures-contribution

Every submitted Lean file is self-contained. It imports only Mathlib and the
pinned Erdős 617 module. The unproved target declaration is not invoked as a
proof; the submitted declarations are independently audited for transitive axioms.

## Existing contribution and attribution boundary

The existing contribution `f3cefb14b528f374f07797e2b23204f122818ee4f8da769ed1e529ecaf6972b4`
contains affine-plane colourings, the square-order variant, pentagon sharpness,
and an elementary link API:
https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-617/f3cefb14b528f374f07797e2b23204f122818ee4f8da769ed1e529ecaf6972b4

It is treated as prior public work, not as a contribution belonging to this submitter.
Its author and reward keys have not been reused. The present work does not import
that artifact or resubmit its affine-plane and pentagon results. Shared elementary
colour-avoidance definitions serve only the self-contained development.
No worldwide mathematical priority is claimed. The submission offers the concrete
checked development below; recognition is for the maintainer to decide.

## Verification and limits

From the contribution checkout, run the official source elaborator against its
prepared pinned workspace:

```sh
contrib elaborate <contribution-directory> --workspace <pinned-formal-conjectures-workspace> --json
contrib check <contribution-directory> --json
```

The second command applies to the final promoted, signed directory, not to an
unsigned draft. Local preparation also separately checks the transitive axiom
closures. Those audit programs are not submitted artifacts. No numerical search,
external solver result, or local research module is imported as proof evidence.
