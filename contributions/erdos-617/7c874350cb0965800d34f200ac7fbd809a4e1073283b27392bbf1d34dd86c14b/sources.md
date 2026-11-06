# Sparse minimal cores, weighted extension, and the five-colour case

## What is contributed

A hypothetical capped r-colouring of K_(r²+1), for r >= 4, has an actual sparse
colour layer and a proper minimal core W. With a = alpha_i(W) and S the sum
of selected degrees minus r inside W, the proved bounds are

    |W| = r*a + 1,    4 <= a <= r-2,    2r-2 <= S <= r(r-a).

This selects a layer from the same original colouring; it is not a relaxation
to an unrelated sparse graph. It makes the original r=5 case impossible and
therefore proves the missing-colour conclusion for every five-colouring of K26.

## Reusable interfaces and explicit use

Under namespace `Contribution.Erdos617SparseCore`:

- `sparse_core_reduction` supplies the actual core, its order, and the simultaneous bounds.
- `five_colour_case` has precisely the type of the original target specialized at r=5,
  with arbitrary finite carrier and no extra colouring hypotheses.
- `Surplus.PrivateStructure.Full.missing_colour_of_excess` supplies a missing-colour
  set on the excess-surplus branch without assuming cappedness in its conclusion theorem.
- The supporting minimal-core, private-incidence, and weighted-extension interfaces
  provide the route to these results rather than isolated, unused helper statements.

The file ends with a checked use site on `Fin 26`. A later solver can use the
first interface to replace the unrestricted hypothetical counterexample by the
specified proper-core constraints; the second closes the entire r=5 instance.
These results constitute one logical unit, not a collection of separate reward requests.

## Provenance

The code was extracted from the submitter's research development and freshly
re-elaborated after namespace and documentation cleanup. The original standalone
research snapshot has SHA-256
`39c785fb679f8fb87c6ccf1eabf2b67e00f42fcdaa28d29b66866bc333d5b777`.
Only the 16-module dependency closure of the weighted-extension and five-colour
results was retained. Unneeded endpoint and support-circuit developments were omitted.
The original research files and verification ledgers remain unchanged.

Parts of the independence-two argument originated in Harmonic Aristotle-assisted
formalization and were ported to the pinned environment. The root-extension
foundation preserves its recorded credits to The Formal Conjectures Authors (2026)
and Ramazan Kara, including Apache-2.0 attribution. These credits are not replaced
by the submitter's signing identity. AI-assisted research and proof development
are not represented as exclusively unaided human work.

## What is not claimed

This does not prove Erdős 617 for all r. No stronger later descent, six-colour
specialization, seven-colour certificate chain, or complete counterexample is
asserted by this contribution. The surviving proper-core ranges remain open
within this development. The seven-colour computational work is not part of the
formal dependency chain.

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
