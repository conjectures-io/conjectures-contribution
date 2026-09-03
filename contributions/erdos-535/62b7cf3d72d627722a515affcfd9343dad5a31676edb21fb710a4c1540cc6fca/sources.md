# Sources and provenance — Erdős 535 basic extremal API

## Target

- Contribution target: `erdos-535`.
- Reward target: `fc-target:Erdos535.erdos_535`.
- Intended mode: `formalized`.
- Pinned Formal Conjectures commit:
  [`379fc0298dc146df549e7061c3ede0353a5bb51f`](https://github.com/google-deepmind/formal-conjectures/tree/379fc0298dc146df549e7061c3ede0353a5bb51f).
- Exact source declaration:
  [`Erdos535.erdos_535`](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/ErdosProblems/535.lean).
- Historical problem record and bibliography:
  [Erdős problem 535](https://www.erdosproblems.com/535).
- Original upper-bound paper:
  [P. Erdős, *On a problem in elementary number theory and a combinatorial problem* (1964)](https://users.renyi.hu/~p_erdos/1964-10.pdf).
- Classical improvement:
  [H. L. Abbott and D. Hanson, *An extremal problem in number theory* (1970)](https://doi.org/10.1112/blms/2.3.324).
- Strong-sunflower formulation cited by the source file:
  [P. Erdős, *Problems and results on combinatorial number theory* (1973)](https://users.renyi.hu/~p_erdos/1973-21.pdf).

At the pinned commit, `Erdos535.f r N` is the supremum of the cardinalities of
finite sets `A ⊆ Finset.Icc 1 N` having no `r`-element subset with constant
pairwise greatest common divisor.  The open target asks for a much sharper
asymptotic upper bound on this same function.

## What this file contributes

The Lean file proves six elementary structural facts directly from the pinned
definition:

1. `f_le`: `Erdos535.f r N ≤ N` for every `r,N`.
2. `f_mono_right`: enlarging `N` cannot decrease `Erdos535.f r N`.
3. `f_mono_left`: enlarging the forbidden-set size `r` cannot decrease
   `Erdos535.f r N`.
4. `exists_extremal`: for `r ≥ 1`, the natural-number supremum defining
   `Erdos535.f r N` is attained by an admissible finite set.
5. `min_sub_one_le_f`: for `r ≥ 1`,
   `min N (r - 1) ≤ Erdos535.f r N`.
6. `f_eq_of_lt`: if `N < r`, then `Erdos535.f r N = N`.

The proofs use only finite-set inclusion/cardinality, the defining `sSup`, and
the observation that a set of fewer than `r` elements has no `r`-element
subset.  They do not invoke the open theorem or any of the source file's
unproved research declarations.

The intended use is foundational: `exists_extremal` lets a later argument start
with an actual maximizing family instead of repeatedly unfolding a
noncomputable supremum, while the two monotonicity lemmas transport finite
estimates as `r` or `N` changes.

## Originality and limits

This Lean formalization was produced for this local portfolio on 2026-09-03.
The mathematical observations are elementary consequences of the definition
and are implicit in standard extremal-function usage; no claim of new
mathematical discovery is made.  The contribution's delta is the checked Lean
API at the exact pinned definition.  At the recorded repository snapshot there
was no merged contribution for `erdos-535` and no open pull request touching
that target, but collision status is time-sensitive.

This is a partial API, not a proof of Erdős 535.  In particular, `f r N ≤ N`
does not approach the conjectured bound
`N ^ (c / log (log N))` for fixed `r ≥ 3`.  Maintainers may reasonably regard
these facts as too basic for recognition even though the extremal-witness and
monotonicity interfaces are target-facing and kernel-checked.
