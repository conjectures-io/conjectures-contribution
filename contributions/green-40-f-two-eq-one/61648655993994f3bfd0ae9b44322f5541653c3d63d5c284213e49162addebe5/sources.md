# Sources

This is an original Lean formalization of the elementary sphere-covering
counting bound, specialized to the definitions used by Green's Problem 40.
It grew out of the author's investigation of radius-two binary linear covering
codes.  No previous contribution for this reward target was used; its public
index contained zero contributions at the pinned base commit.

The mathematical target and notation come from:

- Ben Green, *100 Open Problems*, Problem 40:
  https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40
- The pinned Formal Conjectures statement and definitions:
  https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/GreensOpenProblems/40.lean

The proof uses Mathlib's finite-cardinality, pointwise-set, `ENNReal`, and
filter-liminf APIs:

- https://github.com/leanprover-community/mathlib4

Intended use: `one_le_f 2` proves the universal lower bound half of
`Green40.f 2 = 1`, and `f_two_eq_one_iff_le_one` reduces the open target to
constructing the matching upper bound.  The intermediate declarations expose
the finite counting argument for reuse with any proposed covering subspace.
