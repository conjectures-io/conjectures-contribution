# Minimum auxiliary degree for the S6 permutation-correspondence route

**Verified conclusion.** Degree 36 is the smallest possible degree of an auxiliary field in the fixed S6 splitting field that can supply the missing constituent of the degree-45 flag representation. No collection of fields of degrees strictly below 36 can give a rational equivariant permutation-correspondence factorization of its identity. Moreover, the degree-36 subfield is unique up to conjugacy and hence Q-isomorphism: it is the field already denoted `F36`.

This is a statement about the specified rational correspondence construction. It is not an obstruction to other arithmetic computations or methods, and gives no class-group value or elliptic rank.

## Exact character calculation

The hook-length formula gives the eleven irreducible S6 degrees, in descending lexicographic partition order,

```text
(6)          1      (5,1)        5      (4,2)        9
(4,1,1)     10      (3,3)        5      (3,2,1)     16
(3,1,1,1)   10      (2,2,2)      5      (2,2,1,1)    9
(2,1,1,1,1)  5      (1,1,1,1,1,1) 1
```

Write `chi` for the irreducible character indexed by `(3,2,1)`. Murnaghan–Nakayama gives:

| cycle type | class size | `chi` |
|---|---:|---:|
| `1^6` | 1 | 16 |
| `5,1` | 144 | 1 |
| `3,3` | 40 | -2 |
| `3,1,1,1` | 40 | -2 |
| each other cycle type | — | 0 |

For the 45 perfect matchings with one distinguished pair, the permutation character has values 45 at the identity and zero at the other three rows above. Therefore

\[
\langle\chi,\mathbf Q[X]\rangle=(16\cdot45)/720=1.
\]

For the 36 cyclic subgroups of order five, acted on by conjugation, the corresponding values are 36, 1, 0, 0. Hence

\[
\langle\chi,\mathbf Q[C]\rangle=(16\cdot36+144)/720=1.
\]

The saved verifier calculates the whole Murnaghan–Nakayama character table, verifies all 121 row orthogonality identities and all hook-length dimensions, and independently recomputes the target row by the Jacobi–Trudi/Frobenius formula. It counts the fixed points on the saved G-sets and obtains multiplicities `(1,0,0,1)` in flag45, pair15, matching15, and cyclic5_36. All calculations are integer arithmetic and run in about 0.02 seconds.

## Why degree below 36 is impossible

Let `K=Omega^H` be any subfield of the fixed S6 splitting field, with `d=[S6:H]<36`. Its transitive permutation character has trivial multiplicity exactly one. By Frobenius reciprocity, its sign multiplicity is either zero or one. Every remaining irreducible degree is 5, 9, 10 or 16.

If it contained the 16-dimensional constituent, then for some integers `m>=1`, `a,b,c>=0` and `epsilon in {0,1}`,

\[
d=1+\epsilon+16m+5a+9b+10c. \tag{1}
\]

The degree `d` must divide 720. The only possibilities between 17 and 35 are 18, 20, 24 and 30; these force `m=1`. The differences `d-17` are 1, 3, 7 and 13. Only 1 can be written as `epsilon+5a+9b+10c`. Thus (1) leaves only `d=18`, with permutation character necessarily `1+sign+chi`.

But an index-18 subgroup would have order 40. Its number of Sylow 5-subgroups divides 8 and is congruent to 1 modulo 5, so it is one. If `P` is that normal cyclic subgroup of order five, then

\[
H\le N_{S_6}(P),\qquad |N_{S_6}(P)|=5\cdot4=20,
\]

contradicting `|H|=40`. The normalizer order follows from the usual affine action on the five moved letters; the sixth letter must stay fixed. The verifier also checks the order by enumerating all 720 permutations.

This rules out every auxiliary field of degree below 36. Semisimplicity over Q then rules out any collection of such fields: the source has one copy of the irreducible 16-dimensional representation, while their direct sum has none, so every factorization through that sum vanishes on this constituent and cannot equal the identity or any nonzero scalar multiple of it.

At degree 36, a subgroup has order 20. Its Sylow 5-subgroup is again normal, since its count divides 4 and is 1 modulo 5. It therefore equals the order-20 normalizer. All cyclic subgroups of order five in S6 are conjugate, proving the asserted uniqueness at the minimum degree. The existing coefficient-five relation attains maximum auxiliary degree 36, so the bound is sharp for this route.

## Certificate files

- `node2_minimum_auxiliary_degree.py`: standalone exact verifier using the saved G-set data.
- `node2_minimum_auxiliary_degree.json`: character values, multiplicities, degree checks and normalizer result.
- `node2_minimum_auxiliary_degree.log`: replay output.

No field, point, torsion, rank or class-group arithmetic was rerun.
