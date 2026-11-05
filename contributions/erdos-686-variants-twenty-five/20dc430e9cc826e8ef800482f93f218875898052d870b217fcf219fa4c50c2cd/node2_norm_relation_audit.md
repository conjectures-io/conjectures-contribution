# Session 13: class-group transfer audit and a stronger norm relation

The ordinary class-group bound in session 12 is valid. In fact the saved matrices give the stronger bound

\[
c_2(L)\le c_2(E_P)+c_2(E_M)+c_2(F), \tag{1}
\]

where `c_2(K)=dim_F2 Cl(K)[2]`. The coefficient two on the pair field can be removed. The same bound holds for class groups localized at a **common set of rational primes**. This is an algebraic reduction; no numerical auxiliary class-group bound or elliptic upper rank is asserted.

## 1. The stronger exact relation

Use the precise ordering and orbital matrices in `session12/odd_norm_relation_certificate.json`. Let `J` be the 15-by-15 matrix on unordered pairs with entry 1 exactly when two pairs intersect in one letter. Let `D` be the 15-by-15 matrix with rows perfect matchings and columns unordered pairs, with entry 1 for containment. Directly from the incidence meanings,

\[
J=J^t,\qquad A_1=A_0J,\qquad A_2=B_0D-A_0.
\]

Substituting these identities into the session-12 relation gives

\[
\boxed{
5I_{45}=(-4A_0-3A_1-A_2)A_0^t
        +(A_2D^t-B_0)B_0^t+C_0C_0^t.} \tag{2}
\]

Thus it factors through one copy each of the pair, matching, and cyclic-order-five permutation lattices. Set

\[
\Psi=(A_0^t,B_0^t,C_0^t),\qquad
\Phi=(-4A_0-3A_1-A_2,\ A_2D^t-B_0,\ C_0).
\]

Then `Phi Psi=5I` integrally, not just modulo two. The new independent checker `node2_norm_relation_audit.py` verifies all three subsidiary identities, every entry of (2), and the induced maps on prime-orbit lattices for all eleven S6 Frobenius cycle types. It completed in 0.046 seconds. The explicit maps and results are saved in `node2_norm_relation_audit.json`.

## 2. Orientation of the arithmetic correspondences

Let `Omega/Q` be the S6 splitting field. An orbital matrix `A:Z[Y]->Z[X]` has rows indexed by embeddings of the target field `K_X` and columns indexed by embeddings of the source field `K_Y`. For an orbit represented by `(H,gJ)`, put

\[
K_X=\Omega^H,\quad K_Y=\Omega^J,\quad
C=\Omega^{H\cap gJg^{-1}}=K_X\,g(K_Y).
\]

The corresponding map on ideal classes, in the **same direction as the matrix**, is

\[
\operatorname{Cl}(K_Y)\xrightarrow{g}
\operatorname{Cl}(gK_Y)\xrightarrow{\text{ideal extension}}
\operatorname{Cl}(C)\xrightarrow{N_{C/K_X}}
\operatorname{Cl}(K_X). \tag{3}
\]

In particular `A_0:E_P->L` and `B_0:E_M->L` are extension maps. Their transposes are the ordinary norms `N_{L/E_P}` and `N_{L/E_M}`. The third outgoing channel is the reverse compositum correspondence for `C_0`. No injection of class groups by ideal extension is assumed; capitulation is permitted.

This agrees with the norm/extension convention for cohomological Mackey functors. The transfer of a permutation factorization is stated in Etienne, [*Computing class groups by induction with generalised norm relations*, Theorem 3.4 and Proposition 3.5](https://arxiv.org/html/2411.13124v2). The following direct argument verifies the needed composition rule without importing a ramification hypothesis from a particular presentation of that functor.

## 3. Why ramification does not invalidate the ordinary class-group identity

Choose any finite rational prime set `B` containing every prime ramified in `Omega/Q`. For a subfield `K`, let `I_B(K)` be the fractional ideals supported away from primes above `B`. Every ordinary ideal class of `K` has a representative in `I_B(K)`: multiply any representative by a principal fractional ideal with the opposite valuations at the finitely many excluded places, using weak approximation.

All correspondences (3) preserve this restriction on support and carry principal ideals to principal ideals. At a rational prime `p` outside `B`, let `sigma` be a Frobenius element. The primes of `K_X` correspond to the sigma-orbits on `X`. Identify a divisor with the function on `X` that is constant on each such orbit and equal to that prime's valuation. The arithmetic correspondence (3) acts on these invariant functions by its ordinary incidence matrix `A`:

- extension pulls valuations back along an unramified map;
- norm sums them over a fiber, giving exactly the relative residue-degree multiplicity.

Concretely, the entry from a source orbit `O_Y` to target orbit `O_X` is

\[
 \sum_{y\in O_Y}A_{x,y},\qquad x\in O_X.
\]

It is independent of the selected `x` by equivariance. Thus compositions of correspondences on `I_B` follow ordinary matrix multiplication. This proves (2) on prime-to-`B` ideals. Since these represent every ordinary class, it proves (2) on ordinary class groups. The argument does not invert or kill the ramified prime **classes**; it only chooses alternative representatives of them.

The eleven Frobenius checks in the saved verifier also independently test this normalization of norm versus extension. The argument itself applies to every Frobenius element and every unramified rational prime.

This agrees with the ordinary class-group example in [Spencer's thesis, Example 6.2.1(3)](https://wrap.warwick.ac.uk/id/eprint/95231/1/WRAP_Theses_Spencer_2017.pdf), which identifies norm and ideal extension as the two operations. It is consistent with Bley–Boltje's ordinary class-group framework.

### The caution in Feuerpfeil's Remark 2.4

[Feuerpfeil, version 2, Remark 2.4(1)](https://arxiv.org/html/2509.20144v2#S2.SS1.SSS1) warns that a straightforward construction without all ramified primes need not be a cohomological Mackey functor. That warning must not be used to identify ordinary ideal extension with unweighted restriction on exponential valuation vectors: at a ramified place the valuation of a base element is multiplied by the ramification index. The displayed valuation-to-`H^0` construction in that paper therefore cannot simply be imported after dropping its support hypothesis.

For the **actual norm and ideal-extension class maps (3)**, however, the prime-to-ramification proof above establishes the composition identity directly. Taking the warning as an absolute prohibition on these ordinary class-group maps would conflict with that proof and with the ordinary class-group example cited above. This audit does not rely on the warning, an unweighted ramified-divisor model, or any Hilbert-90 assertion for class groups. The scope needed here is settled by the direct proof.

## 4. Consequence on the full 2-primary class groups

Apply (2) to the maps (3). Multiplication by five is an automorphism on every finite 2-primary group. Consequently

\[
\Psi:\operatorname{Cl}(L)_{(2)}\longrightarrow
\operatorname{Cl}(E_P)_{(2)}\oplus
\operatorname{Cl}(E_M)_{(2)}\oplus
\operatorname{Cl}(F)_{(2)}
\]

is a split injection, with retraction `5^{-1}Phi`. This proves (1), and is stronger than an injection only on elements of order two. In particular, if all three auxiliary class groups have odd order, so does `Cl(L)`. Nothing in the certificate establishes that numerical premise.

The session-12 four-channel bound remains a valid weaker statement. On 2-torsion its proposed outgoing channels `A_1^t,A_2^t,B_0^t,C_0^t` indeed detect every class. The identities in section 1 show that the first two are already determined by `A_0^t` and `B_0^t`, which explains the improvement.

## 5. A support-aware bound requiring smaller auxiliary class groups

For a fixed finite rational prime set `T`, put

\[
\operatorname{Cl}_T(K)=\operatorname{Cl}(K)/
 \langle[\mathfrak p]:\mathfrak p\mid p,\ p\in T\rangle.
\]

Every correspondence (3) sends a class represented by primes over `T` to a sum of classes represented by primes over `T`. Therefore the already proved ordinary class-group maps and identity descend to these quotients, for any common `T`; it is not necessary that `T` contain the ramified primes. This quotient argument is separate from the ramified-valuation presentation discussed above. We obtain

\[
c_2(\operatorname{Cl}_T(L))\le
c_2(\operatorname{Cl}_T(E_P))+
c_2(\operatorname{Cl}_T(E_M))+
c_2(\operatorname{Cl}_T(F)). \tag{4}
\]

If the desired refined support `S_L` contains every L-prime above `T`, then `Cl_{S_L}(L)` is a quotient of `Cl_T(L)`. For a finite abelian group, its 2-rank equals the dimension of its quotient by doubling, so this quotient cannot increase 2-rank. Hence the right side of (4) also bounds the required `c_L(S_L)`.

Reading the previously saved session-11 supports gives:

| masks | permissible common rational `T` |
|---|---|
| 0, 4, 384, 388, 1536, 1920 | `{2,5}` |
| 60, 104, 444, 488, 1596, 1640, 1644, 1980, 2024, 2028 | `{2,3,5}` |

Thus `{2,5}` works uniformly for all sixteen curves; ten permit the stronger `{2,3,5}` version. No refined support contains all primes over 13, and the large discriminant prime was excluded in session 11. The auxiliary quantities in (4) must be certified for these stated supports. An ordinary-class bound is also valid, but potentially larger.

The nonuniform selected prime sets in session 11 are not silently assigned to all auxiliary fields. A still sharper nonuniform quotient would require checking that the actual return correspondences send each proposed auxiliary prime subgroup into the target subgroup. That additional calculation is not part of this certificate.

## 6. Audit result

The coefficient-five identity transfers with the covariant norm/extension orientation described above. Ramification introduces no correction term for the ordinary class-group identity proved using prime-to-ramification representatives. The exact new regrouping reduces the required auxiliary bound to a sum of three class-group 2-ranks, and common localization at `{2,5}` (or, for ten masks, `{2,3,5}`) is valid.

No arithmetic class-group completeness, numerical upper rank, complete Chabauty argument, or all-length multiplier-25 result follows without the remaining arithmetic certificates.
