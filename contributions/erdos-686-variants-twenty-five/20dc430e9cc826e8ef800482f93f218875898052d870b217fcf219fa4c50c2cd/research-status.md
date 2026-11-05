# Current status: partial results, dense arithmetic gap remains

The newly added complete-factor results and their intended uses are documented
in stencil-guide.md. The dense bound retains unbounded coefficients, so neither
length five nor the all-length target is settled. The restricted stencil does
not provide new remaining k5 coverage relative to the prior external proper-
support exclusion. No complete witness or bounty claim accompanies this update.

The following earlier square-pair proof and arithmetic-geometry notes are retained
as background, with their verification boundaries unchanged.

# New verified partial result: all 25 square-pair branches excluded

Let P(n)=product_{h=1}^5(n+h). Suppose P(m)=25P(n), m>=n+5, and some cross pair has n+i=d*a^2 and m+j=d*b^2, with positive integers d,a,b. Put u=n+i and v=m+j. For each i, define P_i(t)=product_{h!=i}(t+h-i). The exact identities Q_i(t)^2-64P_i(t)=R_i(t) are:

| i | Q_i(t) | R_i(t) |
|---|---|---|
|1|8t^2+40t+40|64|
|2|8t^2+20t-5|120t+409|
|3|8t^2-20|144|
|4|8t^2-20t-5|-120t+409|
|5|8t^2-40t+40|64|

Monotonicity bounds m<=2n+4. For n>=16384 this gives 10000<=u<=v<=3u and a<=b. Write U=bQ_j(v), V=5aQ_i(u). The target identity implies

    U^2-V^2 = b^2 R_j(v)-25a^2 R_i(u).

The explicit polynomial bounds give

    |U^2-V^2| <= a^2(4080u+11452),
    U+V  >= 42a u^2.

Since a^2<=u and u>=10000, we have u>=100a, so the first bound is strictly smaller than the second. Positive integers U,V must therefore be equal. The residual equation becomes vR_j(v)=25uR_i(u); all 25 cases are impossible for 10000<=u<=v<=3u, by the displayed constant or linear formulas.

For n<16384, `finite_five_exclusion` uses a dyadic Boolean certificate checked by the Lean kernel. Each n is assigned a strict bracket between consecutive values of P around25P(n), and monotonicity excludes every natural m. The approximate coefficient used to choose brackets is merely a hint: the proof checks the exact integer inequalities and does not assume a floating-point or root estimate.

`cross_ratios_nonsquare` also formalizes the rational-square-to-common-integer-factor reduction, using reduced rational numerators and denominators. The argument and all finite checks are in the standalone `script.lean`; only standard foundational axioms occur. This is an unbounded conditional exclusion, not the full length-five theorem.

## Secondary route audit

A new test of the previously audited finite reductions rejects a cyclic isogeny over the degree 15 base field for each prime degree 2,3,5,7,11,13,17,19,23,29,31,37,41,43,47, on all 16 curves. At each chosen good prime p different from ell, the Frobenius polynomial T^2-a_p T+p has no root over F_ell, whereas a base-field cyclic ell-isogeny would supply an invariant line and hence a root. The certificates are in `isogeny-screen.json`; `verify-isogeny-screen.py` independently recounts the relevant finite curves from the included exact quartic and twist data. Larger prime degrees, arbitrary descents and rank bounds are not addressed. No extra number-field class computation was run for this test.

The recent [permutation-resolution Selmer algorithm](https://www.math.u-bordeaux.fr/~fetienne002/Selmer_groups.pdf), Theorem A, still requires S-unit/class-group computations in extension fields; it does not by itself provide our missing unconditional certificate. This was a method audit, not an implementation or rank calculation.

## Prior research status (still applicable)

# Research handoff: multiplier25, unresolved

The full target and the k=5 case remain unresolved. No admissible witness is known from this work. All sixteen retained covers remain; no upper rank or complete Chabauty calculation is supplied. The formal claims are exactly the declarations in `script.lean`. Supporting computations and written deductions below have a different verification status.

## Length-five quotient and covers

Writing x=n+3,y=m+3 gives S(y)=25S(x), where S(t)=t^5-5t^3+4t. For r=y/x, the Lean quotient bridge yields

    w^2 = 9r^6+400r^5-1250r^3+400r+5625,
    w = 2(r^5-25)x^2 - 5(r^3-25).

The local descent research retained masks
`0,4,60,104,384,388,444,488,1536,1596,1640,1644,1920,1980,2024,2028`.
The compact curve data are in `node2_small_models.json`; the degree 15 quadratic/quartic factorization and exact rational checker are also included. This upload does not formalize the proof that the list is complete.

Previously checked torsion and point computations gave trivial torsion for all sixteen Jacobians; rank lower bounds at least2 for masks0,60,104,444,488,1980, and at least1 for masks4,1596,2028. The seven others do not have a proved rank of zero. No rank upper bound has been obtained. These facts are supporting research history, not conclusions of the submitted Lean module.

## New arithmetic reduction

Let L be the degree45 nonzero2-torsion root field, and let Epair, Ematching and F36 be the degree 15,15,36 fixed fields described by the supplied permutation data. The exact coefficient-five identity factors through one copy of each auxiliary permutation module. Its written ideal-class consequence is

    c2(L) <= c2(Epair)+c2(Ematching)+c2(F36).

The same bound holds for class groups localized at the common rational-prime set {2,5}. The norm-relation audit proves the transfer using ideal representatives away from ramification. `NormRelationBridge` formalizes only the abstract linear algebra after the arithmetic maps and their relation have been established.

The irreducible S6 constituent indexed by(3,2,1) occurs in the flagged-matching representation and forces some auxiliary field to have degree at least36 in any such rational correspondence factorization. The degree 36 field is unique up to conjugacy in this closure. `node2_minimum_auxiliary_degree.py` checks the character calculation by two formulas and the finite group data. This is a limitation of this method, not an obstruction to other mathematics.

## Explicit fields and checks

The original sextic model is

    z^6-2z^5-165z^4-1260z^3-4185z^2-5022z+18954.

The matching field has degree 15, signature(3,6), and discriminant
`2^8*5^28*2003282059^6`. Its exact embedding and the quartic pair-product invariant are supplied. F36 has signature(4,16) and discriminant
`2^36*5^66*2003282059^18`. Its relative Cayley resolvent, absolute norm, reduced model and exact map are supplied. Independent Sage checks reconstruct the resolvent norm by a6x6 determinant and verify the matching embeddings. PARI maximal-order certificates returned empty exception lists for both fields. These maximal-order checks are not class-group completeness certificates.

Bounded candidate class-group attempts: F36 overflowed a1GB stack after23.36s; a2GB run reached120.05s without returning a candidate. Matching15 attempts with512MB and1GB each reached120s without a candidate; changing the factor base and relation strategy did not improve observed throughput. A compositum construction from the two sextic subfields reduced to the same F36 polynomial. No GRH-based numerical answer is promoted to an unconditional theorem.

## Reproduction

Use a checkout with Lean4.33.1, Mathlib0df444a360eaa60ab8c11dca51a86af692955474 and the repository's pinned Formal Conjectures dependencies. Run `lake env lean -DwarningAsError=true script.lean`. Each other artifact is research data or documentation, not an imported Lean premise.

In a scratch copy of this flat contribution directory, the Python-standard-library checkers are `verify_odd_norm_relation.py`, `node2_norm_relation_audit.py`, `node2_minimum_auxiliary_degree.py`, and `quartic_cover_verify.py`. They read adjacent JSON files and write diagnostic JSON beside themselves. The Cayley derivation and the two field checkers use Sage; the imports name the `sage.all__sagemath_schemes` aggregation available in the Passagemath environment used here. A standard Sage installation can import the corresponding objects from `sage.all`. Record tool versions when replaying; these computations are outside the Lean kernel.

The additional Python-standard-library checker `verify-isogeny-screen.py` verifies the small-prime-isogeny obstructions, including independent finite-curve point counts. It supplies no Lean premises.

The raw session archives, installed runtimes, account information and large binary caches are not required by the proofs and are not included in this bounded contribution record. The artifact limit is32 files,1MiB per file,4MiB total. All eight completed research proof modules and the ratio interface are consolidated into the standalone Lean source, with diagnostic duplicates omitted.

## Remaining obstacle

Useful unconditional upper bounds for the localized2-primary class groups are still missing. Even with these, independent Selmer constraints, target rank bounds, complete point analysis, the remaining lengths, and the final pinned Lean theorem would still be required to settle the bounty. The uniform-contact obstruction note is retained so a successor does not repeat that exhausted path.
