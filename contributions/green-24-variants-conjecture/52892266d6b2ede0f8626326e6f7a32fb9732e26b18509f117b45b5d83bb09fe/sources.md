# Green 24: cyclic profile upper bounds and support peeling

## Target, obstacle, and exact contribution

Target: `green-24-variants-conjecture`, reward target
`fc-target:Green24.variants.conjecture`. The official statement is
`Green24.variants.gamma = 1 / 3`.

This submission formalizes a coherent part of the cyclic-profile upper-bound route.
For nonnegative g on Z/qZ, q positive, define

    Gamma_q(g) = (1/6) sum_(s,t) G(g_(3t-2s), 2*g_s, 3*g_t).

The file's `kernel` is symmetric and agrees with the sorted-coordinate formula
in Definition 1.3 of the paper below. Theorem `cyclicScore_eq_relation_sum` proves
the exact relation-sum expression for coefficients (1,2,-3). In particular this
is not a differently normalized toy score.

The main theorem is a weighted finite-support peeling argument. It proves the
bound Gamma_q(g) <= (sum g)^2/3 whenever doubling is injective on the positive
support. For even q this is the mathematical kernel-coset version of having no
occupied antipodal pair. The actual formal hypothesis is stated in terms of
injectivity; no unproved equivalence is needed by the Lean chain.

Consequently the bound holds for every odd modulus. A separate permutation
argument covers every modulus coprime to three. A supercritical profile must
therefore have 6 dividing q AND two distinct positive coordinates with equal
doubles. Constant profiles attain the bound exactly after normalization.

## Reusable declarations and checked use sites

All names are under `Contribution.Green24CyclicProfiles`.

- `rawScore_le_of_support_injective`: the general finite weighted-incidence
  peeling theorem, proved by strong induction on support and an actual minimum
  coordinate; it is not supplied as an axiom or a numerical estimate.
- `cyclicScore_le_of_doubling_inj`: the arbitrary-modulus support theorem.
- `cyclicScore_le_odd`, `cyclicScore_le_coprime_three`, and
  `cyclicScore_le_not_six_dvd`: complete infinite families of cyclic inequalities.
- `supercritical_obstructions`: both necessary modulus/support obstructions.
- `cyclicScore_uniform` and `mass_uniform`: exact normalized equality examples.
- `linearCount_eq_affineCount_add_card`: exact diagonal correction between the
  official affine-pair expression and the ordered linear-equation count.
- `gamma_le_of_remaining_profiles`: a deliberately CONDITIONAL connection to
  the official gamma, described next.

The source contains a checked use on arbitrary real-valued probability profiles
modulo 729 and one for every pure power of two. The uniform-profile theorems
verify nonvacuity and sharpness, not just satisfiability of arbitrary hypotheses.

## The analytic bridge remains explicit

Theorem 1.4 of the cited paper identifies the integer asymptotic constant with a
supremum of cyclic-profile maxima. Its proof uses arithmetic regularity and is
NOT formalized or silently trusted here. Matching that result to the exact
Formal Conjectures integer definition remains a formal proof obligation.

`CyclicApproximation` specifies the required approximation property of the
OFFICIAL `Green24.variants.gamma`: for every positive epsilon, some normalized
positive-modulus profile has score greater than gamma-epsilon. It is merely a
named proposition. The conditional theorem `gamma_le_of_remaining_profiles`
takes it as an explicit argument, together with the as-yet unproved upper bound
for mixed moduli with occupied doubling collisions. It then proves the official
upper bound. Neither missing input is asserted globally, imported as a custom
axiom, or concealed in a typeclass.

The main cyclic upper bounds do NOT depend on `CyclicApproximation`. They are
unconditional under their displayed elementary support/modulus hypotheses.
A later solver can use these declarations to discharge all odd/coprime-three
profile obligations and exclude collision-free supports while formalizing the
published cyclic route. This does not claim that the integer target is solved.
The lower-bound/limsup route is already available in prior contributions.

## Sources and provenance

1. Official target:
   https://github.com/conjectures-io/conjectures-tasks/tree/main/pool/tier-1/green-24-variants-conjecture-formalized
   https://conjectures.io/problems/green24-variants-conjecture
2. Zarko Randjelovic, Xuancheng Shao, Max Wenqiang Xu, Shengtong Zhang, Yuan Zhou,
   *Maximising the number of solutions to linear equations*, arXiv:2609.06975v1,
   7 September 2026. Definition 1.3 supplies G and Theorem 1.4 supplies the
   external mathematical context for the cyclic route:
   https://arxiv.org/html/2609.06975v1
   The paper's Theorem 1.7 is about DIFFERENT coefficient triples and is not
   invoked for the current (1,2,-3) problem.
3. The submitter's ordinary-mathematical research notes dated 18 September 2026:
   `VERIFIED_RESULTS.md`, sections 1--3 (kernel and infinite modulus families),
   source SHA-256 `1587d2068269cbbace788dd13614ba3aa4a2c0063e73519942c9895bb4dd010e`;
   and the support-kernel generalization in `PROOF.md`, SHA-256
   `406274bba893f0774d56918c4fa896bdd4dd672293dfd11a568682ed37f1291e`. These are provenance identifiers, not runtime dependencies.
   The new Lean code was written for this submission from those arguments;
   there were no existing Lean sources in the authoritative Green24 workspace.
4. Mathlib supplies general finite-sum, ring, and ZMod APIs:
   https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474
   The official target's expression is from Formal Conjectures (Apache-2.0):
   https://github.com/google-deepmind/formal-conjectures
   The Apache-2.0 license text is included as `license.txt`.

Research and formalization were AI-assisted. No exclusively unaided human work
or worldwide mathematical-priority claim is made. Novelty claimed for review is
the substantial checked support-peeling/cyclic-profile development and reusable
interfaces, not the renaming of elementary arithmetic or the known interval kernel.
The original research corpus was preserved unchanged.

## Prior contributions and lineage

The comparison baseline is `22019a3051609bca40902de7ac3c9764ac0326d7`.
The two existing target contributions were inspected in full:

- `10e86c934afdeeb8cb74f4b0ae90e14953920084c1118c6d6a5ede4ad19411a3`:
  lower bound gamma >= 1/12 and interval witnesses.
  https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/green-24-variants-conjecture/10e86c934afdeeb8cb74f4b0ae90e14953920084c1118c6d6a5ede4ad19411a3
- `04f219993cb1bf85948ba89049562e47915f0a81ef7961a84cd96450fd4bcc77`:
  sharp lower bound gamma >= 1/3 and limsup/finite-n upper-bound interfaces.
  https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/green-24-variants-conjecture/04f219993cb1bf85948ba89049562e47915f0a81ef7961a84cd96450fd4bcc77

Neither supplies the cyclic kernel, support-peeling proof, or these profile upper
bounds. Their artifacts are not imported, copied into this development, or used
as proof evidence, so no contribution parents are declared. The affine-count
helper simply spells the official target expression and is not claimed as a
novel definition. No lower bound is resubmitted under a new signing identity.
All related lemmas are submitted as ONE logical contribution.

## Verification and reproducibility

The single `script.lean` is self-contained and imports only Mathlib and
`FormalConjectures.GreensOpenProblems.«24»`. It uses Lean 4.33.1, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, and audited Formal Conjectures
`8432eac998110a563e03df65a28c117e97c8c142`, matching the contribution source pin.

```sh
contrib check <signed-contribution-directory> --json
contrib elaborate <signed-contribution-directory> --workspace <pinned-workspace> --json
```

A separate private audit checks all public declarations' transitive axioms against
`propext`, `Classical.choice`, and `Quot.sound`. Its metaprogramming commands are
not submitted as artifacts. No finite-grid result, floating-point optimization,
external solver result, unfinished target theorem, or native computation is used
as a proof premise. The final package is also checked for accidental credentials.

## Deliberately not claimed or included

No complete Green24 solution, no unconditional official gamma upper bound, no
formal proof of the external analytic reduction, no bound for all mixed moduli,
and no classification of their maximizers is claimed. In particular the q=6
four-variable block proof, radial inequality, carry formulas, and historical
computational/KKT campaigns have NOT been represented as formalized here.
The remaining-profile hypothesis still includes q=6. Technical acceptance does
not itself establish recognition, a weight, or a payment.
