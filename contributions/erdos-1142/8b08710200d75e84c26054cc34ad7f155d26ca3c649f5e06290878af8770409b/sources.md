# sources.md — partial contribution to erdos-1142

## Target

`Erdos1142.erdos_1142` in `FormalConjectures/ErdosProblems/1142.lean`: are there infinitely many
`n > 2` such that `n - 2^k` is prime for every `k >= 1` with `2^k < n`? The only known such `n`
are 4, 7, 15, 21, 45, 75, 105. The same file also carries the unproved variant
`erdos_1142.variants.mientka_weitzenkamp`, which asserts that these seven are the only such
`n <= 2^44`.

## The obstacle

`Erdos1142Prop n` is stated as `2 < n /\ forall k, 0 < k -> 2^k < n -> (n - 2^k).Prime`. That is
an unbounded universally quantified primality condition, and in that shape it is inert:

* it kills one `n` at a time only, each time needing an explicit exponent `k`, so the `subseteq`
  half of the Mientka-Weitzenkamp variant is a search over ~1.76e13 candidates with no way to
  eliminate a residue class wholesale;
* the unbounded `forall k` means the predicate carries no `Decidable` instance, so it cannot be
  `decide`d, filtered into a `Finset`, or handed to a finiteness argument;
* the pool file's own helper `prove_erdos_1142_prop` certifies a candidate by
  `interval_cases k <;> simp_all (config := { decide := true })`, i.e. kernel evaluation of
  primality, which does not scale past small numerals;
* the infinitude side of the target statement gives no structural constraint on where solutions
  can live.

## The delta

One self-contained file, `namespace Contribution.Erdos1142Sieve`, 24 declarations (22 theorems,
one `Decidable` instance, one `example`), all proved, no `sorry` anywhere and no added axioms.

The engine is `dvd_of_covering`. If a prime `p` has the property that every nonzero residue mod
`p` is `2^k mod p` for some `1 <= k <= K` — a finite, `by decide`-checkable hypothesis, which for
`K = p - 1` says exactly that 2 is a primitive root mod `p` — then every `n > 2^K + p` with
`Erdos1142Prop n` is divisible by `p`. The proof is the sieve step
`eq_two_pow_add_of_prime_dvd_sub`: since `n - 2^k` is *prime*, any prime `p` dividing it equals
it, pinning `n = 2^k + p <= 2^K + p`, a contradiction. Instantiating at `p = 3, 5, 11, 13, 19`
(2 is a primitive root at each) gives:

* `three_dvd` : `n > 7 -> 3 | n`;
* `five_dvd` : `n > 21 -> 5 | n`;
* `eleven_dvd` : `n > 1035 -> 11 | n`;
* `thirteen_dvd` : `n > 4109 -> 13 | n`;
* `nineteen_dvd` : `n > 262163 -> 19 | n`.

The prime `p = 2` is the one case this sieve cannot supply: for `p = 2` the covering hypothesis
is unsatisfiable, because `2^k = 0 mod 2` for every `k >= 1`, so the residue 1 is never hit.
Parity is therefore proved separately and directly from `eq_two_pow_add_of_prime_dvd_sub`, as
`odd_of_four_lt` : `n > 4 -> Odd n` (4 is the only even solution). Packaged together:

* `mod_thirty_eq_fifteen` : `n > 21 -> n % 30 = 15`  (parity together with `p = 3, 5`);
* `dvd_2145` : `n > 4109 -> 2145 | n`  (2145 = 3 * 5 * 11 * 13);
* `dvd_40755` : `n > 262163 -> 40755 | n`  (40755 = 3 * 5 * 11 * 13 * 19).

Around that: `prop_iff_forall_mem_Icc` replaces the unbounded quantifier by a quantifier over
`Finset.Icc 1 (Nat.log 2 n)` and yields the `Decidable` instance `decidableErdos1142Prop`;
`prop_of_forall_mem_Icc` is the `norm_num`-friendly certification direction with an explicit
exponent bound; `not_prop_of_not_prime_sub` is the one-exponent refutation certificate.

`prop_of_forall_mem_Icc` reaches much further than kernel evaluation, but its reach is bounded,
and the file now says so in measured terms instead of calling it scalable. In this workspace:
`decide` on the predicate already exceeds the default recursion depth at `n = 4095`
(`example : ¬ Erdos1142Prop 4095 := by decide` fails with "maximum recursion depth has been
reached"), while `norm_num` proves a ten-digit primality goal (`Nat.Prime 1000000007`) in about
32 seconds including imports and aborts with a stack overflow on a twelve-digit one
(`Nat.Prime 100000000003`). So the certification route is worth roughly ten digits — far past
`decide`, and far short of `2^44`. Both are measurements run in the pinned workspace, not
estimates.

Two checked search results follow. `eq_of_le_4109` proves that every `n <= 4109` with the
property is one of the seven known solutions — the sieve leaves only 44 values in `[3, 4109]` to
refute (4 below 22, 31 in `(21, 1035]`, 9 in `(1035, 4109]`), each dispatched by a single
exponent and a `norm_num` factorisation. `mientka_weitzenkamp_le_4109` states this in exactly
the shape of the pool's variant with `2^44` replaced by 4109, reusing the target file's own
`erdos_1142.test_4 ... test_105` for the reverse inclusion.

Use sites, all compiled in the file:

* `mientka_weitzenkamp_of_residual` derives the *full* statement of
  `erdos_1142.variants.mientka_weitzenkamp` (bound `2^44`) from the single residual hypothesis
  that no multiple of 2145 in `(4109, 2^44]` has the property. This is the concrete handoff: it
  removes 2144 of every 2145 residues from the remaining search (~1.76e13 candidates down to
  ~8.2e9) and closes `n <= 4109` outright.
* `mientka_weitzenkamp_of_residual_sharp` is the same reduction with the 19-sieve switched on:
  the residual becomes the 121 multiples of 2145 in `(4109, 262163]` plus the multiples of 40755
  in `(262163, 2^44]`, i.e. ~4.3e8 candidates in the range that dominates — a further 19-fold
  cut.
* `infinite_iff_infinite_mod_thirty` rewrites the right-hand side of `erdos_1142` itself:
  `Infinite {n | Erdos1142Prop n} <-> Infinite {n | Erdos1142Prop n /\ n % 30 = 15}`.
* `example : Erdos1142Prop 105` and `not_prop_nine` demonstrate the certification lemma and the
  new `Decidable` instance respectively (`not_prop_nine` is used by `eq_of_le_4109`).

Neither obligation of the pool file is discharged here, and nothing in the file claims otherwise.
4109 is a vanishing fraction of `2^44`, and the residual searches — ~8.2e9, or ~4.3e8 with the
19-sieve — remain far out of kernel reach. What is delivered is the machine-checked initial
segment, the missing `Decidable` instance, and a reduction of the open part by a factor of 2145
(40755 above 262163).

## Verification

Compiled against the pinned workspace (Lean toolchain `leanprover/lean4:v4.27.0`, Mathlib
`v4.27.0`) with `lake env lean CW_erdos_1142.lean`: exit code 0, zero errors, zero warnings,
about 35 seconds wall clock including imports. `#print axioms` was run on all 23 named
declarations (22 theorems and the instance; the `example` has no name to print) and then removed:
each depends only on a subset of `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no new
axiom. `eq_two_pow_add_of_prime_dvd_sub` and `not_prop_of_not_prime_sub` depend on `[propext]`
alone. The file was recompiled clean after the `#print axioms` lines were deleted. It contains no
`sorry`, `admit`, `axiom`, `native_decide`, `#eval`, `unsafe`, `partial`, `extern`,
`implemented_by` or `set_option`; every `decide` in it is plain, kernel-checked `decide`.

All numeric witnesses (which exponent `k` refutes which candidate, and the candidate lists
themselves) were computed independently in Python and then re-derived inside Lean by `norm_num`;
nothing is asserted that the kernel has not checked.

Novelty check: every statement is about the bespoke `Erdos1142.Erdos1142Prop`, so none of it can
exist in Mathlib; `grep` over
`.lake/packages/mathlib/Mathlib` found no counterpart, and the only other occurrences of
`Erdos1142Prop` anywhere in the pinned workspace are automated one-line tactic sweeps
(`Sweep.lean`, `Chunk1.lean`, `Str1.lean`, `Int1.lean`, `Probes/P016.lean`) that prove nothing
about it.

## Corrections made after review

Review found no unsound, duplicated or vacuous declaration, and no proof was changed. What was
wrong was the module docstring, and it has been corrected:

* the claim that `prop_of_forall_mem_Icc` gives "a `norm_num`-friendly way to certify a candidate
  of any size" was false and is gone; the docstring now states the measured ceiling of about ten
  digits and names the failure at twelve;
* the claim that the certification route "scales to candidates far beyond the reach of the kernel
  evaluator" is now bounded on both sides by measurements: `decide` fails at `n = 4095`, and
  `norm_num` primality gives out around eleven to twelve digits, well short of `2^44`;
* `odd_of_four_lt` was listed among "the instances" of `dvd_of_covering`. It is not one and
  cannot be: at `p = 2` the covering hypothesis is unsatisfiable. The contents list and the
  overview paragraph now say that explicitly and separate the parity case from the four (now
  five) genuine instances;
* this file's matching "the scalable replacement for the pool file's `decide`-based local macro"
  wording has been replaced by the same measured bounds.

The review also pointed out that `p = 19` is a free extension of the same engine. It has been
added (`nineteen_dvd`, `dvd_40755`, `mientka_weitzenkamp_of_residual_sharp`), and the whole file
still compiles clean and axiom-clean as reported above.

## Sources

* Erdős Problem 1142 — https://www.erdosproblems.com/1142
* OEIS A039669, "Numbers n > 2 such that n - 2^k is prime for all 0 < 2^k < n" —
  https://oeis.org/A039669
* OEIS A001122, "Primes with primitive root 2" (contains 3, 5, 11, 13, 19, which is exactly why
  the covering hypothesis of `dvd_of_covering` holds for those primes) —
  https://oeis.org/A001122
* W. E. Mientka and R. C. Weitzenkamp, "On f-plentiful numbers", Journal of Combinatorial Theory
  7 (1969), no. 4, 374-377 — issue listing at
  https://www.sciencedirect.com/journal/journal-of-combinatorial-theory/vol/7/issue/4
  (this is the source of the `n <= 2^44` claim formalised in the pool file's variant; I did not
  have access to the paper's text and did not copy its argument — the sieve here was derived
  from scratch)
* Various, "Some of Paul's favorite problems", booklet for the conference "Paul Erdős and his
  mathematics", Budapest, 1999 (cited by the pool file)
* Mathlib — https://github.com/leanprover-community/mathlib4
* formal-conjectures — https://github.com/google-deepmind/formal-conjectures

## Originality

All statements and all proofs in the submitted file are original work written for this
submission. Nothing was copied from any source: not from another contribution, not from a
solution set, not from Mathlib or any other formalisation, not from the Mientka-Weitzenkamp paper
(whose text I did not have), and not from any online write-up. The underlying idea — a covering
argument over primes with primitive root 2 — is classical mathematics in the public domain; every
Lean statement, every proof term and every tactic script expressing it here was written from
scratch, and the numeric witnesses were computed for this file.

## Disclosure

This contribution was produced with AI assistance (Anthropic Claude, driven interactively in a
terminal agent). The mathematical idea, the Lean statements and every proof in the submitted
file were developed in this session. Numeric search (candidate lists and refuting exponents) was
done in Python and is fully re-verified inside Lean. Everything claimed above was checked by
running the compiler; no result is reported that was not compiled, and the tooling limits quoted
above are measurements from this workspace, not estimates.
