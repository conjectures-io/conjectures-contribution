# Sources and provenance — erdos-373 contribution

## Target
- Erdős Problem 373, https://www.erdosproblems.com/373
- Pool file: `FormalConjectures/ErdosProblems/«373».lean`, reward theorem `Erdos373.erdos_373 : Erdos373.S.Finite`
  (`@[category research open, AMS 11]`, body `sorry`). Variants used: `erdos_373.variants.maximal_solution`
  (Hickerson: `(16, [14, 5, 2]) ∈ S ∧ ∀ s ∈ S, s.fst ≤ 16`) and `erdos_373.variants.suranyi`
  (the Surányi set equals `{(10, 7, 6)}`).

## Mathematical background (informal, consulted for orientation only)
- P. Erdős, "Some problems in number theory", Theorem 2, https://users.renyi.hu/~p_erdos/1976-39.pdf
  — the reference cited by the pool file itself for the `P(n(n-1)) > 4 log n` variant. Nothing from this
  paper is formalised here; the file contains only elementary consequences proved from scratch.
- Hickerson's conjectured maximal solution `16! = 14!·5!·2!` and Surányi's `10! = 7!·6!` are the two
  numerical facts quoted on https://www.erdosproblems.com/373 ; both are re-verified in Lean by `decide`
  (`hickerson_mem`, and the `(10, [7, 6]) ∈ S` example), not taken on trust.
- The "no prime in `(a₁, n]`" obstruction and its combination with Bertrand's postulate are textbook
  arguments; they are reproved here from Mathlib primitives.

## Mathlib lemmas relied on (pinned toolchain in this repo)
- `List.Pairwise.head!_le` (`Mathlib/Data/List/Pairwise.lean`) — used directly at both sites where the
  previous version had a hand-rolled duplicate.
- `List.finite_length_le` (`Mathlib/Data/Set/Finite/List.lean`) — requires `[Finite α]`; this is exactly
  the gap `finite_bounded_lists` fills for `List ℕ`.
- `Nat.exists_prime_lt_and_le_two_mul` (Bertrand's postulate).
- `Nat.Prime.dvd_factorial`, `Nat.dvd_factorial`, `Nat.factorial_inj`, `Nat.one_lt_factorial`,
  `Nat.factorial_lt`, `Nat.factorial_ne_zero`, `Prime.dvd_prod_iff`.
- `Nat.Prime.pow_dvd_iff_le_factorization` (`Mathlib/Data/Nat/Factorization/Basic.lean`) and
  `Nat.factorization_factorial_le_div_pred` (`Mathlib/Data/Nat/Choose/Factorization.lean`, Legendre)
  — these give the sharp length bound `length_le_fst : l.length ≤ n`.

## Novelty checks performed
- `exact?` fails on the exact statements of `finite_bounded_lists` and of `two_pow_length_dvd_prod`
  against full Mathlib in this environment, so neither is an existing lemma under another name.
- `grep` over `.lake/packages/mathlib/Mathlib` for `head!_le` located the Mathlib lemma that the previous
  submission duplicated; that duplicate has been deleted and Mathlib is called instead.

## AI assistance
This file was written with AI assistance (Anthropic Claude, model Opus 5, operating as a Lean 4 agent).
The AI drafted every statement and proof, ran the Lean compiler, ran `exact?`/`grep` novelty checks, and
performed the repair pass responding to reviewer feedback. All proofs are machine-checked: the file
compiles with `lake env lean CW_erdos_373.lean` with zero errors and zero warnings, contains no `sorry`,
`axiom`, `native_decide` or trust-raising `set_option`, and `#print axioms` on all 15 named declarations
returns only subsets of `[propext, Classical.choice, Quot.sound]` (two are axiom-free). No mathematical
claim in this file is asserted on the AI's authority; the Lean kernel is the warrant.

## Originality
All Lean statements and proofs in this file are original work produced for this submission; none were copied from an existing formalisation (Mathlib, FormalConjectures, another contribution, or elsewhere). The strict length bound `length_lt_fst` was added in response to review.
