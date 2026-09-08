# Sources and provenance — Erdős Problem 145 partial contribution

**Target.** `Erdos145.erdos_145` in `FormalConjectures/ErdosProblems/145.lean` (reward theorem).
**Contribution file.** `CW_erdos_145.lean`, everything inside `namespace Contribution.Erdos145Gaps`, 20 declarations, no `sorry`/`axiom`/`native_decide`/`set_option`/`#eval`/`partial`/`unsafe`.

## Obstacle

The pool file states three companions — `erdos_145.variants.le_two`, `erdos_145.variants.le_three`, `erdos_145.variants.le_eleven_thirds` — whose conclusions are the *same* unproved formula
`∃ β, Tendsto (fun x ↦ 1 / x * ∑ n ∈ A x, (s (n + 1) - s n : ℝ) ^ α) atTop (𝓝 β)`,
differing only in the admitted range of `α`. Each needs two ingredients present neither in the pool file nor in the pinned Mathlib (`v4.27.0`):

1. a **gap bound** for consecutive squarefree numbers. Grepping the pinned Mathlib for `Squarefree` finds no statement locating a squarefree number in a short interval;
2. the **squarefree density** `#{n ≤ x | Squarefree n} / x → 6 / π²`, which is exactly the `α = 0` case (because `(s (n + 1) - s n) ^ (0 : ℝ) = 1`), and for which Mathlib has no counting or density estimate at all.

In addition the target's index set `A x` is a `Finset.preimage` of an `Icc` under `Nat.nth Squarefree`, a shape to which no Mathlib summation lemma applies; it has to be identified with a `Finset.range` before the sum can be manipulated.

## Delta — what this file adds

* **A checked elementary sieve bound.** `exists_squarefree_mem_Ioc`: if `0 < t` and `16 * (m + t) < (t + 4)^2` then `(m, m + t]` contains a squarefree number. Proof: a non-squarefree `n` in the interval is divisible by `d * d` for some prime `d ≤ √(m + t)`; the multiples of `d * d` in the interval number at most `t / d² + 1` (`card_filter_dvd_Ioc` gives the exact count `m / k + N = (m + t) / k`, avoiding truncated subtraction; `card_filter_dvd_Ioc_le` is its real-valued form); and `∑_{d = 2}^{D} 1 / d² ≤ 3 / 4` (`sum_inv_mul_self_Icc_le`, telescoping `1/d² ≤ 1/(d(d-1))`) leaves a quarter of the interval uncovered as soon as `t + 4 > 4 √(m + t)`.
* **Explicit `O(√m)` squarefree gaps.** `exists_squarefree_Ioc_sqrt` and `nextSquarefree_le`: `nextSquarefree m ≤ m + 4 * Nat.sqrt m + 8` for every `m`; `s_succ_le` transports it to the target's own sequence, `s (n + 1) ≤ s n + 4 * Nat.sqrt (s n) + 8` — the bound any attack on general `α` needs for the large-gap contribution.
* **A definition with its API.** `nextSquarefree` (least squarefree number `> m`) with `squarefree_nextSquarefree`, `lt_nextSquarefree`, `nextSquarefree_le_of_squarefree` (minimality), `nextSquarefree_le`, and the bridge `s_succ : s (n + 1) = nextSquarefree (s n)`.
* **An interface to the target's bespoke objects.** `A_eq_range : Erdos145.A x = Finset.range (Nat.count Squarefree (⌊x⌋₊ + 1))` (unconditional, including `x < 0`); `s_zero`; `sum_sub_eq` (telescoping: the `α = 1` sum equals `nextSquarefree ⌊x⌋₊ - 1`); `sum_rpow_zero` (the `α = 0` sum is the squarefree counting function).
* **A case of the companions, proved.** `tendsto_sum_rpow_one` computes the `α = 1` average (limit `1`); `erdos_145_variants_le_two_at_one` is that result in the exact shape of the companions at `α = 1`.
* **A checked equivalence delimiting what is left.** `erdos_145_at_zero_iff_count`: for every `β`, the `α = 0` case holds with limit `β` **iff** `#{n ∈ range (⌊x⌋₊ + 1) | Squarefree n} / x → β`. This is an equivalence, not a one-way reduction, so it cannot be refuted for any legal instance of the target's binders.

## Verification

* Toolchain `leanprover/lean4:v4.27.0`; Mathlib pinned at rev `v4.27.0` (`lakefile.toml`).
* `lake env lean CW_erdos_145.lean` → exit 0, **zero errors, zero warnings**.
* `#print axioms` on all 20 declarations → `[propext, Classical.choice, Quot.sound]` for every one (run in a scratch copy; the `#print` lines are not shipped).
* **Statement-identity check.** Run in a scratch copy of the file (deliberately not shipped, so that the deliverable depends on no unproved declaration); all three typecheck:

```lean
example (h : (1:ℝ) ∈ Set.Icc (0:ℝ) 2) :
    Contribution.Erdos145Gaps.erdos_145_variants_le_two_at_one
      = Erdos145.erdos_145.variants.le_two h := rfl

example (h : (1:ℝ) ∈ Set.Icc (0:ℝ) 3) :
    Contribution.Erdos145Gaps.erdos_145_variants_le_two_at_one
      = Erdos145.erdos_145.variants.le_three h := rfl

example (h : (1:ℝ) ∈ Set.Icc (0:ℝ) (11/3)) :
    Contribution.Erdos145Gaps.erdos_145_variants_le_two_at_one
      = Erdos145.erdos_145.variants.le_eleven_thirds h := rfl
```

* **Non-vacuity.** `exists_squarefree_mem_Ioc`'s hypotheses are satisfiable for every `m` — the file itself instantiates them (`exists_squarefree_Ioc_sqrt`, with `t = 4 * Nat.sqrt m + 8`) and derives a non-trivial conclusion.
* **Novelty probes** (all run against the pinned environment): `exact?` fails on the statement of `card_filter_dvd_Ioc`; `simp` "made no progress" on `A_eq_range` and on `s_zero`; grepping Mathlib for `Squarefree` alongside `count`/`card`/`density`/`asympt`/`nth` returns only unrelated hits (`ZGroup`, `Moebius`, `Antidiag`).

## References

* Erdős Problem 145: https://www.erdosproblems.com/145
* Pool repository (statement source): https://github.com/google-deepmind/formal-conjectures
* Mathlib `Nat.nth` / `Nat.count` API used throughout: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Nth.html
* Background on squarefree density `6/π²` and squarefree gaps: https://en.wikipedia.org/wiki/Square-free_integer
* Bibliography cited by the pool file (listed for context; **not** consulted, and no argument taken from them): P. Erdős, *Some problems and results in elementary number theory*, Publ. Math. Debrecen 2 (1951), 103–109; C. Hooley, *On the intervals between consecutive terms of sequences*, Proc. Symp. Pure Math. 24 (1973), 129–140; G. Greaves, G. Harman, M. N. Huxley (eds.), *Sieve Methods, Exponential Sums, and their Applications in Number Theory* (1997). The much sharper `O(x^{1/5+ε})` squarefree-gap results (Filaseta–Trifonov) are **not** used or formalised here; the bound proved here is the elementary `O(√m)` one, which is all the `α = 1` case needs.

## AI assistance and originality

This contribution was produced by Claude (Anthropic), driven by the contributor in a Claude Code session on 2026-09-02. All Lean statements, proofs and prose in `CW_erdos_145.lean` were written for this submission and checked by the Lean 4 kernel; nothing was copied from another repository, from Mathlib, or from a `formal_proof` link (the pool file's companions carry no proofs to copy). The underlying counting argument — cover a short interval by multiples of `d²` and use `∑ 1/d² < 1` — is standard elementary number theory; the Lean development, the explicit constants (`4 √m + 8`, the `3/4` bound), the `nextSquarefree` API and the interface lemmas to the pool file's `s` and `A` are original to this file.
