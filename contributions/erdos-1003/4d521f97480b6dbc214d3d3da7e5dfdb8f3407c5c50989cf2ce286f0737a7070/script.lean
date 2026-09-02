import Mathlib
import FormalConjectures.ErdosProblems.«1003»

/-!
# Erdős Problem 1003: a checked API for `φ n = φ (n + 1)`

This file is an incremental contribution towards `Erdos1003.erdos_1003`
([erdosproblems.com/1003](https://www.erdosproblems.com/1003)), which asks whether
`{n | φ n = φ (n + 1)}` is infinite.  Nothing here solves the problem.  The goal is a small
checked API around the three statements of the target file.

## The obstacle

The target file states the same phenomenon three times, in three shapes that do not talk to
each other, and none of the three shapes is directly workable:

* `Erdos1003.erdos_1003` asks for `Set.Infinite {n | φ n = φ (n + 1)}`.  `Set.Infinite` is a
  negated finiteness predicate with no computational content, whereas every analytic route to
  the problem produces *lower bounds on a counting function*.  Mathlib does contain a general
  bridge between the two: `Set.infinite_iff_tendsto_sum_indicator_atTop`
  (`Mathlib/Algebra/Order/Archimedean/IndicatorCard.lean`) states, for any `s : Set ℕ` and any
  `0 < r`, that `s.Infinite ↔ Tendsto (fun n => ∑ k ∈ Finset.range n,
  s.indicator (fun _ => r) k) atTop atTop`, and `Nat.frequently_atTop_iff_infinite`
  (`Mathlib/Order/Filter/Cofinite.lean`) is a second, filter-level bridge into `Set.Infinite`.
  What is missing is only the last step: the general lemma presents the counting function as
  a running sum of indicators, which carries no `Decidable` instance and is not the
  `Finset.filter`-card shape in which a solution count is evaluated, checked against data, or
  shared with the `eps87` variant below.
* `Erdos1003.erdos_1003.variants.Icc` is about the star-shaped family
  `{n | ∀ i ∈ Set.Icc 1 k, φ n = φ (n + i)}`, whose defining condition compares `φ n` with
  every `φ (n + i)` and carries an inconvenient `1 ≤ i` side condition.  As stated it is
  neither induction-friendly nor decidable (a bounded quantifier over a `Set` carries no
  `Decidable` instance), so not even a numerical witness can be checked against it.
* `Erdos1003.erdos_1003.variants.eps87` is a counting statement about `Set.ncard`, which is
  junk-valued (`0`) on infinite sets.  Before any bound can be proved one has to produce a
  finiteness proof and identify the `ncard` with a concrete counting function.

## What is provided

1. **The `ncard` bridge for the `eps87` variant.**  `solCount N` is the `Finset.filter`-card
   count of the solutions `n ≤ N`; unlike a `Set.ncard` it is total, decidable and monotone.
   `setOf_le_eq_coe_filter` identifies the set counted in the `eps87` variant with the
   coercion of an explicit `Finset` (so it is finite, and its `ncard` is not junk-valued), and
   `ncard_setOf_le_eq_solCount` rewrites that `Set.ncard` as `solCount ⌊x⌋₊`.  Neither
   statement was found by `exact?` in a Mathlib-only scope.  *A later solver can use
   declaration `Contribution.Erdos1003TotientRuns.ncard_setOf_le_eq_solCount` to discharge or
   simplify obligation `({n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n + 1)}.ncard : ℝ) ≤ x / Real.exp
   (Real.log x ^ (1 / 3 : ℝ))` in target `Erdos1003.erdos_1003.variants.eps87`*
   (use site 1 below).
2. **The same counting function for the reward theorem.**
   `infinite_sol_iff_tendsto_solCount` is the equivalence
   `{n | φ n = φ (n + 1)}.Infinite ↔ Tendsto solCount atTop atTop`.  This is a *specialisation
   of the Mathlib lemma `Set.infinite_iff_tendsto_sum_indicator_atTop` quoted above, and it is
   proved from that lemma here* rather than re-proved from scratch; the work is the passage
   from the running sum of indicators over `Finset.range n` to the decidable `Finset.filter`
   card over `Finset.range (N + 1)`, together with the resulting index shift.  What the
   specialisation buys is a single counting function shared with the `eps87` variant, on which
   concrete data can be checked: `solCount_105 : solCount 105 = 4`.  *A later solver can use
   declaration `Contribution.Erdos1003TotientRuns.infinite_sol_iff_tendsto_solCount` to
   discharge or simplify obligation `Set.Infinite {n | φ n = φ (n + 1)}` in target
   `Erdos1003.erdos_1003`* (use site 2 below).
3. **The `Icc` variant made usable.**  `Run k` is the set of that variant;
   `mem_run_iff_forall_le` drops the `1 ≤ i` side condition and `mem_run_iff_chain` replaces
   the star shape `φ n = φ (n + 1) = ⋯ = φ (n + k)` by the chain of consecutive equalities
   `∀ i < k, φ (n + i) = φ (n + i + 1)`.  The chain form is induction-friendly and decidable:
   `decidableMemRun` is the resulting instance, and `mem_run_two_5186` is a checked witness
   `φ 5186 = φ 5187 = φ 5188 = 2592` for `k = 2`.  *A later solver can use declaration
   `Contribution.Erdos1003TotientRuns.mem_run_iff_chain` to discharge or simplify obligation
   `∀ k ≥ 1, {n | ∀ i ∈ Set.Icc 1 k, φ n = φ (n + i)}.Infinite` in target
   `Erdos1003.erdos_1003.variants.Icc`* (use site 3 below).

   **Honest framing.**  The `Icc` variant is *strictly stronger* than the reward theorem:
   infinitude of `Run k` for some `k ≥ 1` implies infinitude of `{n | φ n = φ (n + 1)}`, but
   not conversely.  So this part of the file is **not** progress on `erdos_1003`; it is an
   API for the harder `Icc` target, usable only once a run construction exists.  The bridge
   `(Run k).Infinite → {n | φ n = φ (n + 1)}.Infinite` is deliberately *not* stated here: it
   is a one-line consequence of `mem_run_iff_chain` and would advertise as progress a
   reduction that goes the wrong way.
4. **Negative information about solutions.**  `two_mul_totient_le_of_even` (`2 * φ n ≤ n` for
   even `n`) is absent from Mathlib — Mathlib has `Nat.totient_le`, `Nat.totient_lt`,
   `Nat.totient_two_mul_of_even/odd`, none of which give it.  It powers
   `two_mul_totient_le_of_sol`: *every* solution satisfies `2 * φ n ≤ n + 1`, and hence
   neither `n` (`not_prime_of_sol`, for `n ≥ 4`) nor `n + 1` (`not_prime_succ_of_sol`, for
   `n ≥ 2`) is prime.  Both bounds are sharp (`n = 1` with `2` prime, `n = 3` with `3`
   prime).  So no construction of solutions can go through a prime on either side.
5. **A checked search bound.**  `filter_range_106` is an exhaustive kernel check that
   `1, 3, 15, 104` are the only solutions below `106` (OEIS A001274), and `sol_lt_106_iff`
   is its `rcases`-friendly form: any solution `n < 106` is one of those four.

Three worked use sites at the end of the file are stated against the *literal* statements of
`Erdos1003.erdos_1003.variants.eps87`, `Erdos1003.erdos_1003` and
`Erdos1003.erdos_1003.variants.Icc` (each conclusion below was checked to be accepted by
the corresponding target theorem verbatim), and a fourth `example`, next to `decidableMemRun`,
demonstrates that the decidability instance really fires in the kernel.
-/

open scoped Nat
open Filter

namespace Contribution.Erdos1003TotientRuns

/- ### The counting function, and the reward theorem as a counting statement -/

/-- The number of `n ≤ N` with `φ n = φ (n + 1)`.  Unlike the `Set.ncard` of the `eps87`
variant this is a total, decidable, monotone function of `N`. -/
def solCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => φ n = φ (n + 1))).card

/-- **The reward theorem as a counting statement.**  `{n | φ n = φ (n + 1)}` is infinite if
and only if the counting function `solCount` tends to infinity.

This is a specialisation of the Mathlib lemma `Set.infinite_iff_tendsto_sum_indicator_atTop`
(`Mathlib/Algebra/Order/Archimedean/IndicatorCard.lean`), which proves the same equivalence
for an arbitrary `s : Set ℕ` with the counting function written as a running sum of
indicators, and it is *proved from that lemma* below.  What is added here is the passage to
the decidable `Finset.filter` card `solCount N` over `Finset.range (N + 1)` — the encoding on
which numerical data can be checked (`solCount_105`) and which the `eps87` variant reuses
(`ncard_setOf_le_eq_solCount`) — together with the index shift this costs. -/
theorem infinite_sol_iff_tendsto_solCount :
    {n | φ n = φ (n + 1)}.Infinite ↔ Tendsto solCount atTop atTop := by
  have key : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, ({m : ℕ | φ m = φ (m + 1)}).indicator (fun _ => (1 : ℕ)) k
        = ((Finset.range n).filter (fun m => φ m = φ (m + 1))).card := by
    intro n
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : φ k = φ (k + 1) <;> simp [hk]
  rw [Set.infinite_iff_tendsto_sum_indicator_atTop (r := (1 : ℕ)) Nat.one_pos]
  simp only [key]
  constructor
  · intro h
    exact h.comp (tendsto_add_atTop_nat 1)
  · intro h
    refine (h.comp (tendsto_sub_atTop_nat 1)).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply, solCount]
    rw [show n - 1 + 1 = n from by omega]

/- ### The `Set.ncard` of the `eps87` variant -/

/-- The set counted in `Erdos1003.erdos_1003.variants.eps87` is the coercion of an explicit
`Finset`.  In particular it is finite, so its `Set.ncard` is not junk-valued. -/
theorem setOf_le_eq_coe_filter {x : ℝ} (hx : 0 ≤ x) :
    {n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n + 1)}
      = ↑((Finset.range (⌊x⌋₊ + 1)).filter (fun n => φ n = φ (n + 1))) := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Nat.lt_succ_iff,
    Set.mem_setOf_eq, Nat.le_floor_iff hx]

/-- The `Set.ncard` occurring in `Erdos1003.erdos_1003.variants.eps87` equals the decidable
counting function `solCount` evaluated at `⌊x⌋₊`. -/
theorem ncard_setOf_le_eq_solCount {x : ℝ} (hx : 0 ≤ x) :
    {n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n + 1)}.ncard = solCount ⌊x⌋₊ := by
  rw [setOf_le_eq_coe_filter hx, Set.ncard_coe_finset]
  rfl

/- ### A checked search bound -/

/-- An exhaustive kernel check: the only `n ≤ 105` with `φ n = φ (n + 1)` are `1, 3, 15`
and `104` (OEIS A001274).  The check is performed by the kernel (`decide +kernel`), so no
elaboration-depth option is needed and the trusted base is unchanged. -/
theorem filter_range_106 :
    (Finset.range 106).filter (fun n => φ n = φ (n + 1)) = {1, 3, 15, 104} := by
  decide +kernel

/-- The `rcases`-friendly form of the search bound: a solution below `106` is one of the four
explicit values.  This is the form usable inside a proof by cases on a small solution. -/
theorem sol_lt_106_iff {n : ℕ} (hn : n < 106) :
    φ n = φ (n + 1) ↔ n = 1 ∨ n = 3 ∨ n = 15 ∨ n = 104 := by
  constructor
  · intro h
    have hmem : n ∈ (Finset.range 106).filter (fun m => φ m = φ (m + 1)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, h⟩
    rw [filter_range_106] at hmem
    simpa using hmem
  · intro h
    have hmem : n ∈ (Finset.range 106).filter (fun m => φ m = φ (m + 1)) := by
      rw [filter_range_106]
      simpa using h
    exact (Finset.mem_filter.mp hmem).2

/-- Concrete data for the counting function of `infinite_sol_iff_tendsto_solCount`: there are
exactly four solutions `n ≤ 105`. -/
theorem solCount_105 : solCount 105 = 4 := by
  rw [solCount, show (105 + 1 : ℕ) = 106 from by norm_num, filter_range_106]
  decide

/- ### The half bound for even arguments, and the resulting primality obstructions -/

/-- For an even argument the totient is at most half of it.  Mathlib has `Nat.totient_le`,
`Nat.totient_lt` and `Nat.totient_two_mul_of_even`, but not this sharpening; the proof goes
through the `2`-adic valuation (`Nat.ordProj_mul_ordCompl_eq_self`). -/
theorem two_mul_totient_le_of_even {n : ℕ} (hn : Even n) : 2 * φ n ≤ n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  have h2 : (2 : ℕ) ∣ n := hn.two_dvd
  have hkpos : 0 < n.factorization 2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn0 h2
  set k := n.factorization 2 with hk
  have hsplit : 2 ^ k * (n / 2 ^ k) = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime (2 ^ k) (n / 2 ^ k) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn0)
  have htot : φ n = 2 ^ (k - 1) * φ (n / 2 ^ k) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow Nat.prime_two hkpos]
    simp
  have h2k : 2 * 2 ^ (k - 1) = 2 ^ k := by
    conv_rhs => rw [show k = (k - 1) + 1 from by omega]
    rw [pow_succ]
    ring
  calc 2 * φ n = 2 ^ k * φ (n / 2 ^ k) := by rw [htot, ← mul_assoc, h2k]
    _ ≤ 2 ^ k * (n / 2 ^ k) := Nat.mul_le_mul_left _ (Nat.totient_le _)
    _ = n := hsplit

/-- **Every** solution of `φ n = φ (n + 1)` has a small totient: `2 * φ n ≤ n + 1`.  One of
`n`, `n + 1` is even, and the equation transports the half bound to the other one.  This is
the quantitative constraint behind both primality obstructions below. -/
theorem two_mul_totient_le_of_sol {n : ℕ} (h : φ n = φ (n + 1)) : 2 * φ n ≤ n + 1 := by
  rcases Nat.even_or_odd n with he | ho
  · exact le_trans (two_mul_totient_le_of_even he) (Nat.le_succ n)
  · rw [h]
    exact two_mul_totient_le_of_even ho.add_one

/-- No solution of `φ n = φ (n + 1)` with `n ≥ 2` has `n + 1` prime.  (Sharp: `n = 1` is a
solution and `2` is prime.) -/
theorem not_prime_succ_of_sol {n : ℕ} (hn : 2 ≤ n) (h : φ n = φ (n + 1)) : ¬ (n + 1).Prime := by
  intro hp
  have h1 : φ (n + 1) = n := by simpa using Nat.totient_prime hp
  have h2 := two_mul_totient_le_of_sol h
  rw [h, h1] at h2
  omega

/-- No solution of `φ n = φ (n + 1)` with `n ≥ 4` has `n` prime.  (Sharp: `n = 3` is a
solution and `3` is prime.)  Together with `not_prime_succ_of_sol` this says that every
solution `n ≥ 4` is the smaller half of a pair of consecutive composite numbers, so no
construction of solutions can go through a prime on either side. -/
theorem not_prime_of_sol {n : ℕ} (hn : 4 ≤ n) (h : φ n = φ (n + 1)) : ¬ n.Prime := by
  intro hp
  have h1 : φ n = n - 1 := Nat.totient_prime hp
  have h2 := two_mul_totient_le_of_sol h
  rw [h1] at h2
  have h3 : 2 ≤ n := hp.two_le
  omega

/- ### Totient runs: the `Icc` variant made induction-friendly and decidable

Recall the honest framing above: infinitude of `Run k` for `k ≥ 1` is *strictly stronger*
than the reward theorem, so this section is an API for the `Icc` target, not a route to
`erdos_1003`. -/

/-- `Run k` is the set of starting points of a run of `k + 1` equal totient values,
`φ n = φ (n + 1) = ⋯ = φ (n + k)`.  This is definitionally the set appearing in
`Erdos1003.erdos_1003.variants.Icc`. -/
def Run (k : ℕ) : Set ℕ := {n | ∀ i ∈ Set.Icc 1 k, φ n = φ (n + i)}

/-- Membership in `Run k` without the `1 ≤ i` side condition: the case `i = 0` is free. -/
theorem mem_run_iff_forall_le {k n : ℕ} : n ∈ Run k ↔ ∀ i ≤ k, φ n = φ (n + i) := by
  constructor
  · intro h i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simp
    · exact h i (Set.mem_Icc.mpr ⟨hi1, hi⟩)
  · intro h i hi
    exact h i (Set.mem_Icc.mp hi).2

/-- The star-shaped definition of a totient run is equivalent to a chain of consecutive
equalities.  This is the induction-friendly form: it exhibits `Run k` as an intersection of
`k` conditions, each a shifted instance of the predicate of `Erdos1003.erdos_1003`, and it is
what makes runs decidable (`decidableMemRun`) and constructible step by step. -/
theorem mem_run_iff_chain {k n : ℕ} : n ∈ Run k ↔ ∀ i < k, φ (n + i) = φ (n + i + 1) := by
  rw [mem_run_iff_forall_le]
  constructor
  · intro h i hi
    have h1 := h i hi.le
    have h2 := h (i + 1) hi
    rw [show n + (i + 1) = n + i + 1 from by omega] at h2
    exact h1.symm.trans h2
  · intro h i hi
    induction i with
    | zero => simp
    | succ j ih =>
      have hj : j ≤ k := by omega
      have h2 := h j (by omega)
      rw [show n + (j + 1) = n + j + 1 from by omega, ← h2]
      exact ih hj

/-- Membership in `Run k` is decidable, via the chain reformulation.  (The defining
condition `∀ i ∈ Set.Icc 1 k, _` is a bounded quantifier over a `Set`, which carries no
decidability instance, so not even a numerical witness can be checked against the statement
of `Erdos1003.erdos_1003.variants.Icc` as written.) -/
instance decidableMemRun (k n : ℕ) : Decidable (n ∈ Run k) :=
  decidable_of_iff _ mem_run_iff_chain.symm

/-- The decidability instance is not vacuous: membership in a run is now settled by the
kernel.  (`104` is the largest solution below `106`, by `filter_range_106`.) -/
example : (104 : ℕ) ∈ Run 1 := by decide +kernel

/-- A verified witness for the `k = 2` case of `Erdos1003.erdos_1003.variants.Icc`:
`φ 5186 = φ 5187 = φ 5188 = 2592`, using `5186 = 2 · 2593`, `5187 = 3 · 7 · 13 · 19` and
`5188 = 2² · 1297`.  Consequently `5186` and `5187` are two *consecutive* solutions of
`φ n = φ (n + 1)`. -/
theorem mem_run_two_5186 : 5186 ∈ Run 2 := by
  have h0 : φ 5186 = 2592 := by
    rw [show (5186 : ℕ) = 2 * 2593 from by norm_num, Nat.totient_mul (by norm_num),
      Nat.totient_two, Nat.totient_prime (by norm_num)]
  have h1 : φ 5187 = 2592 := by
    rw [show (5187 : ℕ) = 3 * 7 * 13 * 19 from by norm_num,
      Nat.totient_mul (by norm_num), Nat.totient_mul (by norm_num),
      Nat.totient_mul (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num), Nat.totient_prime (by norm_num),
      Nat.totient_prime (by norm_num)]
  have h2 : φ 5188 = 2592 := by
    rw [show (5188 : ℕ) = 2 ^ 2 * 1297 from by norm_num, Nat.totient_mul (by norm_num),
      Nat.totient_prime_pow Nat.prime_two (by norm_num), Nat.totient_prime (by norm_num)]
    norm_num
  rw [mem_run_iff_forall_le]
  intro i hi
  interval_cases i
  · simp
  · rw [show (5186 + 1 : ℕ) = 5187 from by norm_num, h0, h1]
  · rw [show (5186 + 2 : ℕ) = 5188 from by norm_num, h0, h2]

/- ### Worked use sites

Each example below is stated against the *literal* statement of a theorem of
`FormalConjectures.ErdosProblems.«1003»` (the `answer(..)` placeholder elaborates to `True`
in its default setting), so a solver can copy the proof script verbatim. -/

/-- Use site 1: the counting statement `Erdos1003.erdos_1003.variants.eps87` reduces to a
bound on the decidable counting function `solCount`, with no `Set.ncard` left in sight. -/
example (H : ∀ᶠ x : ℝ in atTop,
      (solCount ⌊x⌋₊ : ℝ) ≤ x / Real.exp (Real.log x ^ ((1 : ℝ) / 3))) :
    ∀ᶠ x : ℝ in atTop, ({n : ℕ | (n : ℝ) ≤ x ∧ φ n = φ (n + 1)}.ncard : ℝ)
      ≤ x / Real.exp (Real.log x ^ ((1 : ℝ) / 3)) := by
  filter_upwards [H, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rwa [ncard_setOf_le_eq_solCount hx0]

/-- Use site 2: the reward theorem `Erdos1003.erdos_1003` follows from any lower bound on the
same counting function that grows, with no `Set.Infinite` reasoning left. -/
example (H : Tendsto solCount atTop atTop) :
    True ↔ Set.Infinite {n | φ n = φ (n + 1)} :=
  iff_of_true trivial (infinite_sol_iff_tendsto_solCount.mpr H)

/-- Use site 3: the `Icc` variant `Erdos1003.erdos_1003.variants.Icc` reduces to producing,
above every bound, one start of a chain of `k` consecutive equalities — which is the shape a
construction of runs has, and (unlike the statement as written) a decidable condition. -/
example (H : ∀ k ≥ 1, ∀ N : ℕ, ∃ n, N < n ∧ ∀ i < k, φ (n + i) = φ (n + i + 1)) :
    True ↔ ∀ k ≥ 1, {n | ∀ i ∈ Set.Icc 1 k, φ n = φ (n + i)}.Infinite := by
  refine iff_of_true trivial fun k hk => ?_
  have hRun : {n | ∀ i ∈ Set.Icc 1 k, φ n = φ (n + i)} = Run k := rfl
  rw [hRun]
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨n, hn, h⟩ := H k hk a
  exact ⟨n, mem_run_iff_chain.mpr h, hn⟩

end Contribution.Erdos1003TotientRuns
