import FormalConjectures.ErdosProblems.«1106»
import FormalConjectures.OEIS.«41»

/-!
# Erdős problem 1106, part (ii): computing the partition function

Target: `Erdos1106.erdos_1106.parts.ii`, whose right hand side is
`∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n`. Throughout, `F n` denotes
`#(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors`, the number of distinct primes dividing
`p 1 ⋯ p n`, where `Erdos1106.p n = Fintype.card (Nat.Partition n)` is the partition function.

## What was missing

The pinned environment has next to no evaluation of `Erdos1106.p`. Mathlib knows that
`Nat.Partition n` is a `Fintype` (through the surjection from compositions) and proves identities
*comparing* counts of restricted partitions — `Nat.Partition.card_odds_eq_card_distincts` and
`Nat.Partition.card_restricted_eq_card_countRestricted` — but it contains no recursion and no
value for `Fintype.card (Nat.Partition n)`. Kernel evaluation is not available either: `by decide`
and `by decide +kernel` both fail on `Erdos1106.p 2 = 2`, reduction getting stuck on the
`Decidable` instance. The only values anywhere in the environment are
`OeisA41.a_0, …, OeisA41.a_5`, and only the first two of those (both equal to `1`) are
kernel-checked: from `a_2` on they are obtained by compiler evaluation and rest on
`Lean.ofReduceBool` and `Lean.trustCompiler`. The target's `F n` was therefore out of reach
beyond the trivial range, and the threshold hidden in its `Filter.Eventually` could not be
located at all.

## Contents

* `restrictedCard n k`, the number of partitions of `n` with all parts at most `k`, and
  `restrictedCard_step`, the recursion `restrictedCard n k = restrictedCard n j + restrictedCard
  m k` for `k = j + 1` and `n = m + k`. It is proved by splitting the partitions counted on the
  left according to whether the part `k` occurs, and matching those that do with the partitions
  of `m` counted on the right through the bijection `consPart` (adjoin a part `k`) and its
  inverse (erase a part `k`).
* `p_values`: the value of `Erdos1106.p n` for every `1 ≤ n ≤ 30`, from `Erdos1106.p 1 = 1` to
  `Erdos1106.p 30 = 5604`, obtained by running that recursion over the table of all
  `restrictedCard n k` with `1 ≤ k ≤ n ≤ 30`. Everything in this file is kernel-checked and
  depends only on `propext`, `Classical.choice` and `Quot.sound`; use site 5 reproves
  `OeisA41.a_5` with no such extra trust.
* `primeFactors_prod_subset`: the prime sets, hence `F`, are monotone in `n`.
* `primeFactors_prod_thirty`: the prime factors of `∏ i ∈ Icc 1 30, Erdos1106.p i`. That product
  is `2 ^ 23 * 3 ^ 19 * 5 ^ 11 * 7 ^ 11 * 11 ^ 12 * 13 ^ 2 * 19 * 29 * 43 * 83 * 89 * 101 * 167 *
  251 * 467`, so `F 30 = 15`.
* `card_primeFactors_prod_le_self`: `F n ≤ n` for every `1 ≤ n ≤ 30`. The target's inequality
  therefore fails on that whole range, and every threshold from which it holds is at least `31`
  (use site 1).
* `infinite_primes_of_eventually_lt`: the target implies that infinitely many primes divide
  partition numbers.
* `eventually_lt_of_monotone_block`, an amortised growth criterion for an arbitrary monotone
  `f : ℕ → ℕ`, and its specialisation to the target,
  `eventually_lt_card_primeFactors_prod`.

A later solver can use declaration
`Contribution.Erdos1106PartitionCount.eventually_lt_card_primeFactors_prod` to discharge or
simplify obligation `∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n` in target
`Erdos1106.erdos_1106.parts.ii`: it reduces that obligation to one starting point `N + k < F N`
together with a single window estimate, namely that for every `n ≥ N` the product
`p 1 ⋯ p (n + k)` has at least `k + 1` prime factors not dividing `p 1 ⋯ p n`. These hypotheses
are sufficient and not necessary — they force an average gain of `(k + 1) / k > 1` new primes
per step, while the target tolerates any average gain approaching `1`, and use site 3 exhibits a
monotone function that satisfies the conclusion for which no admissible `N, k` exists. The
target has no binders to instantiate, so no choice of instance can defeat the reduction; what it
costs is recorded here instead of hidden. The unconditional statements
`primeFactors_prod_subset` and `card_primeFactors_prod_le_self` are available to a solver who
prefers to keep the exact slack.

## The obstacle

Everything unconditional above is counting plus computation; none of it produces a *new* prime,
and the window criterion isolates exactly that missing input: a prime dividing
`p (n + 1) ⋯ p (n + k)` but none of `p 1, …, p n`. Nothing in Mathlib produces one, and
`infinite_primes_of_eventually_lt` shows the target implies that infinitely many primes divide
partition numbers, i.e. part (i) of the same problem, which is also open — so part (ii) is at
least as hard. The size of `p` alone does not help: informally `Erdos1106.p n = exp (Θ (√n))`
(Hardy–Ramanujan; not in Mathlib, whose only `Nat.Partition` files are `Basic`, `GenFun` and
`Glaisher`), so `p 1, …, p n` are `n` distinct integers below `exp (c √n)`, and a box count of
the integers all of whose prime factors lie in a fixed finite set `S` then forces only
`2 ≤ #S`.

The verified range is also far from where the phenomenon starts. A computation outside Lean
(sympy; not part of this file's formal content) puts the first `n` with `F n > n` at `n = 116`,
with `F n > n` for every `116 ≤ n ≤ 400`, whereas this file checks `F 30 = 15`. Extending the
table is mechanical — `restrictedCard_step` for the values, one prime factorisation per
checkpoint — but no finite extension can reach an eventual statement: a proof has to be
asymptotic, and it has to come from arithmetic of the numbers `p n`, not from their size.
-/

open Nat Finset Filter Topology

namespace Contribution.Erdos1106PartitionCount

/- ### Counting partitions with bounded parts -/

/-- `restrictedCard n k` is the number of partitions of `n` all of whose parts are at most `k`.
For `n ≤ k` this is the partition number `Erdos1106.p n` itself
(`Contribution.Erdos1106PartitionCount.restrictedCard_eq_p`). -/
def restrictedCard (n k : ℕ) : ℕ := #(Nat.Partition.restricted n (· ≤ k))

/-- A partition of `n` has all its parts bounded by `n`, so the bound `k` becomes inactive as
soon as `n ≤ k`. -/
theorem restrictedCard_eq_p {n k : ℕ} (h : n ≤ k) : restrictedCard n k = Erdos1106.p n := by
  simp only [restrictedCard, Nat.Partition.restricted]
  rw [Finset.filter_true_of_mem fun P _ i hi => (Nat.Partition.le_of_mem_parts hi).trans h,
    Finset.card_univ]
  rfl

/-- A positive number has no partition into parts of size `0`. -/
theorem restrictedCard_zero_right {n : ℕ} (hn : 0 < n) : restrictedCard n 0 = 0 := by
  simp only [restrictedCard, Nat.Partition.restricted, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro P _
  have hne : P.parts ≠ 0 := by
    intro h
    have hs := P.parts_sum
    rw [h] at hs
    simp at hs
    omega
  obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hne
  have := P.parts_pos hi
  exact fun hall => absurd (hall i hi) (by omega)

/-- Adjoining one more part `k + 1` to a partition of `n` gives a partition of `n + (k + 1)`.
This is the map underlying the recursion `restrictedCard_step`. -/
def consPart (k : ℕ) {n : ℕ} (Q : Nat.Partition n) : Nat.Partition (n + (k + 1)) where
  parts := (k + 1) ::ₘ Q.parts
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.1 hi with h | h
    · omega
    · exact Q.parts_pos h
  parts_sum := by rw [Multiset.sum_cons, Q.parts_sum, Nat.add_comm]

/-- **The recursion for the number of partitions with bounded parts.** If `k = j + 1` and
`n = m + k`, then the partitions of `n` with parts at most `k` split into those that do not use
the part `k` (partitions of `n` with parts at most `j`) and those that do (remove one part `k`
to get a partition of `m` with parts at most `k`).

The hypotheses are stated as `j + 1 = k` and `m + k = n` rather than as `k - 1` and `n - k` so
that the recursion can be applied to numerals by `rfl`, which is what makes the table of values
in `p_values` cheap to check. -/
theorem restrictedCard_step {n m j k : ℕ} (hj : j + 1 = k) (hm : m + k = n) :
    restrictedCard n k = restrictedCard n j + restrictedCard m k := by
  classical
  subst hj
  subst hm
  have hnot : (Nat.Partition.restricted (m + (j + 1)) (· ≤ j + 1)).filter
        (fun P => ¬ (j + 1) ∈ P.parts)
      = Nat.Partition.restricted (m + (j + 1)) (· ≤ j) := by
    ext P
    simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hle, hmem⟩ i hi
      have h1 := hle i hi
      have h2 : i ≠ j + 1 := fun h => hmem (h ▸ hi)
      omega
    · intro hle
      refine ⟨fun i hi => (hle i hi).trans (Nat.le_succ j), fun hmem => ?_⟩
      have := hle _ hmem
      omega
  have hmem : #((Nat.Partition.restricted (m + (j + 1)) (· ≤ j + 1)).filter
      (fun P => (j + 1) ∈ P.parts)) = restrictedCard m (j + 1) := by
    symm
    simp only [restrictedCard]
    refine Finset.card_bij (fun Q _ => consPart j Q) ?_ ?_ ?_
    · intro Q hQ
      simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and,
        consPart] at hQ ⊢
      refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
      rcases Multiset.mem_cons.1 hi with h | h
      · omega
      · exact hQ i h
    · intro Q1 h1 Q2 h2 heq
      have hq : (j + 1) ::ₘ Q1.parts = (j + 1) ::ₘ Q2.parts := congrArg Nat.Partition.parts heq
      exact Nat.Partition.ext ((Multiset.cons_inj_right _).1 hq)
    · intro P hP
      simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      obtain ⟨hle, hmemP⟩ := hP
      have hc := Multiset.cons_erase hmemP
      have hsum : (P.parts.erase (j + 1)).sum = m := by
        have h2 : (j + 1) + (P.parts.erase (j + 1)).sum = m + (j + 1) := by
          rw [← Multiset.sum_cons, hc, P.parts_sum]
        omega
      refine ⟨⟨P.parts.erase (j + 1), fun hi => P.parts_pos (Multiset.mem_of_mem_erase hi),
        hsum⟩, ?_, ?_⟩
      · simp only [Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        exact hle i (Multiset.mem_of_mem_erase hi)
      · exact Nat.Partition.ext hc
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Nat.Partition.restricted (m + (j + 1)) (· ≤ j + 1)) (fun P => (j + 1) ∈ P.parts)
  rw [hnot, hmem] at hsplit
  simp only [restrictedCard] at hsplit ⊢
  omega

/- ### The first thirty partition numbers -/

/-- **The values of the partition function up to `30`**, obtained from `restrictedCard_step`
by an explicit dynamic-programming table (`restrictedCard n k` for `1 ≤ k ≤ n ≤ 30`).
These are kernel-checked: unlike the entries `OeisA41.a_2, …, OeisA41.a_5` of the pinned
environment, their proofs use no compiler evaluation and hence neither `Lean.ofReduceBool`
nor `Lean.trustCompiler`. -/
theorem p_values :
      Erdos1106.p 1 = 1 ∧
      Erdos1106.p 2 = 2 ∧
      Erdos1106.p 3 = 3 ∧
      Erdos1106.p 4 = 5 ∧
      Erdos1106.p 5 = 7 ∧
      Erdos1106.p 6 = 11 ∧
      Erdos1106.p 7 = 15 ∧
      Erdos1106.p 8 = 22 ∧
      Erdos1106.p 9 = 30 ∧
      Erdos1106.p 10 = 42 ∧
      Erdos1106.p 11 = 56 ∧
      Erdos1106.p 12 = 77 ∧
      Erdos1106.p 13 = 101 ∧
      Erdos1106.p 14 = 135 ∧
      Erdos1106.p 15 = 176 ∧
      Erdos1106.p 16 = 231 ∧
      Erdos1106.p 17 = 297 ∧
      Erdos1106.p 18 = 385 ∧
      Erdos1106.p 19 = 490 ∧
      Erdos1106.p 20 = 627 ∧
      Erdos1106.p 21 = 792 ∧
      Erdos1106.p 22 = 1002 ∧
      Erdos1106.p 23 = 1255 ∧
      Erdos1106.p 24 = 1575 ∧
      Erdos1106.p 25 = 1958 ∧
      Erdos1106.p 26 = 2436 ∧
      Erdos1106.p 27 = 3010 ∧
      Erdos1106.p 28 = 3718 ∧
      Erdos1106.p 29 = 4565 ∧
      Erdos1106.p 30 = 5604 := by
  have hp0 : Erdos1106.p 0 = 1 := Fintype.card_unique
  have h1_1 : restrictedCard 1 1 = 1 := by
    rw [restrictedCard_step (n := 1) (m := 0) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 1) (by norm_num),
      restrictedCard_eq_p (n := 0) (k := 1) (by norm_num), hp0]
  have hp1 : Erdos1106.p 1 = 1 := (restrictedCard_eq_p (le_refl 1)).symm.trans h1_1
  have h2_1 : restrictedCard 2 1 = 1 := by
    rw [restrictedCard_step (n := 2) (m := 1) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 2) (by norm_num), h1_1]
  have h2_2 : restrictedCard 2 2 = 2 := by
    rw [restrictedCard_step (n := 2) (m := 0) (j := 1) (k := 2) rfl rfl, h2_1,
      restrictedCard_eq_p (n := 0) (k := 2) (by norm_num), hp0]
  have hp2 : Erdos1106.p 2 = 2 := (restrictedCard_eq_p (le_refl 2)).symm.trans h2_2
  have h3_1 : restrictedCard 3 1 = 1 := by
    rw [restrictedCard_step (n := 3) (m := 2) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 3) (by norm_num), h2_1]
  have h3_2 : restrictedCard 3 2 = 2 := by
    rw [restrictedCard_step (n := 3) (m := 1) (j := 1) (k := 2) rfl rfl, h3_1,
      restrictedCard_eq_p (n := 1) (k := 2) (by norm_num), hp1]
  have h3_3 : restrictedCard 3 3 = 3 := by
    rw [restrictedCard_step (n := 3) (m := 0) (j := 2) (k := 3) rfl rfl, h3_2,
      restrictedCard_eq_p (n := 0) (k := 3) (by norm_num), hp0]
  have hp3 : Erdos1106.p 3 = 3 := (restrictedCard_eq_p (le_refl 3)).symm.trans h3_3
  have h4_1 : restrictedCard 4 1 = 1 := by
    rw [restrictedCard_step (n := 4) (m := 3) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 4) (by norm_num), h3_1]
  have h4_2 : restrictedCard 4 2 = 3 := by
    rw [restrictedCard_step (n := 4) (m := 2) (j := 1) (k := 2) rfl rfl, h4_1, h2_2]
  have h4_3 : restrictedCard 4 3 = 4 := by
    rw [restrictedCard_step (n := 4) (m := 1) (j := 2) (k := 3) rfl rfl, h4_2,
      restrictedCard_eq_p (n := 1) (k := 3) (by norm_num), hp1]
  have h4_4 : restrictedCard 4 4 = 5 := by
    rw [restrictedCard_step (n := 4) (m := 0) (j := 3) (k := 4) rfl rfl, h4_3,
      restrictedCard_eq_p (n := 0) (k := 4) (by norm_num), hp0]
  have hp4 : Erdos1106.p 4 = 5 := (restrictedCard_eq_p (le_refl 4)).symm.trans h4_4
  have h5_1 : restrictedCard 5 1 = 1 := by
    rw [restrictedCard_step (n := 5) (m := 4) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 5) (by norm_num), h4_1]
  have h5_2 : restrictedCard 5 2 = 3 := by
    rw [restrictedCard_step (n := 5) (m := 3) (j := 1) (k := 2) rfl rfl, h5_1, h3_2]
  have h5_3 : restrictedCard 5 3 = 5 := by
    rw [restrictedCard_step (n := 5) (m := 2) (j := 2) (k := 3) rfl rfl, h5_2,
      restrictedCard_eq_p (n := 2) (k := 3) (by norm_num), hp2]
  have h5_4 : restrictedCard 5 4 = 6 := by
    rw [restrictedCard_step (n := 5) (m := 1) (j := 3) (k := 4) rfl rfl, h5_3,
      restrictedCard_eq_p (n := 1) (k := 4) (by norm_num), hp1]
  have h5_5 : restrictedCard 5 5 = 7 := by
    rw [restrictedCard_step (n := 5) (m := 0) (j := 4) (k := 5) rfl rfl, h5_4,
      restrictedCard_eq_p (n := 0) (k := 5) (by norm_num), hp0]
  have hp5 : Erdos1106.p 5 = 7 := (restrictedCard_eq_p (le_refl 5)).symm.trans h5_5
  have h6_1 : restrictedCard 6 1 = 1 := by
    rw [restrictedCard_step (n := 6) (m := 5) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 6) (by norm_num), h5_1]
  have h6_2 : restrictedCard 6 2 = 4 := by
    rw [restrictedCard_step (n := 6) (m := 4) (j := 1) (k := 2) rfl rfl, h6_1, h4_2]
  have h6_3 : restrictedCard 6 3 = 7 := by
    rw [restrictedCard_step (n := 6) (m := 3) (j := 2) (k := 3) rfl rfl, h6_2, h3_3]
  have h6_4 : restrictedCard 6 4 = 9 := by
    rw [restrictedCard_step (n := 6) (m := 2) (j := 3) (k := 4) rfl rfl, h6_3,
      restrictedCard_eq_p (n := 2) (k := 4) (by norm_num), hp2]
  have h6_5 : restrictedCard 6 5 = 10 := by
    rw [restrictedCard_step (n := 6) (m := 1) (j := 4) (k := 5) rfl rfl, h6_4,
      restrictedCard_eq_p (n := 1) (k := 5) (by norm_num), hp1]
  have h6_6 : restrictedCard 6 6 = 11 := by
    rw [restrictedCard_step (n := 6) (m := 0) (j := 5) (k := 6) rfl rfl, h6_5,
      restrictedCard_eq_p (n := 0) (k := 6) (by norm_num), hp0]
  have hp6 : Erdos1106.p 6 = 11 := (restrictedCard_eq_p (le_refl 6)).symm.trans h6_6
  have h7_1 : restrictedCard 7 1 = 1 := by
    rw [restrictedCard_step (n := 7) (m := 6) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 7) (by norm_num), h6_1]
  have h7_2 : restrictedCard 7 2 = 4 := by
    rw [restrictedCard_step (n := 7) (m := 5) (j := 1) (k := 2) rfl rfl, h7_1, h5_2]
  have h7_3 : restrictedCard 7 3 = 8 := by
    rw [restrictedCard_step (n := 7) (m := 4) (j := 2) (k := 3) rfl rfl, h7_2, h4_3]
  have h7_4 : restrictedCard 7 4 = 11 := by
    rw [restrictedCard_step (n := 7) (m := 3) (j := 3) (k := 4) rfl rfl, h7_3,
      restrictedCard_eq_p (n := 3) (k := 4) (by norm_num), hp3]
  have h7_5 : restrictedCard 7 5 = 13 := by
    rw [restrictedCard_step (n := 7) (m := 2) (j := 4) (k := 5) rfl rfl, h7_4,
      restrictedCard_eq_p (n := 2) (k := 5) (by norm_num), hp2]
  have h7_6 : restrictedCard 7 6 = 14 := by
    rw [restrictedCard_step (n := 7) (m := 1) (j := 5) (k := 6) rfl rfl, h7_5,
      restrictedCard_eq_p (n := 1) (k := 6) (by norm_num), hp1]
  have h7_7 : restrictedCard 7 7 = 15 := by
    rw [restrictedCard_step (n := 7) (m := 0) (j := 6) (k := 7) rfl rfl, h7_6,
      restrictedCard_eq_p (n := 0) (k := 7) (by norm_num), hp0]
  have hp7 : Erdos1106.p 7 = 15 := (restrictedCard_eq_p (le_refl 7)).symm.trans h7_7
  have h8_1 : restrictedCard 8 1 = 1 := by
    rw [restrictedCard_step (n := 8) (m := 7) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 8) (by norm_num), h7_1]
  have h8_2 : restrictedCard 8 2 = 5 := by
    rw [restrictedCard_step (n := 8) (m := 6) (j := 1) (k := 2) rfl rfl, h8_1, h6_2]
  have h8_3 : restrictedCard 8 3 = 10 := by
    rw [restrictedCard_step (n := 8) (m := 5) (j := 2) (k := 3) rfl rfl, h8_2, h5_3]
  have h8_4 : restrictedCard 8 4 = 15 := by
    rw [restrictedCard_step (n := 8) (m := 4) (j := 3) (k := 4) rfl rfl, h8_3, h4_4]
  have h8_5 : restrictedCard 8 5 = 18 := by
    rw [restrictedCard_step (n := 8) (m := 3) (j := 4) (k := 5) rfl rfl, h8_4,
      restrictedCard_eq_p (n := 3) (k := 5) (by norm_num), hp3]
  have h8_6 : restrictedCard 8 6 = 20 := by
    rw [restrictedCard_step (n := 8) (m := 2) (j := 5) (k := 6) rfl rfl, h8_5,
      restrictedCard_eq_p (n := 2) (k := 6) (by norm_num), hp2]
  have h8_7 : restrictedCard 8 7 = 21 := by
    rw [restrictedCard_step (n := 8) (m := 1) (j := 6) (k := 7) rfl rfl, h8_6,
      restrictedCard_eq_p (n := 1) (k := 7) (by norm_num), hp1]
  have h8_8 : restrictedCard 8 8 = 22 := by
    rw [restrictedCard_step (n := 8) (m := 0) (j := 7) (k := 8) rfl rfl, h8_7,
      restrictedCard_eq_p (n := 0) (k := 8) (by norm_num), hp0]
  have hp8 : Erdos1106.p 8 = 22 := (restrictedCard_eq_p (le_refl 8)).symm.trans h8_8
  have h9_1 : restrictedCard 9 1 = 1 := by
    rw [restrictedCard_step (n := 9) (m := 8) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 9) (by norm_num), h8_1]
  have h9_2 : restrictedCard 9 2 = 5 := by
    rw [restrictedCard_step (n := 9) (m := 7) (j := 1) (k := 2) rfl rfl, h9_1, h7_2]
  have h9_3 : restrictedCard 9 3 = 12 := by
    rw [restrictedCard_step (n := 9) (m := 6) (j := 2) (k := 3) rfl rfl, h9_2, h6_3]
  have h9_4 : restrictedCard 9 4 = 18 := by
    rw [restrictedCard_step (n := 9) (m := 5) (j := 3) (k := 4) rfl rfl, h9_3, h5_4]
  have h9_5 : restrictedCard 9 5 = 23 := by
    rw [restrictedCard_step (n := 9) (m := 4) (j := 4) (k := 5) rfl rfl, h9_4,
      restrictedCard_eq_p (n := 4) (k := 5) (by norm_num), hp4]
  have h9_6 : restrictedCard 9 6 = 26 := by
    rw [restrictedCard_step (n := 9) (m := 3) (j := 5) (k := 6) rfl rfl, h9_5,
      restrictedCard_eq_p (n := 3) (k := 6) (by norm_num), hp3]
  have h9_7 : restrictedCard 9 7 = 28 := by
    rw [restrictedCard_step (n := 9) (m := 2) (j := 6) (k := 7) rfl rfl, h9_6,
      restrictedCard_eq_p (n := 2) (k := 7) (by norm_num), hp2]
  have h9_8 : restrictedCard 9 8 = 29 := by
    rw [restrictedCard_step (n := 9) (m := 1) (j := 7) (k := 8) rfl rfl, h9_7,
      restrictedCard_eq_p (n := 1) (k := 8) (by norm_num), hp1]
  have h9_9 : restrictedCard 9 9 = 30 := by
    rw [restrictedCard_step (n := 9) (m := 0) (j := 8) (k := 9) rfl rfl, h9_8,
      restrictedCard_eq_p (n := 0) (k := 9) (by norm_num), hp0]
  have hp9 : Erdos1106.p 9 = 30 := (restrictedCard_eq_p (le_refl 9)).symm.trans h9_9
  have h10_1 : restrictedCard 10 1 = 1 := by
    rw [restrictedCard_step (n := 10) (m := 9) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 10) (by norm_num), h9_1]
  have h10_2 : restrictedCard 10 2 = 6 := by
    rw [restrictedCard_step (n := 10) (m := 8) (j := 1) (k := 2) rfl rfl, h10_1, h8_2]
  have h10_3 : restrictedCard 10 3 = 14 := by
    rw [restrictedCard_step (n := 10) (m := 7) (j := 2) (k := 3) rfl rfl, h10_2, h7_3]
  have h10_4 : restrictedCard 10 4 = 23 := by
    rw [restrictedCard_step (n := 10) (m := 6) (j := 3) (k := 4) rfl rfl, h10_3, h6_4]
  have h10_5 : restrictedCard 10 5 = 30 := by
    rw [restrictedCard_step (n := 10) (m := 5) (j := 4) (k := 5) rfl rfl, h10_4, h5_5]
  have h10_6 : restrictedCard 10 6 = 35 := by
    rw [restrictedCard_step (n := 10) (m := 4) (j := 5) (k := 6) rfl rfl, h10_5,
      restrictedCard_eq_p (n := 4) (k := 6) (by norm_num), hp4]
  have h10_7 : restrictedCard 10 7 = 38 := by
    rw [restrictedCard_step (n := 10) (m := 3) (j := 6) (k := 7) rfl rfl, h10_6,
      restrictedCard_eq_p (n := 3) (k := 7) (by norm_num), hp3]
  have h10_8 : restrictedCard 10 8 = 40 := by
    rw [restrictedCard_step (n := 10) (m := 2) (j := 7) (k := 8) rfl rfl, h10_7,
      restrictedCard_eq_p (n := 2) (k := 8) (by norm_num), hp2]
  have h10_9 : restrictedCard 10 9 = 41 := by
    rw [restrictedCard_step (n := 10) (m := 1) (j := 8) (k := 9) rfl rfl, h10_8,
      restrictedCard_eq_p (n := 1) (k := 9) (by norm_num), hp1]
  have h10_10 : restrictedCard 10 10 = 42 := by
    rw [restrictedCard_step (n := 10) (m := 0) (j := 9) (k := 10) rfl rfl, h10_9,
      restrictedCard_eq_p (n := 0) (k := 10) (by norm_num), hp0]
  have hp10 : Erdos1106.p 10 = 42 := (restrictedCard_eq_p (le_refl 10)).symm.trans h10_10
  have h11_1 : restrictedCard 11 1 = 1 := by
    rw [restrictedCard_step (n := 11) (m := 10) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 11) (by norm_num), h10_1]
  have h11_2 : restrictedCard 11 2 = 6 := by
    rw [restrictedCard_step (n := 11) (m := 9) (j := 1) (k := 2) rfl rfl, h11_1, h9_2]
  have h11_3 : restrictedCard 11 3 = 16 := by
    rw [restrictedCard_step (n := 11) (m := 8) (j := 2) (k := 3) rfl rfl, h11_2, h8_3]
  have h11_4 : restrictedCard 11 4 = 27 := by
    rw [restrictedCard_step (n := 11) (m := 7) (j := 3) (k := 4) rfl rfl, h11_3, h7_4]
  have h11_5 : restrictedCard 11 5 = 37 := by
    rw [restrictedCard_step (n := 11) (m := 6) (j := 4) (k := 5) rfl rfl, h11_4, h6_5]
  have h11_6 : restrictedCard 11 6 = 44 := by
    rw [restrictedCard_step (n := 11) (m := 5) (j := 5) (k := 6) rfl rfl, h11_5,
      restrictedCard_eq_p (n := 5) (k := 6) (by norm_num), hp5]
  have h11_7 : restrictedCard 11 7 = 49 := by
    rw [restrictedCard_step (n := 11) (m := 4) (j := 6) (k := 7) rfl rfl, h11_6,
      restrictedCard_eq_p (n := 4) (k := 7) (by norm_num), hp4]
  have h11_8 : restrictedCard 11 8 = 52 := by
    rw [restrictedCard_step (n := 11) (m := 3) (j := 7) (k := 8) rfl rfl, h11_7,
      restrictedCard_eq_p (n := 3) (k := 8) (by norm_num), hp3]
  have h11_9 : restrictedCard 11 9 = 54 := by
    rw [restrictedCard_step (n := 11) (m := 2) (j := 8) (k := 9) rfl rfl, h11_8,
      restrictedCard_eq_p (n := 2) (k := 9) (by norm_num), hp2]
  have h11_10 : restrictedCard 11 10 = 55 := by
    rw [restrictedCard_step (n := 11) (m := 1) (j := 9) (k := 10) rfl rfl, h11_9,
      restrictedCard_eq_p (n := 1) (k := 10) (by norm_num), hp1]
  have h11_11 : restrictedCard 11 11 = 56 := by
    rw [restrictedCard_step (n := 11) (m := 0) (j := 10) (k := 11) rfl rfl, h11_10,
      restrictedCard_eq_p (n := 0) (k := 11) (by norm_num), hp0]
  have hp11 : Erdos1106.p 11 = 56 := (restrictedCard_eq_p (le_refl 11)).symm.trans h11_11
  have h12_1 : restrictedCard 12 1 = 1 := by
    rw [restrictedCard_step (n := 12) (m := 11) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 12) (by norm_num), h11_1]
  have h12_2 : restrictedCard 12 2 = 7 := by
    rw [restrictedCard_step (n := 12) (m := 10) (j := 1) (k := 2) rfl rfl, h12_1, h10_2]
  have h12_3 : restrictedCard 12 3 = 19 := by
    rw [restrictedCard_step (n := 12) (m := 9) (j := 2) (k := 3) rfl rfl, h12_2, h9_3]
  have h12_4 : restrictedCard 12 4 = 34 := by
    rw [restrictedCard_step (n := 12) (m := 8) (j := 3) (k := 4) rfl rfl, h12_3, h8_4]
  have h12_5 : restrictedCard 12 5 = 47 := by
    rw [restrictedCard_step (n := 12) (m := 7) (j := 4) (k := 5) rfl rfl, h12_4, h7_5]
  have h12_6 : restrictedCard 12 6 = 58 := by
    rw [restrictedCard_step (n := 12) (m := 6) (j := 5) (k := 6) rfl rfl, h12_5, h6_6]
  have h12_7 : restrictedCard 12 7 = 65 := by
    rw [restrictedCard_step (n := 12) (m := 5) (j := 6) (k := 7) rfl rfl, h12_6,
      restrictedCard_eq_p (n := 5) (k := 7) (by norm_num), hp5]
  have h12_8 : restrictedCard 12 8 = 70 := by
    rw [restrictedCard_step (n := 12) (m := 4) (j := 7) (k := 8) rfl rfl, h12_7,
      restrictedCard_eq_p (n := 4) (k := 8) (by norm_num), hp4]
  have h12_9 : restrictedCard 12 9 = 73 := by
    rw [restrictedCard_step (n := 12) (m := 3) (j := 8) (k := 9) rfl rfl, h12_8,
      restrictedCard_eq_p (n := 3) (k := 9) (by norm_num), hp3]
  have h12_10 : restrictedCard 12 10 = 75 := by
    rw [restrictedCard_step (n := 12) (m := 2) (j := 9) (k := 10) rfl rfl, h12_9,
      restrictedCard_eq_p (n := 2) (k := 10) (by norm_num), hp2]
  have h12_11 : restrictedCard 12 11 = 76 := by
    rw [restrictedCard_step (n := 12) (m := 1) (j := 10) (k := 11) rfl rfl, h12_10,
      restrictedCard_eq_p (n := 1) (k := 11) (by norm_num), hp1]
  have h12_12 : restrictedCard 12 12 = 77 := by
    rw [restrictedCard_step (n := 12) (m := 0) (j := 11) (k := 12) rfl rfl, h12_11,
      restrictedCard_eq_p (n := 0) (k := 12) (by norm_num), hp0]
  have hp12 : Erdos1106.p 12 = 77 := (restrictedCard_eq_p (le_refl 12)).symm.trans h12_12
  have h13_1 : restrictedCard 13 1 = 1 := by
    rw [restrictedCard_step (n := 13) (m := 12) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 13) (by norm_num), h12_1]
  have h13_2 : restrictedCard 13 2 = 7 := by
    rw [restrictedCard_step (n := 13) (m := 11) (j := 1) (k := 2) rfl rfl, h13_1, h11_2]
  have h13_3 : restrictedCard 13 3 = 21 := by
    rw [restrictedCard_step (n := 13) (m := 10) (j := 2) (k := 3) rfl rfl, h13_2, h10_3]
  have h13_4 : restrictedCard 13 4 = 39 := by
    rw [restrictedCard_step (n := 13) (m := 9) (j := 3) (k := 4) rfl rfl, h13_3, h9_4]
  have h13_5 : restrictedCard 13 5 = 57 := by
    rw [restrictedCard_step (n := 13) (m := 8) (j := 4) (k := 5) rfl rfl, h13_4, h8_5]
  have h13_6 : restrictedCard 13 6 = 71 := by
    rw [restrictedCard_step (n := 13) (m := 7) (j := 5) (k := 6) rfl rfl, h13_5, h7_6]
  have h13_7 : restrictedCard 13 7 = 82 := by
    rw [restrictedCard_step (n := 13) (m := 6) (j := 6) (k := 7) rfl rfl, h13_6,
      restrictedCard_eq_p (n := 6) (k := 7) (by norm_num), hp6]
  have h13_8 : restrictedCard 13 8 = 89 := by
    rw [restrictedCard_step (n := 13) (m := 5) (j := 7) (k := 8) rfl rfl, h13_7,
      restrictedCard_eq_p (n := 5) (k := 8) (by norm_num), hp5]
  have h13_9 : restrictedCard 13 9 = 94 := by
    rw [restrictedCard_step (n := 13) (m := 4) (j := 8) (k := 9) rfl rfl, h13_8,
      restrictedCard_eq_p (n := 4) (k := 9) (by norm_num), hp4]
  have h13_10 : restrictedCard 13 10 = 97 := by
    rw [restrictedCard_step (n := 13) (m := 3) (j := 9) (k := 10) rfl rfl, h13_9,
      restrictedCard_eq_p (n := 3) (k := 10) (by norm_num), hp3]
  have h13_11 : restrictedCard 13 11 = 99 := by
    rw [restrictedCard_step (n := 13) (m := 2) (j := 10) (k := 11) rfl rfl, h13_10,
      restrictedCard_eq_p (n := 2) (k := 11) (by norm_num), hp2]
  have h13_12 : restrictedCard 13 12 = 100 := by
    rw [restrictedCard_step (n := 13) (m := 1) (j := 11) (k := 12) rfl rfl, h13_11,
      restrictedCard_eq_p (n := 1) (k := 12) (by norm_num), hp1]
  have h13_13 : restrictedCard 13 13 = 101 := by
    rw [restrictedCard_step (n := 13) (m := 0) (j := 12) (k := 13) rfl rfl, h13_12,
      restrictedCard_eq_p (n := 0) (k := 13) (by norm_num), hp0]
  have hp13 : Erdos1106.p 13 = 101 := (restrictedCard_eq_p (le_refl 13)).symm.trans h13_13
  have h14_1 : restrictedCard 14 1 = 1 := by
    rw [restrictedCard_step (n := 14) (m := 13) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 14) (by norm_num), h13_1]
  have h14_2 : restrictedCard 14 2 = 8 := by
    rw [restrictedCard_step (n := 14) (m := 12) (j := 1) (k := 2) rfl rfl, h14_1, h12_2]
  have h14_3 : restrictedCard 14 3 = 24 := by
    rw [restrictedCard_step (n := 14) (m := 11) (j := 2) (k := 3) rfl rfl, h14_2, h11_3]
  have h14_4 : restrictedCard 14 4 = 47 := by
    rw [restrictedCard_step (n := 14) (m := 10) (j := 3) (k := 4) rfl rfl, h14_3, h10_4]
  have h14_5 : restrictedCard 14 5 = 70 := by
    rw [restrictedCard_step (n := 14) (m := 9) (j := 4) (k := 5) rfl rfl, h14_4, h9_5]
  have h14_6 : restrictedCard 14 6 = 90 := by
    rw [restrictedCard_step (n := 14) (m := 8) (j := 5) (k := 6) rfl rfl, h14_5, h8_6]
  have h14_7 : restrictedCard 14 7 = 105 := by
    rw [restrictedCard_step (n := 14) (m := 7) (j := 6) (k := 7) rfl rfl, h14_6, h7_7]
  have h14_8 : restrictedCard 14 8 = 116 := by
    rw [restrictedCard_step (n := 14) (m := 6) (j := 7) (k := 8) rfl rfl, h14_7,
      restrictedCard_eq_p (n := 6) (k := 8) (by norm_num), hp6]
  have h14_9 : restrictedCard 14 9 = 123 := by
    rw [restrictedCard_step (n := 14) (m := 5) (j := 8) (k := 9) rfl rfl, h14_8,
      restrictedCard_eq_p (n := 5) (k := 9) (by norm_num), hp5]
  have h14_10 : restrictedCard 14 10 = 128 := by
    rw [restrictedCard_step (n := 14) (m := 4) (j := 9) (k := 10) rfl rfl, h14_9,
      restrictedCard_eq_p (n := 4) (k := 10) (by norm_num), hp4]
  have h14_11 : restrictedCard 14 11 = 131 := by
    rw [restrictedCard_step (n := 14) (m := 3) (j := 10) (k := 11) rfl rfl, h14_10,
      restrictedCard_eq_p (n := 3) (k := 11) (by norm_num), hp3]
  have h14_12 : restrictedCard 14 12 = 133 := by
    rw [restrictedCard_step (n := 14) (m := 2) (j := 11) (k := 12) rfl rfl, h14_11,
      restrictedCard_eq_p (n := 2) (k := 12) (by norm_num), hp2]
  have h14_13 : restrictedCard 14 13 = 134 := by
    rw [restrictedCard_step (n := 14) (m := 1) (j := 12) (k := 13) rfl rfl, h14_12,
      restrictedCard_eq_p (n := 1) (k := 13) (by norm_num), hp1]
  have h14_14 : restrictedCard 14 14 = 135 := by
    rw [restrictedCard_step (n := 14) (m := 0) (j := 13) (k := 14) rfl rfl, h14_13,
      restrictedCard_eq_p (n := 0) (k := 14) (by norm_num), hp0]
  have hp14 : Erdos1106.p 14 = 135 := (restrictedCard_eq_p (le_refl 14)).symm.trans h14_14
  have h15_1 : restrictedCard 15 1 = 1 := by
    rw [restrictedCard_step (n := 15) (m := 14) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 15) (by norm_num), h14_1]
  have h15_2 : restrictedCard 15 2 = 8 := by
    rw [restrictedCard_step (n := 15) (m := 13) (j := 1) (k := 2) rfl rfl, h15_1, h13_2]
  have h15_3 : restrictedCard 15 3 = 27 := by
    rw [restrictedCard_step (n := 15) (m := 12) (j := 2) (k := 3) rfl rfl, h15_2, h12_3]
  have h15_4 : restrictedCard 15 4 = 54 := by
    rw [restrictedCard_step (n := 15) (m := 11) (j := 3) (k := 4) rfl rfl, h15_3, h11_4]
  have h15_5 : restrictedCard 15 5 = 84 := by
    rw [restrictedCard_step (n := 15) (m := 10) (j := 4) (k := 5) rfl rfl, h15_4, h10_5]
  have h15_6 : restrictedCard 15 6 = 110 := by
    rw [restrictedCard_step (n := 15) (m := 9) (j := 5) (k := 6) rfl rfl, h15_5, h9_6]
  have h15_7 : restrictedCard 15 7 = 131 := by
    rw [restrictedCard_step (n := 15) (m := 8) (j := 6) (k := 7) rfl rfl, h15_6, h8_7]
  have h15_8 : restrictedCard 15 8 = 146 := by
    rw [restrictedCard_step (n := 15) (m := 7) (j := 7) (k := 8) rfl rfl, h15_7,
      restrictedCard_eq_p (n := 7) (k := 8) (by norm_num), hp7]
  have h15_9 : restrictedCard 15 9 = 157 := by
    rw [restrictedCard_step (n := 15) (m := 6) (j := 8) (k := 9) rfl rfl, h15_8,
      restrictedCard_eq_p (n := 6) (k := 9) (by norm_num), hp6]
  have h15_10 : restrictedCard 15 10 = 164 := by
    rw [restrictedCard_step (n := 15) (m := 5) (j := 9) (k := 10) rfl rfl, h15_9,
      restrictedCard_eq_p (n := 5) (k := 10) (by norm_num), hp5]
  have h15_11 : restrictedCard 15 11 = 169 := by
    rw [restrictedCard_step (n := 15) (m := 4) (j := 10) (k := 11) rfl rfl, h15_10,
      restrictedCard_eq_p (n := 4) (k := 11) (by norm_num), hp4]
  have h15_12 : restrictedCard 15 12 = 172 := by
    rw [restrictedCard_step (n := 15) (m := 3) (j := 11) (k := 12) rfl rfl, h15_11,
      restrictedCard_eq_p (n := 3) (k := 12) (by norm_num), hp3]
  have h15_13 : restrictedCard 15 13 = 174 := by
    rw [restrictedCard_step (n := 15) (m := 2) (j := 12) (k := 13) rfl rfl, h15_12,
      restrictedCard_eq_p (n := 2) (k := 13) (by norm_num), hp2]
  have h15_14 : restrictedCard 15 14 = 175 := by
    rw [restrictedCard_step (n := 15) (m := 1) (j := 13) (k := 14) rfl rfl, h15_13,
      restrictedCard_eq_p (n := 1) (k := 14) (by norm_num), hp1]
  have h15_15 : restrictedCard 15 15 = 176 := by
    rw [restrictedCard_step (n := 15) (m := 0) (j := 14) (k := 15) rfl rfl, h15_14,
      restrictedCard_eq_p (n := 0) (k := 15) (by norm_num), hp0]
  have hp15 : Erdos1106.p 15 = 176 := (restrictedCard_eq_p (le_refl 15)).symm.trans h15_15
  have h16_1 : restrictedCard 16 1 = 1 := by
    rw [restrictedCard_step (n := 16) (m := 15) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 16) (by norm_num), h15_1]
  have h16_2 : restrictedCard 16 2 = 9 := by
    rw [restrictedCard_step (n := 16) (m := 14) (j := 1) (k := 2) rfl rfl, h16_1, h14_2]
  have h16_3 : restrictedCard 16 3 = 30 := by
    rw [restrictedCard_step (n := 16) (m := 13) (j := 2) (k := 3) rfl rfl, h16_2, h13_3]
  have h16_4 : restrictedCard 16 4 = 64 := by
    rw [restrictedCard_step (n := 16) (m := 12) (j := 3) (k := 4) rfl rfl, h16_3, h12_4]
  have h16_5 : restrictedCard 16 5 = 101 := by
    rw [restrictedCard_step (n := 16) (m := 11) (j := 4) (k := 5) rfl rfl, h16_4, h11_5]
  have h16_6 : restrictedCard 16 6 = 136 := by
    rw [restrictedCard_step (n := 16) (m := 10) (j := 5) (k := 6) rfl rfl, h16_5, h10_6]
  have h16_7 : restrictedCard 16 7 = 164 := by
    rw [restrictedCard_step (n := 16) (m := 9) (j := 6) (k := 7) rfl rfl, h16_6, h9_7]
  have h16_8 : restrictedCard 16 8 = 186 := by
    rw [restrictedCard_step (n := 16) (m := 8) (j := 7) (k := 8) rfl rfl, h16_7, h8_8]
  have h16_9 : restrictedCard 16 9 = 201 := by
    rw [restrictedCard_step (n := 16) (m := 7) (j := 8) (k := 9) rfl rfl, h16_8,
      restrictedCard_eq_p (n := 7) (k := 9) (by norm_num), hp7]
  have h16_10 : restrictedCard 16 10 = 212 := by
    rw [restrictedCard_step (n := 16) (m := 6) (j := 9) (k := 10) rfl rfl, h16_9,
      restrictedCard_eq_p (n := 6) (k := 10) (by norm_num), hp6]
  have h16_11 : restrictedCard 16 11 = 219 := by
    rw [restrictedCard_step (n := 16) (m := 5) (j := 10) (k := 11) rfl rfl, h16_10,
      restrictedCard_eq_p (n := 5) (k := 11) (by norm_num), hp5]
  have h16_12 : restrictedCard 16 12 = 224 := by
    rw [restrictedCard_step (n := 16) (m := 4) (j := 11) (k := 12) rfl rfl, h16_11,
      restrictedCard_eq_p (n := 4) (k := 12) (by norm_num), hp4]
  have h16_13 : restrictedCard 16 13 = 227 := by
    rw [restrictedCard_step (n := 16) (m := 3) (j := 12) (k := 13) rfl rfl, h16_12,
      restrictedCard_eq_p (n := 3) (k := 13) (by norm_num), hp3]
  have h16_14 : restrictedCard 16 14 = 229 := by
    rw [restrictedCard_step (n := 16) (m := 2) (j := 13) (k := 14) rfl rfl, h16_13,
      restrictedCard_eq_p (n := 2) (k := 14) (by norm_num), hp2]
  have h16_15 : restrictedCard 16 15 = 230 := by
    rw [restrictedCard_step (n := 16) (m := 1) (j := 14) (k := 15) rfl rfl, h16_14,
      restrictedCard_eq_p (n := 1) (k := 15) (by norm_num), hp1]
  have h16_16 : restrictedCard 16 16 = 231 := by
    rw [restrictedCard_step (n := 16) (m := 0) (j := 15) (k := 16) rfl rfl, h16_15,
      restrictedCard_eq_p (n := 0) (k := 16) (by norm_num), hp0]
  have hp16 : Erdos1106.p 16 = 231 := (restrictedCard_eq_p (le_refl 16)).symm.trans h16_16
  have h17_1 : restrictedCard 17 1 = 1 := by
    rw [restrictedCard_step (n := 17) (m := 16) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 17) (by norm_num), h16_1]
  have h17_2 : restrictedCard 17 2 = 9 := by
    rw [restrictedCard_step (n := 17) (m := 15) (j := 1) (k := 2) rfl rfl, h17_1, h15_2]
  have h17_3 : restrictedCard 17 3 = 33 := by
    rw [restrictedCard_step (n := 17) (m := 14) (j := 2) (k := 3) rfl rfl, h17_2, h14_3]
  have h17_4 : restrictedCard 17 4 = 72 := by
    rw [restrictedCard_step (n := 17) (m := 13) (j := 3) (k := 4) rfl rfl, h17_3, h13_4]
  have h17_5 : restrictedCard 17 5 = 119 := by
    rw [restrictedCard_step (n := 17) (m := 12) (j := 4) (k := 5) rfl rfl, h17_4, h12_5]
  have h17_6 : restrictedCard 17 6 = 163 := by
    rw [restrictedCard_step (n := 17) (m := 11) (j := 5) (k := 6) rfl rfl, h17_5, h11_6]
  have h17_7 : restrictedCard 17 7 = 201 := by
    rw [restrictedCard_step (n := 17) (m := 10) (j := 6) (k := 7) rfl rfl, h17_6, h10_7]
  have h17_8 : restrictedCard 17 8 = 230 := by
    rw [restrictedCard_step (n := 17) (m := 9) (j := 7) (k := 8) rfl rfl, h17_7, h9_8]
  have h17_9 : restrictedCard 17 9 = 252 := by
    rw [restrictedCard_step (n := 17) (m := 8) (j := 8) (k := 9) rfl rfl, h17_8,
      restrictedCard_eq_p (n := 8) (k := 9) (by norm_num), hp8]
  have h17_10 : restrictedCard 17 10 = 267 := by
    rw [restrictedCard_step (n := 17) (m := 7) (j := 9) (k := 10) rfl rfl, h17_9,
      restrictedCard_eq_p (n := 7) (k := 10) (by norm_num), hp7]
  have h17_11 : restrictedCard 17 11 = 278 := by
    rw [restrictedCard_step (n := 17) (m := 6) (j := 10) (k := 11) rfl rfl, h17_10,
      restrictedCard_eq_p (n := 6) (k := 11) (by norm_num), hp6]
  have h17_12 : restrictedCard 17 12 = 285 := by
    rw [restrictedCard_step (n := 17) (m := 5) (j := 11) (k := 12) rfl rfl, h17_11,
      restrictedCard_eq_p (n := 5) (k := 12) (by norm_num), hp5]
  have h17_13 : restrictedCard 17 13 = 290 := by
    rw [restrictedCard_step (n := 17) (m := 4) (j := 12) (k := 13) rfl rfl, h17_12,
      restrictedCard_eq_p (n := 4) (k := 13) (by norm_num), hp4]
  have h17_14 : restrictedCard 17 14 = 293 := by
    rw [restrictedCard_step (n := 17) (m := 3) (j := 13) (k := 14) rfl rfl, h17_13,
      restrictedCard_eq_p (n := 3) (k := 14) (by norm_num), hp3]
  have h17_15 : restrictedCard 17 15 = 295 := by
    rw [restrictedCard_step (n := 17) (m := 2) (j := 14) (k := 15) rfl rfl, h17_14,
      restrictedCard_eq_p (n := 2) (k := 15) (by norm_num), hp2]
  have h17_16 : restrictedCard 17 16 = 296 := by
    rw [restrictedCard_step (n := 17) (m := 1) (j := 15) (k := 16) rfl rfl, h17_15,
      restrictedCard_eq_p (n := 1) (k := 16) (by norm_num), hp1]
  have h17_17 : restrictedCard 17 17 = 297 := by
    rw [restrictedCard_step (n := 17) (m := 0) (j := 16) (k := 17) rfl rfl, h17_16,
      restrictedCard_eq_p (n := 0) (k := 17) (by norm_num), hp0]
  have hp17 : Erdos1106.p 17 = 297 := (restrictedCard_eq_p (le_refl 17)).symm.trans h17_17
  have h18_1 : restrictedCard 18 1 = 1 := by
    rw [restrictedCard_step (n := 18) (m := 17) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 18) (by norm_num), h17_1]
  have h18_2 : restrictedCard 18 2 = 10 := by
    rw [restrictedCard_step (n := 18) (m := 16) (j := 1) (k := 2) rfl rfl, h18_1, h16_2]
  have h18_3 : restrictedCard 18 3 = 37 := by
    rw [restrictedCard_step (n := 18) (m := 15) (j := 2) (k := 3) rfl rfl, h18_2, h15_3]
  have h18_4 : restrictedCard 18 4 = 84 := by
    rw [restrictedCard_step (n := 18) (m := 14) (j := 3) (k := 4) rfl rfl, h18_3, h14_4]
  have h18_5 : restrictedCard 18 5 = 141 := by
    rw [restrictedCard_step (n := 18) (m := 13) (j := 4) (k := 5) rfl rfl, h18_4, h13_5]
  have h18_6 : restrictedCard 18 6 = 199 := by
    rw [restrictedCard_step (n := 18) (m := 12) (j := 5) (k := 6) rfl rfl, h18_5, h12_6]
  have h18_7 : restrictedCard 18 7 = 248 := by
    rw [restrictedCard_step (n := 18) (m := 11) (j := 6) (k := 7) rfl rfl, h18_6, h11_7]
  have h18_8 : restrictedCard 18 8 = 288 := by
    rw [restrictedCard_step (n := 18) (m := 10) (j := 7) (k := 8) rfl rfl, h18_7, h10_8]
  have h18_9 : restrictedCard 18 9 = 318 := by
    rw [restrictedCard_step (n := 18) (m := 9) (j := 8) (k := 9) rfl rfl, h18_8, h9_9]
  have h18_10 : restrictedCard 18 10 = 340 := by
    rw [restrictedCard_step (n := 18) (m := 8) (j := 9) (k := 10) rfl rfl, h18_9,
      restrictedCard_eq_p (n := 8) (k := 10) (by norm_num), hp8]
  have h18_11 : restrictedCard 18 11 = 355 := by
    rw [restrictedCard_step (n := 18) (m := 7) (j := 10) (k := 11) rfl rfl, h18_10,
      restrictedCard_eq_p (n := 7) (k := 11) (by norm_num), hp7]
  have h18_12 : restrictedCard 18 12 = 366 := by
    rw [restrictedCard_step (n := 18) (m := 6) (j := 11) (k := 12) rfl rfl, h18_11,
      restrictedCard_eq_p (n := 6) (k := 12) (by norm_num), hp6]
  have h18_13 : restrictedCard 18 13 = 373 := by
    rw [restrictedCard_step (n := 18) (m := 5) (j := 12) (k := 13) rfl rfl, h18_12,
      restrictedCard_eq_p (n := 5) (k := 13) (by norm_num), hp5]
  have h18_14 : restrictedCard 18 14 = 378 := by
    rw [restrictedCard_step (n := 18) (m := 4) (j := 13) (k := 14) rfl rfl, h18_13,
      restrictedCard_eq_p (n := 4) (k := 14) (by norm_num), hp4]
  have h18_15 : restrictedCard 18 15 = 381 := by
    rw [restrictedCard_step (n := 18) (m := 3) (j := 14) (k := 15) rfl rfl, h18_14,
      restrictedCard_eq_p (n := 3) (k := 15) (by norm_num), hp3]
  have h18_16 : restrictedCard 18 16 = 383 := by
    rw [restrictedCard_step (n := 18) (m := 2) (j := 15) (k := 16) rfl rfl, h18_15,
      restrictedCard_eq_p (n := 2) (k := 16) (by norm_num), hp2]
  have h18_17 : restrictedCard 18 17 = 384 := by
    rw [restrictedCard_step (n := 18) (m := 1) (j := 16) (k := 17) rfl rfl, h18_16,
      restrictedCard_eq_p (n := 1) (k := 17) (by norm_num), hp1]
  have h18_18 : restrictedCard 18 18 = 385 := by
    rw [restrictedCard_step (n := 18) (m := 0) (j := 17) (k := 18) rfl rfl, h18_17,
      restrictedCard_eq_p (n := 0) (k := 18) (by norm_num), hp0]
  have hp18 : Erdos1106.p 18 = 385 := (restrictedCard_eq_p (le_refl 18)).symm.trans h18_18
  have h19_1 : restrictedCard 19 1 = 1 := by
    rw [restrictedCard_step (n := 19) (m := 18) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 19) (by norm_num), h18_1]
  have h19_2 : restrictedCard 19 2 = 10 := by
    rw [restrictedCard_step (n := 19) (m := 17) (j := 1) (k := 2) rfl rfl, h19_1, h17_2]
  have h19_3 : restrictedCard 19 3 = 40 := by
    rw [restrictedCard_step (n := 19) (m := 16) (j := 2) (k := 3) rfl rfl, h19_2, h16_3]
  have h19_4 : restrictedCard 19 4 = 94 := by
    rw [restrictedCard_step (n := 19) (m := 15) (j := 3) (k := 4) rfl rfl, h19_3, h15_4]
  have h19_5 : restrictedCard 19 5 = 164 := by
    rw [restrictedCard_step (n := 19) (m := 14) (j := 4) (k := 5) rfl rfl, h19_4, h14_5]
  have h19_6 : restrictedCard 19 6 = 235 := by
    rw [restrictedCard_step (n := 19) (m := 13) (j := 5) (k := 6) rfl rfl, h19_5, h13_6]
  have h19_7 : restrictedCard 19 7 = 300 := by
    rw [restrictedCard_step (n := 19) (m := 12) (j := 6) (k := 7) rfl rfl, h19_6, h12_7]
  have h19_8 : restrictedCard 19 8 = 352 := by
    rw [restrictedCard_step (n := 19) (m := 11) (j := 7) (k := 8) rfl rfl, h19_7, h11_8]
  have h19_9 : restrictedCard 19 9 = 393 := by
    rw [restrictedCard_step (n := 19) (m := 10) (j := 8) (k := 9) rfl rfl, h19_8, h10_9]
  have h19_10 : restrictedCard 19 10 = 423 := by
    rw [restrictedCard_step (n := 19) (m := 9) (j := 9) (k := 10) rfl rfl, h19_9,
      restrictedCard_eq_p (n := 9) (k := 10) (by norm_num), hp9]
  have h19_11 : restrictedCard 19 11 = 445 := by
    rw [restrictedCard_step (n := 19) (m := 8) (j := 10) (k := 11) rfl rfl, h19_10,
      restrictedCard_eq_p (n := 8) (k := 11) (by norm_num), hp8]
  have h19_12 : restrictedCard 19 12 = 460 := by
    rw [restrictedCard_step (n := 19) (m := 7) (j := 11) (k := 12) rfl rfl, h19_11,
      restrictedCard_eq_p (n := 7) (k := 12) (by norm_num), hp7]
  have h19_13 : restrictedCard 19 13 = 471 := by
    rw [restrictedCard_step (n := 19) (m := 6) (j := 12) (k := 13) rfl rfl, h19_12,
      restrictedCard_eq_p (n := 6) (k := 13) (by norm_num), hp6]
  have h19_14 : restrictedCard 19 14 = 478 := by
    rw [restrictedCard_step (n := 19) (m := 5) (j := 13) (k := 14) rfl rfl, h19_13,
      restrictedCard_eq_p (n := 5) (k := 14) (by norm_num), hp5]
  have h19_15 : restrictedCard 19 15 = 483 := by
    rw [restrictedCard_step (n := 19) (m := 4) (j := 14) (k := 15) rfl rfl, h19_14,
      restrictedCard_eq_p (n := 4) (k := 15) (by norm_num), hp4]
  have h19_16 : restrictedCard 19 16 = 486 := by
    rw [restrictedCard_step (n := 19) (m := 3) (j := 15) (k := 16) rfl rfl, h19_15,
      restrictedCard_eq_p (n := 3) (k := 16) (by norm_num), hp3]
  have h19_17 : restrictedCard 19 17 = 488 := by
    rw [restrictedCard_step (n := 19) (m := 2) (j := 16) (k := 17) rfl rfl, h19_16,
      restrictedCard_eq_p (n := 2) (k := 17) (by norm_num), hp2]
  have h19_18 : restrictedCard 19 18 = 489 := by
    rw [restrictedCard_step (n := 19) (m := 1) (j := 17) (k := 18) rfl rfl, h19_17,
      restrictedCard_eq_p (n := 1) (k := 18) (by norm_num), hp1]
  have h19_19 : restrictedCard 19 19 = 490 := by
    rw [restrictedCard_step (n := 19) (m := 0) (j := 18) (k := 19) rfl rfl, h19_18,
      restrictedCard_eq_p (n := 0) (k := 19) (by norm_num), hp0]
  have hp19 : Erdos1106.p 19 = 490 := (restrictedCard_eq_p (le_refl 19)).symm.trans h19_19
  have h20_1 : restrictedCard 20 1 = 1 := by
    rw [restrictedCard_step (n := 20) (m := 19) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 20) (by norm_num), h19_1]
  have h20_2 : restrictedCard 20 2 = 11 := by
    rw [restrictedCard_step (n := 20) (m := 18) (j := 1) (k := 2) rfl rfl, h20_1, h18_2]
  have h20_3 : restrictedCard 20 3 = 44 := by
    rw [restrictedCard_step (n := 20) (m := 17) (j := 2) (k := 3) rfl rfl, h20_2, h17_3]
  have h20_4 : restrictedCard 20 4 = 108 := by
    rw [restrictedCard_step (n := 20) (m := 16) (j := 3) (k := 4) rfl rfl, h20_3, h16_4]
  have h20_5 : restrictedCard 20 5 = 192 := by
    rw [restrictedCard_step (n := 20) (m := 15) (j := 4) (k := 5) rfl rfl, h20_4, h15_5]
  have h20_6 : restrictedCard 20 6 = 282 := by
    rw [restrictedCard_step (n := 20) (m := 14) (j := 5) (k := 6) rfl rfl, h20_5, h14_6]
  have h20_7 : restrictedCard 20 7 = 364 := by
    rw [restrictedCard_step (n := 20) (m := 13) (j := 6) (k := 7) rfl rfl, h20_6, h13_7]
  have h20_8 : restrictedCard 20 8 = 434 := by
    rw [restrictedCard_step (n := 20) (m := 12) (j := 7) (k := 8) rfl rfl, h20_7, h12_8]
  have h20_9 : restrictedCard 20 9 = 488 := by
    rw [restrictedCard_step (n := 20) (m := 11) (j := 8) (k := 9) rfl rfl, h20_8, h11_9]
  have h20_10 : restrictedCard 20 10 = 530 := by
    rw [restrictedCard_step (n := 20) (m := 10) (j := 9) (k := 10) rfl rfl, h20_9, h10_10]
  have h20_11 : restrictedCard 20 11 = 560 := by
    rw [restrictedCard_step (n := 20) (m := 9) (j := 10) (k := 11) rfl rfl, h20_10,
      restrictedCard_eq_p (n := 9) (k := 11) (by norm_num), hp9]
  have h20_12 : restrictedCard 20 12 = 582 := by
    rw [restrictedCard_step (n := 20) (m := 8) (j := 11) (k := 12) rfl rfl, h20_11,
      restrictedCard_eq_p (n := 8) (k := 12) (by norm_num), hp8]
  have h20_13 : restrictedCard 20 13 = 597 := by
    rw [restrictedCard_step (n := 20) (m := 7) (j := 12) (k := 13) rfl rfl, h20_12,
      restrictedCard_eq_p (n := 7) (k := 13) (by norm_num), hp7]
  have h20_14 : restrictedCard 20 14 = 608 := by
    rw [restrictedCard_step (n := 20) (m := 6) (j := 13) (k := 14) rfl rfl, h20_13,
      restrictedCard_eq_p (n := 6) (k := 14) (by norm_num), hp6]
  have h20_15 : restrictedCard 20 15 = 615 := by
    rw [restrictedCard_step (n := 20) (m := 5) (j := 14) (k := 15) rfl rfl, h20_14,
      restrictedCard_eq_p (n := 5) (k := 15) (by norm_num), hp5]
  have h20_16 : restrictedCard 20 16 = 620 := by
    rw [restrictedCard_step (n := 20) (m := 4) (j := 15) (k := 16) rfl rfl, h20_15,
      restrictedCard_eq_p (n := 4) (k := 16) (by norm_num), hp4]
  have h20_17 : restrictedCard 20 17 = 623 := by
    rw [restrictedCard_step (n := 20) (m := 3) (j := 16) (k := 17) rfl rfl, h20_16,
      restrictedCard_eq_p (n := 3) (k := 17) (by norm_num), hp3]
  have h20_18 : restrictedCard 20 18 = 625 := by
    rw [restrictedCard_step (n := 20) (m := 2) (j := 17) (k := 18) rfl rfl, h20_17,
      restrictedCard_eq_p (n := 2) (k := 18) (by norm_num), hp2]
  have h20_19 : restrictedCard 20 19 = 626 := by
    rw [restrictedCard_step (n := 20) (m := 1) (j := 18) (k := 19) rfl rfl, h20_18,
      restrictedCard_eq_p (n := 1) (k := 19) (by norm_num), hp1]
  have h20_20 : restrictedCard 20 20 = 627 := by
    rw [restrictedCard_step (n := 20) (m := 0) (j := 19) (k := 20) rfl rfl, h20_19,
      restrictedCard_eq_p (n := 0) (k := 20) (by norm_num), hp0]
  have hp20 : Erdos1106.p 20 = 627 := (restrictedCard_eq_p (le_refl 20)).symm.trans h20_20
  have h21_1 : restrictedCard 21 1 = 1 := by
    rw [restrictedCard_step (n := 21) (m := 20) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 21) (by norm_num), h20_1]
  have h21_2 : restrictedCard 21 2 = 11 := by
    rw [restrictedCard_step (n := 21) (m := 19) (j := 1) (k := 2) rfl rfl, h21_1, h19_2]
  have h21_3 : restrictedCard 21 3 = 48 := by
    rw [restrictedCard_step (n := 21) (m := 18) (j := 2) (k := 3) rfl rfl, h21_2, h18_3]
  have h21_4 : restrictedCard 21 4 = 120 := by
    rw [restrictedCard_step (n := 21) (m := 17) (j := 3) (k := 4) rfl rfl, h21_3, h17_4]
  have h21_5 : restrictedCard 21 5 = 221 := by
    rw [restrictedCard_step (n := 21) (m := 16) (j := 4) (k := 5) rfl rfl, h21_4, h16_5]
  have h21_6 : restrictedCard 21 6 = 331 := by
    rw [restrictedCard_step (n := 21) (m := 15) (j := 5) (k := 6) rfl rfl, h21_5, h15_6]
  have h21_7 : restrictedCard 21 7 = 436 := by
    rw [restrictedCard_step (n := 21) (m := 14) (j := 6) (k := 7) rfl rfl, h21_6, h14_7]
  have h21_8 : restrictedCard 21 8 = 525 := by
    rw [restrictedCard_step (n := 21) (m := 13) (j := 7) (k := 8) rfl rfl, h21_7, h13_8]
  have h21_9 : restrictedCard 21 9 = 598 := by
    rw [restrictedCard_step (n := 21) (m := 12) (j := 8) (k := 9) rfl rfl, h21_8, h12_9]
  have h21_10 : restrictedCard 21 10 = 653 := by
    rw [restrictedCard_step (n := 21) (m := 11) (j := 9) (k := 10) rfl rfl, h21_9, h11_10]
  have h21_11 : restrictedCard 21 11 = 695 := by
    rw [restrictedCard_step (n := 21) (m := 10) (j := 10) (k := 11) rfl rfl, h21_10,
      restrictedCard_eq_p (n := 10) (k := 11) (by norm_num), hp10]
  have h21_12 : restrictedCard 21 12 = 725 := by
    rw [restrictedCard_step (n := 21) (m := 9) (j := 11) (k := 12) rfl rfl, h21_11,
      restrictedCard_eq_p (n := 9) (k := 12) (by norm_num), hp9]
  have h21_13 : restrictedCard 21 13 = 747 := by
    rw [restrictedCard_step (n := 21) (m := 8) (j := 12) (k := 13) rfl rfl, h21_12,
      restrictedCard_eq_p (n := 8) (k := 13) (by norm_num), hp8]
  have h21_14 : restrictedCard 21 14 = 762 := by
    rw [restrictedCard_step (n := 21) (m := 7) (j := 13) (k := 14) rfl rfl, h21_13,
      restrictedCard_eq_p (n := 7) (k := 14) (by norm_num), hp7]
  have h21_15 : restrictedCard 21 15 = 773 := by
    rw [restrictedCard_step (n := 21) (m := 6) (j := 14) (k := 15) rfl rfl, h21_14,
      restrictedCard_eq_p (n := 6) (k := 15) (by norm_num), hp6]
  have h21_16 : restrictedCard 21 16 = 780 := by
    rw [restrictedCard_step (n := 21) (m := 5) (j := 15) (k := 16) rfl rfl, h21_15,
      restrictedCard_eq_p (n := 5) (k := 16) (by norm_num), hp5]
  have h21_17 : restrictedCard 21 17 = 785 := by
    rw [restrictedCard_step (n := 21) (m := 4) (j := 16) (k := 17) rfl rfl, h21_16,
      restrictedCard_eq_p (n := 4) (k := 17) (by norm_num), hp4]
  have h21_18 : restrictedCard 21 18 = 788 := by
    rw [restrictedCard_step (n := 21) (m := 3) (j := 17) (k := 18) rfl rfl, h21_17,
      restrictedCard_eq_p (n := 3) (k := 18) (by norm_num), hp3]
  have h21_19 : restrictedCard 21 19 = 790 := by
    rw [restrictedCard_step (n := 21) (m := 2) (j := 18) (k := 19) rfl rfl, h21_18,
      restrictedCard_eq_p (n := 2) (k := 19) (by norm_num), hp2]
  have h21_20 : restrictedCard 21 20 = 791 := by
    rw [restrictedCard_step (n := 21) (m := 1) (j := 19) (k := 20) rfl rfl, h21_19,
      restrictedCard_eq_p (n := 1) (k := 20) (by norm_num), hp1]
  have h21_21 : restrictedCard 21 21 = 792 := by
    rw [restrictedCard_step (n := 21) (m := 0) (j := 20) (k := 21) rfl rfl, h21_20,
      restrictedCard_eq_p (n := 0) (k := 21) (by norm_num), hp0]
  have hp21 : Erdos1106.p 21 = 792 := (restrictedCard_eq_p (le_refl 21)).symm.trans h21_21
  have h22_1 : restrictedCard 22 1 = 1 := by
    rw [restrictedCard_step (n := 22) (m := 21) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 22) (by norm_num), h21_1]
  have h22_2 : restrictedCard 22 2 = 12 := by
    rw [restrictedCard_step (n := 22) (m := 20) (j := 1) (k := 2) rfl rfl, h22_1, h20_2]
  have h22_3 : restrictedCard 22 3 = 52 := by
    rw [restrictedCard_step (n := 22) (m := 19) (j := 2) (k := 3) rfl rfl, h22_2, h19_3]
  have h22_4 : restrictedCard 22 4 = 136 := by
    rw [restrictedCard_step (n := 22) (m := 18) (j := 3) (k := 4) rfl rfl, h22_3, h18_4]
  have h22_5 : restrictedCard 22 5 = 255 := by
    rw [restrictedCard_step (n := 22) (m := 17) (j := 4) (k := 5) rfl rfl, h22_4, h17_5]
  have h22_6 : restrictedCard 22 6 = 391 := by
    rw [restrictedCard_step (n := 22) (m := 16) (j := 5) (k := 6) rfl rfl, h22_5, h16_6]
  have h22_7 : restrictedCard 22 7 = 522 := by
    rw [restrictedCard_step (n := 22) (m := 15) (j := 6) (k := 7) rfl rfl, h22_6, h15_7]
  have h22_8 : restrictedCard 22 8 = 638 := by
    rw [restrictedCard_step (n := 22) (m := 14) (j := 7) (k := 8) rfl rfl, h22_7, h14_8]
  have h22_9 : restrictedCard 22 9 = 732 := by
    rw [restrictedCard_step (n := 22) (m := 13) (j := 8) (k := 9) rfl rfl, h22_8, h13_9]
  have h22_10 : restrictedCard 22 10 = 807 := by
    rw [restrictedCard_step (n := 22) (m := 12) (j := 9) (k := 10) rfl rfl, h22_9, h12_10]
  have h22_11 : restrictedCard 22 11 = 863 := by
    rw [restrictedCard_step (n := 22) (m := 11) (j := 10) (k := 11) rfl rfl, h22_10, h11_11]
  have h22_12 : restrictedCard 22 12 = 905 := by
    rw [restrictedCard_step (n := 22) (m := 10) (j := 11) (k := 12) rfl rfl, h22_11,
      restrictedCard_eq_p (n := 10) (k := 12) (by norm_num), hp10]
  have h22_13 : restrictedCard 22 13 = 935 := by
    rw [restrictedCard_step (n := 22) (m := 9) (j := 12) (k := 13) rfl rfl, h22_12,
      restrictedCard_eq_p (n := 9) (k := 13) (by norm_num), hp9]
  have h22_14 : restrictedCard 22 14 = 957 := by
    rw [restrictedCard_step (n := 22) (m := 8) (j := 13) (k := 14) rfl rfl, h22_13,
      restrictedCard_eq_p (n := 8) (k := 14) (by norm_num), hp8]
  have h22_15 : restrictedCard 22 15 = 972 := by
    rw [restrictedCard_step (n := 22) (m := 7) (j := 14) (k := 15) rfl rfl, h22_14,
      restrictedCard_eq_p (n := 7) (k := 15) (by norm_num), hp7]
  have h22_16 : restrictedCard 22 16 = 983 := by
    rw [restrictedCard_step (n := 22) (m := 6) (j := 15) (k := 16) rfl rfl, h22_15,
      restrictedCard_eq_p (n := 6) (k := 16) (by norm_num), hp6]
  have h22_17 : restrictedCard 22 17 = 990 := by
    rw [restrictedCard_step (n := 22) (m := 5) (j := 16) (k := 17) rfl rfl, h22_16,
      restrictedCard_eq_p (n := 5) (k := 17) (by norm_num), hp5]
  have h22_18 : restrictedCard 22 18 = 995 := by
    rw [restrictedCard_step (n := 22) (m := 4) (j := 17) (k := 18) rfl rfl, h22_17,
      restrictedCard_eq_p (n := 4) (k := 18) (by norm_num), hp4]
  have h22_19 : restrictedCard 22 19 = 998 := by
    rw [restrictedCard_step (n := 22) (m := 3) (j := 18) (k := 19) rfl rfl, h22_18,
      restrictedCard_eq_p (n := 3) (k := 19) (by norm_num), hp3]
  have h22_20 : restrictedCard 22 20 = 1000 := by
    rw [restrictedCard_step (n := 22) (m := 2) (j := 19) (k := 20) rfl rfl, h22_19,
      restrictedCard_eq_p (n := 2) (k := 20) (by norm_num), hp2]
  have h22_21 : restrictedCard 22 21 = 1001 := by
    rw [restrictedCard_step (n := 22) (m := 1) (j := 20) (k := 21) rfl rfl, h22_20,
      restrictedCard_eq_p (n := 1) (k := 21) (by norm_num), hp1]
  have h22_22 : restrictedCard 22 22 = 1002 := by
    rw [restrictedCard_step (n := 22) (m := 0) (j := 21) (k := 22) rfl rfl, h22_21,
      restrictedCard_eq_p (n := 0) (k := 22) (by norm_num), hp0]
  have hp22 : Erdos1106.p 22 = 1002 := (restrictedCard_eq_p (le_refl 22)).symm.trans h22_22
  have h23_1 : restrictedCard 23 1 = 1 := by
    rw [restrictedCard_step (n := 23) (m := 22) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 23) (by norm_num), h22_1]
  have h23_2 : restrictedCard 23 2 = 12 := by
    rw [restrictedCard_step (n := 23) (m := 21) (j := 1) (k := 2) rfl rfl, h23_1, h21_2]
  have h23_3 : restrictedCard 23 3 = 56 := by
    rw [restrictedCard_step (n := 23) (m := 20) (j := 2) (k := 3) rfl rfl, h23_2, h20_3]
  have h23_4 : restrictedCard 23 4 = 150 := by
    rw [restrictedCard_step (n := 23) (m := 19) (j := 3) (k := 4) rfl rfl, h23_3, h19_4]
  have h23_5 : restrictedCard 23 5 = 291 := by
    rw [restrictedCard_step (n := 23) (m := 18) (j := 4) (k := 5) rfl rfl, h23_4, h18_5]
  have h23_6 : restrictedCard 23 6 = 454 := by
    rw [restrictedCard_step (n := 23) (m := 17) (j := 5) (k := 6) rfl rfl, h23_5, h17_6]
  have h23_7 : restrictedCard 23 7 = 618 := by
    rw [restrictedCard_step (n := 23) (m := 16) (j := 6) (k := 7) rfl rfl, h23_6, h16_7]
  have h23_8 : restrictedCard 23 8 = 764 := by
    rw [restrictedCard_step (n := 23) (m := 15) (j := 7) (k := 8) rfl rfl, h23_7, h15_8]
  have h23_9 : restrictedCard 23 9 = 887 := by
    rw [restrictedCard_step (n := 23) (m := 14) (j := 8) (k := 9) rfl rfl, h23_8, h14_9]
  have h23_10 : restrictedCard 23 10 = 984 := by
    rw [restrictedCard_step (n := 23) (m := 13) (j := 9) (k := 10) rfl rfl, h23_9, h13_10]
  have h23_11 : restrictedCard 23 11 = 1060 := by
    rw [restrictedCard_step (n := 23) (m := 12) (j := 10) (k := 11) rfl rfl, h23_10, h12_11]
  have h23_12 : restrictedCard 23 12 = 1116 := by
    rw [restrictedCard_step (n := 23) (m := 11) (j := 11) (k := 12) rfl rfl, h23_11,
      restrictedCard_eq_p (n := 11) (k := 12) (by norm_num), hp11]
  have h23_13 : restrictedCard 23 13 = 1158 := by
    rw [restrictedCard_step (n := 23) (m := 10) (j := 12) (k := 13) rfl rfl, h23_12,
      restrictedCard_eq_p (n := 10) (k := 13) (by norm_num), hp10]
  have h23_14 : restrictedCard 23 14 = 1188 := by
    rw [restrictedCard_step (n := 23) (m := 9) (j := 13) (k := 14) rfl rfl, h23_13,
      restrictedCard_eq_p (n := 9) (k := 14) (by norm_num), hp9]
  have h23_15 : restrictedCard 23 15 = 1210 := by
    rw [restrictedCard_step (n := 23) (m := 8) (j := 14) (k := 15) rfl rfl, h23_14,
      restrictedCard_eq_p (n := 8) (k := 15) (by norm_num), hp8]
  have h23_16 : restrictedCard 23 16 = 1225 := by
    rw [restrictedCard_step (n := 23) (m := 7) (j := 15) (k := 16) rfl rfl, h23_15,
      restrictedCard_eq_p (n := 7) (k := 16) (by norm_num), hp7]
  have h23_17 : restrictedCard 23 17 = 1236 := by
    rw [restrictedCard_step (n := 23) (m := 6) (j := 16) (k := 17) rfl rfl, h23_16,
      restrictedCard_eq_p (n := 6) (k := 17) (by norm_num), hp6]
  have h23_18 : restrictedCard 23 18 = 1243 := by
    rw [restrictedCard_step (n := 23) (m := 5) (j := 17) (k := 18) rfl rfl, h23_17,
      restrictedCard_eq_p (n := 5) (k := 18) (by norm_num), hp5]
  have h23_19 : restrictedCard 23 19 = 1248 := by
    rw [restrictedCard_step (n := 23) (m := 4) (j := 18) (k := 19) rfl rfl, h23_18,
      restrictedCard_eq_p (n := 4) (k := 19) (by norm_num), hp4]
  have h23_20 : restrictedCard 23 20 = 1251 := by
    rw [restrictedCard_step (n := 23) (m := 3) (j := 19) (k := 20) rfl rfl, h23_19,
      restrictedCard_eq_p (n := 3) (k := 20) (by norm_num), hp3]
  have h23_21 : restrictedCard 23 21 = 1253 := by
    rw [restrictedCard_step (n := 23) (m := 2) (j := 20) (k := 21) rfl rfl, h23_20,
      restrictedCard_eq_p (n := 2) (k := 21) (by norm_num), hp2]
  have h23_22 : restrictedCard 23 22 = 1254 := by
    rw [restrictedCard_step (n := 23) (m := 1) (j := 21) (k := 22) rfl rfl, h23_21,
      restrictedCard_eq_p (n := 1) (k := 22) (by norm_num), hp1]
  have h23_23 : restrictedCard 23 23 = 1255 := by
    rw [restrictedCard_step (n := 23) (m := 0) (j := 22) (k := 23) rfl rfl, h23_22,
      restrictedCard_eq_p (n := 0) (k := 23) (by norm_num), hp0]
  have hp23 : Erdos1106.p 23 = 1255 := (restrictedCard_eq_p (le_refl 23)).symm.trans h23_23
  have h24_1 : restrictedCard 24 1 = 1 := by
    rw [restrictedCard_step (n := 24) (m := 23) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 24) (by norm_num), h23_1]
  have h24_2 : restrictedCard 24 2 = 13 := by
    rw [restrictedCard_step (n := 24) (m := 22) (j := 1) (k := 2) rfl rfl, h24_1, h22_2]
  have h24_3 : restrictedCard 24 3 = 61 := by
    rw [restrictedCard_step (n := 24) (m := 21) (j := 2) (k := 3) rfl rfl, h24_2, h21_3]
  have h24_4 : restrictedCard 24 4 = 169 := by
    rw [restrictedCard_step (n := 24) (m := 20) (j := 3) (k := 4) rfl rfl, h24_3, h20_4]
  have h24_5 : restrictedCard 24 5 = 333 := by
    rw [restrictedCard_step (n := 24) (m := 19) (j := 4) (k := 5) rfl rfl, h24_4, h19_5]
  have h24_6 : restrictedCard 24 6 = 532 := by
    rw [restrictedCard_step (n := 24) (m := 18) (j := 5) (k := 6) rfl rfl, h24_5, h18_6]
  have h24_7 : restrictedCard 24 7 = 733 := by
    rw [restrictedCard_step (n := 24) (m := 17) (j := 6) (k := 7) rfl rfl, h24_6, h17_7]
  have h24_8 : restrictedCard 24 8 = 919 := by
    rw [restrictedCard_step (n := 24) (m := 16) (j := 7) (k := 8) rfl rfl, h24_7, h16_8]
  have h24_9 : restrictedCard 24 9 = 1076 := by
    rw [restrictedCard_step (n := 24) (m := 15) (j := 8) (k := 9) rfl rfl, h24_8, h15_9]
  have h24_10 : restrictedCard 24 10 = 1204 := by
    rw [restrictedCard_step (n := 24) (m := 14) (j := 9) (k := 10) rfl rfl, h24_9, h14_10]
  have h24_11 : restrictedCard 24 11 = 1303 := by
    rw [restrictedCard_step (n := 24) (m := 13) (j := 10) (k := 11) rfl rfl, h24_10, h13_11]
  have h24_12 : restrictedCard 24 12 = 1380 := by
    rw [restrictedCard_step (n := 24) (m := 12) (j := 11) (k := 12) rfl rfl, h24_11, h12_12]
  have h24_13 : restrictedCard 24 13 = 1436 := by
    rw [restrictedCard_step (n := 24) (m := 11) (j := 12) (k := 13) rfl rfl, h24_12,
      restrictedCard_eq_p (n := 11) (k := 13) (by norm_num), hp11]
  have h24_14 : restrictedCard 24 14 = 1478 := by
    rw [restrictedCard_step (n := 24) (m := 10) (j := 13) (k := 14) rfl rfl, h24_13,
      restrictedCard_eq_p (n := 10) (k := 14) (by norm_num), hp10]
  have h24_15 : restrictedCard 24 15 = 1508 := by
    rw [restrictedCard_step (n := 24) (m := 9) (j := 14) (k := 15) rfl rfl, h24_14,
      restrictedCard_eq_p (n := 9) (k := 15) (by norm_num), hp9]
  have h24_16 : restrictedCard 24 16 = 1530 := by
    rw [restrictedCard_step (n := 24) (m := 8) (j := 15) (k := 16) rfl rfl, h24_15,
      restrictedCard_eq_p (n := 8) (k := 16) (by norm_num), hp8]
  have h24_17 : restrictedCard 24 17 = 1545 := by
    rw [restrictedCard_step (n := 24) (m := 7) (j := 16) (k := 17) rfl rfl, h24_16,
      restrictedCard_eq_p (n := 7) (k := 17) (by norm_num), hp7]
  have h24_18 : restrictedCard 24 18 = 1556 := by
    rw [restrictedCard_step (n := 24) (m := 6) (j := 17) (k := 18) rfl rfl, h24_17,
      restrictedCard_eq_p (n := 6) (k := 18) (by norm_num), hp6]
  have h24_19 : restrictedCard 24 19 = 1563 := by
    rw [restrictedCard_step (n := 24) (m := 5) (j := 18) (k := 19) rfl rfl, h24_18,
      restrictedCard_eq_p (n := 5) (k := 19) (by norm_num), hp5]
  have h24_20 : restrictedCard 24 20 = 1568 := by
    rw [restrictedCard_step (n := 24) (m := 4) (j := 19) (k := 20) rfl rfl, h24_19,
      restrictedCard_eq_p (n := 4) (k := 20) (by norm_num), hp4]
  have h24_21 : restrictedCard 24 21 = 1571 := by
    rw [restrictedCard_step (n := 24) (m := 3) (j := 20) (k := 21) rfl rfl, h24_20,
      restrictedCard_eq_p (n := 3) (k := 21) (by norm_num), hp3]
  have h24_22 : restrictedCard 24 22 = 1573 := by
    rw [restrictedCard_step (n := 24) (m := 2) (j := 21) (k := 22) rfl rfl, h24_21,
      restrictedCard_eq_p (n := 2) (k := 22) (by norm_num), hp2]
  have h24_23 : restrictedCard 24 23 = 1574 := by
    rw [restrictedCard_step (n := 24) (m := 1) (j := 22) (k := 23) rfl rfl, h24_22,
      restrictedCard_eq_p (n := 1) (k := 23) (by norm_num), hp1]
  have h24_24 : restrictedCard 24 24 = 1575 := by
    rw [restrictedCard_step (n := 24) (m := 0) (j := 23) (k := 24) rfl rfl, h24_23,
      restrictedCard_eq_p (n := 0) (k := 24) (by norm_num), hp0]
  have hp24 : Erdos1106.p 24 = 1575 := (restrictedCard_eq_p (le_refl 24)).symm.trans h24_24
  have h25_1 : restrictedCard 25 1 = 1 := by
    rw [restrictedCard_step (n := 25) (m := 24) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 25) (by norm_num), h24_1]
  have h25_2 : restrictedCard 25 2 = 13 := by
    rw [restrictedCard_step (n := 25) (m := 23) (j := 1) (k := 2) rfl rfl, h25_1, h23_2]
  have h25_3 : restrictedCard 25 3 = 65 := by
    rw [restrictedCard_step (n := 25) (m := 22) (j := 2) (k := 3) rfl rfl, h25_2, h22_3]
  have h25_4 : restrictedCard 25 4 = 185 := by
    rw [restrictedCard_step (n := 25) (m := 21) (j := 3) (k := 4) rfl rfl, h25_3, h21_4]
  have h25_5 : restrictedCard 25 5 = 377 := by
    rw [restrictedCard_step (n := 25) (m := 20) (j := 4) (k := 5) rfl rfl, h25_4, h20_5]
  have h25_6 : restrictedCard 25 6 = 612 := by
    rw [restrictedCard_step (n := 25) (m := 19) (j := 5) (k := 6) rfl rfl, h25_5, h19_6]
  have h25_7 : restrictedCard 25 7 = 860 := by
    rw [restrictedCard_step (n := 25) (m := 18) (j := 6) (k := 7) rfl rfl, h25_6, h18_7]
  have h25_8 : restrictedCard 25 8 = 1090 := by
    rw [restrictedCard_step (n := 25) (m := 17) (j := 7) (k := 8) rfl rfl, h25_7, h17_8]
  have h25_9 : restrictedCard 25 9 = 1291 := by
    rw [restrictedCard_step (n := 25) (m := 16) (j := 8) (k := 9) rfl rfl, h25_8, h16_9]
  have h25_10 : restrictedCard 25 10 = 1455 := by
    rw [restrictedCard_step (n := 25) (m := 15) (j := 9) (k := 10) rfl rfl, h25_9, h15_10]
  have h25_11 : restrictedCard 25 11 = 1586 := by
    rw [restrictedCard_step (n := 25) (m := 14) (j := 10) (k := 11) rfl rfl, h25_10, h14_11]
  have h25_12 : restrictedCard 25 12 = 1686 := by
    rw [restrictedCard_step (n := 25) (m := 13) (j := 11) (k := 12) rfl rfl, h25_11, h13_12]
  have h25_13 : restrictedCard 25 13 = 1763 := by
    rw [restrictedCard_step (n := 25) (m := 12) (j := 12) (k := 13) rfl rfl, h25_12,
      restrictedCard_eq_p (n := 12) (k := 13) (by norm_num), hp12]
  have h25_14 : restrictedCard 25 14 = 1819 := by
    rw [restrictedCard_step (n := 25) (m := 11) (j := 13) (k := 14) rfl rfl, h25_13,
      restrictedCard_eq_p (n := 11) (k := 14) (by norm_num), hp11]
  have h25_15 : restrictedCard 25 15 = 1861 := by
    rw [restrictedCard_step (n := 25) (m := 10) (j := 14) (k := 15) rfl rfl, h25_14,
      restrictedCard_eq_p (n := 10) (k := 15) (by norm_num), hp10]
  have h25_16 : restrictedCard 25 16 = 1891 := by
    rw [restrictedCard_step (n := 25) (m := 9) (j := 15) (k := 16) rfl rfl, h25_15,
      restrictedCard_eq_p (n := 9) (k := 16) (by norm_num), hp9]
  have h25_17 : restrictedCard 25 17 = 1913 := by
    rw [restrictedCard_step (n := 25) (m := 8) (j := 16) (k := 17) rfl rfl, h25_16,
      restrictedCard_eq_p (n := 8) (k := 17) (by norm_num), hp8]
  have h25_18 : restrictedCard 25 18 = 1928 := by
    rw [restrictedCard_step (n := 25) (m := 7) (j := 17) (k := 18) rfl rfl, h25_17,
      restrictedCard_eq_p (n := 7) (k := 18) (by norm_num), hp7]
  have h25_19 : restrictedCard 25 19 = 1939 := by
    rw [restrictedCard_step (n := 25) (m := 6) (j := 18) (k := 19) rfl rfl, h25_18,
      restrictedCard_eq_p (n := 6) (k := 19) (by norm_num), hp6]
  have h25_20 : restrictedCard 25 20 = 1946 := by
    rw [restrictedCard_step (n := 25) (m := 5) (j := 19) (k := 20) rfl rfl, h25_19,
      restrictedCard_eq_p (n := 5) (k := 20) (by norm_num), hp5]
  have h25_21 : restrictedCard 25 21 = 1951 := by
    rw [restrictedCard_step (n := 25) (m := 4) (j := 20) (k := 21) rfl rfl, h25_20,
      restrictedCard_eq_p (n := 4) (k := 21) (by norm_num), hp4]
  have h25_22 : restrictedCard 25 22 = 1954 := by
    rw [restrictedCard_step (n := 25) (m := 3) (j := 21) (k := 22) rfl rfl, h25_21,
      restrictedCard_eq_p (n := 3) (k := 22) (by norm_num), hp3]
  have h25_23 : restrictedCard 25 23 = 1956 := by
    rw [restrictedCard_step (n := 25) (m := 2) (j := 22) (k := 23) rfl rfl, h25_22,
      restrictedCard_eq_p (n := 2) (k := 23) (by norm_num), hp2]
  have h25_24 : restrictedCard 25 24 = 1957 := by
    rw [restrictedCard_step (n := 25) (m := 1) (j := 23) (k := 24) rfl rfl, h25_23,
      restrictedCard_eq_p (n := 1) (k := 24) (by norm_num), hp1]
  have h25_25 : restrictedCard 25 25 = 1958 := by
    rw [restrictedCard_step (n := 25) (m := 0) (j := 24) (k := 25) rfl rfl, h25_24,
      restrictedCard_eq_p (n := 0) (k := 25) (by norm_num), hp0]
  have hp25 : Erdos1106.p 25 = 1958 := (restrictedCard_eq_p (le_refl 25)).symm.trans h25_25
  have h26_1 : restrictedCard 26 1 = 1 := by
    rw [restrictedCard_step (n := 26) (m := 25) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 26) (by norm_num), h25_1]
  have h26_2 : restrictedCard 26 2 = 14 := by
    rw [restrictedCard_step (n := 26) (m := 24) (j := 1) (k := 2) rfl rfl, h26_1, h24_2]
  have h26_3 : restrictedCard 26 3 = 70 := by
    rw [restrictedCard_step (n := 26) (m := 23) (j := 2) (k := 3) rfl rfl, h26_2, h23_3]
  have h26_4 : restrictedCard 26 4 = 206 := by
    rw [restrictedCard_step (n := 26) (m := 22) (j := 3) (k := 4) rfl rfl, h26_3, h22_4]
  have h26_5 : restrictedCard 26 5 = 427 := by
    rw [restrictedCard_step (n := 26) (m := 21) (j := 4) (k := 5) rfl rfl, h26_4, h21_5]
  have h26_6 : restrictedCard 26 6 = 709 := by
    rw [restrictedCard_step (n := 26) (m := 20) (j := 5) (k := 6) rfl rfl, h26_5, h20_6]
  have h26_7 : restrictedCard 26 7 = 1009 := by
    rw [restrictedCard_step (n := 26) (m := 19) (j := 6) (k := 7) rfl rfl, h26_6, h19_7]
  have h26_8 : restrictedCard 26 8 = 1297 := by
    rw [restrictedCard_step (n := 26) (m := 18) (j := 7) (k := 8) rfl rfl, h26_7, h18_8]
  have h26_9 : restrictedCard 26 9 = 1549 := by
    rw [restrictedCard_step (n := 26) (m := 17) (j := 8) (k := 9) rfl rfl, h26_8, h17_9]
  have h26_10 : restrictedCard 26 10 = 1761 := by
    rw [restrictedCard_step (n := 26) (m := 16) (j := 9) (k := 10) rfl rfl, h26_9, h16_10]
  have h26_11 : restrictedCard 26 11 = 1930 := by
    rw [restrictedCard_step (n := 26) (m := 15) (j := 10) (k := 11) rfl rfl, h26_10, h15_11]
  have h26_12 : restrictedCard 26 12 = 2063 := by
    rw [restrictedCard_step (n := 26) (m := 14) (j := 11) (k := 12) rfl rfl, h26_11, h14_12]
  have h26_13 : restrictedCard 26 13 = 2164 := by
    rw [restrictedCard_step (n := 26) (m := 13) (j := 12) (k := 13) rfl rfl, h26_12, h13_13]
  have h26_14 : restrictedCard 26 14 = 2241 := by
    rw [restrictedCard_step (n := 26) (m := 12) (j := 13) (k := 14) rfl rfl, h26_13,
      restrictedCard_eq_p (n := 12) (k := 14) (by norm_num), hp12]
  have h26_15 : restrictedCard 26 15 = 2297 := by
    rw [restrictedCard_step (n := 26) (m := 11) (j := 14) (k := 15) rfl rfl, h26_14,
      restrictedCard_eq_p (n := 11) (k := 15) (by norm_num), hp11]
  have h26_16 : restrictedCard 26 16 = 2339 := by
    rw [restrictedCard_step (n := 26) (m := 10) (j := 15) (k := 16) rfl rfl, h26_15,
      restrictedCard_eq_p (n := 10) (k := 16) (by norm_num), hp10]
  have h26_17 : restrictedCard 26 17 = 2369 := by
    rw [restrictedCard_step (n := 26) (m := 9) (j := 16) (k := 17) rfl rfl, h26_16,
      restrictedCard_eq_p (n := 9) (k := 17) (by norm_num), hp9]
  have h26_18 : restrictedCard 26 18 = 2391 := by
    rw [restrictedCard_step (n := 26) (m := 8) (j := 17) (k := 18) rfl rfl, h26_17,
      restrictedCard_eq_p (n := 8) (k := 18) (by norm_num), hp8]
  have h26_19 : restrictedCard 26 19 = 2406 := by
    rw [restrictedCard_step (n := 26) (m := 7) (j := 18) (k := 19) rfl rfl, h26_18,
      restrictedCard_eq_p (n := 7) (k := 19) (by norm_num), hp7]
  have h26_20 : restrictedCard 26 20 = 2417 := by
    rw [restrictedCard_step (n := 26) (m := 6) (j := 19) (k := 20) rfl rfl, h26_19,
      restrictedCard_eq_p (n := 6) (k := 20) (by norm_num), hp6]
  have h26_21 : restrictedCard 26 21 = 2424 := by
    rw [restrictedCard_step (n := 26) (m := 5) (j := 20) (k := 21) rfl rfl, h26_20,
      restrictedCard_eq_p (n := 5) (k := 21) (by norm_num), hp5]
  have h26_22 : restrictedCard 26 22 = 2429 := by
    rw [restrictedCard_step (n := 26) (m := 4) (j := 21) (k := 22) rfl rfl, h26_21,
      restrictedCard_eq_p (n := 4) (k := 22) (by norm_num), hp4]
  have h26_23 : restrictedCard 26 23 = 2432 := by
    rw [restrictedCard_step (n := 26) (m := 3) (j := 22) (k := 23) rfl rfl, h26_22,
      restrictedCard_eq_p (n := 3) (k := 23) (by norm_num), hp3]
  have h26_24 : restrictedCard 26 24 = 2434 := by
    rw [restrictedCard_step (n := 26) (m := 2) (j := 23) (k := 24) rfl rfl, h26_23,
      restrictedCard_eq_p (n := 2) (k := 24) (by norm_num), hp2]
  have h26_25 : restrictedCard 26 25 = 2435 := by
    rw [restrictedCard_step (n := 26) (m := 1) (j := 24) (k := 25) rfl rfl, h26_24,
      restrictedCard_eq_p (n := 1) (k := 25) (by norm_num), hp1]
  have h26_26 : restrictedCard 26 26 = 2436 := by
    rw [restrictedCard_step (n := 26) (m := 0) (j := 25) (k := 26) rfl rfl, h26_25,
      restrictedCard_eq_p (n := 0) (k := 26) (by norm_num), hp0]
  have hp26 : Erdos1106.p 26 = 2436 := (restrictedCard_eq_p (le_refl 26)).symm.trans h26_26
  have h27_1 : restrictedCard 27 1 = 1 := by
    rw [restrictedCard_step (n := 27) (m := 26) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 27) (by norm_num), h26_1]
  have h27_2 : restrictedCard 27 2 = 14 := by
    rw [restrictedCard_step (n := 27) (m := 25) (j := 1) (k := 2) rfl rfl, h27_1, h25_2]
  have h27_3 : restrictedCard 27 3 = 75 := by
    rw [restrictedCard_step (n := 27) (m := 24) (j := 2) (k := 3) rfl rfl, h27_2, h24_3]
  have h27_4 : restrictedCard 27 4 = 225 := by
    rw [restrictedCard_step (n := 27) (m := 23) (j := 3) (k := 4) rfl rfl, h27_3, h23_4]
  have h27_5 : restrictedCard 27 5 = 480 := by
    rw [restrictedCard_step (n := 27) (m := 22) (j := 4) (k := 5) rfl rfl, h27_4, h22_5]
  have h27_6 : restrictedCard 27 6 = 811 := by
    rw [restrictedCard_step (n := 27) (m := 21) (j := 5) (k := 6) rfl rfl, h27_5, h21_6]
  have h27_7 : restrictedCard 27 7 = 1175 := by
    rw [restrictedCard_step (n := 27) (m := 20) (j := 6) (k := 7) rfl rfl, h27_6, h20_7]
  have h27_8 : restrictedCard 27 8 = 1527 := by
    rw [restrictedCard_step (n := 27) (m := 19) (j := 7) (k := 8) rfl rfl, h27_7, h19_8]
  have h27_9 : restrictedCard 27 9 = 1845 := by
    rw [restrictedCard_step (n := 27) (m := 18) (j := 8) (k := 9) rfl rfl, h27_8, h18_9]
  have h27_10 : restrictedCard 27 10 = 2112 := by
    rw [restrictedCard_step (n := 27) (m := 17) (j := 9) (k := 10) rfl rfl, h27_9, h17_10]
  have h27_11 : restrictedCard 27 11 = 2331 := by
    rw [restrictedCard_step (n := 27) (m := 16) (j := 10) (k := 11) rfl rfl, h27_10, h16_11]
  have h27_12 : restrictedCard 27 12 = 2503 := by
    rw [restrictedCard_step (n := 27) (m := 15) (j := 11) (k := 12) rfl rfl, h27_11, h15_12]
  have h27_13 : restrictedCard 27 13 = 2637 := by
    rw [restrictedCard_step (n := 27) (m := 14) (j := 12) (k := 13) rfl rfl, h27_12, h14_13]
  have h27_14 : restrictedCard 27 14 = 2738 := by
    rw [restrictedCard_step (n := 27) (m := 13) (j := 13) (k := 14) rfl rfl, h27_13,
      restrictedCard_eq_p (n := 13) (k := 14) (by norm_num), hp13]
  have h27_15 : restrictedCard 27 15 = 2815 := by
    rw [restrictedCard_step (n := 27) (m := 12) (j := 14) (k := 15) rfl rfl, h27_14,
      restrictedCard_eq_p (n := 12) (k := 15) (by norm_num), hp12]
  have h27_16 : restrictedCard 27 16 = 2871 := by
    rw [restrictedCard_step (n := 27) (m := 11) (j := 15) (k := 16) rfl rfl, h27_15,
      restrictedCard_eq_p (n := 11) (k := 16) (by norm_num), hp11]
  have h27_17 : restrictedCard 27 17 = 2913 := by
    rw [restrictedCard_step (n := 27) (m := 10) (j := 16) (k := 17) rfl rfl, h27_16,
      restrictedCard_eq_p (n := 10) (k := 17) (by norm_num), hp10]
  have h27_18 : restrictedCard 27 18 = 2943 := by
    rw [restrictedCard_step (n := 27) (m := 9) (j := 17) (k := 18) rfl rfl, h27_17,
      restrictedCard_eq_p (n := 9) (k := 18) (by norm_num), hp9]
  have h27_19 : restrictedCard 27 19 = 2965 := by
    rw [restrictedCard_step (n := 27) (m := 8) (j := 18) (k := 19) rfl rfl, h27_18,
      restrictedCard_eq_p (n := 8) (k := 19) (by norm_num), hp8]
  have h27_20 : restrictedCard 27 20 = 2980 := by
    rw [restrictedCard_step (n := 27) (m := 7) (j := 19) (k := 20) rfl rfl, h27_19,
      restrictedCard_eq_p (n := 7) (k := 20) (by norm_num), hp7]
  have h27_21 : restrictedCard 27 21 = 2991 := by
    rw [restrictedCard_step (n := 27) (m := 6) (j := 20) (k := 21) rfl rfl, h27_20,
      restrictedCard_eq_p (n := 6) (k := 21) (by norm_num), hp6]
  have h27_22 : restrictedCard 27 22 = 2998 := by
    rw [restrictedCard_step (n := 27) (m := 5) (j := 21) (k := 22) rfl rfl, h27_21,
      restrictedCard_eq_p (n := 5) (k := 22) (by norm_num), hp5]
  have h27_23 : restrictedCard 27 23 = 3003 := by
    rw [restrictedCard_step (n := 27) (m := 4) (j := 22) (k := 23) rfl rfl, h27_22,
      restrictedCard_eq_p (n := 4) (k := 23) (by norm_num), hp4]
  have h27_24 : restrictedCard 27 24 = 3006 := by
    rw [restrictedCard_step (n := 27) (m := 3) (j := 23) (k := 24) rfl rfl, h27_23,
      restrictedCard_eq_p (n := 3) (k := 24) (by norm_num), hp3]
  have h27_25 : restrictedCard 27 25 = 3008 := by
    rw [restrictedCard_step (n := 27) (m := 2) (j := 24) (k := 25) rfl rfl, h27_24,
      restrictedCard_eq_p (n := 2) (k := 25) (by norm_num), hp2]
  have h27_26 : restrictedCard 27 26 = 3009 := by
    rw [restrictedCard_step (n := 27) (m := 1) (j := 25) (k := 26) rfl rfl, h27_25,
      restrictedCard_eq_p (n := 1) (k := 26) (by norm_num), hp1]
  have h27_27 : restrictedCard 27 27 = 3010 := by
    rw [restrictedCard_step (n := 27) (m := 0) (j := 26) (k := 27) rfl rfl, h27_26,
      restrictedCard_eq_p (n := 0) (k := 27) (by norm_num), hp0]
  have hp27 : Erdos1106.p 27 = 3010 := (restrictedCard_eq_p (le_refl 27)).symm.trans h27_27
  have h28_1 : restrictedCard 28 1 = 1 := by
    rw [restrictedCard_step (n := 28) (m := 27) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 28) (by norm_num), h27_1]
  have h28_2 : restrictedCard 28 2 = 15 := by
    rw [restrictedCard_step (n := 28) (m := 26) (j := 1) (k := 2) rfl rfl, h28_1, h26_2]
  have h28_3 : restrictedCard 28 3 = 80 := by
    rw [restrictedCard_step (n := 28) (m := 25) (j := 2) (k := 3) rfl rfl, h28_2, h25_3]
  have h28_4 : restrictedCard 28 4 = 249 := by
    rw [restrictedCard_step (n := 28) (m := 24) (j := 3) (k := 4) rfl rfl, h28_3, h24_4]
  have h28_5 : restrictedCard 28 5 = 540 := by
    rw [restrictedCard_step (n := 28) (m := 23) (j := 4) (k := 5) rfl rfl, h28_4, h23_5]
  have h28_6 : restrictedCard 28 6 = 931 := by
    rw [restrictedCard_step (n := 28) (m := 22) (j := 5) (k := 6) rfl rfl, h28_5, h22_6]
  have h28_7 : restrictedCard 28 7 = 1367 := by
    rw [restrictedCard_step (n := 28) (m := 21) (j := 6) (k := 7) rfl rfl, h28_6, h21_7]
  have h28_8 : restrictedCard 28 8 = 1801 := by
    rw [restrictedCard_step (n := 28) (m := 20) (j := 7) (k := 8) rfl rfl, h28_7, h20_8]
  have h28_9 : restrictedCard 28 9 = 2194 := by
    rw [restrictedCard_step (n := 28) (m := 19) (j := 8) (k := 9) rfl rfl, h28_8, h19_9]
  have h28_10 : restrictedCard 28 10 = 2534 := by
    rw [restrictedCard_step (n := 28) (m := 18) (j := 9) (k := 10) rfl rfl, h28_9, h18_10]
  have h28_11 : restrictedCard 28 11 = 2812 := by
    rw [restrictedCard_step (n := 28) (m := 17) (j := 10) (k := 11) rfl rfl, h28_10, h17_11]
  have h28_12 : restrictedCard 28 12 = 3036 := by
    rw [restrictedCard_step (n := 28) (m := 16) (j := 11) (k := 12) rfl rfl, h28_11, h16_12]
  have h28_13 : restrictedCard 28 13 = 3210 := by
    rw [restrictedCard_step (n := 28) (m := 15) (j := 12) (k := 13) rfl rfl, h28_12, h15_13]
  have h28_14 : restrictedCard 28 14 = 3345 := by
    rw [restrictedCard_step (n := 28) (m := 14) (j := 13) (k := 14) rfl rfl, h28_13, h14_14]
  have h28_15 : restrictedCard 28 15 = 3446 := by
    rw [restrictedCard_step (n := 28) (m := 13) (j := 14) (k := 15) rfl rfl, h28_14,
      restrictedCard_eq_p (n := 13) (k := 15) (by norm_num), hp13]
  have h28_16 : restrictedCard 28 16 = 3523 := by
    rw [restrictedCard_step (n := 28) (m := 12) (j := 15) (k := 16) rfl rfl, h28_15,
      restrictedCard_eq_p (n := 12) (k := 16) (by norm_num), hp12]
  have h28_17 : restrictedCard 28 17 = 3579 := by
    rw [restrictedCard_step (n := 28) (m := 11) (j := 16) (k := 17) rfl rfl, h28_16,
      restrictedCard_eq_p (n := 11) (k := 17) (by norm_num), hp11]
  have h28_18 : restrictedCard 28 18 = 3621 := by
    rw [restrictedCard_step (n := 28) (m := 10) (j := 17) (k := 18) rfl rfl, h28_17,
      restrictedCard_eq_p (n := 10) (k := 18) (by norm_num), hp10]
  have h28_19 : restrictedCard 28 19 = 3651 := by
    rw [restrictedCard_step (n := 28) (m := 9) (j := 18) (k := 19) rfl rfl, h28_18,
      restrictedCard_eq_p (n := 9) (k := 19) (by norm_num), hp9]
  have h28_20 : restrictedCard 28 20 = 3673 := by
    rw [restrictedCard_step (n := 28) (m := 8) (j := 19) (k := 20) rfl rfl, h28_19,
      restrictedCard_eq_p (n := 8) (k := 20) (by norm_num), hp8]
  have h28_21 : restrictedCard 28 21 = 3688 := by
    rw [restrictedCard_step (n := 28) (m := 7) (j := 20) (k := 21) rfl rfl, h28_20,
      restrictedCard_eq_p (n := 7) (k := 21) (by norm_num), hp7]
  have h28_22 : restrictedCard 28 22 = 3699 := by
    rw [restrictedCard_step (n := 28) (m := 6) (j := 21) (k := 22) rfl rfl, h28_21,
      restrictedCard_eq_p (n := 6) (k := 22) (by norm_num), hp6]
  have h28_23 : restrictedCard 28 23 = 3706 := by
    rw [restrictedCard_step (n := 28) (m := 5) (j := 22) (k := 23) rfl rfl, h28_22,
      restrictedCard_eq_p (n := 5) (k := 23) (by norm_num), hp5]
  have h28_24 : restrictedCard 28 24 = 3711 := by
    rw [restrictedCard_step (n := 28) (m := 4) (j := 23) (k := 24) rfl rfl, h28_23,
      restrictedCard_eq_p (n := 4) (k := 24) (by norm_num), hp4]
  have h28_25 : restrictedCard 28 25 = 3714 := by
    rw [restrictedCard_step (n := 28) (m := 3) (j := 24) (k := 25) rfl rfl, h28_24,
      restrictedCard_eq_p (n := 3) (k := 25) (by norm_num), hp3]
  have h28_26 : restrictedCard 28 26 = 3716 := by
    rw [restrictedCard_step (n := 28) (m := 2) (j := 25) (k := 26) rfl rfl, h28_25,
      restrictedCard_eq_p (n := 2) (k := 26) (by norm_num), hp2]
  have h28_27 : restrictedCard 28 27 = 3717 := by
    rw [restrictedCard_step (n := 28) (m := 1) (j := 26) (k := 27) rfl rfl, h28_26,
      restrictedCard_eq_p (n := 1) (k := 27) (by norm_num), hp1]
  have h28_28 : restrictedCard 28 28 = 3718 := by
    rw [restrictedCard_step (n := 28) (m := 0) (j := 27) (k := 28) rfl rfl, h28_27,
      restrictedCard_eq_p (n := 0) (k := 28) (by norm_num), hp0]
  have hp28 : Erdos1106.p 28 = 3718 := (restrictedCard_eq_p (le_refl 28)).symm.trans h28_28
  have h29_1 : restrictedCard 29 1 = 1 := by
    rw [restrictedCard_step (n := 29) (m := 28) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 29) (by norm_num), h28_1]
  have h29_2 : restrictedCard 29 2 = 15 := by
    rw [restrictedCard_step (n := 29) (m := 27) (j := 1) (k := 2) rfl rfl, h29_1, h27_2]
  have h29_3 : restrictedCard 29 3 = 85 := by
    rw [restrictedCard_step (n := 29) (m := 26) (j := 2) (k := 3) rfl rfl, h29_2, h26_3]
  have h29_4 : restrictedCard 29 4 = 270 := by
    rw [restrictedCard_step (n := 29) (m := 25) (j := 3) (k := 4) rfl rfl, h29_3, h25_4]
  have h29_5 : restrictedCard 29 5 = 603 := by
    rw [restrictedCard_step (n := 29) (m := 24) (j := 4) (k := 5) rfl rfl, h29_4, h24_5]
  have h29_6 : restrictedCard 29 6 = 1057 := by
    rw [restrictedCard_step (n := 29) (m := 23) (j := 5) (k := 6) rfl rfl, h29_5, h23_6]
  have h29_7 : restrictedCard 29 7 = 1579 := by
    rw [restrictedCard_step (n := 29) (m := 22) (j := 6) (k := 7) rfl rfl, h29_6, h22_7]
  have h29_8 : restrictedCard 29 8 = 2104 := by
    rw [restrictedCard_step (n := 29) (m := 21) (j := 7) (k := 8) rfl rfl, h29_7, h21_8]
  have h29_9 : restrictedCard 29 9 = 2592 := by
    rw [restrictedCard_step (n := 29) (m := 20) (j := 8) (k := 9) rfl rfl, h29_8, h20_9]
  have h29_10 : restrictedCard 29 10 = 3015 := by
    rw [restrictedCard_step (n := 29) (m := 19) (j := 9) (k := 10) rfl rfl, h29_9, h19_10]
  have h29_11 : restrictedCard 29 11 = 3370 := by
    rw [restrictedCard_step (n := 29) (m := 18) (j := 10) (k := 11) rfl rfl, h29_10, h18_11]
  have h29_12 : restrictedCard 29 12 = 3655 := by
    rw [restrictedCard_step (n := 29) (m := 17) (j := 11) (k := 12) rfl rfl, h29_11, h17_12]
  have h29_13 : restrictedCard 29 13 = 3882 := by
    rw [restrictedCard_step (n := 29) (m := 16) (j := 12) (k := 13) rfl rfl, h29_12, h16_13]
  have h29_14 : restrictedCard 29 14 = 4057 := by
    rw [restrictedCard_step (n := 29) (m := 15) (j := 13) (k := 14) rfl rfl, h29_13, h15_14]
  have h29_15 : restrictedCard 29 15 = 4192 := by
    rw [restrictedCard_step (n := 29) (m := 14) (j := 14) (k := 15) rfl rfl, h29_14,
      restrictedCard_eq_p (n := 14) (k := 15) (by norm_num), hp14]
  have h29_16 : restrictedCard 29 16 = 4293 := by
    rw [restrictedCard_step (n := 29) (m := 13) (j := 15) (k := 16) rfl rfl, h29_15,
      restrictedCard_eq_p (n := 13) (k := 16) (by norm_num), hp13]
  have h29_17 : restrictedCard 29 17 = 4370 := by
    rw [restrictedCard_step (n := 29) (m := 12) (j := 16) (k := 17) rfl rfl, h29_16,
      restrictedCard_eq_p (n := 12) (k := 17) (by norm_num), hp12]
  have h29_18 : restrictedCard 29 18 = 4426 := by
    rw [restrictedCard_step (n := 29) (m := 11) (j := 17) (k := 18) rfl rfl, h29_17,
      restrictedCard_eq_p (n := 11) (k := 18) (by norm_num), hp11]
  have h29_19 : restrictedCard 29 19 = 4468 := by
    rw [restrictedCard_step (n := 29) (m := 10) (j := 18) (k := 19) rfl rfl, h29_18,
      restrictedCard_eq_p (n := 10) (k := 19) (by norm_num), hp10]
  have h29_20 : restrictedCard 29 20 = 4498 := by
    rw [restrictedCard_step (n := 29) (m := 9) (j := 19) (k := 20) rfl rfl, h29_19,
      restrictedCard_eq_p (n := 9) (k := 20) (by norm_num), hp9]
  have h29_21 : restrictedCard 29 21 = 4520 := by
    rw [restrictedCard_step (n := 29) (m := 8) (j := 20) (k := 21) rfl rfl, h29_20,
      restrictedCard_eq_p (n := 8) (k := 21) (by norm_num), hp8]
  have h29_22 : restrictedCard 29 22 = 4535 := by
    rw [restrictedCard_step (n := 29) (m := 7) (j := 21) (k := 22) rfl rfl, h29_21,
      restrictedCard_eq_p (n := 7) (k := 22) (by norm_num), hp7]
  have h29_23 : restrictedCard 29 23 = 4546 := by
    rw [restrictedCard_step (n := 29) (m := 6) (j := 22) (k := 23) rfl rfl, h29_22,
      restrictedCard_eq_p (n := 6) (k := 23) (by norm_num), hp6]
  have h29_24 : restrictedCard 29 24 = 4553 := by
    rw [restrictedCard_step (n := 29) (m := 5) (j := 23) (k := 24) rfl rfl, h29_23,
      restrictedCard_eq_p (n := 5) (k := 24) (by norm_num), hp5]
  have h29_25 : restrictedCard 29 25 = 4558 := by
    rw [restrictedCard_step (n := 29) (m := 4) (j := 24) (k := 25) rfl rfl, h29_24,
      restrictedCard_eq_p (n := 4) (k := 25) (by norm_num), hp4]
  have h29_26 : restrictedCard 29 26 = 4561 := by
    rw [restrictedCard_step (n := 29) (m := 3) (j := 25) (k := 26) rfl rfl, h29_25,
      restrictedCard_eq_p (n := 3) (k := 26) (by norm_num), hp3]
  have h29_27 : restrictedCard 29 27 = 4563 := by
    rw [restrictedCard_step (n := 29) (m := 2) (j := 26) (k := 27) rfl rfl, h29_26,
      restrictedCard_eq_p (n := 2) (k := 27) (by norm_num), hp2]
  have h29_28 : restrictedCard 29 28 = 4564 := by
    rw [restrictedCard_step (n := 29) (m := 1) (j := 27) (k := 28) rfl rfl, h29_27,
      restrictedCard_eq_p (n := 1) (k := 28) (by norm_num), hp1]
  have h29_29 : restrictedCard 29 29 = 4565 := by
    rw [restrictedCard_step (n := 29) (m := 0) (j := 28) (k := 29) rfl rfl, h29_28,
      restrictedCard_eq_p (n := 0) (k := 29) (by norm_num), hp0]
  have hp29 : Erdos1106.p 29 = 4565 := (restrictedCard_eq_p (le_refl 29)).symm.trans h29_29
  have h30_1 : restrictedCard 30 1 = 1 := by
    rw [restrictedCard_step (n := 30) (m := 29) (j := 0) (k := 1) rfl rfl,
      restrictedCard_zero_right (n := 30) (by norm_num), h29_1]
  have h30_2 : restrictedCard 30 2 = 16 := by
    rw [restrictedCard_step (n := 30) (m := 28) (j := 1) (k := 2) rfl rfl, h30_1, h28_2]
  have h30_3 : restrictedCard 30 3 = 91 := by
    rw [restrictedCard_step (n := 30) (m := 27) (j := 2) (k := 3) rfl rfl, h30_2, h27_3]
  have h30_4 : restrictedCard 30 4 = 297 := by
    rw [restrictedCard_step (n := 30) (m := 26) (j := 3) (k := 4) rfl rfl, h30_3, h26_4]
  have h30_5 : restrictedCard 30 5 = 674 := by
    rw [restrictedCard_step (n := 30) (m := 25) (j := 4) (k := 5) rfl rfl, h30_4, h25_5]
  have h30_6 : restrictedCard 30 6 = 1206 := by
    rw [restrictedCard_step (n := 30) (m := 24) (j := 5) (k := 6) rfl rfl, h30_5, h24_6]
  have h30_7 : restrictedCard 30 7 = 1824 := by
    rw [restrictedCard_step (n := 30) (m := 23) (j := 6) (k := 7) rfl rfl, h30_6, h23_7]
  have h30_8 : restrictedCard 30 8 = 2462 := by
    rw [restrictedCard_step (n := 30) (m := 22) (j := 7) (k := 8) rfl rfl, h30_7, h22_8]
  have h30_9 : restrictedCard 30 9 = 3060 := by
    rw [restrictedCard_step (n := 30) (m := 21) (j := 8) (k := 9) rfl rfl, h30_8, h21_9]
  have h30_10 : restrictedCard 30 10 = 3590 := by
    rw [restrictedCard_step (n := 30) (m := 20) (j := 9) (k := 10) rfl rfl, h30_9, h20_10]
  have h30_11 : restrictedCard 30 11 = 4035 := by
    rw [restrictedCard_step (n := 30) (m := 19) (j := 10) (k := 11) rfl rfl, h30_10, h19_11]
  have h30_12 : restrictedCard 30 12 = 4401 := by
    rw [restrictedCard_step (n := 30) (m := 18) (j := 11) (k := 12) rfl rfl, h30_11, h18_12]
  have h30_13 : restrictedCard 30 13 = 4691 := by
    rw [restrictedCard_step (n := 30) (m := 17) (j := 12) (k := 13) rfl rfl, h30_12, h17_13]
  have h30_14 : restrictedCard 30 14 = 4920 := by
    rw [restrictedCard_step (n := 30) (m := 16) (j := 13) (k := 14) rfl rfl, h30_13, h16_14]
  have h30_15 : restrictedCard 30 15 = 5096 := by
    rw [restrictedCard_step (n := 30) (m := 15) (j := 14) (k := 15) rfl rfl, h30_14, h15_15]
  have h30_16 : restrictedCard 30 16 = 5231 := by
    rw [restrictedCard_step (n := 30) (m := 14) (j := 15) (k := 16) rfl rfl, h30_15,
      restrictedCard_eq_p (n := 14) (k := 16) (by norm_num), hp14]
  have h30_17 : restrictedCard 30 17 = 5332 := by
    rw [restrictedCard_step (n := 30) (m := 13) (j := 16) (k := 17) rfl rfl, h30_16,
      restrictedCard_eq_p (n := 13) (k := 17) (by norm_num), hp13]
  have h30_18 : restrictedCard 30 18 = 5409 := by
    rw [restrictedCard_step (n := 30) (m := 12) (j := 17) (k := 18) rfl rfl, h30_17,
      restrictedCard_eq_p (n := 12) (k := 18) (by norm_num), hp12]
  have h30_19 : restrictedCard 30 19 = 5465 := by
    rw [restrictedCard_step (n := 30) (m := 11) (j := 18) (k := 19) rfl rfl, h30_18,
      restrictedCard_eq_p (n := 11) (k := 19) (by norm_num), hp11]
  have h30_20 : restrictedCard 30 20 = 5507 := by
    rw [restrictedCard_step (n := 30) (m := 10) (j := 19) (k := 20) rfl rfl, h30_19,
      restrictedCard_eq_p (n := 10) (k := 20) (by norm_num), hp10]
  have h30_21 : restrictedCard 30 21 = 5537 := by
    rw [restrictedCard_step (n := 30) (m := 9) (j := 20) (k := 21) rfl rfl, h30_20,
      restrictedCard_eq_p (n := 9) (k := 21) (by norm_num), hp9]
  have h30_22 : restrictedCard 30 22 = 5559 := by
    rw [restrictedCard_step (n := 30) (m := 8) (j := 21) (k := 22) rfl rfl, h30_21,
      restrictedCard_eq_p (n := 8) (k := 22) (by norm_num), hp8]
  have h30_23 : restrictedCard 30 23 = 5574 := by
    rw [restrictedCard_step (n := 30) (m := 7) (j := 22) (k := 23) rfl rfl, h30_22,
      restrictedCard_eq_p (n := 7) (k := 23) (by norm_num), hp7]
  have h30_24 : restrictedCard 30 24 = 5585 := by
    rw [restrictedCard_step (n := 30) (m := 6) (j := 23) (k := 24) rfl rfl, h30_23,
      restrictedCard_eq_p (n := 6) (k := 24) (by norm_num), hp6]
  have h30_25 : restrictedCard 30 25 = 5592 := by
    rw [restrictedCard_step (n := 30) (m := 5) (j := 24) (k := 25) rfl rfl, h30_24,
      restrictedCard_eq_p (n := 5) (k := 25) (by norm_num), hp5]
  have h30_26 : restrictedCard 30 26 = 5597 := by
    rw [restrictedCard_step (n := 30) (m := 4) (j := 25) (k := 26) rfl rfl, h30_25,
      restrictedCard_eq_p (n := 4) (k := 26) (by norm_num), hp4]
  have h30_27 : restrictedCard 30 27 = 5600 := by
    rw [restrictedCard_step (n := 30) (m := 3) (j := 26) (k := 27) rfl rfl, h30_26,
      restrictedCard_eq_p (n := 3) (k := 27) (by norm_num), hp3]
  have h30_28 : restrictedCard 30 28 = 5602 := by
    rw [restrictedCard_step (n := 30) (m := 2) (j := 27) (k := 28) rfl rfl, h30_27,
      restrictedCard_eq_p (n := 2) (k := 28) (by norm_num), hp2]
  have h30_29 : restrictedCard 30 29 = 5603 := by
    rw [restrictedCard_step (n := 30) (m := 1) (j := 28) (k := 29) rfl rfl, h30_28,
      restrictedCard_eq_p (n := 1) (k := 29) (by norm_num), hp1]
  have h30_30 : restrictedCard 30 30 = 5604 := by
    rw [restrictedCard_step (n := 30) (m := 0) (j := 29) (k := 30) rfl rfl, h30_29,
      restrictedCard_eq_p (n := 0) (k := 30) (by norm_num), hp0]
  have hp30 : Erdos1106.p 30 = 5604 := (restrictedCard_eq_p (le_refl 30)).symm.trans h30_30
  exact ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16,
    hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30⟩

/- ### The prime factors of `p 1 ⋯ p n` -/

/-- The set of primes dividing `∏ i ∈ Icc 1 n, Erdos1106.p i` only grows with `n`: the target's
`F` is monotone. -/
theorem primeFactors_prod_subset {m n : ℕ} (h : m ≤ n) :
    (∏ i ∈ Icc 1 m, Erdos1106.p i).primeFactors ⊆
      (∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors := by
  refine Nat.primeFactors_mono (Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.Icc_subset_Icc_right h)) ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => (Fintype.card_pos (α := Nat.Partition i)).ne'

/-- **The prime factorisation of the product of the first thirty partition numbers.** The product
`∏ i ∈ Icc 1 30, Erdos1106.p i` is
`172765791733800831981440427087707432623858429368762777600000000000`, and it has exactly fifteen
prime factors, so the target's `F 30` equals `15`. -/
theorem primeFactors_prod_thirty :
    (∏ i ∈ Icc 1 30, Erdos1106.p i).primeFactors =
      {2, 3, 5, 7, 11, 13, 19, 29, 43, 83, 89, 101, 167, 251, 467} := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16,
    hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30⟩ := p_values
  have key : ∀ q e a : ℕ, q.Prime → e ≠ 0 → a ≠ 0 →
      (q ^ e * a).primeFactors = insert q a.primeFactors := by
    intro q e a hq he ha
    rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) ha, Nat.primeFactors_pow _ he,
      hq.primeFactors]
    exact (Finset.insert_eq q _).symm
  have step : ∀ b : ℕ, ∏ i ∈ Icc 1 (b + 1), Erdos1106.p i
      = (∏ i ∈ Icc 1 b, Erdos1106.p i) * Erdos1106.p (b + 1) :=
    fun b => Finset.prod_Icc_succ_top (by omega) _
  have e1 : ∏ i ∈ Icc 1 1, Erdos1106.p i = 1 := by simp [hp1]
  have e2 : ∏ i ∈ Icc 1 2, Erdos1106.p i = 2 := by
    have h := step 1
    norm_num [e1, hp2] at h
    exact h
  have e3 : ∏ i ∈ Icc 1 3, Erdos1106.p i = 6 := by
    have h := step 2
    norm_num [e2, hp3] at h
    exact h
  have e4 : ∏ i ∈ Icc 1 4, Erdos1106.p i = 30 := by
    have h := step 3
    norm_num [e3, hp4] at h
    exact h
  have e5 : ∏ i ∈ Icc 1 5, Erdos1106.p i = 210 := by
    have h := step 4
    norm_num [e4, hp5] at h
    exact h
  have e6 : ∏ i ∈ Icc 1 6, Erdos1106.p i = 2310 := by
    have h := step 5
    norm_num [e5, hp6] at h
    exact h
  have e7 : ∏ i ∈ Icc 1 7, Erdos1106.p i = 34650 := by
    have h := step 6
    norm_num [e6, hp7] at h
    exact h
  have e8 : ∏ i ∈ Icc 1 8, Erdos1106.p i = 762300 := by
    have h := step 7
    norm_num [e7, hp8] at h
    exact h
  have e9 : ∏ i ∈ Icc 1 9, Erdos1106.p i = 22869000 := by
    have h := step 8
    norm_num [e8, hp9] at h
    exact h
  have e10 : ∏ i ∈ Icc 1 10, Erdos1106.p i = 960498000 := by
    have h := step 9
    norm_num [e9, hp10] at h
    exact h
  have e11 : ∏ i ∈ Icc 1 11, Erdos1106.p i = 53787888000 := by
    have h := step 10
    norm_num [e10, hp11] at h
    exact h
  have e12 : ∏ i ∈ Icc 1 12, Erdos1106.p i = 4141667376000 := by
    have h := step 11
    norm_num [e11, hp12] at h
    exact h
  have e13 : ∏ i ∈ Icc 1 13, Erdos1106.p i = 418308404976000 := by
    have h := step 12
    norm_num [e12, hp13] at h
    exact h
  have e14 : ∏ i ∈ Icc 1 14, Erdos1106.p i = 56471634671760000 := by
    have h := step 13
    norm_num [e13, hp14] at h
    exact h
  have e15 : ∏ i ∈ Icc 1 15, Erdos1106.p i = 9939007702229760000 := by
    have h := step 14
    norm_num [e14, hp15] at h
    exact h
  have e16 : ∏ i ∈ Icc 1 16, Erdos1106.p i = 2295910779215074560000 := by
    have h := step 15
    norm_num [e15, hp16] at h
    exact h
  have e17 : ∏ i ∈ Icc 1 17, Erdos1106.p i = 681885501426877144320000 := by
    have h := step 16
    norm_num [e16, hp17] at h
    exact h
  have e18 : ∏ i ∈ Icc 1 18, Erdos1106.p i = 262525918049347700563200000 := by
    have h := step 17
    norm_num [e17, hp18] at h
    exact h
  have e19 : ∏ i ∈ Icc 1 19, Erdos1106.p i = 128637699844180373275968000000 := by
    have h := step 18
    norm_num [e18, hp19] at h
    exact h
  have e20 : ∏ i ∈ Icc 1 20, Erdos1106.p i = 80655837802301094044031936000000 := by
    have h := step 19
    norm_num [e19, hp20] at h
    exact h
  have e21 : ∏ i ∈ Icc 1 21, Erdos1106.p i = 63879423539422466482873293312000000 := by
    have h := step 20
    norm_num [e20, hp21] at h
    exact h
  have e22 : ∏ i ∈ Icc 1 22, Erdos1106.p i = 64007182386501311415839039898624000000 := by
    have h := step 21
    norm_num [e21, hp22] at h
    exact h
  have e23 : ∏ i ∈ Icc 1 23, Erdos1106.p i = 80329013895059145826877995072773120000000 := by
    have h := step 22
    norm_num [e22, hp23] at h
    exact h
  have e24 : ∏ i ∈ Icc 1 24, Erdos1106.p i = 126518196884718154677332842239617664000000000 := by
    have h := step 23
    norm_num [e23, hp24] at h
    exact h
  have e25 : ∏ i ∈ Icc 1 25, Erdos1106.p i = 247722629500278146858217705105171386112000000000 := by
    have h := step 24
    norm_num [e24, hp25] at h
    exact h
  have e26 : ∏ i ∈ Icc 1 26, Erdos1106.p i =
      603452325462677565746618329636197496568832000000000 := by
    have h := step 25
    norm_num [e25, hp26] at h
    exact h
  have e27 : ∏ i ∈ Icc 1 27, Erdos1106.p i =
      1816391499642659472897321172204954464672184320000000000 := by
    have h := step 26
    norm_num [e26, hp27] at h
    exact h
  have e28 : ∏ i ∈ Icc 1 28, Erdos1106.p i =
      6753343595671407920232240118258020699651181301760000000000 := by
    have h := step 27
    norm_num [e27, hp28] at h
    exact h
  have e29 : ∏ i ∈ Icc 1 29, Erdos1106.p i =
      30829013514239977155860176139847864493907642642534400000000000 := by
    have h := step 28
    norm_num [e28, hp29] at h
    exact h
  have e30 : ∏ i ∈ Icc 1 30, Erdos1106.p i =
      172765791733800831981440427087707432623858429368762777600000000000 := by
    have h := step 29
    norm_num [e29, hp30] at h
    exact h
  rw [e30,
    show (172765791733800831981440427087707432623858429368762777600000000000 : ℕ) =
      2 ^ 23 * (3 ^ 19 * (5 ^ 11 * (7 ^ 11 * (11 ^ 12 * (13 ^ 2 * (19 ^ 1 * (29 ^ 1 * (43 ^ 1 * (
        83 ^ 1 * (89 ^ 1 * (101 ^ 1 * (167 ^ 1 * (251 ^ 1 * (467)))))))))))))) by norm_num,
    key 2 23 _ (by norm_num) (by norm_num) (by positivity),
    key 3 19 _ (by norm_num) (by norm_num) (by positivity),
    key 5 11 _ (by norm_num) (by norm_num) (by positivity),
    key 7 11 _ (by norm_num) (by norm_num) (by positivity),
    key 11 12 _ (by norm_num) (by norm_num) (by positivity),
    key 13 2 _ (by norm_num) (by norm_num) (by positivity),
    key 19 1 _ (by norm_num) (by norm_num) (by positivity),
    key 29 1 _ (by norm_num) (by norm_num) (by positivity),
    key 43 1 _ (by norm_num) (by norm_num) (by positivity),
    key 83 1 _ (by norm_num) (by norm_num) (by positivity),
    key 89 1 _ (by norm_num) (by norm_num) (by positivity),
    key 101 1 _ (by norm_num) (by norm_num) (by positivity),
    key 167 1 _ (by norm_num) (by norm_num) (by positivity),
    key 251 1 _ (by norm_num) (by norm_num) (by positivity),
    Nat.Prime.primeFactors (p := 467) (by norm_num)]

/-- **The target's inequality fails for every `n ≤ 30`.** For `1 ≤ n ≤ 30` the number of
distinct primes dividing `p 1 ⋯ p n` is at most `n`; the four exact computations at
`n = 1, 3, 5, 14` and `primeFactors_prod_thirty`, together with the monotonicity
`primeFactors_prod_subset`, cover the whole range. -/
theorem card_primeFactors_prod_le_self {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 30) :
    #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors ≤ n := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _⟩ := p_values
  have key : ∀ q e a : ℕ, q.Prime → e ≠ 0 → a ≠ 0 →
      (q ^ e * a).primeFactors = insert q a.primeFactors := by
    intro q e a hq he ha
    rw [Nat.primeFactors_mul (pow_ne_zero _ hq.ne_zero) ha, Nat.primeFactors_pow _ he,
      hq.primeFactors]
    exact (Finset.insert_eq q _).symm
  have step : ∀ b : ℕ, ∏ i ∈ Icc 1 (b + 1), Erdos1106.p i
      = (∏ i ∈ Icc 1 b, Erdos1106.p i) * Erdos1106.p (b + 1) :=
    fun b => Finset.prod_Icc_succ_top (by omega) _
  have e1 : ∏ i ∈ Icc 1 1, Erdos1106.p i = 1 := by simp [hp1]
  have e2 : ∏ i ∈ Icc 1 2, Erdos1106.p i = 2 := by
    have h := step 1
    norm_num [e1, hp2] at h
    exact h
  have e3 : ∏ i ∈ Icc 1 3, Erdos1106.p i = 6 := by
    have h := step 2
    norm_num [e2, hp3] at h
    exact h
  have e4 : ∏ i ∈ Icc 1 4, Erdos1106.p i = 30 := by
    have h := step 3
    norm_num [e3, hp4] at h
    exact h
  have e5 : ∏ i ∈ Icc 1 5, Erdos1106.p i = 210 := by
    have h := step 4
    norm_num [e4, hp5] at h
    exact h
  have e6 : ∏ i ∈ Icc 1 6, Erdos1106.p i = 2310 := by
    have h := step 5
    norm_num [e5, hp6] at h
    exact h
  have e7 : ∏ i ∈ Icc 1 7, Erdos1106.p i = 34650 := by
    have h := step 6
    norm_num [e6, hp7] at h
    exact h
  have e8 : ∏ i ∈ Icc 1 8, Erdos1106.p i = 762300 := by
    have h := step 7
    norm_num [e7, hp8] at h
    exact h
  have e9 : ∏ i ∈ Icc 1 9, Erdos1106.p i = 22869000 := by
    have h := step 8
    norm_num [e8, hp9] at h
    exact h
  have e10 : ∏ i ∈ Icc 1 10, Erdos1106.p i = 960498000 := by
    have h := step 9
    norm_num [e9, hp10] at h
    exact h
  have e11 : ∏ i ∈ Icc 1 11, Erdos1106.p i = 53787888000 := by
    have h := step 10
    norm_num [e10, hp11] at h
    exact h
  have e12 : ∏ i ∈ Icc 1 12, Erdos1106.p i = 4141667376000 := by
    have h := step 11
    norm_num [e11, hp12] at h
    exact h
  have e13 : ∏ i ∈ Icc 1 13, Erdos1106.p i = 418308404976000 := by
    have h := step 12
    norm_num [e12, hp13] at h
    exact h
  have e14 : ∏ i ∈ Icc 1 14, Erdos1106.p i = 56471634671760000 := by
    have h := step 13
    norm_num [e13, hp14] at h
    exact h
  have mono : ∀ a b : ℕ, a ≤ b →
      #(∏ i ∈ Icc 1 a, Erdos1106.p i).primeFactors ≤
        #(∏ i ∈ Icc 1 b, Erdos1106.p i).primeFactors :=
    fun a b hab => Finset.card_le_card (primeFactors_prod_subset hab)
  have c1 : #(∏ i ∈ Icc 1 1, Erdos1106.p i).primeFactors = 0 := by rw [e1]; simp
  have s3 : (∏ i ∈ Icc 1 3, Erdos1106.p i).primeFactors = {2, 3} := by
    rw [e3, show (6 : ℕ) = 2 ^ 1 * (3) by norm_num,
      key 2 1 _ (by norm_num) (by norm_num) (by positivity),
      Nat.Prime.primeFactors (p := 3) (by norm_num)]
  have c3 : #(∏ i ∈ Icc 1 3, Erdos1106.p i).primeFactors = 2 := by
    rw [s3]; decide
  have s5 : (∏ i ∈ Icc 1 5, Erdos1106.p i).primeFactors = {2, 3, 5, 7} := by
    rw [e5, show (210 : ℕ) = 2 ^ 1 * (3 ^ 1 * (5 ^ 1 * (7))) by norm_num,
      key 2 1 _ (by norm_num) (by norm_num) (by positivity),
      key 3 1 _ (by norm_num) (by norm_num) (by positivity),
      key 5 1 _ (by norm_num) (by norm_num) (by positivity),
      Nat.Prime.primeFactors (p := 7) (by norm_num)]
  have c5 : #(∏ i ∈ Icc 1 5, Erdos1106.p i).primeFactors = 4 := by
    rw [s5]; decide
  have s14 : (∏ i ∈ Icc 1 14, Erdos1106.p i).primeFactors = {2, 3, 5, 7, 11, 101} := by
    rw [e14,
      show (56471634671760000 : ℕ) =
        2 ^ 7 * (3 ^ 7 * (5 ^ 4 * (7 ^ 4 * (11 ^ 3 * (101))))) by norm_num,
      key 2 7 _ (by norm_num) (by norm_num) (by positivity),
      key 3 7 _ (by norm_num) (by norm_num) (by positivity),
      key 5 4 _ (by norm_num) (by norm_num) (by positivity),
      key 7 4 _ (by norm_num) (by norm_num) (by positivity),
      key 11 3 _ (by norm_num) (by norm_num) (by positivity),
      Nat.Prime.primeFactors (p := 101) (by norm_num)]
  have c14 : #(∏ i ∈ Icc 1 14, Erdos1106.p i).primeFactors = 6 := by
    rw [s14]; decide
  have c30 : #(∏ i ∈ Icc 1 30, Erdos1106.p i).primeFactors = 15 := by
    rw [primeFactors_prod_thirty]; decide
  rcases le_or_gt n 1 with h | h
  · obtain rfl : n = 1 := le_antisymm h h1
    omega
  rcases le_or_gt n 3 with h' | h'
  · have := mono n 3 h'
    omega
  rcases le_or_gt n 5 with h'' | h''
  · have := mono n 5 h''
    omega
  rcases le_or_gt n 14 with h₃ | h₃
  · have := mono n 14 h₃
    omega
  · have := mono n 30 h2
    omega

/- ### What the target implies -/

/-- **The target implies that infinitely many primes divide partition numbers.** If the right
hand side of `Erdos1106.erdos_1106.parts.ii` holds then no finite set of primes contains the
prime factors of every partition number: `F n` would be bounded by the size of that set, while
the target forces `F n > n`. -/
theorem infinite_primes_of_eventually_lt
    (h : ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n) :
    {q : ℕ | q.Prime ∧ ∃ i, q ∣ Erdos1106.p i}.Infinite := by
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  intro hfin
  obtain ⟨T, hT⟩ := hfin.exists_finset
  have key : ∀ n, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors ≤ #T := by
    intro n
    refine Finset.card_le_card fun q hq => ?_
    rw [hT q]
    have hprime := Nat.prime_of_mem_primeFactors hq
    obtain ⟨i, -, hi⟩ := hprime.prime.exists_mem_finset_dvd (Nat.dvd_of_mem_primeFactors hq)
    exact ⟨hprime, i, hi⟩
  have h1 := hN (max N (#T)) (le_max_left _ _)
  have h2 := key (max N (#T))
  have h3 : #T ≤ max N (#T) := le_max_right _ _
  omega

/- ### A criterion for the target -/

/-- **An amortised growth criterion for monotone functions.** If `f` is monotone, if `f` starts
above the diagonal with a margin of `k` at some point `N`, and if every window of `k` steps past
`N` gains at least `k + 1`, then `n < f n` eventually.

The point of the window form is that individual steps may gain nothing: only the average gain
per step has to exceed `1`. This is a sufficient criterion, not a necessary one; use site 3
below exhibits a monotone `f` satisfying the conclusion for which no admissible `N, k` exists. -/
theorem eventually_lt_of_monotone_block {f : ℕ → ℕ} (hf : Monotone f) {N k : ℕ} (hk : 0 < k)
    (hN : N + k < f N) (hstep : ∀ n, N ≤ n → f n + (k + 1) ≤ f (n + k)) :
    ∀ᶠ n in atTop, n < f n := by
  have inv : ∀ q : ℕ, N + q * k + k < f (N + q * k) := by
    intro q
    induction q with
    | zero => simpa using hN
    | succ q ih =>
      have h1 : f (N + q * k) + (k + 1) ≤ f (N + q * k + k) := hstep _ (by omega)
      have h2 : N + (q + 1) * k = N + q * k + k := by ring
      rw [h2]
      omega
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨q, r, hrk, rfl⟩ : ∃ q r, r < k ∧ n = N + q * k + r := by
    refine ⟨(n - N) / k, (n - N) % k, Nat.mod_lt _ hk, ?_⟩
    have h2 : (n - N) / k * k + (n - N) % k = n - N := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod _ _
    omega
  calc N + q * k + r < N + q * k + k := by omega
    _ < f (N + q * k) := inv q
    _ ≤ f (N + q * k + r) := hf (by omega)

/-- **The criterion, specialised to the target.** Write `F n` for
`#(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors`. If `F N > N + k` for one `N` and if, for every
`n ≥ N`, the product `p 1 ⋯ p (n + k)` acquires at least `k + 1` prime factors that do not
divide `p 1 ⋯ p n`, then the right hand side of `Erdos1106.erdos_1106.parts.ii` holds. -/
theorem eventually_lt_card_primeFactors_prod {N k : ℕ} (hk : 0 < k)
    (hN : N + k < #(∏ i ∈ Icc 1 N, Erdos1106.p i).primeFactors)
    (hgain : ∀ n, N ≤ n → k + 1 ≤ #((∏ i ∈ Icc 1 (n + k), Erdos1106.p i).primeFactors \
      (∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors)) :
    ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n := by
  refine eventually_lt_of_monotone_block
    (f := fun n => #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors)
    (fun a b hab => Finset.card_le_card (primeFactors_prod_subset hab)) hk hN (fun n hn => ?_)
  have hsub := Finset.card_sdiff_add_card_eq_card (primeFactors_prod_subset (m := n) (n := n + k)
    (by omega))
  have hg := hgain n hn
  omega

/- ### Worked use sites against the target statement -/

/-- Use site 1: the `Filter.Eventually` in `Erdos1106.erdos_1106.parts.ii` is not cosmetic. Every
threshold `N` from which the target's inequality holds satisfies `31 ≤ N`. -/
example (N : ℕ) (hN : ∀ n ≥ N, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n) : 31 ≤ N := by
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos N with rfl | h1
  · have h := hN 1 (by omega)
    have := card_primeFactors_prod_le_self (n := 1) (by norm_num) (by norm_num)
    omega
  · have h := hN N le_rfl
    have := card_primeFactors_prod_le_self (n := N) h1 (by omega)
    omega

/-- Use site 2: the target `Erdos1106.erdos_1106.parts.ii` itself, in the shape
`answer ↔ ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n` with the answer
filled in as `True`, discharged from the window hypothesis of
`eventually_lt_card_primeFactors_prod`. -/
example {N k : ℕ} (hk : 0 < k)
    (hN : N + k < #(∏ i ∈ Icc 1 N, Erdos1106.p i).primeFactors)
    (hgain : ∀ n, N ≤ n → k + 1 ≤ #((∏ i ∈ Icc 1 (n + k), Erdos1106.p i).primeFactors \
      (∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors)) :
    True ↔ ∀ᶠ n in atTop, #(∏ i ∈ Icc 1 n, Erdos1106.p i).primeFactors > n :=
  iff_of_true trivial (eventually_lt_card_primeFactors_prod hk hN hgain)

/-- Use site 3: the window criterion is strictly stronger than the target. The monotone function
`f n = n + 1` satisfies `∀ᶠ n in atTop, n < f n`, yet `N + k < f N = N + 1` is impossible for
`0 < k`, so no instance of `eventually_lt_of_monotone_block` applies to it. -/
example : (∀ᶠ n in atTop, n < n + 1) ∧ ∀ N k : ℕ, 0 < k → ¬ N + k < N + 1 :=
  ⟨Filter.Eventually.of_forall fun n => Nat.lt_succ_self n, fun _ _ hk => by omega⟩

/-- Use site 4: the hypotheses of `eventually_lt_of_monotone_block` are satisfiable —
`f n = 2 * n + 5` passes them with `N = 0` and `k = 1`. -/
example : ∀ᶠ n in atTop, n < 2 * n + 5 :=
  eventually_lt_of_monotone_block (f := fun n => 2 * n + 5) (fun a b hab => by dsimp only; omega)
    (N := 0) (k := 1) one_pos (by norm_num) (fun n _ => by omega)

/-- Use site 5: the value `OeisA41.a 5 = 7` of the pinned environment, whose proof there is by
compiler evaluation and therefore rests on `Lean.ofReduceBool` and `Lean.trustCompiler`, follows
from `p_values` with no such dependency. -/
example : OeisA41.a 5 = 7 := p_values.2.2.2.2.1

end Contribution.Erdos1106PartitionCount
