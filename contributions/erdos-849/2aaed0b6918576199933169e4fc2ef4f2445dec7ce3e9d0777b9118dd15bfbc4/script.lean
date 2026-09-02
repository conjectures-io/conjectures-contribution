import Mathlib
import FormalConjectures.ErdosProblems.«849»

/-!
# Erdős 849: counting the `n` with `a` a binomial coefficient of `n`

Target: `Erdos849.erdos_849` — is it true that for every `t ≥ 1` there is an `a` for which
`{n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t`?  Nothing here decides the problem;
this file is a checked API for the set that the reward statement counts.

## The obstacle

The reward statement counts, with `Set.ncard`, a set of naturals that is presented as an
unbounded `Set ℕ` with an existential over `k` inside it.  Every attempt to produce a witness
`a` runs into the same three walls:

* `Set.ncard` is junk-valued (`0`) on infinite sets, so *no* upper bound on the number of
  solutions can even be stated, let alone proved, before the set has been shown to be finite;
  and finiteness is not obvious from the shape `{n | ∃ k, …}`.
* The set is not visibly decidable: the bound `2 * k ≤ n` bounds `k` in terms of `n`, but
  nothing in the statement bounds `n`, so the naive `Finset` reformulation ranges over all
  of `ℕ`.
* Even after a bound on `n` is found, checking a concrete witness by `decide` is hopeless,
  because the kernel evaluates `Nat.choose n k` through Pascal's recurrence, at a cost of
  about `n.choose k` additions (`Nat.choose 78 39` is out of reach).

## What is provided

* Left-half monotonicity of binomial coefficients, `choose_le_choose_of_le_half`
  (`i ≤ j` and `2 * j ≤ n` imply `n.choose i ≤ n.choose j`).  Mathlib has only the single-step
  version `Nat.choose_le_succ_of_lt_half_left` and the comparison with the middle coefficient
  `Nat.choose_le_middle`; its two-index lemma `choose_le_middle_of_le_half_left` is private and
  compares with the middle coefficient only, so this form is not available.  Its corollaries
  `self_le_choose` and `self_lt_choose` are what make the target's set finite: a solution `n`
  satisfies `n ≤ a`, with equality forced when `k = 1`.
* `not_prime_choose`: for `2 ≤ k` and `2 * k ≤ n` the binomial coefficient `n.choose k` is
  never prime.  Consequently `sols_of_prime : p.Prime → sols p = {p}`, i.e. *every* prime is a
  witness for `t = 1` — an infinite family, not the single sporadic example.
* `sols`, the counted set, with the degenerate cases (`sols_eq_empty_of_lt_two`,
  `self_mem_sols`, `one_le_ncard_sols`: no `a < 2` can ever be a witness, and every `a ≥ 2` is
  a solution of itself, so `t = 0` is unattainable and the answer for `t = 1` is exactly the
  `a` with no `k ≥ 2` representation).
* The finite search: `HasProperRep` is the `k ≥ 2` part of membership, phrased through
  `Nat.descFactorial` so that the kernel evaluates it with a handful of multiplications
  instead of Pascal's recurrence, together with its decidability instance and the bridge
  `hasProperRep_iff` back to `Nat.choose`.  `properSols a B` is the resulting `Finset`, and
  `sols_eq_insert_properSols` / `ncard_sols_eq` turn the target's `ncard` into a `Finset.card`
  that `decide` really can evaluate, for any user-supplied bound `B` with `2 * a < (B + 1) * B`.

A later solver can use declaration `Contribution.Erdos849Counting.ncard_sols_eq` to discharge
the obligation `{n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = t` in target
`Erdos849.erdos_849`, by reducing it to one kernel-checkable finite computation.  The final
section is the worked use site: `erdos_849_of_le_four` proves the target's right-hand side,
verbatim in the reward statement's own syntax, for every `t ≤ 4`.

*References:*
- [erdosproblems.com/849](https://www.erdosproblems.com/849)
- D. Singmaster, *How often does an integer occur as a binomial coefficient?*,
  Amer. Math. Monthly 78 (1971), 385-386.
-/

namespace Contribution.Erdos849Counting

open Nat

variable {a n k i j p B : ℕ}

/- ### Binomial coefficients on the left half of a row -/

/-- `Nat.choose n ·` is monotone on `[0, n / 2]`.  Mathlib has the single-step version
`Nat.choose_le_succ_of_lt_half_left` and the comparison `Nat.choose_le_middle` with the middle
coefficient; the two-index statement is not available (`choose_le_middle_of_le_half_left` is
private, and compares with the middle coefficient only). -/
theorem choose_le_choose_of_le_half (hij : i ≤ j) (hj : 2 * j ≤ n) :
    n.choose i ≤ n.choose j := by
  induction j with
  | zero => simp_all
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    · have hji : i = j + 1 := by omega
      subst hji; exact le_rfl

/-- Every binomial coefficient in the left half of row `n`, other than `n.choose 0`, is at
least `n`. -/
theorem self_le_choose (hk : 1 ≤ k) (hkn : 2 * k ≤ n) : n ≤ n.choose k := by
  have h := choose_le_choose_of_le_half hk hkn
  rwa [Nat.choose_one_right] at h

/-- A division-free form of `Nat.choose_two_right`. -/
theorem two_mul_choose_two : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]

theorem lt_choose_two (hn : 4 ≤ n) : n < n.choose 2 := by
  have h2 := two_mul_choose_two (n := n)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h3 : m + 4 - 1 = m + 3 := by omega
  rw [h3] at h2
  nlinarith [h2]

/-- The strict form of `self_le_choose`: for `k ≥ 2` in the left half, `n.choose k` is
*strictly* bigger than `n`.  This is what forces `k = 1` in any solution with `n = a`. -/
theorem self_lt_choose (hk : 2 ≤ k) (hkn : 2 * k ≤ n) : n < n.choose k :=
  (lt_choose_two (by omega)).trans_le (choose_le_choose_of_le_half hk hkn)

/-- A binomial coefficient `n.choose k` with `2 ≤ k` and `2 * k ≤ n` is never prime.
Indeed `k * n.choose k = n * (n - 1).choose (k - 1)`, and `n.choose k > n` would make a prime
`n.choose k` divide `(n - 1).choose (k - 1)`, forcing `n ∣ k`. -/
theorem not_prime_choose (hk : 2 ≤ k) (hkn : 2 * k ≤ n) : ¬ (n.choose k).Prime := by
  intro hp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set C := (m + 1).choose (j + 1) with hC
  have key : (m + 1) * m.choose j = C * (j + 1) := Nat.add_one_mul_choose_eq m j
  have hlt : m + 1 < C := self_lt_choose hk hkn
  have hdvd : C ∣ (m + 1) * m.choose j := ⟨j + 1, key⟩
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  · obtain ⟨c, hc⟩ := h
    have hpos : 0 < C := Nat.choose_pos (by omega)
    have h4 : C * ((m + 1) * c) = C * (j + 1) := by rw [← key, hc]; ring
    have h5 : (m + 1) * c = j + 1 := Nat.eq_of_mul_eq_mul_left hpos h4
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | h6
      · simp at h5
      · exact h6
    have h7 : m + 1 ≤ (m + 1) * c := Nat.le_mul_of_pos_right _ hc1
    omega

/- ### The set counted by the target -/

/-- The set of `n` counted by `Erdos849.erdos_849`: those `n` for which `a` occurs in row `n`
of Pascal's triangle at some position `k` with `1 ≤ k ≤ n / 2`. -/
def sols (a : ℕ) : Set ℕ := {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}

/-- `sols` is *definitionally* the set appearing in the reward statement. -/
theorem sols_eq_target (a : ℕ) :
    sols a = {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a} := rfl

theorem mem_sols_iff : n ∈ sols a ↔ ∃ k, 1 ≤ k ∧ 2 * k ≤ n ∧ n.choose k = a := Iff.rfl

/-- Every solution is at most `a`: this is the finiteness mechanism. -/
theorem le_of_mem_sols (hn : n ∈ sols a) : n ≤ a := by
  obtain ⟨k, hk1, hk2, hk3⟩ := hn
  exact hk3 ▸ self_le_choose hk1 hk2

theorem sols_finite (a : ℕ) : (sols a).Finite :=
  (Set.finite_Icc 0 a).subset fun _ hn => ⟨Nat.zero_le _, le_of_mem_sols hn⟩

/-- Every `a ≥ 2` occurs in its own row, at `k = 1`. -/
theorem self_mem_sols (ha : 2 ≤ a) : a ∈ sols a :=
  ⟨1, le_rfl, by omega, Nat.choose_one_right a⟩

/-- Degenerate case: `0` and `1` have no solutions at all, so a witness for `t ≥ 1` must
be at least `2`. -/
theorem sols_eq_empty_of_lt_two (ha : a < 2) : sols a = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun n hn => ?_
  have hna := le_of_mem_sols hn
  obtain ⟨k, hk1, hk2, -⟩ := hn
  omega

/-- Consequently `t = 0` is not attainable in the target statement. -/
theorem one_le_ncard_sols (ha : 2 ≤ a) : 1 ≤ (sols a).ncard :=
  (Set.ncard_pos (sols_finite a)).2 ⟨a, self_mem_sols ha⟩

/-- A prime has exactly one solution, namely itself: `t = 1` is realised by an infinite
family. -/
theorem sols_of_prime (hp : p.Prime) : sols p = {p} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨self_mem_sols hp.two_le, ?_⟩
  rintro n ⟨k, hk1, hk2, hk3⟩
  rcases eq_or_lt_of_le hk1 with rfl | hk
  · rwa [Nat.choose_one_right] at hk3
  · exact absurd (hk3 ▸ hp) (not_prime_choose hk hk2)

theorem ncard_sols_of_prime (hp : p.Prime) : (sols p).ncard = 1 := by
  rw [sols_of_prime hp, Set.ncard_singleton]

/- ### A kernel-checkable finite search -/

/-- `HasProperRep a n` says that `a` occurs in row `n` at a position `k` with `2 ≤ k ≤ n / 2`,
i.e. a solution *other than* the trivial one `n = a, k = 1`.

The binomial coefficient is computed as `n.descFactorial k / k !` rather than by
`Nat.choose`: the two are equal (`hasProperRep_iff`), but the kernel evaluates the former
with `2 * k` multiplications and one division, whereas unfolding `Nat.choose` costs about
`n.choose k` additions.  This is what makes `decide` usable on concrete instances. -/
def HasProperRep (a n : ℕ) : Prop :=
  ∃ k ∈ Finset.Icc 2 (n / 2), n.descFactorial k / k.factorial = a

instance decidableHasProperRep (a n : ℕ) : Decidable (HasProperRep a n) :=
  inferInstanceAs (Decidable (∃ k ∈ Finset.Icc 2 (n / 2), n.descFactorial k / k.factorial = a))

theorem hasProperRep_iff : HasProperRep a n ↔ ∃ k, 2 ≤ k ∧ 2 * k ≤ n ∧ n.choose k = a := by
  simp only [HasProperRep, Finset.mem_Icc, Nat.choose_eq_descFactorial_div_factorial]
  constructor
  · rintro ⟨k, ⟨hk1, hk2⟩, hk3⟩; exact ⟨k, hk1, by omega, hk3⟩
  · rintro ⟨k, hk1, hk2, hk3⟩; exact ⟨k, ⟨hk1, by omega⟩, hk3⟩

/-- A nontrivial solution is quadratically small: `n * (n - 1) ≤ 2 * a`.  This is the bound
that makes the search finite *and* short. -/
theorem mul_pred_le_of_hasProperRep (h : HasProperRep a n) : 4 ≤ n ∧ n * (n - 1) ≤ 2 * a := by
  obtain ⟨k, hk1, hk2, hk3⟩ := hasProperRep_iff.1 h
  refine ⟨by omega, ?_⟩
  calc n * (n - 1) = 2 * n.choose 2 := two_mul_choose_two.symm
    _ ≤ 2 * n.choose k := by
        exact Nat.mul_le_mul_left 2 (choose_le_choose_of_le_half hk1 hk2)
    _ = 2 * a := by rw [hk3]

/-- The nontrivial solutions for `a`, searched over `[4, B]`. -/
def properSols (a B : ℕ) : Finset ℕ := (Finset.Icc 4 B).filter (HasProperRep a)

theorem mem_properSols :
    n ∈ properSols a B ↔ (4 ≤ n ∧ n ≤ B) ∧ ∃ k, 2 ≤ k ∧ 2 * k ≤ n ∧ n.choose k = a := by
  rw [properSols, Finset.mem_filter, Finset.mem_Icc, hasProperRep_iff]

/-- **Structure theorem.** For `a ≥ 4` and any bound `B` with `2 * a < (B + 1) * B` and
`B < a`, the solution set is the trivial solution `a` together with the finite,
decidable set `properSols a B`. -/
theorem sols_eq_insert_properSols (ha : 4 ≤ a) (hB : 2 * a < (B + 1) * B) (hBa : B < a) :
    sols a = insert a ↑(properSols a B) := by
  ext n
  simp only [Set.mem_insert_iff, Finset.mem_coe, mem_properSols]
  constructor
  · intro hn
    rcases eq_or_ne n a with rfl | hne
    · exact Or.inl rfl
    obtain ⟨k, hk1, hk2, hk3⟩ := hn
    have hk : 2 ≤ k := by
      rcases eq_or_lt_of_le hk1 with rfl | hk
      · rw [Nat.choose_one_right] at hk3; exact absurd hk3 hne
      · omega
    have hrep : HasProperRep a n := hasProperRep_iff.2 ⟨k, hk, hk2, hk3⟩
    obtain ⟨h4, hquad⟩ := mul_pred_le_of_hasProperRep hrep
    refine Or.inr ⟨⟨h4, ?_⟩, k, hk, hk2, hk3⟩
    by_contra hnB
    have h1 : B + 1 ≤ n := by omega
    have h2 : B ≤ n - 1 := by omega
    have := Nat.mul_le_mul h1 h2
    omega
  · rintro (rfl | ⟨-, k, hk, hk2, hk3⟩)
    · exact self_mem_sols (by omega)
    · exact ⟨k, by omega, hk2, hk3⟩

/-- **Counting theorem.**  The target's `ncard` becomes a `Finset.card` that the kernel can
evaluate. -/
theorem ncard_sols_eq (ha : 4 ≤ a) (hB : 2 * a < (B + 1) * B) (hBa : B < a) :
    (sols a).ncard = (properSols a B).card + 1 := by
  rw [sols_eq_insert_properSols ha hB hBa, Set.ncard_insert_of_notMem, Set.ncard_coe_finset]
  simp only [Finset.mem_coe, mem_properSols]
  rintro ⟨⟨-, h⟩, -⟩
  omega

/- ### Worked use site

The reward statement asks for a witness `a` for each `t ≥ 1`.  Below are the four values of
`t` for which a witness is known, proved in the reward statement's own syntax.  Note that the
sets are the target's, verbatim: no translation into `sols` is needed, because `sols` is
definitionally equal to them (`sols_eq_target`).

The recipe is always the same three steps: pick a bound `B` with `2 * a < (B + 1) * B`,
apply `ncard_sols_eq`, and let the kernel run the search. -/

theorem ncard_sols_six : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = 6}.ncard = 2 := by
  have h : (sols 6).ncard = (properSols 6 4).card + 1 :=
    ncard_sols_eq (by norm_num) (by norm_num) (by norm_num)
  rw [← sols_eq_target, h]
  decide

theorem ncard_sols_onetwenty :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = 120}.ncard = 3 := by
  have h : (sols 120).ncard = (properSols 120 16).card + 1 :=
    ncard_sols_eq (by norm_num) (by norm_num) (by norm_num)
  rw [← sols_eq_target, h]
  decide

/-- `3003 = C(3003, 1) = C(78, 2) = C(15, 5) = C(14, 6)` is Singmaster's example of an
integer occurring eight times in Pascal's triangle, i.e. four times in the left half.
Kernel-checking this is what the `descFactorial` form of `HasProperRep` buys: the search
range `[4, 78]` involves `Nat.choose 78 39`, which Pascal's recurrence cannot evaluate. -/
theorem ncard_sols_3003 : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = 3003}.ncard = 4 := by
  have h : (sols 3003).ncard = (properSols 3003 78).card + 1 :=
    ncard_sols_eq (by norm_num) (by norm_num) (by norm_num)
  rw [← sols_eq_target, h]
  decide

/-- The right-hand side of `Erdos849.erdos_849`, restricted to `t ≤ 4`: for each such `t`
there is an `a` whose set of solutions has exactly `t` elements.  `t = 1` uses the prime `3`
(any prime works, by `ncard_sols_of_prime`); `t = 2, 3, 4` use `6`, `120` and `3003`. -/
theorem erdos_849_of_le_four (t : ℕ) (ht1 : 1 ≤ t) (ht4 : t ≤ 4) :
    ∃ a : ℕ, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = a}.ncard = t := by
  interval_cases t
  · exact ⟨3, ncard_sols_of_prime (by norm_num)⟩
  · exact ⟨6, ncard_sols_six⟩
  · exact ⟨120, ncard_sols_onetwenty⟩
  · exact ⟨3003, ncard_sols_3003⟩

/-- The same recipe on a value that is not used anywhere above: `210 = C(210, 1) = C(21, 2)
= C(10, 4)`, so `210` is a second witness for `t = 3`.  Only the bound `B = 21` had to be
supplied by hand (`2 * 210 < 22 * 21`); everything else is mechanical. -/
example : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ Nat.choose n k = 210}.ncard = 3 := by
  have h : (sols 210).ncard = (properSols 210 21).card + 1 :=
    ncard_sols_eq (by norm_num) (by norm_num) (by norm_num)
  rw [← sols_eq_target, h]
  decide

end Contribution.Erdos849Counting
