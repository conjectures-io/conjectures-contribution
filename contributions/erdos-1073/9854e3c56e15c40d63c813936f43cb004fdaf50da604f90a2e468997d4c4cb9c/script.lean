import Mathlib
import FormalConjectures.ErdosProblems.«1073»

/-!
# Erdős Problem 1073: composite divisors of `n ! + 1`

The target is `Erdos1073.erdos_1073`.  Writing
`S = {u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u]}`, the problem file defines
`Erdos1073.A x = (S ∩ [0, x)).ncard` and asks whether `A x ≤ x ^ (o x)` for some `o = o(1)`.

## The obstacle

*The counting function is opaque.*  `Erdos1073.A` is the `Set.ncard` of a set carved out by an
**unbounded** existential `∃ n, n ! + 1 ≡ 0 [MOD u]`; the definition is `noncomputable` and the
membership condition carries no `Decidable` instance, so nothing about `Erdos1073.A` is
accessible to kernel computation until that existential is replaced by a bounded one.  The
obvious normalisation of the witness is wrong: `witness_ne_minFac_pred` checks that `121` lies
in `S` with witness `n = 5`, while the Wilson witness `n = (121).minFac - 1 = 10` fails.

*The `o(1)` exponent.*  The right-hand side asks for a *function* `o` with `o =o[atTop] 1` and
`A x ≤ x ^ (o x)` for **all** `x`, including the degenerate `x = 0` (where `(0 : ℝ) ^ (o 0)` is
`1` when `o 0 = 0` and `0` otherwise) and `x = 1` (where the bound reads `A 1 ≤ 1`).  Every
argument a number theorist would write produces instead, for each fixed `ε > 0`, a bound
`A x ≤ x ^ ε` valid only for large `x`.

## What is proved here

*Bounding the witness.*  `lt_minFac_of_dvd_factorial_add_one` says every prime factor of a
`u ∣ n ! + 1` with `u ≠ 1` exceeds `n`; `succ_sq_le_of_dvd_factorial_add_one` upgrades this for
*composite* `u` to `(n + 1) ^ 2 ≤ u`, which is what turns the unbounded existential into a
finite search.  `five_le_minFac` and `twentyFive_le` push it one step further: no element of `S`
has a prime factor below `5`, hence `25 ≤ u` for every `u ∈ S`, and `25 = 4 ! + 1 ∈ S` shows
that bound is attained.

*A kernel-sized evaluator.*  `factMod u k` computes `k ! % u` by `k` modular multiplications,
never forming `k !`; `factMod_eq` and `dvd_factorial_add_one_iff` are its API.  This is what
makes the problem experimentally accessible.  `IsFactorialDivisor` is the resulting bounded,
decidable membership test, proved equivalent to membership in `S` by `isFactorialDivisor_iff`,
and `A_eq_card` identifies the noncomputable `Erdos1073.A x` with `(support x).card` for a
computable `Finset`.  The kernel then evaluates `support_2000`, giving
`A_2000 : Erdos1073.A 2000 = 15`.

*A member far beyond brute force.*  `sq_dvd_factorial_add_one_563` certifies
`563 ^ 2 ∣ 562 ! + 1` — i.e. that `563`, the largest known Wilson prime, really is one — by a
single kernel evaluation of `factMod 316969 562`; `mem_support_563` turns it into an element of
`S` at `316969 = 563 ^ 2`, more than a hundred times beyond the range certified by exhaustive
search.  `sq_mem_of_wilson` records the general mechanism: the square of every Wilson prime
lies in `S`.  All three known Wilson primes are now accounted for inside this file, since
`support_2000` contains `25 = 5 ^ 2` and `169 = 13 ^ 2`.

*An exact finite decomposition.*  `support_eq_biUnion` is an **equality**, not merely an
inclusion: the set counted by `Erdos1073.A x` is exactly the union, over `n < Nat.sqrt x`, of
the composite divisors of `n ! + 1` below `x`.  No existential and no bespoke definition
survive.  `A_le_sum_card_divisors` is the resulting majorant by a finite sum of divisor counts,
the shape in which the conjecture is usually attacked.

*The `o(1)` interface.*  `exists_isLittleO_one_rpow_iff` is a general equivalence
`(∃ o = o(1), ∀ x, f x ≤ x ^ (o x)) ↔ (∀ ε > 0, ∀ᶠ x, f x ≤ x ^ ε)` for any `f : ℕ → ℝ` with
`f 0 ≤ 1` and `f 1 ≤ 1`, the exponent being `log (max (f x) 1) / log x`.  Specialised in
`erdos_1073_rhs_iff`, it removes the existential exponent from the target completely.

*Non-vacuity.*  `composite_factorial_pred_add_one` (from Wilson's theorem: `(p - 1)! + 1` is
composite for every prime `p ≥ 5`) gives `infinite_setOf_composite_dvd_factorial_add_one`, so
`S` is infinite and `exists_le_A` shows `Erdos1073.A` is unbounded; the conjecture is not the
assertion that finitely many `u` occur.

*Compositeness is load-bearing.*  `not_exists_isLittleO_one_rpow_Aall` **refutes** the exact
analogue of the conjecture for `Aall`, the same count with `u.Composite` weakened to `1 < u`:
by Wilson's theorem every prime `p` divides `(p - 1)! + 1`, so `Aall x` dominates the prime
counting function, and the Chebyshev-type lower bound proved here from the central binomial
coefficient (`centralBinom_le_pow_primeCounting'`, `four_pow_lt_pow_primeCounting'_succ`)
forces `π'(x) > x ^ (1 / 2)` infinitely often.  Any proof of `Erdos1073.erdos_1073` must
therefore use `Nat.Composite` essentially.  (I found no quantitative lower bound for
`Nat.primeCounting` or `Nat.primeCounting'` in the pinned Mathlib:
`Mathlib/NumberTheory/PrimeCounting.lean` states `Nat.primeCounting'_add_le`, an upper bound,
and the qualitative `Nat.tendsto_primeCounting'`, while `Mathlib/NumberTheory/Chebyshev.lean`
proves `Nat.theta_le_log4_mul_x` and `Nat.eventually_primeCounting_le`, both upper bounds; so
the lower bound is proved here from scratch.)

A later solver can use declaration `erdos_1073_rhs_iff` to discharge or simplify obligation
`∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ x, Erdos1073.A x ≤ x ^ (o x)` — the right-hand side
of the `↔` in the statement — in target `Erdos1073.erdos_1073`, reducing it to the elementary
estimate `∀ ε > 0, ∀ᶠ x in atTop, ((support x).card : ℝ) ≤ x ^ ε` about a computable `Finset`.
`erdos_1073_iff_card_support_le` is that reduction applied to the pool statement verbatim, in
both directions, so nothing is lost.
-/

open Nat Filter Asymptotics Topology

namespace Contribution.Erdos1073FactorialDivisors

/- ### Part 1: bounding the witness `n` -/

/-- If `u ∣ n ! + 1` and `u ≠ 1`, then every prime factor of `u` exceeds `n`. -/
theorem lt_minFac_of_dvd_factorial_add_one {u n : ℕ} (hu : u ≠ 1) (h : u ∣ n ! + 1) :
    n < u.minFac := by
  rw [← Nat.coprime_factorial_iff hu]
  exact Nat.Coprime.coprime_dvd_left h (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _))

/-- The search bound: a *composite* `u` dividing `n ! + 1` satisfies `(n + 1) ^ 2 ≤ u`.
Consequently the existential `∃ n, u ∣ n ! + 1` may be searched over `n < u.sqrt` only. -/
theorem succ_sq_le_of_dvd_factorial_add_one {u n : ℕ} (hu : u.Composite) (h : u ∣ n ! + 1) :
    (n + 1) ^ 2 ≤ u := by
  have h1 : 1 < u := hu.1
  have h2 : n + 1 ≤ u.minFac := lt_minFac_of_dvd_factorial_add_one (by omega) h
  calc (n + 1) ^ 2 ≤ u.minFac ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ u := Nat.minFac_sq_le_self (by omega) hu.2

/-- Every prime factor of a composite `u` dividing some `n ! + 1` is at least `5`. -/
theorem five_le_minFac {u n : ℕ} (hu : u.Composite) (h : u ∣ n ! + 1) : 5 ≤ u.minFac := by
  have h1 : 1 < u := hu.1
  have h4 : 4 ≤ u := by
    rcases Nat.lt_or_ge u 4 with h' | h'
    · interval_cases u
      · exact absurd Nat.prime_two hu.2
      · exact absurd Nat.prime_three hu.2
    · exact h'
  have hq : (u.minFac).Prime := Nat.minFac_prime (by omega)
  have hn : n < u.minFac := lt_minFac_of_dvd_factorial_add_one (by omega) h
  by_contra hcon
  have hq4 : u.minFac ≠ 4 := by
    intro h4
    rw [h4] at hq
    norm_num at hq
  have hn2 : n ≤ 2 := by have := hq.two_le; omega
  have hle : u ≤ n ! + 1 := Nat.le_of_dvd (by positivity) h
  interval_cases n <;> simp [Nat.factorial] at hle <;> omega

/-- Every composite `u` dividing some `n ! + 1` satisfies `25 ≤ u`; `25 = 4 ! + 1` occurs, so
the bound is attained. -/
theorem twentyFive_le {u : ℕ} (hu : u.Composite) (h : ∃ n, u ∣ n ! + 1) : 25 ≤ u := by
  obtain ⟨n, hn⟩ := h
  calc (25 : ℕ) = 5 ^ 2 := by norm_num
    _ ≤ u.minFac ^ 2 := Nat.pow_le_pow_left (five_le_minFac hu hn) 2
    _ ≤ u := Nat.minFac_sq_le_self (by have := hu.1; omega) hu.2

/-- The witness cannot be normalised away.  `121 = 5 ! + 1` lies in the counted set with
witness `n = 5`, but the *Wilson* witness `n = u.minFac - 1 = 10` fails for it.  So the search
range `n < u.sqrt` of `IsFactorialDivisor` below cannot be collapsed to the single value
`u.minFac - 1`, even though that is the witness for `25`, for `169` and for `316969`. -/
theorem witness_ne_minFac_pred :
    (121 : ℕ).minFac = 11 ∧ (121 : ℕ) ∣ 5 ! + 1 ∧
      ¬ ((121 : ℕ) ∣ ((121 : ℕ).minFac - 1)! + 1) := by
  have hm : (121 : ℕ).minFac = 11 := by
    have h : (121 : ℕ) = 11 ^ 2 := by norm_num
    rw [h]
    exact Nat.Prime.pow_minFac (by norm_num) (by norm_num)
  refine ⟨hm, by decide, ?_⟩
  rw [hm]
  decide

/- ### Part 2: a kernel-sized evaluator for `n ! + 1 mod u` -/

/-- `factMod u k` is `k ! % u`, computed by `k` modular multiplications: the intermediate
values never exceed `u`, so the kernel can evaluate it for `k` in the hundreds. -/
def factMod (u : ℕ) : ℕ → ℕ
  | 0 => 1 % u
  | k + 1 => factMod u k * (k + 1) % u

theorem factMod_eq (u : ℕ) : ∀ k, factMod u k = k ! % u
  | 0 => rfl
  | k + 1 => by
      rw [factMod, factMod_eq u k, Nat.factorial_succ, Nat.mod_mul_mod, Nat.mul_comm]

/-- Divisibility of `n ! + 1`, expressed through the evaluator. -/
theorem dvd_factorial_add_one_iff (u n : ℕ) : u ∣ n ! + 1 ↔ (factMod u n + 1) % u = 0 := by
  rw [factMod_eq, Nat.mod_add_mod, Nat.dvd_iff_mod_eq_zero]

/- ### Part 3: a decidable membership test, and `Erdos1073.A` as a `Finset` cardinality -/

/-- A bounded, decidable test for membership in the set counted by `Erdos1073.A`: `u` has a
divisor `2 ≤ d ≤ u.sqrt` (so `u` is composite) and `u ∣ n ! + 1` for some `n < u.sqrt`. -/
def IsFactorialDivisor (u : ℕ) : Prop :=
  1 < u ∧ (∃ d ∈ Finset.range (u.sqrt + 1), 2 ≤ d ∧ u % d = 0) ∧
    ∃ n ∈ Finset.range u.sqrt, (factMod u n + 1) % u = 0

instance : DecidablePred IsFactorialDivisor := fun u => by
  unfold IsFactorialDivisor; infer_instance

/-- The bounded test is correct: it decides the a priori unbounded membership condition of the
set counted by `Erdos1073.A`. -/
theorem isFactorialDivisor_iff {u : ℕ} :
    IsFactorialDivisor u ↔ u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] := by
  simp only [IsFactorialDivisor, Finset.mem_range, Nat.modEq_zero_iff_dvd, Nat.Composite,
    ← dvd_factorial_add_one_iff]
  constructor
  · rintro ⟨h1, ⟨d, hd, hd2, hdu⟩, n, -, hn⟩
    have hdvd : d ∣ u := Nat.dvd_iff_mod_eq_zero.2 hdu
    have hdlt : d < u := lt_of_le_of_lt (by omega) (Nat.sqrt_lt_self h1)
    refine ⟨⟨h1, fun hp => ?_⟩, n, hn⟩
    rcases hp.eq_one_or_self_of_dvd d hdvd with h | h <;> omega
  · rintro ⟨hu, n, hn⟩
    have h1 : 1 < u := hu.1
    have hq : (u.minFac).Prime := Nat.minFac_prime (by omega)
    refine ⟨h1, ⟨u.minFac, ?_, hq.two_le, Nat.dvd_iff_mod_eq_zero.1 (Nat.minFac_dvd u)⟩,
      n, ?_, hn⟩
    · have : u.minFac ≤ u.sqrt := Nat.le_sqrt.2 (by
        have := Nat.minFac_sq_le_self (by omega : 0 < u) hu.2
        nlinarith [this])
      omega
    · have : n + 1 ≤ u.sqrt :=
        Nat.le_sqrt.2 (by nlinarith [succ_sq_le_of_dvd_factorial_add_one hu hn])
      omega

/-- The finite set of `u < x` counted by `Erdos1073.A x`. -/
def support (x : ℕ) : Finset ℕ := (Finset.range x).filter IsFactorialDivisor

@[simp]
theorem mem_support_iff {x u : ℕ} :
    u ∈ support x ↔ (u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u]) ∧ u < x := by
  simp [support, isFactorialDivisor_iff, and_comm]

/-- The counting function of the problem is the cardinality of a computable `Finset`. -/
theorem A_eq_card (x : ℕ) : Erdos1073.A x = (support x).card := by
  have hcoe : (support x : Set ℕ) = {u | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} := by
    ext u
    simp [exists_and_right, and_assoc]
  unfold Erdos1073.A
  rw [← hcoe, Set.ncard_coe_finset]

theorem support_eq_empty_of_le {x : ℕ} (hx : x ≤ 25) : support x = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro u hu
  rw [mem_support_iff] at hu
  obtain ⟨⟨hc, n, hn⟩, hlt⟩ := hu
  have := twentyFive_le hc ⟨n, Nat.modEq_zero_iff_dvd.1 hn⟩
  omega

/-- The composite `u < 2000` dividing some `n ! + 1`, computed in the kernel. -/
theorem support_2000 : support 2000 =
    {25, 121, 169, 437, 551, 667, 721, 1037, 1159, 1273, 1349, 1403, 1541, 1769, 1943} := by
  decide +kernel

theorem A_2000 : Erdos1073.A 2000 = 15 := by
  have h : (support 2000).card = 15 := by rw [support_2000]; decide
  rw [A_eq_card, h]
  norm_num

/- ### Part 4: an exact finite decomposition, with no existential left -/

/-- The set counted by `Erdos1073.A x` is **exactly** the union, over `n < Nat.sqrt x`, of the
composite divisors of `n ! + 1` below `x`. -/
theorem support_eq_biUnion (x : ℕ) :
    support x = (Finset.range (Nat.sqrt x)).biUnion
      fun n => (n ! + 1).divisors.filter fun d => d.Composite ∧ d < x := by
  ext u
  simp only [mem_support_iff, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hc, n, hn⟩, hlt⟩
    have hdvd : u ∣ n ! + 1 := Nat.modEq_zero_iff_dvd.1 hn
    have hsq := succ_sq_le_of_dvd_factorial_add_one hc hdvd
    have hnu : n + 1 ≤ Nat.sqrt u := Nat.le_sqrt.2 (by nlinarith)
    have hux : Nat.sqrt u ≤ Nat.sqrt x := Nat.sqrt_le_sqrt hlt.le
    exact ⟨n, by omega, ⟨hdvd, by positivity⟩, hc, hlt⟩
  · rintro ⟨n, -, ⟨hdvd, -⟩, hc, hlt⟩
    exact ⟨⟨hc, n, Nat.modEq_zero_iff_dvd.2 hdvd⟩, hlt⟩

/-- The counting function is bounded by a *finite* sum of divisor counts: it suffices to bound
the number of divisors below `x` of the numbers `n ! + 1` with `n < Nat.sqrt x`. -/
theorem A_le_sum_card_divisors (x : ℕ) :
    Erdos1073.A x ≤ ((∑ n ∈ Finset.range (Nat.sqrt x),
      ((n ! + 1).divisors.filter fun d => d < x).card : ℕ) : ℝ) := by
  rw [A_eq_card]
  have h1 : (support x).card ≤ ∑ n ∈ Finset.range (Nat.sqrt x),
      ((n ! + 1).divisors.filter fun d => d.Composite ∧ d < x).card := by
    rw [support_eq_biUnion]
    exact Finset.card_biUnion_le
  have h2 : ∀ n : ℕ, ((n ! + 1).divisors.filter fun d => d.Composite ∧ d < x).card ≤
      ((n ! + 1).divisors.filter fun d => d < x).card := by
    intro n
    refine Finset.card_le_card fun d hd => ?_
    simp only [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.2⟩
  have h3 := h1.trans (Finset.sum_le_sum fun n _ => h2 n)
  exact_mod_cast h3

/- ### Part 5: Wilson primes supply members far beyond the reach of brute force -/

/-- The square of a Wilson prime (a prime `p` with `p ^ 2 ∣ (p - 1)! + 1`) lies in the set
counted by `Erdos1073.A`. -/
theorem sq_mem_of_wilson {p : ℕ} (hp : p.Prime) (h : p ^ 2 ∣ (p - 1)! + 1) :
    (p ^ 2).Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD p ^ 2] := by
  refine ⟨⟨?_, ?_⟩, p - 1, Nat.modEq_zero_iff_dvd.2 h⟩
  · have := hp.two_le
    nlinarith
  · intro hq
    have h2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq p h2) with h' | h'
    · exact absurd h' hp.one_lt.ne'
    · have := hp.two_le
      nlinarith [h'.symm]

/-- `563` is a Wilson prime: `563 ^ 2 ∣ 562 ! + 1`.  The kernel checks this through `562`
modular multiplications; `562 !` itself has more than `1200` digits. -/
theorem sq_dvd_factorial_add_one_563 : (563 ^ 2 : ℕ) ∣ 562 ! + 1 := by
  have h : (562)! % 316969 = 316968 := by
    rw [← factMod_eq]
    decide +kernel
  omega

/-- A certified member of the counted set at `316969 = 563 ^ 2`, far above the range `2000`
settled by exhaustive search in `support_2000`. -/
theorem mem_support_563 {x : ℕ} (hx : 316969 < x) : 316969 ∈ support x := by
  have hp : Nat.Prime 563 := by norm_num
  have hd : (563 : ℕ) ^ 2 ∣ (563 - 1)! + 1 := by
    have h562 : (563 : ℕ) - 1 = 562 := by norm_num
    rw [h562]
    exact sq_dvd_factorial_add_one_563
  obtain ⟨hc, hn⟩ := sq_mem_of_wilson hp hd
  have he : (563 : ℕ) ^ 2 = 316969 := by norm_num
  rw [he] at hc hn
  exact mem_support_iff.2 ⟨⟨hc, hn⟩, hx⟩

/- ### Part 6: removing the `o(1)` exponent -/

/-- A bound `f x ≤ x ^ (o x)` with `o = o(1)` is the same thing as a family of eventual bounds
`f x ≤ x ^ ε`, one for each `ε > 0`.  The exponent is `log (max (f x) 1) / log x`. -/
theorem exists_isLittleO_one_rpow_iff {f : ℕ → ℝ} (h0 : f 0 ≤ 1) (h1 : f 1 ≤ 1) :
    (∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ x, f x ≤ (x : ℝ) ^ (o x)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, f x ≤ (x : ℝ) ^ ε := by
  constructor
  · rintro ⟨o, ho, hle⟩ ε hε
    have h2 : Tendsto o atTop (𝓝 0) := (isLittleO_one_iff ℝ).1 ho
    filter_upwards [NormedAddCommGroup.tendsto_nhds_zero.1 h2 ε hε, eventually_ge_atTop 1]
      with x hx hx1
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    refine (hle x).trans (Real.rpow_le_rpow_of_exponent_le hx1' ?_)
    calc o x ≤ |o x| := le_abs_self _
      _ ≤ ε := le_of_lt (by simpa [Real.norm_eq_abs] using hx)
  · intro h
    refine ⟨fun x => Real.log (max (f x) 1) / Real.log x, ?_, ?_⟩
    · apply (isLittleO_one_iff ℝ).2
      rw [NormedAddCommGroup.tendsto_nhds_zero]
      intro ε hε
      filter_upwards [h (ε / 2) (by linarith), eventually_ge_atTop 2] with x hx hx2
      have hx2' : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx2
      have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
      have hmax : (1 : ℝ) ≤ max (f x) 1 := le_max_right _ _
      have hnum : 0 ≤ Real.log (max (f x) 1) := Real.log_nonneg hmax
      have hle : max (f x) 1 ≤ (x : ℝ) ^ (ε / 2) :=
        max_le hx (Real.one_le_rpow (by linarith) (by linarith))
      have hlog : Real.log (max (f x) 1) ≤ ε / 2 * Real.log x := by
        calc Real.log (max (f x) 1) ≤ Real.log ((x : ℝ) ^ (ε / 2)) :=
              Real.log_le_log (by linarith) hle
          _ = ε / 2 * Real.log x := Real.log_rpow (by linarith) _
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum hlogx.le), div_lt_iff₀ hlogx]
      nlinarith
    · intro x
      rcases Nat.lt_or_ge x 2 with hx | hx
      · interval_cases x <;> simp <;> assumption
      · have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
        have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
        have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
        have hmax : (0 : ℝ) < max (f x) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
        rw [Real.rpow_def_of_pos hxpos, mul_div_cancel₀ _ hlogx.ne', Real.exp_log hmax]
        exact le_max_left _ _

/-- The right-hand side of `Erdos1073.erdos_1073`, with the existential exponent removed and
the counting function replaced by the computable `support`. -/
theorem erdos_1073_rhs_iff :
    (∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ x, Erdos1073.A x ≤ (x : ℝ) ^ (o x)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, ((support x).card : ℝ) ≤ (x : ℝ) ^ ε := by
  have h0 : (((support 0).card : ℝ)) ≤ 1 := by
    rw [support_eq_empty_of_le (by norm_num)]; norm_num
  have h1 : (((support 1).card : ℝ)) ≤ 1 := by
    rw [support_eq_empty_of_le (by norm_num)]; norm_num
  simpa only [A_eq_card] using
    exists_isLittleO_one_rpow_iff (f := fun x => ((support x).card : ℝ)) h0 h1

/- ### Part 7: the counted set is infinite, so `Erdos1073.A` is unbounded -/

/-- Wilson's theorem makes `(p - 1)! + 1` composite for every prime `p ≥ 5`. -/
theorem composite_factorial_pred_add_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((p - 1)! + 1).Composite := by
  have hfac : p - 1 < (p - 1)! := Nat.lt_factorial_self (by omega)
  have hw : ((p - 1)! : ZMod p) = -1 := (Nat.prime_iff_fac_equiv_neg_one (by omega)).1 hp
  have hdvd : p ∣ (p - 1)! + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hw]
    ring
  refine ⟨by have := Nat.factorial_pos (p - 1); omega, fun hq => ?_⟩
  rcases hq.eq_one_or_self_of_dvd p hdvd with h | h
  · exact absurd h hp.one_lt.ne'
  · omega

theorem infinite_setOf_composite_dvd_factorial_add_one :
    {u : ℕ | u.Composite ∧ ∃ n, n ! + 1 ≡ 0 [MOD u]}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes (max (a + 1) 5)
  have h5 : 5 ≤ p := le_trans (le_max_right _ _) hpa
  have ha : a < p := lt_of_lt_of_le (by omega : a < max (a + 1) 5) hpa
  have hfac : p - 1 ≤ (p - 1)! := Nat.self_le_factorial _
  exact ⟨(p - 1)! + 1, ⟨composite_factorial_pred_add_one hp h5,
    ⟨p - 1, Nat.modEq_zero_iff_dvd.2 dvd_rfl⟩⟩, by omega⟩

/-- `Erdos1073.A` is unbounded: the conjecture is not the assertion that only finitely many
composite `u` divide some `n ! + 1`. -/
theorem exists_le_A (N : ℕ) : ∃ x, (N : ℝ) ≤ Erdos1073.A x := by
  obtain ⟨t, hts, htc⟩ :=
    infinite_setOf_composite_dvd_factorial_add_one.exists_subset_card_eq N
  refine ⟨t.sup id + 1, ?_⟩
  rw [A_eq_card, ← htc]
  refine Nat.cast_le.2 (Finset.card_le_card fun u hu => ?_)
  have hmem := hts (Finset.mem_coe.2 hu)
  have hsup : id u ≤ t.sup id := Finset.le_sup hu
  rw [mem_support_iff]
  simp only [id] at hsup
  exact ⟨hmem, by omega⟩

/- ### Part 8: compositeness is load-bearing.
The same count with `u.Composite` weakened to `1 < u` obeys no bound `x ^ o(1)`. -/

/-- `Erdos1073.A` with the compositeness condition weakened to `1 < u`. -/
noncomputable def Aall (x : ℕ) : ℝ := {u | 1 < u ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x}.ncard

/-- The finite set counted by `Aall`.  The search over `n` may be cut at `u` because every
prime factor of `u ∣ n ! + 1` exceeds `n`. -/
def supportAll (x : ℕ) : Finset ℕ :=
  (Finset.range x).filter fun u => 1 < u ∧ ∃ n ∈ Finset.range u, (factMod u n + 1) % u = 0

@[simp]
theorem mem_supportAll_iff {x u : ℕ} :
    u ∈ supportAll x ↔ (1 < u ∧ ∃ n, n ! + 1 ≡ 0 [MOD u]) ∧ u < x := by
  simp only [supportAll, Finset.mem_filter, Finset.mem_range, Nat.modEq_zero_iff_dvd,
    ← dvd_factorial_add_one_iff]
  constructor
  · rintro ⟨hx, h1, n, -, hn⟩
    exact ⟨⟨h1, n, hn⟩, hx⟩
  · rintro ⟨⟨h1, n, hn⟩, hx⟩
    have hlt : n < u.minFac := lt_minFac_of_dvd_factorial_add_one (by omega) hn
    have hle : u.minFac ≤ u := Nat.minFac_le (by omega)
    exact ⟨hx, h1, n, by omega, hn⟩

theorem Aall_eq_card (x : ℕ) : Aall x = (supportAll x).card := by
  have hcoe : (supportAll x : Set ℕ) = {u | 1 < u ∧ ∃ n, n ! + 1 ≡ 0 [MOD u] ∧ u < x} := by
    ext u
    simp [exists_and_right, and_assoc]
  unfold Aall
  rw [← hcoe, Set.ncard_coe_finset]

/-- Wilson's theorem: every prime below `x` is counted by `Aall x`. -/
theorem primesBelow_subset_supportAll (x : ℕ) : Nat.primesBelow x ⊆ supportAll x := by
  intro p hp
  rw [Nat.mem_primesBelow] at hp
  obtain ⟨hpx, hp⟩ := hp
  have hw : ((p - 1)! : ZMod p) = -1 := (Nat.prime_iff_fac_equiv_neg_one hp.one_lt.ne').1 hp
  have hdvd : p ∣ (p - 1)! + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hw]
    ring
  exact mem_supportAll_iff.2 ⟨⟨hp.one_lt, p - 1, Nat.modEq_zero_iff_dvd.2 hdvd⟩, hpx⟩

theorem primeCounting'_le_card_supportAll (x : ℕ) :
    Nat.primeCounting' x ≤ (supportAll x).card := by
  rw [← Nat.primesBelow_card_eq_primeCounting']
  exact Finset.card_le_card (primesBelow_subset_supportAll x)

/-- Each prime power dividing `Nat.centralBinom n` is at most `2 * n`, and there are at most
`π'(2 * n + 1)` of them. -/
theorem centralBinom_le_pow_primeCounting' {n : ℕ} (hn : 0 < n) :
    n.centralBinom ≤ (2 * n) ^ Nat.primeCounting' (2 * n + 1) := by
  rw [← Nat.primesBelow_card_eq_primeCounting']
  calc n.centralBinom
      = ∏ p ∈ Finset.range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p :=
        (Nat.prod_pow_factorization_centralBinom n).symm
    _ = ∏ p ∈ Nat.primesBelow (2 * n + 1), p ^ (Nat.centralBinom n).factorization p := by
        refine (Finset.prod_subset (fun p hp => Finset.mem_range.2 (Nat.lt_of_mem_primesBelow hp))
          ?_).symm
        intro p hp hp2
        rw [Nat.mem_primesBelow] at hp2
        rw [Nat.factorization_eq_zero_of_not_prime _ (fun h => hp2 ⟨Finset.mem_range.1 hp, h⟩),
          pow_zero]
    _ ≤ (2 * n) ^ (Nat.primesBelow (2 * n + 1)).card :=
        Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_factorization_choose_le (by omega)

/-- A Chebyshev-type **lower** bound for the prime counting function, in the form
`4 ^ n < (2 * n) ^ (π'(2 * n + 1) + 1)`. -/
theorem four_pow_lt_pow_primeCounting'_succ {n : ℕ} (hn : 4 ≤ n) :
    4 ^ n < (2 * n) ^ (Nat.primeCounting' (2 * n + 1) + 1) := by
  calc 4 ^ n < n * n.centralBinom := Nat.four_pow_lt_mul_centralBinom n hn
    _ ≤ 2 * n * (2 * n) ^ Nat.primeCounting' (2 * n + 1) :=
        Nat.mul_le_mul (by omega) (centralBinom_le_pow_primeCounting' (by omega))
    _ = (2 * n) ^ (Nat.primeCounting' (2 * n + 1) + 1) := by ring

/-- **Compositeness is load-bearing.**  The exact analogue of `Erdos1073.erdos_1073` for the
count `Aall`, in which `u.Composite` is weakened to `1 < u`, is false: every prime `p` divides
`(p - 1)! + 1`, so `Aall` dominates the prime counting function, which exceeds `x ^ (1 / 2)`
infinitely often. -/
theorem not_exists_isLittleO_one_rpow_Aall :
    ¬ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ x, Aall x ≤ (x : ℝ) ^ (o x) := by
  rintro ⟨o, ho, hle⟩
  have hpk : ∀ j : ℕ, 3 ≤ j → 2 * j + 1 ≤ 2 ^ j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ m _ ih =>
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
  have e0 : (supportAll 0).card = 0 := by decide
  have e1 : (supportAll 1).card = 0 := by decide
  have hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, ((supportAll x).card : ℝ) ≤ (x : ℝ) ^ ε := by
    refine (exists_isLittleO_one_rpow_iff (f := fun x => ((supportAll x).card : ℝ))
      (by show ((supportAll 0).card : ℝ) ≤ 1; rw [e0]; norm_num)
      (by show ((supportAll 1).card : ℝ) ≤ 1; rw [e1]; norm_num)).1 ⟨o, ho, fun x => ?_⟩
    rw [← Aall_eq_card]
    exact hle x
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev (1 / 2) (by norm_num))
  -- work at `x = 2 * 4 ^ k + 1` for a large `k`
  set k := max 3 N with hkdef
  have hk3 : 3 ≤ k := le_max_left _ _
  have hkN : N ≤ k := le_max_right _ _
  have hlt : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
  have hpow : ∀ j : ℕ, (4 : ℕ) ^ j = 2 ^ (2 * j) := fun j => by rw [pow_mul]; norm_num
  set m := Nat.primeCounting' (2 * 4 ^ k + 1) with hmdef
  -- the assumed bound gives `m ^ 2 ≤ 2 * 4 ^ k + 1`
  have hmr : (m : ℝ) ≤ ((2 * 4 ^ k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
    le_trans (by exact_mod_cast primeCounting'_le_card_supportAll (2 * 4 ^ k + 1))
      (hN (2 * 4 ^ k + 1) (by omega))
  have hmsq : m ^ 2 ≤ 2 * 4 ^ k + 1 := by
    have hx : (0 : ℝ) ≤ ((2 * 4 ^ k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : ((m : ℝ)) ^ (2 : ℕ) ≤ (((2 * 4 ^ k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg m) hmr 2
    rw [← Real.rpow_natCast (((2 * 4 ^ k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul hx] at h2
    norm_num at h2
    exact_mod_cast h2
  -- hence `m + 1 ≤ 2 ^ (k + 1)`
  have hone : 1 ≤ (4 : ℕ) ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hm1 : m + 1 ≤ 2 ^ (k + 1) := by
    by_contra hcon
    have hge : 2 ^ (k + 1) ≤ m := by omega
    have hsq : (2 ^ (k + 1)) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hge 2
    have hval : (2 ^ (k + 1)) ^ 2 = 4 * 4 ^ k := by
      rw [hpow k, ← pow_mul]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      ring_nf
    omega
  -- the Chebyshev bound, read in base `2`
  have hkey := four_pow_lt_pow_primeCounting'_succ (n := 4 ^ k) (by omega)
  rw [← hmdef] at hkey
  have hbase : 2 * 4 ^ k = 2 ^ (2 * k + 1) := by rw [hpow k, pow_succ]; ring
  rw [hpow (4 ^ k), hbase, ← pow_mul] at hkey
  have hexp : 2 * 4 ^ k < (2 * k + 1) * (m + 1) :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 (by rw [← hbase] at hkey; exact hkey)
  -- and now a contradiction with `2 * k + 1 ≤ 2 ^ k`
  have hsplit : 2 * 4 ^ k = 2 ^ k * 2 ^ (k + 1) := by
    rw [hbase, ← pow_add]
    ring_nf
  have hfin : 2 ^ k * 2 ^ (k + 1) < (2 * k + 1) * 2 ^ (k + 1) :=
    lt_of_lt_of_le (hsplit ▸ hexp) (Nat.mul_le_mul_left _ hm1)
  have := Nat.lt_of_mul_lt_mul_right hfin
  have := hpk k hk3
  omega

/- ### Part 9: a worked use site against the pool statement -/

/-- Worked use site.  The left-hand side is `Erdos1073.erdos_1073` **verbatim** (the
`answer(..)` placeholder of the pool file elaborates to `True`); the right-hand side is an
elementary bound on a computable `Finset`, with no existential exponent and no `Set.ncard`.
The equivalence goes both ways, so the reduction loses nothing. -/
theorem erdos_1073_iff_card_support_le :
    (True ↔ ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧ ∀ x, Erdos1073.A x ≤ (x : ℝ) ^ (o x)) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in atTop, ((support x).card : ℝ) ≤ (x : ℝ) ^ ε := by
  constructor
  · intro h
    exact erdos_1073_rhs_iff.1 (h.1 trivial)
  · intro h
    exact ⟨fun _ => erdos_1073_rhs_iff.2 h, fun _ => trivial⟩

end Contribution.Erdos1073FactorialDivisors
