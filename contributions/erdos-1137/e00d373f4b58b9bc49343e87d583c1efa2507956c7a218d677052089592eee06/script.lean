import Mathlib
import FormalConjectures.ErdosProblems.«1137»

/-!
# Erdős 1137: a local, division-free criterion for the maximal adjacent gap product

Target: `Erdos1137.erdos_1137`. The `FormalConjectures` `lean_lib` in `lakefile.toml` sets no
`google.answer` option and `register_option google.answer` has `defValue := .alwaysTrue`, so the
`answer(…)` placeholder in the reward statement elaborates to `True`; running
`#check @Erdos1137.erdos_1137` against this repository prints

`True ↔ Tendsto (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
(((range x).sup primeGap : ℕ) : ℝ) ^ 2) atTop (𝓝 0)`.

So the whole mathematical content of the reward theorem is that `Tendsto` obligation.

## The obstacle

The obligation is a limit in `ℝ` of a quotient of two `Finset.sup`s over `ℕ`, the numerator being
a sup of a *product* of two gaps whose indices differ by one, with truncated subtraction `n - 1`
inside.

* The numerator does not split: `Finset.sup` of a product is not the product of the `Finset.sup`s,
  and the bound that comes for free, `maxAdjProd x ≤ maxGap x ^ 2`, is exactly the trivial bound
  that Erdős' question asks to beat.
* The whole numerical content sits in the interaction between one index and its predecessor, but
  the statement never mentions a pair of adjacent gaps: a solver has to re-derive by hand, at
  every step, that `n - 1 < x` whenever `n < x`, and that the `n = 0` term is
  `primeGap 0 * primeGap 0` because `0 - 1 = 0` in `ℕ`.
* Every quantity in sight is a natural number, but the obligation lives in `ℝ` and divides by a
  square, so each step must be transported across `Nat.cast` and guarded by positivity of the
  denominator -- which needs positivity of `primeGap`, unavailable (next point).
* `primeGap` is defined in `FormalConjecturesForMathlib.NumberTheory.PrimeGap`, whose file
  contains that definition and nothing else: no positivity lemma, no recursion, no way to evaluate
  it at a numeral. `grep primeGap` over the pinned `Mathlib/` source returns no hits at all, and
  the only declarations there that mention `Nat.nth Nat.Prime` are `Nat.nth_prime_zero_eq_two` …
  `Nat.nth_prime_four_eq_eleven`, `Nat.add_two_le_nth_prime`, `Nat.prime_nth_prime` and
  `Nat.primeCounting'_nth_eq`: no statement about differences of consecutive primes, in
  particular nothing saying that prime gaps are unbounded.

## The contribution

**1. The sandwich.** The awkward numerator is controlled, in both directions, by the *smaller* of
each pair of adjacent gaps. Write `maxGap x = (range x).sup primeGap` (the target's denominator,
unsquared), `maxAdjProd x` for the target's numerator, and
`maxAdjMin x = (range x).sup fun n ↦ min (primeGap n) (primeGap (n - 1))`. Because
`a * b = max a b * min a b`, the two `ℕ`-inequalities

* `sq_maxAdjMin_le_maxAdjProd : maxAdjMin x ^ 2 ≤ maxAdjProd x` and
* `maxAdjProd_le_maxGap_mul_maxAdjMin : maxAdjProd x ≤ maxGap x * maxAdjMin x`

pin `ratio x = maxAdjProd x / maxGap x ^ 2` between `adjRatio x ^ 2` and `adjRatio x`, where
`adjRatio x = maxAdjMin x / maxGap x`. Since `t ↦ t ^ 2` and `t ↦ t` tend to `0` together on
`[0, ∞)`, `tendsto_ratio_iff_tendsto_adjRatio` is an **equivalence**, not a one-way reduction: the
target obligation holds if and only if `adjRatio x → 0`. This is the step that disposes of the
target's numerator, i.e. of the sup of a product of two shifted gaps; the forward direction is the
one with content, and it goes through `Real.sqrt`, because what the numerator returns is a bound
on a *square*. The two bounds are genuinely different: `sandwich_sharp_at_four` checks that at
`x = 4` the left one is strict (`4 < 8`) while the right one is attained (`8 = 4 * 2`), so the
squeeze cannot be collapsed to a single equality and the constant `1` on the right cannot be
lowered.

**2. Down to `ℕ`, then to a single index.** `tendsto_adjRatio_iff` removes `ℝ` and the division;
`nat_criterion_iff` removes the `Finset.sup` that defines `maxAdjMin`, leaving a condition on one
index at a time; `criterion_iff_local` then replaces the uniform "for all `n < x`, compare with
`maxGap x`" by the local "for all large `n`, compare with `maxGap (n + 1)`". Chaining these gives
`erdos_1137_tendsto_iff`: the target obligation is equivalent to

  for every `k > 0`, for all sufficiently large `n`,
  `k * min (primeGap n) (primeGap (n - 1)) < (range (n + 1)).sup primeGap`,

i.e. *eventually, no gap that has a neighbour of comparable size is more than a fixed fraction of
the record gap so far* -- with no division, no square, no product, and a single `Finset.sup`,
evaluated at the running index. `erdos_1137_not_tendsto_iff` is the negation, already pushed
through the filter: the obligation fails exactly when for some `k > 0` there are infinitely many `n` with
`(range (n + 1)).sup primeGap ≤ k * min (primeGap n) (primeGap (n - 1))`.

**3. Unbounded prime gaps.** The `←` direction of `criterion_iff_local` has to swallow the
finitely many small indices, and it does so with `maxGap x → ∞`, proved here unconditionally and
from scratch: `exists_lt_primeGap` (for every `b` some prime gap exceeds `b`, via the classical
run of composites `m ! + 2, …, m ! + m` run against `Nat.nth Nat.Prime`) and
`tendsto_maxGap_atTop`, which says that the denominator of the quotient in Erdős 1137 tends to
infinity. To be honest about what is load-bearing: that growth could also have been squeezed out
of the hypothesis of that direction, since every gap is at least `1`; what is proved here is the
*unconditional* statement, which is what tells a solver that the quotient is never of the shape
`bounded / bounded`, and which the pinned Mathlib does not contain in any form. Being
unconditional, it says nothing about whether the criterion of `erdos_1137_tendsto_iff` is
satisfiable -- the satisfiability of that criterion *is* the open problem.

**4. Evaluating the target's own quotient.** `primeGap_eq_of_count` turns two `decide`-checkable
`Nat.count Nat.Prime` facts into the value of `primeGap` at a numeral, and `primeGap_values`
tabulates `d_0, …, d_8 = 1, 2, 2, 4, 2, 4, 2, 4, 6` with it. With that,
`erdos_1137_quotient_four` and `erdos_1137_quotient_nine` compute the sequence appearing in the
target: it equals `1 / 2` at `x = 4` and `2 / 3` at `x = 9`. In particular the sequence is not
antitone (`not_antitone_ratio`), so it cannot be handled by a monotone-convergence argument, and
the sandwich sharpness of part 1 is checked rather than asserted.

A later solver can use declaration `Contribution.Erdos1137AdjacentGaps.erdos_1137_tendsto_iff` to
discharge or simplify obligation
`Tendsto (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
(((range x).sup primeGap : ℕ) : ℝ) ^ 2) atTop (𝓝 0)` in target `Erdos1137.erdos_1137`.
The worked use site is `erdos_1137_true_of_isolated`, whose conclusion is exactly the type of
`Erdos1137.erdos_1137` as it elaborates today (`True ↔ …`), obtained from the local criterion.

Supporting API for the bespoke `primeGap`, all new here: `primeGap_pos`, `nth_prime_succ_eq` (the
recursion `p_{n+1} = p_n + d_n`, which is what lets index arithmetic be done by `omega`),
`le_maxGap` and `maxGap_pos`.
-/

open Filter Finset
open scoped Topology

namespace Contribution.Erdos1137AdjacentGaps

/- ### The three `Finset.sup`s -/

/-- `maxGap x` is the largest prime gap `p_{n+1} - p_n` with `n < x`; this is the (unsquared)
denominator of Erdős problem 1137. -/
noncomputable def maxGap (x : ℕ) : ℕ := (range x).sup primeGap

/-- `maxAdjProd x` is the largest product `d_n * d_{n-1}` of two adjacent prime gaps with `n < x`;
this is the numerator of Erdős problem 1137. Note that the `n = 0` term is `d_0 ^ 2`, since
subtraction on `ℕ` is truncated. -/
noncomputable def maxAdjProd (x : ℕ) : ℕ :=
  (range x).sup fun n ↦ primeGap n * primeGap (n - 1)

/-- `maxAdjMin x` is the largest value of `min (d_n) (d_{n-1})` for `n < x`: the largest gap below
`x` that has a neighbour at least as large. -/
noncomputable def maxAdjMin (x : ℕ) : ℕ :=
  (range x).sup fun n ↦ min (primeGap n) (primeGap (n - 1))

/- ### Basic API for `primeGap` -/

/-- Every prime gap is positive, because `Nat.nth Nat.Prime` is strictly monotone. This is what
keeps the denominator of Erdős 1137 away from `0`. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n :=
  Nat.sub_pos_of_lt (Nat.nth_strictMono Nat.infinite_setOf_prime n.lt_succ_self)

/-- The defining recursion `p_{n+1} = p_n + d_n`, with the truncated subtraction in the definition
of `primeGap` already discharged, so that index arithmetic becomes available to `omega`. -/
theorem nth_prime_succ_eq (n : ℕ) :
    Nat.nth Nat.Prime (n + 1) = Nat.nth Nat.Prime n + primeGap n := by
  have h : Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime (n + 1) :=
    (Nat.nth_strictMono Nat.infinite_setOf_prime n.lt_succ_self).le
  simp only [primeGap]
  omega

/-- **Evaluation interface.** `primeGap` is noncomputable, being defined through `Nat.nth`, but
`Nat.count Nat.Prime` *is* decidable, so a value of `primeGap` at a numeral is certified by two
`decide` calls: `a` and `b` are consecutive primes precisely when `count Nat.Prime a = n` and
`count Nat.Prime b = n + 1`. -/
theorem primeGap_eq_of_count (n a b d : ℕ) (ha : Nat.Prime a) (hb : Nat.Prime b)
    (hca : Nat.count Nat.Prime a = n) (hcb : Nat.count Nat.Prime b = n + 1)
    (hd : a + d = b) : primeGap n = d := by
  have h1 : Nat.nth Nat.Prime n = a := by rw [← hca]; exact Nat.nth_count ha
  have h2 : Nat.nth Nat.Prime (n + 1) = b := by rw [← hcb]; exact Nat.nth_count hb
  simp only [primeGap, h1, h2]
  omega

/-- The first nine prime gaps, each certified by `primeGap_eq_of_count`. -/
theorem primeGap_values :
    primeGap 0 = 1 ∧ primeGap 1 = 2 ∧ primeGap 2 = 2 ∧ primeGap 3 = 4 ∧ primeGap 4 = 2 ∧
      primeGap 5 = 4 ∧ primeGap 6 = 2 ∧ primeGap 7 = 4 ∧ primeGap 8 = 6 :=
  ⟨primeGap_eq_of_count 0 2 3 1 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 1 3 5 2 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 2 5 7 2 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 3 7 11 4 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 4 11 13 2 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 5 13 17 4 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 6 17 19 2 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 7 19 23 4 (by norm_num) (by norm_num) (by decide) (by decide) rfl,
   primeGap_eq_of_count 8 23 29 6 (by norm_num) (by norm_num) (by decide) (by decide) rfl⟩

/- ### Prime gaps are unbounded -/

/-- **Prime gaps are unbounded.** For every `b` there is an `n` with `d_n > b`.

The proof is the classical one: `(b + 2)! + 2, …, (b + 2)! + (b + 2)` are all composite, so the
smallest prime `q` that is at least `(b + 2)! + 2` must exceed `(b + 2)! + 1 + b`, whereas if
every gap were at most `b` then the prime preceding `q` -- which is smaller than `(b + 2)! + 2`
-- would force `q ≤ (b + 2)! + 1 + b`. -/
theorem exists_lt_primeGap (b : ℕ) : ∃ n, b < primeGap n := by
  by_contra hcon
  push_neg at hcon
  have hinf := Nat.infinite_setOf_prime
  have hfac : b + 2 ≤ Nat.factorial (b + 2) := Nat.self_le_factorial _
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.count Nat.Prime (Nat.factorial (b + 2) + 2) := ⟨_, rfl⟩
  have hqN : Nat.factorial (b + 2) + 2 ≤ Nat.nth Nat.Prime c := by
    rw [hc]; exact Nat.le_nth_count hinf _
  have hqp : Nat.Prime (Nat.nth Nat.Prime c) := Nat.nth_mem_of_infinite hinf c
  have hub : Nat.nth Nat.Prime c ≤ Nat.factorial (b + 2) + 1 + b := by
    rcases c with _ | c'
    · rw [Nat.nth_prime_zero_eq_two]; omega
    · have hlt : Nat.nth Nat.Prime c' < Nat.factorial (b + 2) + 2 :=
        Nat.nth_lt_of_lt_count (by omega)
      have hstep := nth_prime_succ_eq c'
      have := hcon c'
      omega
  set q := Nat.nth Nat.Prime c with hq
  obtain ⟨j, hj⟩ : ∃ j, q = Nat.factorial (b + 2) + j := ⟨q - Nat.factorial (b + 2), by omega⟩
  have hdvd : j ∣ q := by
    rw [hj]
    exact Nat.dvd_add (Nat.dvd_factorial (by omega) (by omega)) dvd_rfl
  rcases hqp.eq_one_or_self_of_dvd _ hdvd with h | h <;> omega

theorem le_maxGap {n x : ℕ} (h : n < x) : primeGap n ≤ maxGap x :=
  Finset.le_sup (f := primeGap) (mem_range.mpr h)

theorem maxGap_pos {x : ℕ} (hx : 0 < x) : 0 < maxGap x :=
  lt_of_lt_of_le (primeGap_pos 0) (le_maxGap hx)

/-- **The denominator of Erdős 1137 tends to infinity.** This is unconditional: it is exactly the
statement that prime gaps are unbounded, packaged for the target's denominator. -/
theorem tendsto_maxGap_atTop : Tendsto maxGap atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  obtain ⟨n, hn⟩ := exists_lt_primeGap b
  filter_upwards [eventually_ge_atTop (n + 1)] with x hx
  exact hn.le.trans (le_maxGap (by omega))

/- ### The sandwich -/

/-- **Lower bound for the numerator.** The square of the largest "gap with a large neighbour" is
at most the largest product of adjacent gaps, because `min a b * min a b ≤ a * b`. -/
theorem sq_maxAdjMin_le_maxAdjProd (x : ℕ) : maxAdjMin x ^ 2 ≤ maxAdjProd x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [maxAdjMin, maxAdjProd]
  obtain ⟨k, hk, hks⟩ := Finset.exists_mem_eq_sup (range x) (nonempty_range_iff.mpr hx.ne')
    fun n ↦ min (primeGap n) (primeGap (n - 1))
  have h2 : primeGap k * primeGap (k - 1) ≤ maxAdjProd x :=
    Finset.le_sup (f := fun n ↦ primeGap n * primeGap (n - 1)) hk
  calc maxAdjMin x ^ 2
      = min (primeGap k) (primeGap (k - 1)) * min (primeGap k) (primeGap (k - 1)) := by
        rw [show maxAdjMin x = min (primeGap k) (primeGap (k - 1)) from hks, sq]
    _ ≤ primeGap k * primeGap (k - 1) := Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
    _ ≤ maxAdjProd x := h2

/-- **Upper bound for the numerator.** Each product of adjacent gaps factors as `max * min`, and
the two factors are bounded by `maxGap` and `maxAdjMin` respectively. -/
theorem maxAdjProd_le_maxGap_mul_maxAdjMin (x : ℕ) : maxAdjProd x ≤ maxGap x * maxAdjMin x := by
  refine Finset.sup_le fun n hn ↦ ?_
  have hn' : n < x := mem_range.mp hn
  have hn1 : n - 1 < x := lt_of_le_of_lt (Nat.sub_le n 1) hn'
  have hmin : min (primeGap n) (primeGap (n - 1)) ≤ maxAdjMin x :=
    Finset.le_sup (f := fun n ↦ min (primeGap n) (primeGap (n - 1))) hn
  rcases le_total (primeGap n) (primeGap (n - 1)) with h | h
  · rw [min_eq_left h] at hmin
    calc primeGap n * primeGap (n - 1) ≤ maxAdjMin x * maxGap x :=
          Nat.mul_le_mul hmin (le_maxGap hn1)
      _ = maxGap x * maxAdjMin x := Nat.mul_comm _ _
  · rw [min_eq_right h] at hmin
    exact Nat.mul_le_mul (le_maxGap hn') hmin

/- ### The equivalence -/

/-- The quantity whose limit Erdős 1137 asks about. -/
noncomputable def ratio (x : ℕ) : ℝ := (maxAdjProd x : ℝ) / (maxGap x : ℝ) ^ 2

/-- The proposed replacement: the largest gap having a comparable neighbour, relative to the
largest gap. -/
noncomputable def adjRatio (x : ℕ) : ℝ := (maxAdjMin x : ℝ) / (maxGap x : ℝ)

theorem ratio_le_adjRatio {x : ℕ} (hx : 0 < x) : ratio x ≤ adjRatio x := by
  have hM : (0 : ℝ) < (maxGap x : ℝ) := by exact_mod_cast maxGap_pos hx
  have hP : (maxAdjProd x : ℝ) ≤ (maxGap x : ℝ) * (maxAdjMin x : ℝ) := by
    exact_mod_cast maxAdjProd_le_maxGap_mul_maxAdjMin x
  rw [ratio, adjRatio, div_le_div_iff₀ (by positivity) hM]
  nlinarith [mul_le_mul_of_nonneg_right hP hM.le]

theorem sq_adjRatio_le_ratio (x : ℕ) : adjRatio x ^ 2 ≤ ratio x := by
  have hS : ((maxAdjMin x : ℝ)) ^ 2 ≤ (maxAdjProd x : ℝ) := by
    exact_mod_cast sq_maxAdjMin_le_maxAdjProd x
  rw [adjRatio, div_pow, ratio]
  gcongr

/-- **The main equivalence.** The limit asked about in Erdős 1137 vanishes if and only if the
largest prime gap below `x` having a neighbour of comparable size is `o(maxGap x)`. This is the
step that removes the target's numerator, the `Finset.sup` of the product of two shifted gaps. -/
theorem tendsto_ratio_iff_tendsto_adjRatio :
    Tendsto ratio atTop (𝓝 0) ↔ Tendsto adjRatio atTop (𝓝 0) := by
  constructor
  · intro h
    have hsq : Tendsto (fun x ↦ Real.sqrt (ratio x)) atTop (𝓝 0) := by
      simpa using h.sqrt
    refine squeeze_zero' (.of_forall fun x ↦ by simp only [adjRatio]; positivity)
      (.of_forall fun x ↦ ?_) hsq
    calc adjRatio x
        = Real.sqrt (adjRatio x ^ 2) := (Real.sqrt_sq (by simp only [adjRatio]; positivity)).symm
      _ ≤ Real.sqrt (ratio x) := Real.sqrt_le_sqrt (sq_adjRatio_le_ratio x)
  · intro h
    refine squeeze_zero' (.of_forall fun x ↦ by simp only [ratio]; positivity) ?_ h
    filter_upwards [eventually_gt_atTop 0] with x hx using ratio_le_adjRatio hx

/-- **Removing the reals.** The replacement limit is a statement about natural numbers only. -/
theorem tendsto_adjRatio_iff :
    Tendsto adjRatio atTop (𝓝 0) ↔
      ∀ k : ℕ, 0 < k → ∀ᶠ x in atTop, k * maxAdjMin x < maxGap x := by
  constructor
  · intro h k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    filter_upwards [h.eventually_lt_const (one_div_pos.mpr hkR), eventually_gt_atTop 0]
      with x hx1 hx2
    have hM : (0 : ℝ) < (maxGap x : ℝ) := by exact_mod_cast maxGap_pos hx2
    rw [adjRatio, div_lt_div_iff₀ hM hkR] at hx1
    have : (k : ℝ) * (maxAdjMin x : ℝ) < (maxGap x : ℝ) := by linarith
    exact_mod_cast this
  · intro h
    rw [NormedAddCommGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    filter_upwards [h (k + 1) k.succ_pos, eventually_gt_atTop 0] with x hx1 hx2
    have hM : (0 : ℝ) < (maxGap x : ℝ) := by exact_mod_cast maxGap_pos hx2
    have hkR : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
    have hx1' : ((k : ℝ) + 1) * (maxAdjMin x : ℝ) < (maxGap x : ℝ) := by exact_mod_cast hx1
    have hlt : adjRatio x < 1 / ((k : ℝ) + 1) := by
      rw [adjRatio, div_lt_div_iff₀ hM hkR]
      linarith
    have h0 : (0 : ℝ) ≤ adjRatio x := by simp only [adjRatio]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    linarith

/-- **Removing the sup from `maxAdjMin`.** For `x > 0` the criterion of `tendsto_adjRatio_iff`
says exactly that no two adjacent gaps below `x` are both at least `maxGap x / k`. -/
theorem nat_criterion_iff {x : ℕ} (hx : 0 < x) (k : ℕ) :
    k * maxAdjMin x < maxGap x ↔
      ∀ n < x, k * min (primeGap n) (primeGap (n - 1)) < maxGap x := by
  constructor
  · intro h n hn
    exact lt_of_le_of_lt (Nat.mul_le_mul_left k
      (Finset.le_sup (f := fun n ↦ min (primeGap n) (primeGap (n - 1))) (mem_range.mpr hn))) h
  · intro h
    obtain ⟨k₀, hk₀, hk₀s⟩ := Finset.exists_mem_eq_sup (range x) (nonempty_range_iff.mpr hx.ne')
      fun n ↦ min (primeGap n) (primeGap (n - 1))
    rw [show maxAdjMin x = min (primeGap k₀) (primeGap (k₀ - 1)) from hk₀s]
    exact h k₀ (mem_range.mp hk₀)

/-- **Localisation.** The uniform criterion (compare every `n < x` with the record gap below `x`,
for all large `x`) is equivalent to the local one (compare `n` with the record gap below `n + 1`,
for all large `n`). The `←` direction is where `tendsto_maxGap_atTop` is used: the finitely many
small indices are swallowed only because the record gap really does grow without bound. -/
theorem criterion_iff_local :
    (∀ k : ℕ, 0 < k → ∀ᶠ x in atTop, k * maxAdjMin x < maxGap x) ↔
      ∀ k : ℕ, 0 < k → ∀ᶠ n in atTop,
        k * min (primeGap n) (primeGap (n - 1)) < maxGap (n + 1) := by
  have hmono : ∀ {a b : ℕ}, a ≤ b → maxGap a ≤ maxGap b := fun h ↦
    Finset.sup_mono (Finset.range_subset_range.mpr h)
  constructor
  · intro h k hk
    filter_upwards [(tendsto_add_atTop_nat 1).eventually (h k hk)] with n hn
    refine lt_of_le_of_lt (Nat.mul_le_mul_left k ?_) hn
    exact Finset.le_sup (f := fun n ↦ min (primeGap n) (primeGap (n - 1)))
      (mem_range.mpr n.lt_succ_self)
  · intro h k hk
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h k hk)
    filter_upwards [tendsto_atTop.mp tendsto_maxGap_atTop (k * maxAdjMin (N + 1) + 1),
      eventually_gt_atTop 0] with x hB hx0
    refine (nat_criterion_iff hx0 k).mpr fun n hn ↦ ?_
    rcases lt_or_ge n N with h1 | h1
    · have : k * min (primeGap n) (primeGap (n - 1)) ≤ k * maxAdjMin (N + 1) :=
        Nat.mul_le_mul_left k (Finset.le_sup
          (f := fun n ↦ min (primeGap n) (primeGap (n - 1))) (mem_range.mpr (by omega)))
      omega
    · exact lt_of_lt_of_le (hN n h1) (hmono (by omega))

/-- **The handoff.** The obligation of `Erdos1137.erdos_1137` is equivalent to a local,
division-free statement about adjacent prime gaps: for every `k > 0`, every sufficiently large `n`
has the property that the smaller of the two gaps `d_n`, `d_{n-1}` is less than `1 / k` of the
largest gap seen up to `n`. -/
theorem erdos_1137_tendsto_iff :
    Tendsto (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
        (((range x).sup primeGap : ℕ) : ℝ) ^ 2) atTop (𝓝 0) ↔
      ∀ k : ℕ, 0 < k → ∀ᶠ n in atTop,
        k * min (primeGap n) (primeGap (n - 1)) < (range (n + 1)).sup primeGap := by
  have hfun : (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
      (((range x).sup primeGap : ℕ) : ℝ) ^ 2) = ratio := rfl
  rw [hfun, tendsto_ratio_iff_tendsto_adjRatio, tendsto_adjRatio_iff, criterion_iff_local]
  rfl

/-- **The refutation route.** The negation of the target obligation, with the filter quantifiers
already pushed through: a single `k` together with infinitely many indices at which two adjacent
gaps are both at least a `1 / k` fraction of the record gap so far. -/
theorem erdos_1137_not_tendsto_iff :
    (¬ Tendsto (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
        (((range x).sup primeGap : ℕ) : ℝ) ^ 2) atTop (𝓝 0)) ↔
      ∃ k : ℕ, 0 < k ∧ ∃ᶠ n in atTop,
        (range (n + 1)).sup primeGap ≤ k * min (primeGap n) (primeGap (n - 1)) := by
  rw [erdos_1137_tendsto_iff, not_forall]
  constructor
  · rintro ⟨k, hk⟩
    rw [_root_.not_imp] at hk
    refine ⟨k, hk.1, ?_⟩
    rw [Filter.not_eventually] at hk
    exact hk.2.mono fun n hn ↦ not_lt.mp hn
  · rintro ⟨k, hk0, hk1⟩
    refine ⟨k, ?_⟩
    rw [_root_.not_imp, Filter.not_eventually]
    exact ⟨hk0, hk1.mono fun n hn ↦ not_lt.mpr hn⟩

/- ### Checked values of the target's own quotient -/

/-- The quotient of Erdős 1137 at `x = 4`: the gaps `1, 2, 2, 4` give numerator
`sup {1, 2, 4, 8} = 8` and denominator `4 ^ 2 = 16`. -/
theorem erdos_1137_quotient_four :
    (((range 4).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
      (((range 4).sup primeGap : ℕ) : ℝ) ^ 2 = 1 / 2 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := primeGap_values
  have hnum : ((range 4).sup fun n ↦ primeGap n * primeGap (n - 1)) = 8 := by
    simp [Finset.range_add_one, h0, h1, h2, h3]
  have hden : (range 4).sup primeGap = 4 := by
    simp [Finset.range_add_one, h0, h1, h2, h3]
  rw [hnum, hden]
  norm_num

/-- The quotient of Erdős 1137 at `x = 9`: the gaps `1, 2, 2, 4, 2, 4, 2, 4, 6` give numerator
`6 * 4 = 24` and denominator `6 ^ 2 = 36`. -/
theorem erdos_1137_quotient_nine :
    (((range 9).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
      (((range 9).sup primeGap : ℕ) : ℝ) ^ 2 = 2 / 3 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := primeGap_values
  have hnum : ((range 9).sup fun n ↦ primeGap n * primeGap (n - 1)) = 24 := by
    simp [Finset.range_add_one, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have hden : (range 9).sup primeGap = 6 := by
    simp [Finset.range_add_one, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  rw [hnum, hden]
  norm_num

/-- The sequence whose limit Erdős 1137 asks about is **not** antitone: it takes the value `1 / 2`
at `x = 4` and the larger value `2 / 3` at `x = 9`. So no monotone-convergence argument applies,
and the conjectured decay is not visible at the start of the sequence. -/
theorem not_antitone_ratio : ¬ Antitone ratio := by
  intro h
  have h49 : ratio 9 ≤ ratio 4 := h (by norm_num)
  rw [show ratio 9 = 2 / 3 from erdos_1137_quotient_nine,
    show ratio 4 = 1 / 2 from erdos_1137_quotient_four] at h49
  norm_num at h49

/-- **The sandwich is sharp at both ends.** At `x = 4` the lower bound
`sq_maxAdjMin_le_maxAdjProd` is strict (`2 ^ 2 = 4 < 8`), so the two bounds are not the same
statement and the `Real.sqrt` step in `tendsto_ratio_iff_tendsto_adjRatio` cannot be avoided;
and the upper bound `maxAdjProd_le_maxGap_mul_maxAdjMin` is attained (`8 = 4 * 2`), so its
constant `1` cannot be lowered. -/
theorem sandwich_sharp_at_four :
    maxAdjMin 4 ^ 2 < maxAdjProd 4 ∧ maxAdjProd 4 = maxGap 4 * maxAdjMin 4 := by
  obtain ⟨h0, h1, h2, h3, -⟩ := primeGap_values
  have hmin : maxAdjMin 4 = 2 := by
    simp [maxAdjMin, Finset.range_add_one, h0, h1, h2, h3]
  have hprod : maxAdjProd 4 = 8 := by
    simp [maxAdjProd, Finset.range_add_one, h0, h1, h2, h3]
  have hgap : maxGap 4 = 4 := by
    simp [maxGap, Finset.range_add_one, h0, h1, h2, h3]
  rw [hmin, hprod, hgap]
  norm_num

/- ### Worked use site -/

/-- **Worked use site.** Feeding the local criterion to `erdos_1137_tendsto_iff` produces exactly
the type of `Erdos1137.erdos_1137` as it elaborates in this repository, namely `True ↔ Tendsto …`.
-/
theorem erdos_1137_true_of_isolated
    (H : ∀ k : ℕ, 0 < k → ∀ᶠ n in atTop,
      k * min (primeGap n) (primeGap (n - 1)) < (range (n + 1)).sup primeGap) :
    True ↔ Tendsto (fun x ↦ (((range x).sup fun n ↦ primeGap n * primeGap (n - 1) : ℕ) : ℝ) /
      (((range x).sup primeGap : ℕ) : ℝ) ^ 2) atTop (𝓝 0) :=
  iff_of_true trivial (erdos_1137_tendsto_iff.mpr H)

end Contribution.Erdos1137AdjacentGaps
