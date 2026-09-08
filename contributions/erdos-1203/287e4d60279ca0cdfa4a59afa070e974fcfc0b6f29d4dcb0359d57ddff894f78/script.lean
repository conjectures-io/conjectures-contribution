import FormalConjectures.ErdosProblems.«1203»

/-!
# Erdős 1203: making `F` a genuine supremum, and bracketing it between `1` and `∞`

A contribution towards `Erdos1203.erdos_1203`
([erdosproblems.com/1203](https://www.erdosproblems.com/1203)), which asks whether
`F n = ⨆ k, ω (n + k) * (log (log k) / log k)` tends to infinity.

## The obstacle

`Erdos1203.F` is an `iSup` of a family of reals indexed by `ℕ`. `ℝ` is only a
*conditionally* complete lattice: `Real.iSup_of_not_bddAbove` says that `⨆` collapses to `0`
as soon as the family is unbounded above. Consequently **every lower bound on `F n`** — and
`Tendsto F atTop atTop` is a family of lower bounds — has to be routed through `le_ciSup`,
whose side condition is

`BddAbove (Set.range fun k => (ω (n + k) : ℝ) * (Real.log (Real.log k) / Real.log k))`.

Discharging that side condition is not bookkeeping: it is exactly the classical *maximal order
of `ω`*. Terms with `n + k` a primorial and `k` comparable to `n + k` have size `≍ 1`, so
boundedness genuinely needs `ω m ≪ log m / log log m`. The `ω` API of the pinned Mathlib
(`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean`) consists of exact-value lemmas
(`cardDistinctFactors_apply_prime`, `cardDistinctFactors_mul`, `cardDistinctFactors_prod`, …)
and contains no inequality bounding `ω m` in terms of `m`; grepping the whole library for a
bound on `Nat.primeFactors.card` also returns nothing. So the bound is built from scratch
here, with an explicit (crude) constant.

## What is proved here

Effective maximal order of `ω`, from scratch:

* `factorial_card_succ_le_prod`: for a finset `S` of naturals all `≥ 2`,
  `(S.card + 1)! ≤ ∏ p ∈ S, p`. (Attained: `S = {2, 3}` gives `3! = 6 = 2 * 3`.)
* `factorial_omega_succ_le`: hence `(ω m + 1)! ≤ m` for `m ≠ 0`, with equality at `m = 1, 2, 6`.
* `mul_log_div_le`: the analytic core. If `2 ≤ t` and `R * log R ≤ 2 * t` then
  `(2 * R + 1) * (log t / t) ≤ 12`, by splitting on `R ≤ √t`.
* `omega_mul_ratio_le`: combining the two, `ω m * (log (log k) / log k) ≤ 12` whenever
  `8 ≤ k` and `m ≤ 2 * k`.
* `cardDistinctFactors_mul_log_log_le`: the special case `m = k`, i.e. the effective maximal
  order `ω m * log (log m) ≤ 12 * log m` for `8 ≤ m`. Only the constant `12` is lossy here
  (the truth is `(1 + o(1)) * log m / log log m`); no attempt at sharpness is made.

The supremum API this buys for the target:

* `bddAbove_range`: the `⨆` is a genuine supremum. `le_F` and `F_le` are its two one-line
  consequences (`le_ciSup`, `ciSup_le`), recorded because every downstream argument needs them;
  they give the explicit envelope `F n ≤ 2 * n + 20`.
* `le_F_of_subset_primeFactors`: the practical lower-bound handle — exhibit primes dividing
  `n + k`.

Both halves of what is unconditionally known about `F`, proved:

* `one_le_F`: **`1 ≤ F n` for every `n`**, by taking `n + k` in the residue class `0 mod 510510`
  with `2 ^ 18 < k ≤ 2 ^ 20`. Hence `variants_lower_bound`, which is the companion
  `Erdos1203.erdos_1203.variants.lower_bound` of the target module (left unproved there),
  discharged outright and in the stronger uniform form.
* `frequently_le_F`, `not_bddAbove_range_F`: **`F` is unbounded**, indeed `C ≤ F n` for
  arbitrarily large `n`, for every `C`. This is the `limsup` half of the open problem, and it
  is elementary: `omega_shift_le_F` gives `ω (n + 16) / 3 ≤ F n`, and
  `exists_cardDistinctFactors_eq` produces integers with prescribed `ω`.

So the open problem is exactly the gap between these two: the `liminf` of `F` is known to lie in
`[1, ∞]` and the question is whether it is `∞`.

Reformulations with no supremum in them:

* `tendsto_atTop_iff`, `tendsto_atTop_iff_primeFactors`: two `Iff`s, so neither direction is
  lost. The second is in the shape a number theorist verifies ("for every `C`, all large `n`
  have a nearby integer with many prime factors").
* `multiplied_out_vacuous`: a checked warning that the *unrestricted* multiplied-out shape
  `C * log k ≤ ω (n + k) * log (log k)` is a theorem, hence useless as a reformulation. Its
  proof is one line; the statement, not the proof, is the content.

## Verification

The file compiles with no errors and no warnings, and every theorem in it was checked to
depend only on `propext`, `Classical.choice` and `Quot.sound` — in particular nothing here
leans on the unproved `Erdos1203.erdos_1203` or `Erdos1203.erdos_1203.variants.lower_bound`
of the imported module. That check matters for `variants_lower_bound`: since the imported
module *declares* `Erdos1203.erdos_1203.variants.lower_bound` (without proving it), `exact?`
reports that statement as closable — by the very declaration this file is meant to supply a
proof for. The dependency check is what distinguishes the two.

## Handoff

A later solver can use declaration `Contribution.Erdos1203OmegaSup.bddAbove_range` to discharge
obligation `BddAbove (Set.range fun k => (ω (n + k) : ℝ) * (Real.log (Real.log k) / Real.log k))`
in target `Erdos1203.erdos_1203`. That obligation is the side condition of `le_ciSup`, and it
guards every lower bound on `Erdos1203.F n`, hence every route to the conclusion
`Tendsto Erdos1203.F atTop atTop`.

Likewise, a later solver can use declaration `Contribution.Erdos1203OmegaSup.one_le_F` to
discharge obligation `∀ ε > 0, ∀ᶠ n in atTop, Erdos1203.F n ≥ 1 - ε` in target
`Erdos1203.erdos_1203.variants.lower_bound`; `variants_lower_bound` below is that one-line
derivation, so that companion is completely settled.

After the supremum is under control, `tendsto_atTop_iff_primeFactors` replaces the goal
`Tendsto Erdos1203.F atTop atTop` by an equivalent statement about prime factors of `n + k`,
and `frequently_le_F` says that any counterexample must be a genuine exceptional set: `F`
already exceeds every constant infinitely often. The division in the ratio must be kept:
`Real.log 1 = 0` and `x / 0 = 0` in Lean, so the `k = 1` term of the family is `0` and the
multiplied-out form is satisfied by `k = 1` for every `C` and every `n`; that trap is recorded
as `multiplied_out_vacuous`, which is why `tendsto_atTop_iff_primeFactors` carries `3 ≤ k`.
-/

open Filter Real
open scoped ArithmeticFunction.omega

namespace Contribution.Erdos1203OmegaSup

/- ### The combinatorial input: a factorial lower bound for products of primes -/

/-- A finset of naturals all of which are `≥ 2` has product at least `(card + 1)!`.
The bound is attained: `S = {2, 3}` gives `3! = 6 = 2 * 3`. -/
theorem factorial_card_succ_le_prod :
    ∀ (S : Finset ℕ), (∀ p ∈ S, 2 ≤ p) → Nat.factorial (S.card + 1) ≤ ∏ p ∈ S, p := by
  intro S
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    intro hS
    have hans : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h2 : ∀ x ∈ s, 2 ≤ x := fun x hx => hS x (Finset.mem_insert_of_mem hx)
    have hsub : s ⊆ Finset.Ico 2 a := by
      intro x hx
      simp only [Finset.mem_Ico]
      exact ⟨h2 x hx, ha x hx⟩
    have hcard : s.card + 2 ≤ a := by
      have hle := Finset.card_le_card hsub
      simp only [Nat.card_Ico] at hle
      have h2a : 2 ≤ a := hS a (Finset.mem_insert_self a s)
      omega
    rw [Finset.prod_insert hans, Finset.card_insert_of_notMem hans]
    calc Nat.factorial (s.card + 1 + 1) = (s.card + 2) * Nat.factorial (s.card + 1) := by
          rw [Nat.factorial_succ]
      _ ≤ a * ∏ p ∈ s, p := Nat.mul_le_mul hcard (ih h2)

/-- If `m ≠ 0` then `(ω m + 1)! ≤ m`, where `ω` counts distinct prime factors.
This is the quantitative form of "a number with many distinct prime factors is large";
equality holds at `m = 1`, `m = 2` and `m = 6`. -/
theorem factorial_omega_succ_le {m : ℕ} (hm : m ≠ 0) : Nat.factorial (ω m + 1) ≤ m := by
  rw [show ω m = m.primeFactors.card from rfl]
  refine le_trans (factorial_card_succ_le_prod _ ?_) ?_
  · exact fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

/- ### The analytic core -/

/-- The analytic heart of the boundedness proof: a growth constraint of the shape
`R * log R ≤ 2 * t` forces `R` to be `O (t / log t)`, hence `R * (log t / t)` to be bounded.
The split is on `R ≤ √t` (where `log t / √t ≤ 2` does the work) versus `R > √t` (where
`log R > (log t) / 2` does). -/
theorem mul_log_div_le {t R : ℝ} (ht : 2 ≤ t) (h : R * Real.log R ≤ 2 * t) :
    (2 * R + 1) * (Real.log t / t) ≤ 12 := by
  have htpos : (0 : ℝ) < t := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlt' : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htpos
  rw [mul_div_assoc', div_le_iff₀ htpos]
  set S := Real.sqrt t with hSdef
  have hSsq : S ^ 2 = t := Real.sq_sqrt htpos.le
  have hSpos : 0 < S := Real.sqrt_pos.mpr htpos
  have hS1 : 1 ≤ S := by
    rw [hSdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hlogS : Real.log S = Real.log t / 2 := Real.log_sqrt htpos.le
  have hlogS' : Real.log S ≤ S - 1 := Real.log_le_sub_one_of_pos hSpos
  rcases le_or_gt R S with hc | hc
  · have h1 : (2 * R + 1) * Real.log t ≤ (2 * S + 1) * Real.log t := by
      apply mul_le_mul_of_nonneg_right _ hlt.le
      linarith
    nlinarith [hlt.le, hSpos.le]
  · have hlogR : Real.log S < Real.log R := Real.log_lt_log hSpos hc
    have hR1 : 1 ≤ R := le_trans hS1 hc.le
    have hRpos : 0 < R := by linarith
    have h2 : R * (Real.log t / 2) < R * Real.log R := by
      apply mul_lt_mul_of_pos_left _ hRpos
      linarith
    have h3 : R * Real.log t < 4 * t := by linarith
    nlinarith [hlt.le]

/-- Numerical helper: `2 ≤ log k` as soon as `8 ≤ k`, since `log 8 = 3 log 2 > 2.079`. -/
theorem two_le_log_natCast {k : ℕ} (hk : 8 ≤ k) : 2 ≤ Real.log k := by
  have h8 : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hmono : Real.log 8 ≤ Real.log k := Real.log_le_log (by norm_num) h8
  have h83 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  linarith

/-- The uniform bound behind boundedness of the family defining `Erdos1203.F`:
if `8 ≤ k` and `m ≤ 2 * k` then `ω m * (log (log k) / log k) ≤ 12`.
The proof runs `(ω m + 1)! ≤ m` through `r ^ r ≤ (2 * r)!` with `r = ω m / 2`, and feeds the
resulting `r * log r ≤ 2 * log k` to `mul_log_div_le`. -/
theorem omega_mul_ratio_le {m k : ℕ} (hk : 8 ≤ k) (hmk : m ≤ 2 * k) :
    (ω m : ℝ) * (Real.log (Real.log k) / Real.log k) ≤ 12 := by
  have ht : 2 ≤ Real.log k := two_le_log_natCast hk
  have htpos : (0 : ℝ) < Real.log k := by linarith
  have hratio : 0 ≤ Real.log (Real.log k) / Real.log k := by
    exact div_nonneg (Real.log_nonneg (by linarith)) htpos.le
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set j := ω m with hj
  set r := j / 2 with hr
  have hfac : Nat.factorial (j + 1) ≤ m := factorial_omega_succ_le (by omega)
  have hrr : r ^ r ≤ 2 * k := by
    have hstep := Nat.factorial_mul_pow_le_factorial (m := r) (n := r)
    calc r ^ r ≤ (r + 1) ^ r := Nat.pow_le_pow_left (by omega) r
      _ ≤ Nat.factorial r * (r + 1) ^ r := Nat.le_mul_of_pos_left _ (Nat.factorial_pos r)
      _ ≤ Nat.factorial (r + r) := hstep
      _ = Nat.factorial (2 * r) := by ring_nf
      _ ≤ Nat.factorial (j + 1) := Nat.factorial_le (by omega)
      _ ≤ m := hfac
      _ ≤ 2 * k := hmk
  have hcast : ((r : ℝ)) ^ r ≤ 2 * (k : ℝ) := by exact_mod_cast hrr
  have hRlog : (r : ℝ) * Real.log r ≤ 2 * Real.log k := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
      linarith
    · have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h0
      have hpow : (0 : ℝ) < (r : ℝ) ^ r := pow_pos hrpos r
      have hlog := Real.log_le_log hpow hcast
      rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity)] at hlog
      have hlog2 : Real.log 2 ≤ Real.log k := by
        refine Real.log_le_log (by norm_num) ?_
        have : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith
      linarith
  have hjr : (j : ℝ) ≤ 2 * (r : ℝ) + 1 := by
    have : j ≤ 2 * r + 1 := by omega
    exact_mod_cast this
  calc (j : ℝ) * (Real.log (Real.log k) / Real.log k)
      ≤ (2 * (r : ℝ) + 1) * (Real.log (Real.log k) / Real.log k) :=
        mul_le_mul_of_nonneg_right hjr hratio
    _ ≤ 12 := mul_log_div_le ht hRlog

/-- An effective form of the maximal order of `ω`: for `8 ≤ m`,
`ω m * log (log m) ≤ 12 * log m`, i.e. `ω m ≤ 12 * log m / log (log m)`.
The constant `12` is crude — the truth is `(1 + o(1)) * log m / log log m` — but it is explicit
and unconditional. -/
theorem cardDistinctFactors_mul_log_log_le {m : ℕ} (hm : 8 ≤ m) :
    (ω m : ℝ) * Real.log (Real.log m) ≤ 12 * Real.log m := by
  have h := omega_mul_ratio_le (m := m) (k := m) hm (by omega)
  have ht : 2 ≤ Real.log m := two_le_log_natCast hm
  rw [mul_div_assoc', div_le_iff₀ (by linarith)] at h
  linarith

/- ### The supremum API for `Erdos1203.F` -/

/-- Every term of the family defining `Erdos1203.F n` is at most `2 * n + 20`. -/
theorem term_le (n k : ℕ) :
    (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) ≤ 2 * (n : ℝ) + 20 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases le_or_gt k (max 8 n) with hk | hk
  · have hlk : 0 ≤ Real.log (k : ℝ) := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · simp [h0]
      · exact Real.log_nonneg (by exact_mod_cast h0)
    have hratio : Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) ≤ 1 := by
      rcases eq_or_lt_of_le hlk with h | h
      · rw [← h]; simp
      · rw [div_le_one h]
        linarith [Real.log_le_sub_one_of_pos h]
    have homega : (ω (n + k) : ℝ) ≤ 2 * (n : ℝ) + 20 := by
      have h1 : ω (n + k) ≤ n + k := by
        rcases Nat.eq_zero_or_pos (n + k) with h0 | h0
        · simp [h0]
        · have hf := factorial_omega_succ_le (m := n + k) (by omega)
          have h2 := Nat.self_le_factorial (ω (n + k) + 1)
          omega
      have h3 : k ≤ 8 + n := by omega
      have h4 : (ω (n + k) : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h4
      have hkr : (k : ℝ) ≤ 8 + (n : ℝ) := by exact_mod_cast h3
      linarith
    calc (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))
        ≤ (ω (n + k) : ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg _) hratio
      _ ≤ 2 * (n : ℝ) + 20 := homega
  · have h := omega_mul_ratio_le (m := n + k) (k := k) (by omega) (by omega)
    linarith

/-- **The obligation this file exists to discharge.** The family whose supremum defines
`Erdos1203.F n` is bounded above, so the `⨆` really is a supremum and not the junk value `0`.
This is the side condition of `le_ciSup`. -/
theorem bddAbove_range (n : ℕ) :
    BddAbove (Set.range fun k : ℕ =>
      (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
  refine ⟨2 * (n : ℝ) + 20, ?_⟩
  rintro x ⟨k, rfl⟩
  exact term_le n k

/-- Each term of the defining family bounds `Erdos1203.F n` from below. This is `le_ciSup`
with its side condition discharged, and is the entry point for every lower bound on `F`. -/
theorem le_F (n k : ℕ) :
    (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) ≤ Erdos1203.F n :=
  le_ciSup (bddAbove_range n) k

/-- `Erdos1203.F n` is finite, with the explicit envelope `F n ≤ 2 * n + 20`. -/
theorem F_le (n : ℕ) : Erdos1203.F n ≤ 2 * (n : ℝ) + 20 :=
  ciSup_le (term_le n)

/-- The practical lower-bound handle: exhibiting a finset `S` of primes dividing `n + k`
bounds `F n` below. The hypothesis `3 ≤ k` rules out exactly the one shift at which the ratio
`log (log k) / log k` is negative, namely `k = 2` (there `log k ∈ (0, 1)`); at `k = 0` and
`k = 1` the ratio is `0 / 0 = 0`. -/
theorem le_F_of_subset_primeFactors (n k : ℕ) (S : Finset ℕ)
    (hS : S ⊆ (n + k).primeFactors) (hk : 3 ≤ k) :
    (S.card : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) ≤ Erdos1203.F n := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : (1 : ℝ) ≤ Real.log (k : ℝ) := le_trans hlog3 (Real.log_le_log (by norm_num) hk3)
  have hratio : 0 ≤ Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) :=
    div_nonneg (Real.log_nonneg h1) (by linarith)
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hratio) (le_F n k)
  have hcard : S.card ≤ (n + k).primeFactors.card := Finset.card_le_card hS
  rw [show ω (n + k) = (n + k).primeFactors.card from rfl]
  exact_mod_cast hcard

/- ### The `liminf` half: `1 ≤ F n` for every `n` -/

/-- **`1 ≤ F n` for every `n`.** Choose `k = 2 * 510510 - n % 510510`, so that
`510510 = 2 * 3 * 5 * 7 * 11 * 13 * 17` divides `n + k` and `2 ^ 18 < k ≤ 2 ^ 20`. Then
`ω (n + k) ≥ 7`, `log (log k) ≥ 3 log 2` and `log k ≤ 20 log 2`, and `7 * 3 ≥ 20`. -/
theorem one_le_F (n : ℕ) : 1 ≤ Erdos1203.F n := by
  set k : ℕ := 2 * 510510 - n % 510510 with hkdef
  have hk1 : 510511 ≤ k := by omega
  have hdvd : (510510 : ℕ) ∣ n + k := ⟨n / 510510 + 2, by omega⟩
  have hsub : ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ) ⊆ (n + k).primeFactors := by
    intro p hp
    fin_cases hp <;>
      exact Nat.mem_primeFactors.mpr ⟨by norm_num, dvd_trans (by norm_num) hdvd, by omega⟩
  have hcardN : ({2, 3, 5, 7, 11, 13, 17} : Finset ℕ).card = 7 := by decide
  have hcard : (({2, 3, 5, 7, 11, 13, 17} : Finset ℕ).card : ℝ) = 7 := by
    rw [hcardN]; norm_num
  have key := le_F_of_subset_primeFactors n k _ hsub (by omega)
  rw [hcard] at key
  refine le_trans ?_ key
  have hlog2 := Real.log_two_gt_d9
  have hkr1 : ((262144 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (262144 : ℕ) ≤ k)
  have hkr2 : (k : ℝ) ≤ ((1048576 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : k ≤ 1048576)
  have hlk1 : (18 : ℝ) * Real.log 2 ≤ Real.log (k : ℝ) := by
    have e1 : Real.log ((262144 : ℕ) : ℝ) = 18 * Real.log 2 := by
      rw [show ((262144 : ℕ) : ℝ) = 2 ^ (18 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [← e1]
    exact Real.log_le_log (by norm_num) hkr1
  have hlk2 : Real.log (k : ℝ) ≤ 20 * Real.log 2 := by
    have e1 : Real.log ((1048576 : ℕ) : ℝ) = 20 * Real.log 2 := by
      rw [show ((1048576 : ℕ) : ℝ) = 2 ^ (20 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [← e1]
    refine Real.log_le_log ?_ hkr2
    have : (510511 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hll : 3 * Real.log 2 ≤ Real.log (Real.log (k : ℝ)) := by
    have h8 : (8 : ℝ) ≤ Real.log (k : ℝ) := by linarith
    have e1 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [← e1]
    exact Real.log_le_log (by norm_num) h8
  have hpos : 0 < Real.log (k : ℝ) := by linarith
  rw [mul_div_assoc', le_div_iff₀ hpos]
  linarith

/-- The companion `Erdos1203.erdos_1203.variants.lower_bound` of the target module
(left unproved there), discharged outright -- indeed in the stronger uniform form `1 ≤ F n`
for *all* `n`, not merely eventually and not merely up to `ε`. -/
theorem variants_lower_bound : ∀ ε > 0, ∀ᶠ n in atTop, Erdos1203.F n ≥ 1 - ε := by
  intro ε _
  filter_upwards with n
  linarith [one_le_F n]

/- ### The `limsup` half: `F` is unbounded -/

/-- `1 / 3 ≤ log (log 16) / log 16`; the true value is `≈ 0.3678`. Over `t > 1` the function
`log (log t) / log t` is maximised at `t = exp (exp 1) ≈ 15.15` (its derivative in `L = log t`
is `(1 - log L) / L ^ 2`), so no integer shift beats `16` by more than a fraction of a percent;
`16` is used rather than `15` because `log 16 = 4 * log 2` keeps the numerics inside the
rational bounds `Real.log_two_gt_d9` and `Real.log_two_lt_d9`. -/
theorem one_third_le_ratio_sixteen : (1 : ℝ) / 3 ≤ Real.log (Real.log 16) / Real.log 16 := by
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlb := Real.log_two_gt_d9
  have hub := Real.log_two_lt_d9
  have hL : (2.7725887 : ℝ) ≤ Real.log 16 := by rw [h2]; linarith
  have hL' : Real.log 16 ≤ 2.7725888 := by rw [h2]; linarith
  have hhalf : Real.log 16 / 2 = 2 * Real.log 2 := by rw [h2]; ring
  have hsplit : Real.log (Real.log 16) = Real.log 2 + Real.log (Real.log 16 / 2) := by
    rw [← Real.log_mul (by norm_num) (by rw [hhalf]; positivity)]
    congr 1
    field_simp
  have hpos : (0 : ℝ) < Real.log 16 / 2 := by rw [hhalf]; positivity
  have hinv : 1 - (Real.log 16 / 2)⁻¹ ≤ Real.log (Real.log 16 / 2) :=
    Real.one_sub_inv_le_log_of_pos hpos
  rw [hhalf] at hinv
  have hkey : (0.97 : ℝ) ≤ Real.log (Real.log 16) := by
    rw [hsplit, hhalf]
    have hinv2 : (2 * Real.log 2)⁻¹ ≤ 0.7213476 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- A single shift already forces `F` up: `ω (n + 16) / 3 ≤ F n` for every `n`.
This is just the `k = 16` term of the defining family, kept honest by `bddAbove_range`; the
shift `16` is chosen by `one_third_le_ratio_sixteen`. -/
theorem omega_shift_le_F (n : ℕ) : (ω (n + 16) : ℝ) / 3 ≤ Erdos1203.F n := by
  have h := le_F n 16
  simp only [Nat.cast_ofNat] at h
  refine le_trans ?_ h
  have hw : (0 : ℝ) ≤ (ω (n + 16) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left one_third_le_ratio_sixteen hw
  linarith

/-- Integers with prescribed `ω` exist, and can be taken large: for every `j` there is
`m ≥ 2 ^ j` with `ω m = j`, namely a product of `j` distinct primes. -/
theorem exists_cardDistinctFactors_eq (j : ℕ) : ∃ m : ℕ, 2 ^ j ≤ m ∧ ω m = j := by
  obtain ⟨S, hSsub, hScard⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq j
  have hprime : ∀ p ∈ S, Nat.Prime p := fun p hp => hSsub (Finset.mem_coe.mpr hp)
  refine ⟨∏ p ∈ S, p, ?_, ?_⟩
  · calc (2 : ℕ) ^ j = 2 ^ S.card := by rw [hScard]
      _ ≤ ∏ p ∈ S, p := Finset.pow_card_le_prod S id 2 (fun x hx => (hprime x hx).two_le)
  · rw [show ω (∏ p ∈ S, p) = (∏ p ∈ S, p).primeFactors.card from rfl,
      Nat.primeFactors_prod hprime, hScard]

/-- **`F` exceeds every constant arbitrarily late.** For every `C` and every `N` there is
`n ≥ N` with `C ≤ F n`: take `n = m - 16` where `m` is a product of more than `3 * C` distinct
primes. Together with `one_le_F` this brackets what is unconditionally known about `F`, and it
shows that a negative answer to the target would require a genuine exceptional set rather than
an eventual bound. -/
theorem exists_le_F (C : ℝ) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ C ≤ Erdos1203.F n := by
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (3 * C)
  set j : ℕ := max j₀ (N + 16) with hjdef
  obtain ⟨m, hm2, hmw⟩ := exists_cardDistinctFactors_eq j
  have hjm : j < m := lt_of_lt_of_le Nat.lt_two_pow_self hm2
  have hNm : N + 16 ≤ m := le_trans (le_max_right j₀ (N + 16)) hjm.le
  refine ⟨m - 16, by omega, ?_⟩
  have hshift : m - 16 + 16 = m := by omega
  have hkey := omega_shift_le_F (m - 16)
  rw [hshift, hmw] at hkey
  have hj0j : (j₀ : ℝ) ≤ (j : ℝ) := by exact_mod_cast le_max_left j₀ (N + 16)
  linarith

/-- **`F` is frequently large.** For every `C`, `C ≤ F n` holds for arbitrarily large `n`.
This is the `limsup` half of the open problem, settled unconditionally. -/
theorem frequently_le_F (C : ℝ) : ∃ᶠ n in atTop, C ≤ Erdos1203.F n :=
  Filter.frequently_atTop.mpr fun N => exists_le_F C N

/-- `F` is not bounded above. Hence the open problem is not "is `F` unbounded?" but the strictly
harder "does `F` eventually stay large?": by `one_le_F` the `liminf` of `F` lies in `[1, ∞]`, by
`frequently_le_F` the `limsup` is `∞`, and `Erdos1203.erdos_1203` asks whether the `liminf` is
`∞` as well. -/
theorem not_bddAbove_range_F : ¬ BddAbove (Set.range Erdos1203.F) := by
  rintro ⟨B, hB⟩
  obtain ⟨n, -, hn⟩ := exists_le_F (B + 1) 0
  have hmem := hB (Set.mem_range_self (f := Erdos1203.F) n)
  linarith

/- ### Supremum-free reformulations of the open problem -/

/-- The target statement `Tendsto Erdos1203.F atTop atTop` is *equivalent* to a statement in
which no supremum occurs. The `←` direction is `le_F`; the `→` direction is
`exists_lt_of_lt_ciSup`. Both directions are proved, so nothing is lost by switching to the
right-hand side. -/
theorem tendsto_atTop_iff :
    Tendsto Erdos1203.F atTop atTop ↔
      ∀ C : ℝ, ∀ᶠ n in atTop, ∃ k : ℕ,
        C ≤ (ω (n + k) : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) := by
  constructor
  · intro h C
    filter_upwards [h.eventually_ge_atTop (C + 1)] with n hn
    have hlt : C < Erdos1203.F n := by linarith
    rw [Erdos1203.F] at hlt
    obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup hlt
    exact ⟨k, hk.le⟩
  · intro h
    rw [tendsto_atTop]
    intro C
    filter_upwards [h C] with n hn
    obtain ⟨k, hk⟩ := hn
    exact le_trans hk (le_F n k)

/-- The target in the shape a number theorist would verify: for each `C` and all large `n` one
must find `k ≥ 3` and enough primes dividing `n + k`. This is an `Iff`, not merely a sufficient
condition, so the right-hand side is neither too strong (it is implied by the target) nor too
weak (it implies the target). The hypothesis `3 ≤ k` is essential; see `multiplied_out_vacuous`.
-/
theorem tendsto_atTop_iff_primeFactors :
    Tendsto Erdos1203.F atTop atTop ↔
      ∀ C : ℝ, ∀ᶠ n in atTop, ∃ (k : ℕ) (S : Finset ℕ), 3 ≤ k ∧ S ⊆ (n + k).primeFactors ∧
        C * Real.log (k : ℝ) ≤ (S.card : ℝ) * Real.log (Real.log (k : ℝ)) := by
  have hlog3 : (1 : ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr (by linarith [Real.exp_one_lt_d9])
  have hlog_ge : ∀ k : ℕ, 3 ≤ k → (1 : ℝ) ≤ Real.log (k : ℝ) := by
    intro k hk
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact le_trans hlog3 (Real.log_le_log (by norm_num) hk3)
  constructor
  · intro h C
    rcases le_or_gt C 0 with hC | hC
    · filter_upwards with n
      refine ⟨3, ∅, le_refl 3, Finset.empty_subset _, ?_⟩
      have h3 : (1 : ℝ) ≤ Real.log ((3 : ℕ) : ℝ) := hlog_ge 3 le_rfl
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      nlinarith
    · filter_upwards [h.eventually_ge_atTop (C + 1)] with n hn
      have hlt : C < Erdos1203.F n := by linarith
      rw [Erdos1203.F] at hlt
      obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup hlt
      have hk3 : 3 ≤ k := by
        by_contra hcon
        interval_cases k
        · simp at hk; linarith
        · simp at hk; linarith
        · have hpos : (0 : ℝ) < Real.log ((2 : ℕ) : ℝ) := by
            rw [Nat.cast_ofNat]; exact Real.log_pos (by norm_num)
          have hneg : Real.log (Real.log ((2 : ℕ) : ℝ)) < 0 := by
            refine Real.log_neg hpos ?_
            rw [Nat.cast_ofNat]
            nlinarith [Real.log_two_lt_d9]
          have hterm : (ω (n + 2) : ℝ) *
              (Real.log (Real.log ((2 : ℕ) : ℝ)) / Real.log ((2 : ℕ) : ℝ)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
              (div_nonpos_of_nonpos_of_nonneg hneg.le hpos.le)
          linarith
      refine ⟨k, (n + k).primeFactors, hk3, Finset.Subset.refl _, ?_⟩
      have h1 : (1 : ℝ) ≤ Real.log (k : ℝ) := hlog_ge k hk3
      rw [show ω (n + k) = (n + k).primeFactors.card from rfl] at hk
      rw [mul_div_assoc', lt_div_iff₀ (by linarith)] at hk
      linarith
  · intro h
    rw [tendsto_atTop]
    intro C
    filter_upwards [h C] with n hn
    obtain ⟨k, S, hk, hS, hle⟩ := hn
    refine le_trans ?_ (le_F_of_subset_primeFactors n k S hS hk)
    have h1 : (1 : ℝ) ≤ Real.log (k : ℝ) := hlog_ge k hk
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    linarith

/-- **A trap, checked.** One is tempted to clear the denominator in `tendsto_atTop_iff` and ask
for `C * log k ≤ ω (n + k) * log (log k)`. Without a lower bound on `k` that condition is a
*theorem*: at `k = 1` one has `Real.log 1 = 0`, hence also `Real.log (Real.log 1) = 0`, so both
sides vanish for every `C` and every `n`. Any reformulation of the target in that shape is
therefore vacuous, which is why `tendsto_atTop_iff_primeFactors` carries `3 ≤ k`. -/
theorem multiplied_out_vacuous (C : ℝ) : ∀ᶠ n in atTop, ∃ k : ℕ,
    C * Real.log (k : ℝ) ≤ (ω (n + k) : ℝ) * Real.log (Real.log (k : ℝ)) := by
  filter_upwards with n
  exact ⟨1, by norm_num⟩

/- ### Worked use sites against the target module -/

/-- Use site 1: the companion declaration of the target module, verbatim, discharged. -/
example : ∀ ε > 0, ∀ᶠ n in atTop, Erdos1203.F n ≥ 1 - ε := variants_lower_bound

/-- Use site 2: `Erdos1203.F n` is a genuine real number lying in `[1, 2n + 20]`. In particular
it is not the junk value `0` that an unbounded family would have produced, so the lower bound
`F n ≥ 1 - ε` really is a statement about a supremum. -/
example (n : ℕ) : Erdos1203.F n ∈ Set.Icc (1 : ℝ) (2 * (n : ℝ) + 20) :=
  ⟨one_le_F n, F_le n⟩

/-- Use site 3: how a solver closes the open target with this API -- no `iSup`, no `BddAbove`,
just "for every `C`, eventually every `n` has a nearby integer with many prime factors". -/
example
    (h : ∀ C : ℝ, ∀ᶠ n in atTop, ∃ (k : ℕ) (S : Finset ℕ), 3 ≤ k ∧ S ⊆ (n + k).primeFactors ∧
      C * Real.log (k : ℝ) ≤ (S.card : ℝ) * Real.log (Real.log (k : ℝ))) :
    Tendsto Erdos1203.F atTop atTop :=
  tendsto_atTop_iff_primeFactors.mpr h

/-- Use site 4: the two unconditional halves side by side. `F` is everywhere at least `1` and
frequently at least `C`; what `Erdos1203.erdos_1203` asks is whether the second can be upgraded
from `∃ᶠ` to `∀ᶠ`. -/
example (C : ℝ) : (∀ n : ℕ, 1 ≤ Erdos1203.F n) ∧ (∃ᶠ n in atTop, C ≤ Erdos1203.F n) :=
  ⟨one_le_F, frequently_le_F C⟩

end Contribution.Erdos1203OmegaSup
