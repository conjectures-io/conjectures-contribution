import Mathlib
import FormalConjectures.ErdosProblems.«1095»

/-!
# Erdős Problem 1095: the two halves of `log g ≍ k / log k`, and the length of the period

The Erdős–Selfridge function of the pool module is
`Erdos1095.g k = sInf {m | k + 1 < m ∧ k < (m.choose k).minFac}`, the least `m > k + 1` all of
whose prime factors of `m.choose k` exceed `k`. The reward statement
`Erdos1095.erdos_1095.variants.log_isTheta` is the heuristic of Sorenson–Sorenson–Webster [SSW20],
`(fun k ↦ Real.log (g k)) =Θ[atTop] (fun k ↦ (k : ℝ) / Real.log k)`. It is open; nothing here
proves it or either of its halves.

## The obstacle

**(1) `g` may be junk.** `sInf (∅ : Set ℕ) = 0` and `Real.log 0 = 0`, so if the defining set were
empty for infinitely many `k`, the reward statement would be *false* rather than open; and no
statement of the shape `Real.exp t ≤ g k` can be extracted from a bound on `Real.log (g k)`
without `0 < g k`. The pool module proves no lemma about `g` at all, and nonemptiness of its
defining set is a statement about carries in binomial coefficients, not about `sInf`.

**(2) The two halves sit at very different distances from what is known.** In exponential form the
target is the conjunction of `∃ c > 0, ∀ᶠ k in atTop, g k ≥ exp (c * k / log k)`, which is
verbatim the companion `Erdos1095.erdos_1095.variants.lower_conjecture` of
Erdős–Lacampagne–Selfridge, with `∃ C > 0, ∀ᶠ k in atTop, (g k : ℝ) ≤ exp (C * k / log k)`; this
is `log_isTheta_iff`. The two `research solved` companions bracket these only loosely: Konyagin's
`variants.lower_solved` gives `exp (c (log k) ^ 2) = O (g k)` and Ecklund–Erdős–Selfridge's
`variants.upper_conjecture` gives `g k ≤ exp ((1 + o(1)) k)`. The target implies both
(`lower_solved_of_log_isTheta`, `upper_conjecture_of_log_isTheta`), so a solution must in
particular reprove Konyagin's theorem; the lower half beats it by a factor `k / (log k) ^ 3`
(this is where `Real.log k ^ 3 ≤ k` enters the proof) and the upper half beats
Ecklund–Erdős–Selfridge by a factor `log k`.

**(3) The periodic construction is one factor `log k` short.** Admissibility is periodic:
`minFac_choose_congr` shows that for `k < n` the condition `k < (n.choose k).minFac` depends only
on `n % modulus k`, where `modulus k = ∏_{p ≤ k} p ^ (Nat.log p k + 1)`. The last element of a
period is always admissible (`lt_minFac_choose_witness`), which makes `g` well defined and bounds
`g k` by one period, `g k ≤ (k + 3) * modulus k`. But the period is long: `two_pow_le_mul_modulus`
proves `2 ^ k ≤ 2 * ((k + 1) * modulus k)`, i.e. `modulus k ≥ 2 ^ k / (2 * (k + 1))`, by showing
that the central binomial coefficient divides `modulus (2 * m)` and invoking Chebyshev's bound
`4 ^ m ≤ (2 * m + 1) * (2 * m).choose m`. Hence any upper bound for `g` that is at least one
period has logarithm `Ω (k)` and is provably not `O (k / log k)`: `not_isBigO_of_modulus_le`,
applied to the bound proved here in `not_isBigO_log_periodic_bound`. Under the target the first
admissible integer is instead a vanishing power of the period
(`isLittleO_log_g_log_modulus_of_log_isTheta`), so the upper half needs an admissible `n` found in
a vanishingly small initial segment of a period — no such argument is known.

## What is proved here

* **Kummer's theorem in divisibility form, both directions.** `not_dvd_choose_of_forall_mod_le`
  (`¬ p ∣ n.choose k` when every base-`p` truncation of `k` is dominated by that of `n`) and its
  converse `dvd_choose_of_mod_lt_mod`, resting on the arithmetic identity
  `mod_add_sub_mod_lt_iff` between Kummer carries and base-`p` borrows. Mathlib states Kummer's
  theorem as the carry-*counting* formula `Nat.factorization_choose` and has Lucas' theorem
  `Choose.lucas_theorem` modulo `p`; the divisibility criterion for a given pair `(k, n)` is not
  in the pinned Mathlib (`exact?`, `simp`, `omega` all fail on these statements).
* **The defining condition of `g`, in both directions.** `lt_minFac_choose_of_forall_mod_le` and
  `forall_mod_le_of_lt_minFac_choose`, with `forall_mod_le_of_le_log_succ` cutting the range of
  the digit index down to `Nat.log p k + 1`.
* **Periodicity and well-definedness.** `minFac_choose_congr`, the explicit admissible integer
  `witness k = (k + 3) * modulus k - 1` (`forall_mod_le_witness`, `lt_minFac_choose_witness`), and
  `g_spec : k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac`, together with
  `one_lt_g`, `g_cast_pos`, `log_g_pos` and `g_le_mul_modulus`.
* **The period is exponentially long.** `centralBinom_dvd_modulus`, `four_pow_le_mul_modulus`,
  `two_pow_le_mul_modulus`, `eventually_log_modulus_ge`
  (`Real.log 2 / 2 * k ≤ Real.log (modulus k)` for large `k`) and `isBigO_natCast_log_modulus`.
* **A checked obstruction.** `not_isBigO_of_modulus_le` : for every `N : ℕ → ℕ` with
  `modulus k ≤ N k` eventually, `(fun k ↦ Real.log (N k))` is *not* `O (k / log k)`.
* **The target, split.** `log_isTheta_iff`, an `Iff`, and the two implications
  `lower_solved_of_log_isTheta` and `upper_conjecture_of_log_isTheta` into the solved companions,
  plus the auxiliary asymptotics `isLittleO_natCast_div_log` and
  `isLittleO_log_two_mul`.

## Handoff

A later solver can use declaration `Contribution.Erdos1095Theta.log_isTheta_iff` to discharge or
simplify obligation `(fun k ↦ Real.log ↑(Erdos1095.g k)) =Θ[atTop] fun k ↦ ↑k / Real.log ↑k` in
target `Erdos1095.erdos_1095.variants.log_isTheta`: it replaces that goal by the pool's own
`Erdos1095.erdos_1095.variants.lower_conjecture`, verbatim, together with the matching upper bound
`∃ C > 0, ∀ᶠ k in atTop, (Erdos1095.g k : ℝ) ≤ Real.exp (C * k / Real.log k)`. A later solver can
use declaration `Contribution.Erdos1095Theta.g_spec` to discharge or simplify obligation
`0 < Erdos1095.g k` — needed to pass between `Real.log (g k)` and `g k`, and false when the set
defining `g` is empty — in target `Erdos1095.erdos_1095.variants.log_isTheta`. Both use sites are
worked out against the target statement at the end of the file.

## What is not proved

Neither half of the target, and none of the four statements of the pool module. No upper bound for
`modulus k` is proved here, so `g_le_mul_modulus` is not even shown to be `exp (O (k))`; in
particular this file does not prove `Erdos1095.erdos_1095.variants.upper_conjecture`, whose
constant `1 + o(1)` is out of reach of the periodic construction. The obstruction
`not_isBigO_of_modulus_le` limits bounds that are at least one period long; it says nothing about
arguments that locate an admissible integer early inside a period, which is what a proof of the
upper half would have to do.

*References:*
- [erdosproblems.com/1095](https://www.erdosproblems.com/1095)
- [EES74] Ecklund, Erdős, Selfridge, *A new function associated with the prime factors of
  `n.choose k`*, Math. Comp. 28 (1974), 647--649.
- [ELS93] Erdős, Lacampagne, Selfridge, *Estimates of the least prime factor of a binomial
  coefficient*, Math. Comp. 61 (1993), 215--224.
- [Ko99b] Konyagin, *Estimates of the least prime factor of a binomial coefficient*,
  Mathematika 46 (1999), 41--55.
- [SSW20] Sorenson, Sorenson, Webster, *An algorithm and estimates for the Erdős–Selfridge
  function* (2020), 371--385.
-/

open Filter Real
open scoped Asymptotics Topology

namespace Contribution.Erdos1095Theta

/- ### Base-`p` digits and binomial coefficients -/

/-- Subtraction commutes with taking remainders when there is no borrow. -/
theorem sub_mod_of_mod_le {d n k : ℕ} (hkn : k ≤ n) (h : k % d ≤ n % d) :
    (n - k) % d = n % d - k % d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h1 : n / d * d + n % d = n := Nat.div_add_mod' n d
  have h2 : k / d * d + k % d = k := Nat.div_add_mod' k d
  have hdiv : k / d ≤ n / d := Nat.div_le_div_right hkn
  have hmul : (n / d - k / d) * d = n / d * d - k / d * d := Nat.sub_mul _ _ _
  have hle : k / d * d ≤ n / d * d := Nat.mul_le_mul_right _ hdiv
  have key : n - k = (n % d - k % d) + (n / d - k / d) * d := by rw [hmul]; omega
  rw [key, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  have := Nat.mod_lt n hd
  omega

/-- Adding `k` and `n - k` produces no carry out of the block of the `d` lowest base-`p` digits
exactly when the `d`-truncation of `k` is dominated by that of `n`. The left-hand side is the
condition counted by `Nat.factorization_choose`; the right-hand side is the one that can be
checked for a given pair. -/
theorem mod_add_sub_mod_lt_iff {d n k : ℕ} (hd : 0 < d) (hkn : k ≤ n) :
    k % d + (n - k) % d < d ↔ k % d ≤ n % d := by
  constructor
  · intro hlt
    have h : n % d = k % d + (n - k) % d := by
      conv_lhs => rw [show n = k + (n - k) by omega]
      rw [Nat.add_mod, Nat.mod_eq_of_lt hlt]
    omega
  · intro h
    rw [sub_mod_of_mod_le hkn h]
    have := Nat.mod_lt n hd
    omega

/-- **Carry-free implies prime-free.** If every base-`p` truncation of `k` is dominated by the
corresponding truncation of `n`, then `p` does not divide `n.choose k`. Mathlib states Kummer's
theorem as the carry-*counting* formula `Nat.factorization_choose`; this is the form in which it
is used to *construct* binomial coefficients without small prime factors. -/
theorem not_dvd_choose_of_forall_mod_le {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (h : ∀ i, k % p ^ i ≤ n % p ^ i) : ¬ p ∣ n.choose k := by
  intro hdvd
  rw [hp.dvd_iff_one_le_factorization (Nat.choose_pos hkn).ne',
    Nat.factorization_choose hp hkn (Nat.lt_succ_self _)] at hdvd
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hdvd
  rw [Finset.mem_filter] at hi
  exact absurd hi.2
    (Nat.not_le.2 ((mod_add_sub_mod_lt_iff (Nat.pow_pos hp.pos) hkn).2 (h i)))

/-- **A borrow produces a small prime factor.** The converse of
`not_dvd_choose_of_forall_mod_le`: if some base-`p` truncation of `k` exceeds that of `n`, then
`p ∣ n.choose k`. -/
theorem dvd_choose_of_mod_lt_mod {p n k i : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hi : n % p ^ i < k % p ^ i) : p ∣ n.choose k := by
  have hq : 0 < p ^ i := Nat.pow_pos hp.pos
  have hkmod : k % p ^ i ≤ k := Nat.mod_le _ _
  have hle : p ^ i ≤ n := by
    by_contra hc
    rw [Nat.mod_eq_of_lt (Nat.not_le.1 hc)] at hi
    omega
  have hn0 : n ≠ 0 := by omega
  rw [hp.dvd_iff_one_le_factorization (Nat.choose_pos hkn).ne',
    Nat.factorization_choose hp hkn (Nat.lt_succ_self _)]
  refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩⟩
  · rcases Nat.eq_zero_or_pos i with rfl | h
    · rw [pow_zero, Nat.mod_one, Nat.mod_one] at hi
      omega
    · exact h
  · exact Nat.lt_succ_of_le ((Nat.le_log_iff_pow_le hp.one_lt hn0).mpr hle)
  · by_contra hcon
    exact absurd ((mod_add_sub_mod_lt_iff hq hkn).1 (Nat.not_le.1 hcon)) (by omega)

/-- Membership in the set defining `Erdos1095.g` forces digit domination in every base `p ≤ k`. -/
theorem forall_mod_le_of_lt_minFac_choose {n k : ℕ} (hkn : k < n)
    (h : k < (n.choose k).minFac) {p : ℕ} (hp : p.Prime) (hpk : p ≤ k) (i : ℕ) :
    k % p ^ i ≤ n % p ^ i := by
  by_contra hc
  have := Nat.minFac_le_of_dvd hp.two_le (dvd_choose_of_mod_lt_mod hp hkn.le (Nat.not_le.1 hc))
  omega

/-- Only the truncations below the top base-`p` digit of `k` matter: once
`k ≤ n % p ^ (Nat.log p k + 1)`, every higher truncation is dominated automatically. -/
theorem forall_mod_le_of_le_log_succ {p k n : ℕ} (hp : p.Prime)
    (h : ∀ i ≤ Nat.log p k + 1, k % p ^ i ≤ n % p ^ i) (i : ℕ) : k % p ^ i ≤ n % p ^ i := by
  rcases le_or_gt i (Nat.log p k + 1) with hi | hi
  · exact h i hi
  · have hka : k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self hp.one_lt k
    have hki : k < p ^ i := lt_of_lt_of_le hka (Nat.pow_le_pow_right hp.pos hi.le)
    have h1 : k ≤ n % p ^ (Nat.log p k + 1) := by
      have := h _ le_rfl
      rwa [Nat.mod_eq_of_lt hka] at this
    have h2 : n % p ^ i % p ^ (Nat.log p k + 1) = n % p ^ (Nat.log p k + 1) :=
      Nat.mod_mod_of_dvd n (pow_dvd_pow p hi.le)
    have h3 : n % p ^ i % p ^ (Nat.log p k + 1) ≤ n % p ^ i := Nat.mod_le _ _
    rw [Nat.mod_eq_of_lt hki]
    omega

/-- The membership condition of the set defining `Erdos1095.g`, produced from digit domination. -/
theorem lt_minFac_choose_of_forall_mod_le {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (h : ∀ p, p.Prime → p ≤ k → ∀ i, k % p ^ i ≤ n % p ^ i) : k < (n.choose k).minFac := by
  have hne : n.choose k ≠ 1 := by
    rw [Ne, Nat.choose_eq_one_iff]
    omega
  have hall : ∀ p, p.Prime → p ∣ n.choose k → k + 1 ≤ p := by
    intro p hp hdvd
    by_contra hcon
    exact not_dvd_choose_of_forall_mod_le hp hkn.le (h p hp (by omega)) hdvd
  rcases Nat.le_minFac.2 hall with h' | h'
  · exact absurd h' hne
  · omega

/-- A multiple of `d`, decreased by one, has the largest possible remainder modulo `d`. -/
theorem pred_mod_of_dvd {N d : ℕ} (hd : 0 < d) (hdN : d ∣ N) (hN : 0 < N) :
    (N - 1) % d = d - 1 := by
  obtain ⟨q, rfl⟩ := hdN
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h1 : d * (r + 1) = r * d + d := by ring
  rw [show d * (r + 1) - 1 = (d - 1) + r * d by omega, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt (by omega)]

/- ### The period of the admissible set -/

/-- `modulus k` is the product over the primes `p ≤ k` of the least power of `p` exceeding `k`
(that is, `lcm (1, …, k)` times the primorial of `k`). Digit domination in every base `p ≤ k`
only depends on the residue modulo `modulus k`, so this is the period of the set whose infimum
defines `Erdos1095.g`. -/
def modulus (k : ℕ) : ℕ := ∏ p ∈ (k + 1).primesBelow, p ^ (Nat.log p k + 1)

theorem modulus_pos (k : ℕ) : 0 < modulus k :=
  Finset.prod_pos fun _ hp => Nat.pow_pos (Nat.prime_of_mem_primesBelow hp).pos

theorem pow_log_succ_dvd_modulus {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    p ^ (Nat.log p k + 1) ∣ modulus k :=
  Finset.dvd_prod_of_mem _ (Nat.mem_primesBelow.2 ⟨by omega, hp⟩)

theorem modulus_le_modulus {k l : ℕ} (h : k ≤ l) : modulus k ≤ modulus l := by
  calc modulus k ≤ ∏ p ∈ (k + 1).primesBelow, p ^ (Nat.log p l + 1) :=
        Finset.prod_le_prod' fun p hp =>
          Nat.pow_le_pow_right (Nat.prime_of_mem_primesBelow hp).pos
            (by have := Nat.log_mono_right (b := p) h; omega)
    _ ≤ modulus l := Finset.prod_le_prod_of_subset_of_one_le'
        (fun p hp => Nat.mem_primesBelow.2
          ⟨by have := Nat.lt_of_mem_primesBelow hp; omega, Nat.prime_of_mem_primesBelow hp⟩)
        (fun p hp _ => Nat.one_le_pow _ _ (Nat.prime_of_mem_primesBelow hp).pos)

/-- **`modulus k` really is a period.** Above `k`, whether all prime factors of `n.choose k`
exceed `k` depends only on the residue of `n` modulo `modulus k`. So the set whose infimum
defines `Erdos1095.g k` is a union of residue classes modulo `modulus k`; a search for `g k` may
be confined to one period, and the construction below takes the last element of a period. -/
theorem minFac_choose_congr {k n n' : ℕ} (hk : 0 < k) (hn : k < n) (hn' : k < n')
    (h : n % modulus k = n' % modulus k) :
    k < (n.choose k).minFac ↔ k < (n'.choose k).minFac := by
  have key : ∀ m m' : ℕ, k < m → k < m' → m % modulus k = m' % modulus k →
      k < (m.choose k).minFac → k < (m'.choose k).minFac := by
    intro m m' hm hm' hmm hlt
    refine lt_minFac_choose_of_forall_mod_le hk hm' fun p hp hpk => ?_
    refine forall_mod_le_of_le_log_succ hp fun i hi => ?_
    have hdvd : p ^ i ∣ modulus k :=
      (pow_dvd_pow p hi).trans (pow_log_succ_dvd_modulus hp hpk)
    have hmod : m % p ^ i = m' % p ^ i := by
      rw [← Nat.mod_mod_of_dvd m hdvd, ← Nat.mod_mod_of_dvd m' hdvd, hmm]
    rw [← hmod]
    exact forall_mod_le_of_lt_minFac_choose hm hlt hp hpk i
  exact ⟨key n n' hn hn' h, key n' n hn' hn h.symm⟩

/- ### `Erdos1095.g` is well defined -/

/-- The explicit admissible integer used below: one less than a multiple of the period. -/
def witness (k : ℕ) : ℕ := (k + 3) * modulus k - 1

theorem lt_witness (k : ℕ) : k + 1 < witness k := by
  have h : k + 3 ≤ (k + 3) * modulus k := Nat.le_mul_of_pos_right _ (modulus_pos k)
  simp only [witness]
  omega

/-- Every base-`p` truncation of `k` is dominated by that of `witness k`, for every prime
`p ≤ k`: below the top digit of `k` the digits of `witness k` are all `p - 1`, and above it the
truncation of `witness k` already exceeds `k`. -/
theorem forall_mod_le_witness {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) (i : ℕ) :
    k % p ^ i ≤ witness k % p ^ i := by
  set N := (k + 3) * modulus k with hN
  have hNpos : 0 < N := Nat.mul_pos (by omega) (modulus_pos k)
  have hdvdN : p ^ (Nat.log p k + 1) ∣ N :=
    Dvd.dvd.mul_left (pow_log_succ_dvd_modulus hp hpk) _
  have hkp : k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self hp.one_lt k
  rcases le_or_gt i (Nat.log p k + 1) with hi | hi
  · have hdvd : p ^ i ∣ N := (pow_dvd_pow p hi).trans hdvdN
    have := pred_mod_of_dvd (Nat.pow_pos hp.pos) hdvd hNpos
    have hlt := Nat.mod_lt k (Nat.pow_pos (n := i) hp.pos)
    simp only [witness, ← hN, this]
    omega
  · have hmod := pred_mod_of_dvd (Nat.pow_pos (n := Nat.log p k + 1) hp.pos) hdvdN hNpos
    have hdd : p ^ (Nat.log p k + 1) ∣ p ^ i := pow_dvd_pow p hi.le
    have h2 : (N - 1) % p ^ i % p ^ (Nat.log p k + 1) = (N - 1) % p ^ (Nat.log p k + 1) :=
      Nat.mod_mod_of_dvd _ hdd
    have h3 : (N - 1) % p ^ i % p ^ (Nat.log p k + 1) ≤ (N - 1) % p ^ i := Nat.mod_le _ _
    have h4 : k % p ^ i ≤ k := Nat.mod_le _ _
    simp only [witness, ← hN]
    omega

theorem lt_minFac_choose_witness (k : ℕ) : k < ((witness k).choose k).minFac := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact lt_minFac_choose_of_forall_mod_le hk (by have := lt_witness k; omega)
      fun p hp hpk => forall_mod_le_witness hp hpk

theorem setOf_nonempty (k : ℕ) : {m | k + 1 < m ∧ k < (m.choose k).minFac}.Nonempty :=
  ⟨witness k, lt_witness k, lt_minFac_choose_witness k⟩

/-- **`Erdos1095.g` is well defined.** The set whose infimum defines `g` is nonempty, so `g k`
really is the least `m > k + 1` all of whose prime factors of `m.choose k` exceed `k`; without
this `g k` could be `sInf ∅ = 0` and every asymptotic statement about `Real.log (g k)` would be
false rather than open. -/
theorem g_spec (k : ℕ) : k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac :=
  Nat.sInf_mem (setOf_nonempty k)

theorem one_lt_g (k : ℕ) : 1 < Erdos1095.g k := by have := (g_spec k).1; omega

theorem g_cast_pos (k : ℕ) : (0 : ℝ) < (Erdos1095.g k : ℝ) := by
  have := one_lt_g k
  positivity

theorem log_g_pos (k : ℕ) : 0 < Real.log (Erdos1095.g k) :=
  Real.log_pos (by exact_mod_cast one_lt_g k)

/-- The unconditional upper bound that periodicity provides: `g k` is at most a fixed multiple of
the period. -/
theorem g_le_mul_modulus (k : ℕ) : Erdos1095.g k ≤ (k + 3) * modulus k := by
  have h : Erdos1095.g k ≤ witness k := Nat.sInf_le ⟨lt_witness k, lt_minFac_choose_witness k⟩
  have : witness k ≤ (k + 3) * modulus k := Nat.sub_le _ _
  omega

/- ### The period is exponentially long -/

theorem le_factorization_modulus {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    Nat.log p k + 1 ≤ (modulus k).factorization p := by
  have hdvd := pow_log_succ_dvd_modulus hp hpk
  have h := (Nat.factorization_le_iff_dvd (pow_ne_zero (Nat.log p k + 1) hp.pos.ne')
    (modulus_pos k).ne').2 hdvd
  have := Finsupp.le_def.1 h p
  rwa [hp.factorization_pow, Finsupp.single_eq_same] at this

/-- Every prime power dividing `(2 * m).choose m` is at most `2 * m`, so the central binomial
coefficient divides the period at `2 * m`. -/
theorem centralBinom_dvd_modulus (m : ℕ) : Nat.centralBinom m ∣ modulus (2 * m) := by
  rw [← Nat.factorization_le_iff_dvd (Nat.centralBinom_ne_zero m) (modulus_pos _).ne']
  refine Finsupp.le_def.2 fun p => ?_
  by_cases hp : p.Prime
  · by_cases hpk : p ≤ 2 * m
    · calc (Nat.centralBinom m).factorization p ≤ Nat.log p (2 * m) :=
            Nat.factorization_choose_le_log
        _ ≤ Nat.log p (2 * m) + 1 := Nat.le_succ _
        _ ≤ _ := le_factorization_modulus hp hpk
    · rw [Nat.factorization_centralBinom_eq_zero_of_two_mul_lt (by omega)]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem four_pow_le_mul_modulus (m : ℕ) : 4 ^ m ≤ (2 * m + 1) * modulus (2 * m) :=
  le_trans (Nat.four_pow_le_two_mul_add_one_mul_central_binom m)
    (Nat.mul_le_mul_left _ (Nat.le_of_dvd (modulus_pos _) (centralBinom_dvd_modulus m)))

/-- **Chebyshev's lower bound for the period.** `modulus k ≥ 2 ^ k / (2 * (k + 1))`. -/
theorem two_pow_le_mul_modulus (k : ℕ) : 2 ^ k ≤ 2 * ((k + 1) * modulus k) := by
  have hhalf : 2 * (k / 2) ≤ k := by omega
  have h1 : 4 ^ (k / 2) ≤ (2 * (k / 2) + 1) * modulus (2 * (k / 2)) := four_pow_le_mul_modulus _
  have h2 : (2 * (k / 2) + 1) * modulus (2 * (k / 2)) ≤ (k + 1) * modulus k :=
    Nat.mul_le_mul (by omega) (modulus_le_modulus hhalf)
  have h4 : 2 ^ k ≤ 2 * 4 ^ (k / 2) := by
    have hpow : (4 : ℕ) ^ (k / 2) = 2 ^ (2 * (k / 2)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [hpow, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 2 ^ k ≤ 2 * 4 ^ (k / 2) := h4
    _ ≤ 2 * ((k + 1) * modulus k) := Nat.mul_le_mul_left _ (h1.trans h2)

theorem log_two_mul_le (k : ℕ) :
    (k : ℝ) * Real.log 2 ≤ Real.log (2 * ((k : ℝ) + 1)) + Real.log (modulus k) := by
  have hcast : ((2 : ℝ)) ^ k ≤ (2 * ((k : ℝ) + 1)) * (modulus k : ℝ) := by
    have h := two_pow_le_mul_modulus k
    have : ((2 ^ k : ℕ) : ℝ) ≤ ((2 * ((k + 1) * modulus k) : ℕ) : ℝ) := Nat.cast_le.2 h
    push_cast at this
    linarith
  have h1 : (0 : ℝ) < 2 ^ k := by positivity
  have h2 : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have h3 : (0 : ℝ) < (modulus k : ℝ) := by exact_mod_cast modulus_pos k
  have h := Real.log_le_log h1 hcast
  rwa [Real.log_mul h2.ne' h3.ne', Real.log_pow] at h

theorem isLittleO_log_two_mul :
    (fun k : ℕ ↦ Real.log (2 * ((k : ℝ) + 1))) =o[atTop] fun k : ℕ ↦ (k : ℝ) := by
  have h1 : Filter.Tendsto (fun k : ℕ ↦ 2 * ((k : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num)
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := Real.isLittleO_log_id_atTop.comp_tendsto h1
  simp only [Function.comp_def, id_eq] at h2
  refine h2.trans_isBigO (Asymptotics.IsBigO.of_bound 4 ?_)
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity)]
  linarith

/-- The period is at least `exp ((log 2 / 2) * k)` for all large `k`. -/
theorem eventually_log_modulus_ge :
    ∀ᶠ k : ℕ in atTop, Real.log 2 / 2 * (k : ℝ) ≤ Real.log (modulus k) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [isLittleO_log_two_mul.def (show (0 : ℝ) < Real.log 2 / 2 by positivity)]
    with k hk
  have hb := log_two_mul_le k
  have habs : Real.log (2 * ((k : ℝ) + 1)) ≤ Real.log 2 / 2 * (k : ℝ) := by
    calc Real.log (2 * ((k : ℝ) + 1)) ≤ |Real.log (2 * ((k : ℝ) + 1))| := le_abs_self _
      _ ≤ Real.log 2 / 2 * |(k : ℝ)| := by
          rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]; exact hk
      _ = Real.log 2 / 2 * (k : ℝ) := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ))]
  linarith

theorem isBigO_natCast_log_modulus :
    (fun k : ℕ ↦ (k : ℝ)) =O[atTop] fun k : ℕ ↦ Real.log (modulus k) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine Asymptotics.IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [eventually_log_modulus_ge] with k hk
  have hmod : (0 : ℝ) ≤ Real.log (modulus k) :=
    Real.log_nonneg (Nat.one_le_cast.2 (modulus_pos k))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hmod]
  have h := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 2 / Real.log 2)
  have he : 2 / Real.log 2 * (Real.log 2 / 2 * (k : ℝ)) = (k : ℝ) := by field_simp
  linarith

/-- **A checked limitation of the periodic construction.** An upper bound for `Erdos1095.g` that
is at least one period long — such as the bound `g_le_mul_modulus` proved here, and any bound
obtained by searching a whole period — fails to have the shape `exp (O (k / log k))` demanded by
the upper half of `Erdos1095.erdos_1095.variants.log_isTheta`: its logarithm is `Ω (k)`, larger by
a factor `log k`. -/
theorem not_isBigO_of_modulus_le {N : ℕ → ℕ} (hN : ∀ᶠ k : ℕ in atTop, modulus k ≤ N k) :
    ¬ ((fun k : ℕ ↦ Real.log (N k)) =O[atTop] fun k : ℕ ↦ (k : ℝ) / Real.log k) := by
  intro h
  have hbig : (fun k : ℕ ↦ (k : ℝ)) =O[atTop] fun k : ℕ ↦ Real.log (N k) := by
    refine isBigO_natCast_log_modulus.trans (Asymptotics.IsBigO.of_bound 1 ?_)
    filter_upwards [hN] with k hk
    have h0 : (0 : ℝ) ≤ Real.log (modulus k) :=
      Real.log_nonneg (Nat.one_le_cast.2 (modulus_pos k))
    have h1 : Real.log (modulus k) ≤ Real.log (N k) :=
      Real.log_le_log (by exact_mod_cast modulus_pos k) (Nat.cast_le.2 hk)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (h0.trans h1)]
    linarith
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.1 (hbig.trans h)
  have hlog : ∀ᶠ k : ℕ in atTop, C < Real.log k := by
    have := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop C
    simpa [Function.comp_def] using this
  obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := ((hC.and hlog).and (Filter.eventually_ge_atTop 2)).exists
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogpos : (0 : ℝ) < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hkpos.le,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) / Real.log k)] at hk1
  have h1 : (k : ℝ) * Real.log k ≤ C * (k : ℝ) := by
    have := mul_le_mul_of_nonneg_right hk1 hlogpos.le
    rwa [mul_assoc, div_mul_cancel₀ _ hlogpos.ne'] at this
  have h2 : Real.log k ≤ C :=
    le_of_mul_le_mul_left (by linarith : (k : ℝ) * Real.log k ≤ (k : ℝ) * C) hkpos
  linarith

/-- The concrete unconditional bound proved above, `g k ≤ (k + 3) * modulus k`, is provably too
weak for the upper half of the target, for every choice of constant. -/
theorem not_isBigO_log_periodic_bound :
    ¬ ((fun k : ℕ ↦ Real.log (((k + 3) * modulus k : ℕ) : ℝ)) =O[atTop]
      fun k : ℕ ↦ (k : ℝ) / Real.log k) :=
  not_isBigO_of_modulus_le (Filter.Eventually.of_forall fun k =>
    Nat.le_mul_of_pos_left (modulus k) (show 0 < k + 3 by omega))

/- ### The target, split into its two halves -/

/-- **The target is equivalent to the conjunction of its two halves, each in exponential form.**
The first conjunct is, verbatim, the statement of the companion
`Erdos1095.erdos_1095.variants.lower_conjecture` of Erdős–Lacampagne–Selfridge; the second is the
matching upper bound suggested by the heuristics of [SSW20]. Being an `Iff`, this cannot be a
wrong-direction reduction: a solver may replace the target by the two bounds and nothing is lost.
Turning the `Θ` into bounds for `g` itself (rather than for `Real.log (g k)`) uses `0 < g k`,
i.e. `g_spec`. -/
theorem log_isTheta_iff :
    (fun k : ℕ ↦ Real.log (Erdos1095.g k)) =Θ[atTop] (fun k : ℕ ↦ (k : ℝ) / Real.log k) ↔
      (∃ c > 0, ∀ᶠ k : ℕ in atTop, (Erdos1095.g k : ℝ) ≥ Real.exp (c * k / Real.log k)) ∧
        ∃ C > 0, ∀ᶠ k : ℕ in atTop, (Erdos1095.g k : ℝ) ≤ Real.exp (C * k / Real.log k) := by
  have hev : ∀ᶠ k : ℕ in atTop, (0 : ℝ) < (k : ℝ) / Real.log k := by
    filter_upwards [Filter.eventually_ge_atTop 2] with k hk
    have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h2 : (0 : ℝ) < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    positivity
  constructor
  · intro h
    obtain ⟨C, hC, hb1⟩ := h.1.exists_pos
    obtain ⟨c, hc, hb2⟩ := h.2.exists_pos
    refine ⟨⟨1 / c, by positivity, ?_⟩, C, hC, ?_⟩
    · filter_upwards [hb2.bound, hev] with k hk hpos
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos.le,
        abs_of_nonneg (log_g_pos k).le] at hk
      rw [ge_iff_le, ← Real.le_log_iff_exp_le (g_cast_pos k), mul_div_assoc,
        div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
      linarith
    · filter_upwards [hb1.bound, hev] with k hk hpos
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_g_pos k).le,
        abs_of_nonneg hpos.le] at hk
      rw [← Real.log_le_iff_le_exp (g_cast_pos k), mul_div_assoc]
      exact hk
  · rintro ⟨⟨c, hc, h1⟩, C, hC, h2⟩
    refine ⟨Asymptotics.IsBigO.of_bound C ?_, Asymptotics.IsBigO.of_bound (1 / c) ?_⟩
    · filter_upwards [h2, hev] with k hk hpos
      rw [← Real.log_le_iff_le_exp (g_cast_pos k), mul_div_assoc] at hk
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_g_pos k).le,
        abs_of_nonneg hpos.le]
      exact hk
    · filter_upwards [h1, hev] with k hk hpos
      rw [ge_iff_le, ← Real.le_log_iff_exp_le (g_cast_pos k), mul_div_assoc] at hk
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos.le,
        abs_of_nonneg (log_g_pos k).le, div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      linarith

/- ### The target implies both solved companions -/

theorem isLittleO_natCast_div_log :
    (fun k : ℕ ↦ (k : ℝ) / Real.log k) =o[atTop] fun k : ℕ ↦ (k : ℝ) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hlarge : ∀ᶠ k : ℕ in atTop, 1 / ε ≤ Real.log k := by
    have := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / ε)
    simpa [Function.comp_def] using this
  filter_upwards [hlarge, Filter.eventually_ge_atTop 2] with k hk hk2
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlogpos : (0 : ℝ) < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg hkpos.le,
    div_le_iff₀ hlogpos]
  have hinv : 1 ≤ ε * Real.log k := by
    rw [div_le_iff₀ hε] at hk
    linarith
  nlinarith

/-- **The target implies Konyagin's theorem** `Erdos1095.erdos_1095.variants.lower_solved`, the
current record `g k ≫ exp (c (log k) ^ 2)` [Ko99b]. So the target is strictly stronger than the
best known result, and any solution must in particular reprove it. -/
theorem lower_solved_of_log_isTheta
    (h : (fun k : ℕ ↦ Real.log (Erdos1095.g k)) =Θ[atTop] fun k : ℕ ↦ (k : ℝ) / Real.log k) :
    ∃ c > 0, (fun k : ℕ ↦ Real.exp (c * Real.log k ^ 2)) =O[atTop]
      fun k : ℕ ↦ (Erdos1095.g k : ℝ) := by
  obtain ⟨c, hc, hb⟩ := (log_isTheta_iff.1 h).1
  refine ⟨c, hc, Asymptotics.IsBigO.of_bound 1 ?_⟩
  have hcube3 : (fun k : ℕ ↦ Real.log k ^ 3) =o[atTop] fun k : ℕ ↦ (k : ℝ) := by
    simpa [Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := 3)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hb, hcube3.def (c := 1) one_pos,
    Filter.eventually_ge_atTop 2] with k hk hcube hk2
  have hlogpos : (0 : ℝ) < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hcube
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
    abs_of_nonneg (g_cast_pos k).le, one_mul]
  refine le_trans (Real.exp_le_exp.2 ?_) hk
  rw [le_div_iff₀ hlogpos]
  have hcube_le : Real.log k ^ 3 ≤ (k : ℝ) := by
    rw [abs_of_nonneg hkpos.le] at hcube
    linarith
  calc c * Real.log k ^ 2 * Real.log k = c * Real.log k ^ 3 := by ring
    _ ≤ c * (k : ℝ) := mul_le_mul_of_nonneg_left hcube_le hc.le

/-- **The target implies the Ecklund–Erdős–Selfridge bound**
`Erdos1095.erdos_1095.variants.upper_conjecture`, `g k ≤ exp ((1 + o(1)) k)` [EES74]. -/
theorem upper_conjecture_of_log_isTheta
    (h : (fun k : ℕ ↦ Real.log (Erdos1095.g k)) =Θ[atTop] fun k : ℕ ↦ (k : ℝ) / Real.log k) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ᶠ k : ℕ in atTop, (Erdos1095.g k : ℝ) ≤ Real.exp (k * (1 + f k)) := by
  obtain ⟨C, hC, hb⟩ := (log_isTheta_iff.1 h).2
  refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
  have hlogC : ∀ᶠ k : ℕ in atTop, C ≤ Real.log k := by
    have := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C
    simpa [Function.comp_def] using this
  filter_upwards [hb, hlogC, Filter.eventually_ge_atTop 2] with k hk hlk hk2
  refine hk.trans (Real.exp_le_exp.2 ?_)
  have hlogpos : (0 : ℝ) < Real.log k := lt_of_lt_of_le hC hlk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [div_le_iff₀ hlogpos]
  nlinarith

/-- Under the target, the first admissible integer above `k + 1` is a vanishing power of the
period. So a proof of the upper half has to locate an admissible integer inside a vanishingly
small initial segment of a period, which no periodicity argument alone can do. -/
theorem isLittleO_log_g_log_modulus_of_log_isTheta
    (h : (fun k : ℕ ↦ Real.log (Erdos1095.g k)) =Θ[atTop] fun k : ℕ ↦ (k : ℝ) / Real.log k) :
    (fun k : ℕ ↦ Real.log (Erdos1095.g k)) =o[atTop] fun k : ℕ ↦ Real.log (modulus k) :=
  (h.1.trans_isLittleO isLittleO_natCast_div_log).trans_isBigO isBigO_natCast_log_modulus

/- ### Worked use sites against the target statement -/

/-- Use site: the target statement of `Erdos1095.erdos_1095.variants.log_isTheta`, discharged from
the Erdős–Lacampagne–Selfridge lower bound together with the matching upper bound. -/
example
    (hlow : ∃ c > 0, ∀ᶠ k in atTop, Erdos1095.g k ≥ exp (c * k / log k))
    (hupp : ∃ C > 0, ∀ᶠ k in atTop, (Erdos1095.g k : ℝ) ≤ exp (C * k / log k)) :
    (fun k ↦ log (Erdos1095.g k)) =Θ[atTop] fun k ↦ (k : ℝ) / log k :=
  log_isTheta_iff.2 ⟨hlow, hupp⟩

/-- Use site: from the target, the companion `Erdos1095.erdos_1095.variants.lower_conjecture`,
stated verbatim. -/
example (h : (fun k ↦ log (Erdos1095.g k)) =Θ[atTop] fun k ↦ (k : ℝ) / log k) :
    ∃ c > 0, ∀ᶠ k in atTop, Erdos1095.g k ≥ exp (c * k / log k) := (log_isTheta_iff.1 h).1

/-- Use site: from the target, the companion `Erdos1095.erdos_1095.variants.lower_solved` of
Konyagin, stated verbatim. -/
example (h : (fun k ↦ log (Erdos1095.g k)) =Θ[atTop] fun k ↦ (k : ℝ) / log k) :
    ∃ c > 0, (fun k : ℕ ↦ exp (c * log k ^ 2)) =O[atTop] fun k ↦ (Erdos1095.g k : ℝ) :=
  lower_solved_of_log_isTheta h

/-- Use site: from the target, the companion `Erdos1095.erdos_1095.variants.upper_conjecture` of
Ecklund–Erdős–Selfridge, stated verbatim. -/
example (h : (fun k ↦ log (Erdos1095.g k)) =Θ[atTop] fun k ↦ (k : ℝ) / log k) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ k in atTop, Erdos1095.g k ≤ exp (k * (1 + f k)) :=
  upper_conjecture_of_log_isTheta h

end Contribution.Erdos1095Theta
