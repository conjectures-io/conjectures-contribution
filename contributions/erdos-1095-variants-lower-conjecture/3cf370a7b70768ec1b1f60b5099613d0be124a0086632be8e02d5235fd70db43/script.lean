import Mathlib
import FormalConjectures.ErdosProblems.«1095»

/-!
# Erdős Problem 1095: the Erdős–Selfridge function in the shift coordinate

A contribution towards `Erdos1095.erdos_1095.variants.lower_conjecture`
([erdosproblems.com/1095](https://www.erdosproblems.com/1095)), which asserts
`∃ c > 0, ∀ᶠ k in atTop, g k ≥ exp (c * k / log k)` for
`Erdos1095.g k = sInf {m | k + 1 < m ∧ k < (m.choose k).minFac}`. The problem is open — the record
is Konyagin's `g k ≫ exp (c * (log k) ^ 2)` — and nothing here solves it.

## The obstacle

*`g` may be junk.* `sInf (∅ : Set ℕ)` is `0`, so until the defining set is shown to be nonempty
the reward statement is false rather than open. Nothing in the target module addresses this.

*The membership test is opaque.* `k < (m.choose k).minFac` is a statement about `Nat.minFac` of a
binomial coefficient. Mathlib's handle on primes in binomial coefficients is Kummer's theorem in
carry-*counting* form (`Nat.factorization_choose`, `Nat.factorization_choose'`: an equation between
a `p`-adic valuation and a `Finset.card`), plus divisibility lemmas restricted to a single base-`p`
digit (`Nat.Prime.dvd_choose_add`, `Nat.Prime.dvd_choose`) or to `m = p ^ n`
(`Nat.Prime.dvd_choose_pow_iff`). None of them decides `p ∣ m.choose k` for general `m` and `k`.

*Where the mathematics is hard.* Admissibility of `m` depends only on `m` modulo an explicit
modulus, so the admissible `m` form a nonempty union of residue classes and the whole question is
where the **first** class member above `k + 1` sits. Congruence and counting information determines
how *dense* the admissible set is — equivalently the *mean* gap — but says nothing about the
location of any particular gap, and the conjecture asserts that the very first gap is as long as a
typical one. That is the gap this file makes precise rather than closes.

## What is proved here

*Kummer as a criterion.* `not_dvd_choose_add_iff` : for `p` prime,
`¬ p ∣ (k + t).choose k ↔ ∀ i, k % p ^ i + t % p ^ i < p ^ i`, i.e. adding `k` and `t` in base `p`
never carries; `forall_mod_add_lt_iff` converts block carries into single-digit carries.

*A change of coordinate.* `NoCarry k t` says that adding `k` and `t` carries in no base `p ≤ k`;
`noCarry_iff_lt_minFac` proves `NoCarry k t ↔ k < ((k + t).choose k).minFac` for `t > 0`, and
`g_eq_add_shift` proves `Erdos1095.g k = k + shift k`, where `shift k = sInf {t | 1 < t ∧
NoCarry k t}`. After this rewrite the problem contains no `Nat.choose`, no `Nat.minFac` and no
condition on `m` at all: only base-`p` digits of `k` and `t`. `noCarry_iff_bounded` cuts both
quantifiers to finite ranges without mentioning `Nat.log`, which makes `NoCarry` decidable by
kernel computation (`decidableNoCarry`).

*Well-definedness, and a two-sided sandwich.* `noCarry_of_modulus_dvd` shows every multiple of
`modulus k = ∏_{p ≤ k} p ^ (log_p k + 1)` is an admissible shift, whence `shift_mem`, `g_spec`
(`k + 1 < g k ∧ k < ((g k).choose k).minFac`, so `g k ≠ 0`) and `g_le_add_two_mul_modulus`.
*A later solver can use declaration `Contribution.Erdos1095Shift.g_spec` to discharge or simplify
obligation `k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac` — the nonemptiness of
the set whose `sInf` defines `g`, without which `g k = 0` and the goal is false — in target
`Erdos1095.erdos_1095.variants.lower_conjecture`.* The index set of the product is Mathlib's
`Nat.primesBelow (k + 1)`, so `Nat.mem_primesBelow` and `Nat.prime_of_mem_primesBelow` are the
only membership API needed.

*An unconditional lower bound.* `pow_dvd_of_noCarry`: if `p ≤ k` is prime and `p ^ i ∣ k + 1`, then
`p ^ i` divides **every** admissible shift (the bottom `i` base-`p` digits of `k` are all `p - 1`,
so those of `t` must all be `0`). Hence `succ_dvd_shift` (`k + 1 ∣ shift k` whenever `k + 1` is not
prime) and `two_mul_add_one_le_g` : `¬ (k + 1).Prime → 2 * k + 1 ≤ Erdos1095.g k`. This is sharp:
`g_three` proves `Erdos1095.g 3 = 7 = 2 * 3 + 1` with no search at all. The hypothesis is also
necessary, not an artefact: `not_two_mul_add_one_le_g_four` proves `¬ 2 * 4 + 1 ≤ Erdos1095.g 4`,
since `5` is prime and `g 4 ≤ 7`. `two_mul_add_one_le_g_odd` records the hypothesis-free
consequence `2 * (2 * j + 3) + 1 ≤ Erdos1095.g (2 * j + 3)`, valid along the odd numbers
`k = 2 * j + 3` (it is `k + 1` that is even there, hence composite).

*The exact density of admissible shifts.* `card_noCarry_period`: of the `modulus k` residues in one
period, exactly `∏_{p ≤ k} ∏_{i ≤ log_p k} (p - k_i(p))` are admissible, `k_i(p)` being the `i`-th
base-`p` digit of `k`. The reciprocal of the resulting density is the mean gap between admissible
shifts, which is the quantity the heuristic of [SSW20] compares `log g` to. It rests on two general
counting lemmas proved here, `card_filter_range_mul` and `card_filter_range_prod`: for pairwise
coprime moduli `M i` and predicates `P i` that are `M i`-periodic, the number of `n < ∏ M i`
satisfying all of them is `∏ i, #{r < M i | P i r}` (a Chinese remainder bijection), together with
the per-prime count `card_filter_digit_add_lt`. For `k = 13` this is checked:
`modulus_thirteen` (`10821610800`) and `card_noCarry_period_thirteen` (`8087040`), a `Finset` with
more than `10 ^ 10` elements that no `decide` could count directly, so the mean gap at `k = 13` is
about `1338`, while the tabulated value `g 13 = 2239` makes the true first gap `2226`.

*A checked long gap.* `exists_noCarry_free_window` turns sparsity into a pigeonhole: if
`(C + 1) * L ≤ modulus k`, where `C` is the count above, then **some** window of `L` consecutive
integers contains no admissible shift. `exists_noCarry_free_window_thirteen` is a fully checked
instance: for `k = 13` some `1338` consecutive integers are all inadmissible. The window is not
located, and locating it at `t = 2` is exactly the open problem.

*The reward statement, restated and used.* `le_g_iff` : `N ≤ Erdos1095.g k ↔ ∀ t, 1 < t →
k + t < N → ¬ NoCarry k t`, an equivalence, and `lower_conjecture_iff_noCarry` is the resulting
equivalence between the literal reward statement and a statement about base-`p` digits with no `g`,
no `sInf`, no `Nat.minFac` and no `Nat.choose`. *A later solver can use declaration
`Contribution.Erdos1095Shift.lower_conjecture_iff_noCarry` to discharge or simplify obligation
`∃ c > 0, ∀ᶠ k in atTop, ↑(Erdos1095.g k) ≥ Real.exp (c * ↑k / Real.log ↑k)` in target
`Erdos1095.erdos_1095.variants.lower_conjecture`.* Being an `Iff` it cannot be a wrong-direction
reduction. `lower_conjecture_of_covering` is a worked use site producing the reward statement
verbatim from the output of a sieve argument: an explicit bound `N k` and, for all large `k` and
each `t` with `k + t < N k`, a prime `p ≤ k` and a digit position where adding `k` and `t` carries.
Both of its hypotheses are eventual (`∀ᶠ k in atTop`), so a sieve that only controls large `k`
suffices. `lower_conjecture_iff_covering` shows this use site loses nothing: the covering data is
*equivalent* to the reward statement, the forward direction being witnessed by `N = Erdos1095.g`.

## What is *not* provided

No lower bound on `g` that grows faster than linearly, and no proof of any of the four statements
of the target module. `two_mul_add_one_le_g` is enormously weaker than the conjectured
`exp (c * k / log k)`, and the counting results bound the *mean* gap, not the first one. Supplying
the covering hypothesis of `lower_conjecture_of_covering` for a bound `N k` of size
`exp (c * k / log k)` is the analytic step the conjecture needs, and `lower_conjecture_iff_covering`
says covering data of that size exists exactly when the conjecture holds: this file makes the
problem cleaner, not easier. That step is not carried out here, and it is carried out in neither
cited paper — [ELS93] only conjectured the bound ('it is clear to every right-thinking person'),
and [Ko99b] proves the strictly weaker `exp (c * (log k) ^ 2)`.

*References:*
- [erdosproblems.com/1095](https://www.erdosproblems.com/1095)
- [EES74] Ecklund, Erdős, Selfridge, *A new function associated with the prime factors of
  `n.choose k`*, Math. Comp. (1974), 647--649.
- [ELS93] Erdős, Lacampagne, Selfridge, *Estimates of the least prime factor of a binomial
  coefficient*, Math. Comp. (1993), 215--224.
- [Ko99b] Konyagin, *Estimates of the least prime factor of a binomial coefficient*,
  Mathematika (1999), 41--55.
- [SSW20] Sorenson, Sorenson, Webster, *An algorithm and estimates for the Erdős–Selfridge
  function* (2020), 371--385.
-/

namespace Contribution.Erdos1095Shift

open Filter Real

/- ### Kummer's theorem as a no-carry criterion -/

/-- Carries out of base-`p` blocks versus carries of single base-`p` digits. -/
theorem forall_mod_add_lt_iff {p k t : ℕ} (hp : 0 < p) :
    (∀ i, k % p ^ i + t % p ^ i < p ^ i) ↔ ∀ i, k / p ^ i % p + t / p ^ i % p < p := by
  constructor
  · intro h i
    have h1 := h (i + 1)
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ] at h1
    by_contra hc
    push_neg at hc
    have h5 : p ^ (i + 1) ≤ p ^ i * (k / p ^ i % p) + p ^ i * (t / p ^ i % p) := by
      calc p ^ (i + 1) = p ^ i * p := by ring
        _ ≤ p ^ i * (k / p ^ i % p + t / p ^ i % p) := Nat.mul_le_mul_left _ hc
        _ = p ^ i * (k / p ^ i % p) + p ^ i * (t / p ^ i % p) := by ring
    exact absurd (lt_of_lt_of_le h1 h5)
      (Nat.not_lt.mpr (Nat.add_le_add (Nat.le_add_left _ _) (Nat.le_add_left _ _)))
  · intro h i
    induction i with
    | zero => simp only [pow_zero]; omega
    | succ n ih =>
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ]
      have h1 := h n
      have h2 : p ^ n * (k / p ^ n % p) + p ^ n * (t / p ^ n % p)
          = p ^ n * (k / p ^ n % p + t / p ^ n % p) := by ring
      have h3 : p ^ n * (k / p ^ n % p + t / p ^ n % p) ≤ p ^ n * (p - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h4 : p ^ n * (p - 1) + p ^ n = p ^ n * p := by
        have hp1 : p - 1 + 1 = p := by omega
        calc p ^ n * (p - 1) + p ^ n = p ^ n * (p - 1 + 1) := by ring
          _ = p ^ n * p := by rw [hp1]
      have h5 : p ^ (n + 1) = p ^ n * p := by ring
      omega

/--
**Kummer's theorem as a divisibility criterion.** A prime `p` fails to divide `(k + t).choose k`
exactly when adding `k` and `t` in base `p` produces no carry out of any block.
-/
theorem not_dvd_choose_add_iff {p k t : ℕ} (hp : p.Prime) :
    ¬ p ∣ (k + t).choose k ↔ ∀ i, k % p ^ i + t % p ^ i < p ^ i := by
  have hne : (k + t).choose k ≠ 0 := (Nat.choose_pos (Nat.le_add_right k t)).ne'
  have hfact : ((k + t).choose k).factorization p
      = ((Finset.Ico 1 (Nat.log p (t + k) + 1)).filter
          (fun i => p ^ i ≤ k % p ^ i + t % p ^ i)).card := by
    rw [Nat.add_comm k t]
    exact Nat.factorization_choose' hp (Nat.lt_succ_self _)
  rw [hp.dvd_iff_one_le_factorization hne, hfact]
  simp only [not_le, Nat.lt_one_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_Ico, not_le]
  constructor
  · intro h i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero]; omega
    · by_cases hib : i < Nat.log p (t + k) + 1
      · exact h ⟨hi, hib⟩
      · have hlt : t + k < p ^ i :=
          lt_of_lt_of_le (Nat.lt_pow_succ_log_self hp.one_lt (t + k))
            (Nat.pow_le_pow_right hp.pos (by omega))
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
  · intro h i _
    exact h i

/- ### The shift coordinate -/

/--
`NoCarry k t` : adding `k` and `t` in base `p` produces no carry, for every prime `p ≤ k`.
By `noCarry_iff_lt_minFac` this is exactly the membership condition of the set defining
`Erdos1095.g`, written in the coordinate `t = m - k`.
-/
def NoCarry (k t : ℕ) : Prop := ∀ p ≤ k, p.Prime → ∀ i, k / p ^ i % p + t / p ^ i % p < p

theorem noCarry_iff_forall_mod {k t : ℕ} :
    NoCarry k t ↔ ∀ p ≤ k, p.Prime → ∀ i, k % p ^ i + t % p ^ i < p ^ i := by
  constructor
  · intro h p hpk hp
    exact (forall_mod_add_lt_iff hp.pos).mpr (h p hpk hp)
  · intro h p hpk hp
    exact (forall_mod_add_lt_iff hp.pos).mp (h p hpk hp)

/-- Both quantifiers in `NoCarry` are bounded: primes are `≤ k`, and any `b` with `k < 2 ^ b`
bounds the digit index. This is what makes `NoCarry` decidable without evaluating `Nat.log`,
`Nat.choose` or `Nat.minFac`. -/
theorem noCarry_iff_bounded {k t b : ℕ} (hb : k < 2 ^ b) :
    NoCarry k t ↔ ∀ p < k + 1, p.Prime → ∀ i < b, k / p ^ i % p + t / p ^ i % p < p := by
  constructor
  · intro h p hp hpp i _
    exact h p (by omega) hpp i
  · intro h p hpk hp i
    rcases lt_or_ge i b with hi | hi
    · exact h p (by omega) hp i hi
    · have h1 : (2 : ℕ) ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      have h2 : (2 : ℕ) ^ i ≤ p ^ i := Nat.pow_le_pow_left hp.two_le i
      have h3 : k / p ^ i = 0 := Nat.div_eq_of_lt (by omega)
      have h4 : t / p ^ i % p < p := Nat.mod_lt _ hp.pos
      rw [h3]
      simpa using h4

instance decidableNoCarry (k t : ℕ) : Decidable (NoCarry k t) :=
  decidable_of_iff _ (noCarry_iff_bounded (t := t) k.lt_two_pow_self).symm

/-- **The membership condition of the set defining `Erdos1095.g`, in the shift coordinate.** -/
theorem noCarry_iff_lt_minFac {k t : ℕ} (ht : 0 < t) :
    NoCarry k t ↔ k < ((k + t).choose k).minFac := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hall : ∀ q, q.Prime → q ∣ (k + t).choose k → k + 1 ≤ q := by
        intro q hq hdvd
        by_contra hcon
        have hqk : q ≤ k := by omega
        exact absurd hdvd ((not_dvd_choose_add_iff hq).2
          (noCarry_iff_forall_mod.1 h q hqk hq))
      rcases Nat.le_minFac.2 hall with h' | h'
      · rw [Nat.choose_eq_one_iff] at h'
        omega
      · omega
  · intro h
    rw [noCarry_iff_forall_mod]
    intro p hpk hp
    rw [← not_dvd_choose_add_iff hp]
    intro hdvd
    have := Nat.minFac_le_of_dvd hp.two_le hdvd
    omega

/- ### The period of the admissible shifts -/

/-- The product of the least power of `p` exceeding `k`, over the primes `p ≤ k` (the primes
`p ≤ k` are `Nat.primesBelow (k + 1)`). -/
def modulus (k : ℕ) : ℕ := ∏ p ∈ Nat.primesBelow (k + 1), p ^ (Nat.log p k + 1)

theorem modulus_pos (k : ℕ) : 0 < modulus k :=
  Finset.prod_pos fun _ hp => Nat.pow_pos (Nat.prime_of_mem_primesBelow hp).pos

theorem pow_dvd_modulus {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    p ^ (Nat.log p k + 1) ∣ modulus k :=
  Finset.dvd_prod_of_mem _ (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩)

/-- Every multiple of `modulus k` is an admissible shift. -/
theorem noCarry_of_modulus_dvd {k t : ℕ} (h : modulus k ∣ t) : NoCarry k t := by
  intro p hpk hp i
  have ht : t / p ^ i % p < p := Nat.mod_lt _ hp.pos
  rcases lt_or_ge i (Nat.log p k + 1) with hi | hi
  · have hdvd : p ^ (i + 1) ∣ t :=
      (pow_dvd_pow p (by omega)).trans ((pow_dvd_modulus hp hpk).trans h)
    obtain ⟨c, rfl⟩ := hdvd
    have hrw : p ^ (i + 1) * c = p ^ i * (p * c) := by ring
    rw [hrw, Nat.mul_div_cancel_left _ (Nat.pow_pos hp.pos), Nat.mul_mod_right]
    have := Nat.mod_lt (k / p ^ i) hp.pos
    omega
  · have hkl : k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self hp.one_lt k
    have hz : k / p ^ i = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hkl (Nat.pow_le_pow_right hp.pos hi))
    rw [hz]
    simpa using ht

/- ### `Erdos1095.g` in the shift coordinate -/

/-- The least admissible shift: the least `t > 1` such that adding `k` and `t` in base `p`
carries for no prime `p ≤ k`. -/
noncomputable def shift (k : ℕ) : ℕ := sInf {t | 1 < t ∧ NoCarry k t}

theorem shift_le {k t : ℕ} (h1 : 1 < t) (h2 : NoCarry k t) : shift k ≤ t :=
  Nat.sInf_le ⟨h1, h2⟩

/-- The set of admissible shifts is nonempty, so `shift k` is a member of it. -/
theorem shift_mem (k : ℕ) : 1 < shift k ∧ NoCarry k (shift k) := by
  have hM := modulus_pos k
  refine Nat.sInf_mem (s := {t | 1 < t ∧ NoCarry k t}) ⟨2 * modulus k, ?_, ?_⟩
  · omega
  · exact noCarry_of_modulus_dvd ⟨2, by ring⟩

theorem shift_le_two_mul_modulus (k : ℕ) : shift k ≤ 2 * modulus k := by
  have hM := modulus_pos k
  exact shift_le (by omega) (noCarry_of_modulus_dvd ⟨2, by ring⟩)

/--
**The Erdős–Selfridge function in the shift coordinate.** `Erdos1095.g k = k + shift k`:
the `sInf` over `m` of the bespoke condition `k < (m.choose k).minFac` is the `sInf` over
`t = m - k` of a purely base-`p` carry condition.
-/
theorem g_eq_add_shift (k : ℕ) : Erdos1095.g k = k + shift k := by
  obtain ⟨hs1, hs2⟩ := shift_mem k
  have hmem : k + shift k ∈ {m | k + 1 < m ∧ k < (m.choose k).minFac} :=
    ⟨by omega, (noCarry_iff_lt_minFac (by omega)).1 hs2⟩
  have hle : Erdos1095.g k ≤ k + shift k := Nat.sInf_le hmem
  have hspec : k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac :=
    Nat.sInf_mem ⟨_, hmem⟩
  have hnc : NoCarry k (Erdos1095.g k - k) := by
    refine (noCarry_iff_lt_minFac (by omega)).2 ?_
    have hrw : k + (Erdos1095.g k - k) = Erdos1095.g k := by omega
    rw [hrw]
    exact hspec.2
  have := shift_le (show 1 < Erdos1095.g k - k by omega) hnc
  omega

/-- **`Erdos1095.g` is well defined.** The set `{m | k + 1 < m ∧ k < (m.choose k).minFac}` is
nonempty, so `Erdos1095.g k` is a member of it and in particular is not the junk value
`sInf ∅ = 0`. -/
theorem g_spec (k : ℕ) :
    k + 1 < Erdos1095.g k ∧ k < ((Erdos1095.g k).choose k).minFac := by
  obtain ⟨hs1, hs2⟩ := shift_mem k
  have hmem : k + shift k ∈ {m | k + 1 < m ∧ k < (m.choose k).minFac} :=
    ⟨by omega, (noCarry_iff_lt_minFac (by omega)).1 hs2⟩
  exact Nat.sInf_mem ⟨_, hmem⟩

/-- The upper bound coming from periodicity alone. It is very far from the companion statement
`Erdos1095.erdos_1095.variants.upper_conjecture`, which it does not prove. -/
theorem g_le_add_two_mul_modulus (k : ℕ) : Erdos1095.g k ≤ k + 2 * modulus k := by
  have h := shift_le_two_mul_modulus k
  rw [g_eq_add_shift]
  omega

/-- **Lower bounds on `Erdos1095.g` are statements about admissible shifts.** An equivalence,
so nothing is lost by passing to it. -/
theorem le_g_iff {k N : ℕ} : N ≤ Erdos1095.g k ↔ ∀ t, 1 < t → k + t < N → ¬ NoCarry k t := by
  rw [g_eq_add_shift]
  constructor
  · intro h t ht1 ht2 hnc
    have := shift_le ht1 hnc
    omega
  · intro H
    by_contra hcon
    push_neg at hcon
    obtain ⟨hs1, hs2⟩ := shift_mem k
    exact H (shift k) hs1 (by omega) hs2

/- ### An unconditional lower bound from the divisibility of admissible shifts -/

/--
**Prime powers dividing `k + 1` divide every admissible shift.** If `p ≤ k` is prime and
`p ^ i ∣ k + 1`, then the bottom `i` base-`p` digits of `k` are all `p - 1`, so an admissible
`t` must have `p ^ i ∣ t`.
-/
theorem pow_dvd_of_noCarry {k t p i : ℕ} (hp : p.Prime) (hpk : p ≤ k) (hd : p ^ i ∣ k + 1)
    (h : NoCarry k t) : p ^ i ∣ t := by
  have hq : 0 < p ^ i := Nat.pow_pos hp.pos
  obtain ⟨c, hc⟩ := hd
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h'
    · rw [Nat.mul_zero] at hc; omega
    · exact h'
  have hcomm : k + 1 = c * p ^ i := by rw [hc]; ring
  have hk : k % p ^ i = p ^ i - 1 := by
    have hstep : (c - 1) * p ^ i + p ^ i = c * p ^ i := by
      have h2 : c - 1 + 1 = c := by omega
      calc (c - 1) * p ^ i + p ^ i = (c - 1 + 1) * p ^ i := by ring
        _ = c * p ^ i := by rw [h2]
    have hkey : k = p ^ i - 1 + (c - 1) * p ^ i := by omega
    rw [hkey, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt := noCarry_iff_forall_mod.1 h p hpk hp i
  rw [hk] at hlt
  have hsucc : p ^ i - 1 + 1 = p ^ i := Nat.succ_pred_eq_of_pos hq
  have h2 : p ^ i - 1 + t % p ^ i < p ^ i - 1 + 1 := by rw [hsucc]; exact hlt
  exact Nat.dvd_of_mod_eq_zero (Nat.lt_one_iff.mp (Nat.lt_of_add_lt_add_left h2))

/-- **`k + 1` divides every admissible shift, unless `k + 1` is prime.** -/
theorem succ_dvd_shift {k : ℕ} (hnp : ¬ (k + 1).Prime) : k + 1 ∣ shift k := by
  have hs0 : shift k ≠ 0 := by have := (shift_mem k).1; omega
  rw [← Nat.factorization_le_iff_dvd (by omega) hs0, Finsupp.le_iff]
  intro p hp
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  obtain ⟨hpp, hdvd, -⟩ := hp
  have hple : p ≤ k := by
    have h1 : p ≤ k + 1 := Nat.le_of_dvd (by omega) hdvd
    rcases eq_or_lt_of_le h1 with h2 | h2
    · exact absurd (h2 ▸ hpp) hnp
    · omega
  have hpow : p ^ ((k + 1).factorization p) ∣ k + 1 := Nat.ordProj_dvd _ _
  exact (Nat.Prime.pow_dvd_iff_le_factorization hpp hs0).1
    (pow_dvd_of_noCarry hpp hple hpow (shift_mem k).2)

/--
**An unconditional lower bound on the Erdős–Selfridge function.** If `k + 1` is not prime then
`g k ≥ 2 * k + 1`. (For `k + 1` prime the statement fails in general: `g 4 = 7 < 9`.)
-/
theorem two_mul_add_one_le_g {k : ℕ} (hnp : ¬ (k + 1).Prime) : 2 * k + 1 ≤ Erdos1095.g k := by
  have h1 := succ_dvd_shift hnp
  have h2 := (shift_mem k).1
  have h3 : k + 1 ≤ shift k := Nat.le_of_dvd (by omega) h1
  have h4 := g_eq_add_shift k
  omega

/-- **A hypothesis-free corollary.** Along the odd numbers `k = 2 * j + 3` the number `k + 1` is
even, hence composite, so `two_mul_add_one_le_g` applies with no hypothesis at all: `g` is at
least linear infinitely often. (This is a corollary of the unconditional bound, not a step
towards the reward statement.) -/
theorem two_mul_add_one_le_g_odd (j : ℕ) : 2 * (2 * j + 3) + 1 ≤ Erdos1095.g (2 * j + 3) := by
  refine two_mul_add_one_le_g ?_
  intro hp
  have h2 : (2 : ℕ) ∣ 2 * j + 3 + 1 := ⟨j + 2, by ring⟩
  have := (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2)
  omega

/-- `shift 3 = 4`, proved with no search at all: `4` is admissible, and `4 ∣ shift 3`. -/
theorem shift_three : shift 3 = 4 := by
  have h1 : shift 3 ≤ 4 := shift_le (by norm_num) (by decide)
  have h2 : (3 + 1) ∣ shift 3 := succ_dvd_shift (by norm_num)
  have h3 : 0 < shift 3 := by have := (shift_mem 3).1; omega
  have h4 := Nat.le_of_dvd h3 h2
  omega

/-- `Erdos1095.g 3 = 7`, with no binomial coefficient evaluated and no candidate search. Together
with `two_mul_add_one_le_g` this shows the bound `2 * k + 1 ≤ g k` is attained. -/
theorem g_three : Erdos1095.g 3 = 7 := by rw [g_eq_add_shift, shift_three]

/-- `3` is an admissible shift for `k = 4`, so `Erdos1095.g 4 ≤ 7`. -/
theorem g_four_le : Erdos1095.g 4 ≤ 7 := by
  have h : shift 4 ≤ 3 := shift_le (by norm_num) (by decide)
  rw [g_eq_add_shift]
  omega

/-- **The hypothesis of `two_mul_add_one_le_g` cannot be dropped.** For `k = 4` the number
`k + 1 = 5` is prime, no prime `p ≤ 4` divides it, nothing forces an admissible shift to be
large, and indeed `g 4 ≤ 7 < 9 = 2 * 4 + 1`. -/
theorem not_two_mul_add_one_le_g_four : ¬ 2 * 4 + 1 ≤ Erdos1095.g 4 := by
  have h := g_four_le
  omega

/- ### The number of admissible shifts in one period -/

/-- Counting solutions of a pair of coprime periodic conditions: a Chinese remainder
bijection. -/
theorem card_filter_range_mul {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ x y : ℕ, x % a = y % a → (P x ↔ P y))
    (hQ : ∀ x y : ℕ, x % b = y % b → (Q x ↔ Q y)) :
    ((Finset.range (a * b)).filter (fun n => P n ∧ Q n)).card
      = ((Finset.range a).filter P).card * ((Finset.range b).filter Q).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij' (fun n => (n % a, n % b))
    (fun x => (Nat.chineseRemainder hab x.1 x.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ ha, ?_⟩, Nat.mod_lt _ hb, ?_⟩
    · exact (hP _ n (Nat.mod_mod_of_dvd n dvd_rfl)).mpr hn.2.1
    · exact (hQ _ n (Nat.mod_mod_of_dvd n dvd_rfl)).mpr hn.2.2
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨⟨hx1, hPx⟩, hx2, hQx⟩ := hx
    have hprop := (Nat.chineseRemainder hab x.1 x.2).prop
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
    refine ⟨Nat.chineseRemainder_lt_mul hab x.1 x.2 ha.ne' hb.ne', ?_, ?_⟩
    · exact (hP _ x.1 hprop.1).mpr hPx
    · exact (hQ _ x.2 hprop.2).mpr hQx
  · intro n hn
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
    have h1 : n ≡ (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) [MOD a * b] :=
      Nat.chineseRemainder_modEq_unique hab (Nat.mod_modEq n a).symm (Nat.mod_modEq n b).symm
    have h2 : (Nat.chineseRemainder hab (n % a) (n % b) : ℕ) < a * b :=
      Nat.chineseRemainder_lt_mul hab _ _ ha.ne' hb.ne'
    have h3 := h1
    unfold Nat.ModEq at h3
    rw [Nat.mod_eq_of_lt hn.1, Nat.mod_eq_of_lt h2] at h3
    exact h3.symm
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨⟨hx1, -⟩, hx2, -⟩ := hx
    have hprop := (Nat.chineseRemainder hab x.1 x.2).prop
    have e1 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % a = x.1 := by
      have h1 := hprop.1
      unfold Nat.ModEq at h1
      rw [h1, Nat.mod_eq_of_lt hx1]
    have e2 : (Nat.chineseRemainder hab x.1 x.2 : ℕ) % b = x.2 := by
      have h2 := hprop.2
      unfold Nat.ModEq at h2
      rw [h2, Nat.mod_eq_of_lt hx2]
    exact Prod.ext e1 e2

/-- The multiplicative counting principle for a family of pairwise coprime periodic
conditions. -/
theorem card_filter_range_prod {ι : Type*} [DecidableEq ι] (M : ι → ℕ) (P : ι → ℕ → Prop)
    [∀ i, DecidablePred (P i)] (S : Finset ι) (hM : ∀ i ∈ S, 0 < M i)
    (hP : ∀ i ∈ S, ∀ x y : ℕ, x % M i = y % M i → (P i x ↔ P i y))
    (hcop : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (M i) (M j)) :
    ((Finset.range (∏ i ∈ S, M i)).filter (fun n => ∀ i ∈ S, P i n)).card
      = ∏ i ∈ S, ((Finset.range (M i)).filter (P i)).card := by
  revert hM hP hcop
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert a S ha ih =>
    intro hM hP hcop
    have hMS : ∀ i ∈ S, 0 < M i := fun i hi => hM i (Finset.mem_insert_of_mem hi)
    have hPS : ∀ i ∈ S, ∀ x y : ℕ, x % M i = y % M i → (P i x ↔ P i y) :=
      fun i hi => hP i (Finset.mem_insert_of_mem hi)
    have hprodpos : 0 < ∏ i ∈ S, M i := Finset.prod_pos hMS
    have hcopS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Nat.Coprime (M i) (M j) := by
      intro i hi j hj hij
      exact hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcopa : Nat.Coprime (M a) (∏ i ∈ S, M i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (Finset.mem_insert_self a S) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact ha hi)
    have hQ : ∀ x y : ℕ, x % (∏ i ∈ S, M i) = y % (∏ i ∈ S, M i) →
        ((∀ i ∈ S, P i x) ↔ (∀ i ∈ S, P i y)) := by
      intro x y hxy
      have key : ∀ i ∈ S, x % M i = y % M i := by
        intro i hi
        have hdvd : M i ∣ ∏ j ∈ S, M j := Finset.dvd_prod_of_mem M hi
        rw [← Nat.mod_mod_of_dvd x hdvd, hxy, Nat.mod_mod_of_dvd y hdvd]
      exact ⟨fun h i hi => (hPS i hi x y (key i hi)).mp (h i hi),
        fun h i hi => (hPS i hi x y (key i hi)).mpr (h i hi)⟩
    have hfil : (Finset.range (M a * ∏ i ∈ S, M i)).filter
          (fun n => ∀ i ∈ insert a S, P i n)
        = (Finset.range (M a * ∏ i ∈ S, M i)).filter (fun n => P a n ∧ ∀ i ∈ S, P i n) := by
      refine Finset.filter_congr fun n _ => ?_
      simp
    simp only [Finset.prod_insert ha]
    rw [hfil, card_filter_range_mul hcopa (hM a (Finset.mem_insert_self a S)) hprodpos (P a)
      (fun n => ∀ i ∈ S, P i n) (hP a (Finset.mem_insert_self a S)) hQ, ih hMS hPS hcopS]

/-- **The number of carry-free residues in one base-`p` block.** Exactly
`∏ i < e, (p - k_i)` of the residues `t < p ^ e` add to `k` without a carry in the bottom `e`
digits, where `k_i` is the `i`-th base-`p` digit of `k`. -/
theorem card_filter_digit_add_lt (p : ℕ) (hp : 0 < p) :
    ∀ e k : ℕ,
      ((Finset.range (p ^ e)).filter
          (fun t => ∀ i < e, k / p ^ i % p + t / p ^ i % p < p)).card
        = ∏ i ∈ Finset.range e, (p - k / p ^ i % p) := by
  intro e
  induction e with
  | zero => intro k; simp
  | succ e ih =>
    intro k
    have hstep : ∀ x j : ℕ, x / p ^ (j + 1) = x / p / p ^ j := by
      intro x j
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    have hcard :
        ((Finset.range (p ^ (e + 1))).filter
            (fun t => ∀ i < e + 1, k / p ^ i % p + t / p ^ i % p < p)).card
          = (((Finset.range p).filter (fun r => k % p + r < p)) ×ˢ
              ((Finset.range (p ^ e)).filter
                (fun q => ∀ i < e, k / p / p ^ i % p + q / p ^ i % p < p))).card := by
      refine Finset.card_nbij' (fun m => (m % p, m / p)) (fun x => x.1 + x.2 * p) ?_ ?_ ?_ ?_
      · intro m hm
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hm
        obtain ⟨hm1, hm2⟩ := hm
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, ?_, ?_⟩
        · have h0 := hm2 0 (Nat.succ_pos e)
          simpa using h0
        · rw [Nat.div_lt_iff_lt_mul hp, ← pow_succ]
          exact hm1
        · intro i hi
          have h1 := hm2 (i + 1) (by omega)
          rwa [hstep k i, hstep m i] at h1
      · intro x hx
        simp only [Finset.mem_product, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_range] at hx
        obtain ⟨⟨hr1, hr2⟩, hq1, hq2⟩ := hx
        have hmodr : (x.1 + x.2 * p) % p = x.1 := by
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr1]
        have hdivq : (x.1 + x.2 * p) / p = x.2 := by
          rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr1, Nat.zero_add]
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
        constructor
        · have h2 : (x.2 + 1) * p ≤ p ^ e * p := Nat.mul_le_mul_right p hq1
          have h3 : (x.2 + 1) * p = x.2 * p + p := by ring
          rw [pow_succ]
          omega
        · intro i hi
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · simpa [hmodr] using hr2
          · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            rw [hstep k j, hstep (x.1 + x.2 * p) j, hdivq]
            exact hq2 j (by omega)
      · intro m _
        exact Nat.mod_add_div' m p
      · intro x hx
        simp only [Finset.mem_product, Finset.mem_coe, Finset.mem_filter,
          Finset.mem_range] at hx
        obtain ⟨⟨hr1, hr2⟩, hq1, hq2⟩ := hx
        have hmodr : (x.1 + x.2 * p) % p = x.1 := by
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr1]
        have hdivq : (x.1 + x.2 * p) / p = x.2 := by
          rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr1, Nat.zero_add]
        simp [hmodr, hdivq]
    rw [hcard, Finset.card_product, ih (k / p)]
    obtain ⟨d, hd, hdp⟩ : ∃ d, k % p = d ∧ d < p := ⟨k % p, rfl, Nat.mod_lt _ hp⟩
    have hA : ((Finset.range p).filter (fun r => k % p + r < p)) = Finset.range (p - k % p) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, hd]
      omega
    rw [hA, Finset.card_range, Finset.prod_range_succ']
    have hd : ∀ i, k / p / p ^ i % p = k / p ^ (i + 1) % p := by
      intro i; rw [hstep k i]
    simp only [hd, pow_zero, Nat.div_one]
    ring

/-- The bottom `e` base-`p` digit conditions depend only on the residue modulo `p ^ e`. -/
theorem digit_add_lt_congr_mod {p k e a b : ℕ} (h : a % p ^ e = b % p ^ e) :
    (∀ i < e, k / p ^ i % p + a / p ^ i % p < p) ↔
      (∀ i < e, k / p ^ i % p + b / p ^ i % p < p) := by
  have key : ∀ i < e, a / p ^ i % p = b / p ^ i % p := by
    intro i hi
    have hdvd : p ^ (i + 1) ∣ p ^ e := pow_dvd_pow p (by omega)
    have hab : a % p ^ (i + 1) = b % p ^ (i + 1) := by
      rw [← Nat.mod_mod_of_dvd a hdvd, h, Nat.mod_mod_of_dvd b hdvd]
    have ha : a % (p ^ i * p) / p ^ i = a / p ^ i % p := Nat.mod_mul_right_div_self a _ _
    have hb : b % (p ^ i * p) / p ^ i = b / p ^ i % p := Nat.mod_mul_right_div_self b _ _
    rw [← ha, ← hb, ← pow_succ, hab]
  constructor
  · intro H i hi; rw [← key i hi]; exact H i hi
  · intro H i hi; rw [key i hi]; exact H i hi

/-- `NoCarry` with both quantifiers cut to the ranges that the period `modulus k` sees. -/
theorem noCarry_iff_primesBelow {k t : ℕ} :
    NoCarry k t ↔
      ∀ p ∈ Nat.primesBelow (k + 1), ∀ i < Nat.log p k + 1,
        k / p ^ i % p + t / p ^ i % p < p := by
  constructor
  · intro h p hp i _
    obtain ⟨hlt, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact h p (by omega) hpp i
  · intro h p hpk hp i
    rcases lt_or_ge i (Nat.log p k + 1) with hi | hi
    · exact h p (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩) i hi
    · have he : k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self hp.one_lt k
      have h1 : p ^ (Nat.log p k + 1) ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi
      have h2 : k / p ^ i = 0 := Nat.div_eq_of_lt (by omega)
      have h3 : t / p ^ i % p < p := Nat.mod_lt _ hp.pos
      rw [h2]
      simpa using h3

/--
**The exact number of admissible shifts in one period.** Of the `modulus k` residues, exactly
`∏_{p ≤ k} ∏_{i ≤ log_p k} (p - k_i(p))` are admissible, where `k_i(p)` is the `i`-th base-`p`
digit of `k`. This is the density that underlies the heuristic of [SSW20].
-/
theorem card_noCarry_period (k : ℕ) :
    ((Finset.range (modulus k)).filter (fun t => NoCarry k t)).card
      = ∏ p ∈ Nat.primesBelow (k + 1), ∏ i ∈ Finset.range (Nat.log p k + 1),
          (p - k / p ^ i % p) := by
  have hcop : ∀ p ∈ Nat.primesBelow (k + 1), ∀ q ∈ Nat.primesBelow (k + 1), p ≠ q →
      Nat.Coprime (p ^ (Nat.log p k + 1)) (q ^ (Nat.log q k + 1)) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _
      ((Nat.coprime_primes (Nat.prime_of_mem_primesBelow hp)
        (Nat.prime_of_mem_primesBelow hq)).mpr hpq)
  have key := card_filter_range_prod (fun p => p ^ (Nat.log p k + 1))
      (fun p t => ∀ i < Nat.log p k + 1, k / p ^ i % p + t / p ^ i % p < p)
      (Nat.primesBelow (k + 1))
      (fun p hp => Nat.pow_pos (Nat.prime_of_mem_primesBelow hp).pos)
      (fun _ _ x y hxy => digit_add_lt_congr_mod hxy) hcop
  have hprod : ∏ p ∈ Nat.primesBelow (k + 1),
        ((Finset.range (p ^ (Nat.log p k + 1))).filter
          (fun t => ∀ i < Nat.log p k + 1, k / p ^ i % p + t / p ^ i % p < p)).card
      = ∏ p ∈ Nat.primesBelow (k + 1), ∏ i ∈ Finset.range (Nat.log p k + 1),
          (p - k / p ^ i % p) :=
    Finset.prod_congr rfl fun p hp =>
      card_filter_digit_add_lt p (Nat.prime_of_mem_primesBelow hp).pos _ k
  rw [← hprod, ← key, modulus]
  exact congrArg Finset.card (Finset.filter_congr fun m _ => noCarry_iff_primesBelow)

/--
**Long admissible-free windows exist.** If the admissible residues are sparse enough in one
period, then some window of length `L` contains no admissible shift at all. The window is not
located: this is exactly the gap between the average behaviour and the reward statement, which
asks for the window starting at `t = 2`.
-/
theorem exists_noCarry_free_window (k L : ℕ)
    (h : (((Finset.range (modulus k)).filter (fun t => NoCarry k t)).card + 1) * L
      ≤ modulus k) :
    ∃ x, ∀ t, x ≤ t → t < x + L → ¬ NoCarry k t := by
  by_contra hcon
  push_neg at hcon
  choose f hf1 hf2 hf3 using hcon
  set C := ((Finset.range (modulus k)).filter (fun t => NoCarry k t)).card with hC
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · exact absurd (hf2 0) (by omega)
    · exact hL
  have hmaps : Set.MapsTo (fun j => f (j * L)) (Finset.range (C + 1) : Set ℕ)
      (((Finset.range (modulus k)).filter (fun t => NoCarry k t)) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    simp only [Finset.mem_coe]
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hf3 _⟩
    have h1 : f (j * L) < j * L + L := hf2 _
    have h2 : (j + 1) * L ≤ (C + 1) * L := Nat.mul_le_mul_right L (by omega)
    have h3 : (j + 1) * L = j * L + L := by ring
    omega
  have hinj : Set.InjOn (fun j => f (j * L)) (Finset.range (C + 1) : Set ℕ) := by
    intro i _ j _ hij
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · have h1 : f (i * L) < i * L + L := hf2 _
      have h2 : j * L ≤ f (j * L) := hf1 _
      have h3 : (i + 1) * L ≤ j * L := Nat.mul_le_mul_right L (by omega)
      have h4 : (i + 1) * L = i * L + L := by ring
      simp only at hij
      omega
    · have hlt : j < i := by omega
      have h1 : f (j * L) < j * L + L := hf2 _
      have h2 : i * L ≤ f (i * L) := hf1 _
      have h3 : (j + 1) * L ≤ i * L := Nat.mul_le_mul_right L (by omega)
      have h4 : (j + 1) * L = j * L + L := by ring
      simp only at hij
      omega
  have hle := Finset.card_le_card_of_injOn (fun j => f (j * L)) hmaps hinj
  rw [Finset.card_range, ← hC] at hle
  omega

/- ### A checked instance of the count -/

theorem modulus_thirteen : modulus 13 = 10821610800 := by
  have hP : Nat.primesBelow (13 + 1) = ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by decide
  have h2 : Nat.log 2 13 = 3 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 13 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5 : Nat.log 5 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h7 : Nat.log 7 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h11 : Nat.log 11 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h13 : Nat.log 13 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [modulus, hP]
  norm_num [Finset.prod_insert, h2, h3, h5, h7, h11, h13]

/--
**A checked instance of the counting formula.** For `k = 13` the period is `10821610800` and
exactly `8087040` of its residues are admissible shifts. The `Finset` on the left has more than
`10 ^ 10` elements, so this value is out of reach of `decide`; the formula turns it into a
product over six primes.
-/
theorem card_noCarry_period_thirteen :
    ((Finset.range (modulus 13)).filter (fun t => NoCarry 13 t)).card = 8087040 := by
  have hP : Nat.primesBelow (13 + 1) = ({2, 3, 5, 7, 11, 13} : Finset ℕ) := by decide
  have h2 : Nat.log 2 13 = 3 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h3 : Nat.log 3 13 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h5 : Nat.log 5 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h7 : Nat.log 7 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h11 : Nat.log 11 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h13 : Nat.log 13 13 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rw [card_noCarry_period, hP]
  norm_num [Finset.prod_insert, h2, h3, h5, h7, h11, h13, Finset.prod_range_succ]

/-- A checked long gap: for `k = 13` some window of `1338` consecutive integers contains no
admissible shift. -/
theorem exists_noCarry_free_window_thirteen :
    ∃ x, ∀ t, x ≤ t → t < x + 1338 → ¬ NoCarry 13 t := by
  refine exists_noCarry_free_window 13 1338 ?_
  rw [card_noCarry_period_thirteen, modulus_thirteen]
  norm_num

/- ### The reward statement, in the shift coordinate -/

/--
**The reward statement with no `sInf`, no `Nat.choose` and no `Nat.minFac`.**
`Erdos1095.erdos_1095.variants.lower_conjecture` holds if and only if there is `c > 0` such that
for all large `k` no `t > 1` with `k + t < exp (c * k / log k)` is carry-free with `k` in every
base `p ≤ k`. Being an `Iff` this is not a wrong-direction reduction.
-/
theorem lower_conjecture_iff_noCarry :
    (∃ c > 0, ∀ᶠ k : ℕ in atTop, (Erdos1095.g k : ℝ) ≥ exp (c * k / log k)) ↔
      ∃ c > 0, ∀ᶠ k : ℕ in atTop, ∀ t : ℕ, 1 < t → (k : ℝ) + t < exp (c * k / log k) →
        ¬ NoCarry k t := by
  constructor <;> rintro ⟨c, hc, h⟩ <;> refine ⟨c, hc, ?_⟩
  · filter_upwards [h] with k hk
    intro t ht1 ht2
    have hle : ⌈exp (c * k / log k)⌉₊ ≤ Erdos1095.g k := Nat.ceil_le.mpr hk
    refine le_g_iff.mp hle t ht1 (Nat.lt_ceil.mpr ?_)
    push_cast
    exact ht2
  · filter_upwards [h] with k hk
    rw [ge_iff_le, ← Nat.ceil_le]
    refine le_g_iff.mpr fun t ht1 ht2 hnc => ?_
    refine hk t ht1 ?_ hnc
    have h2 := Nat.lt_ceil.mp ht2
    push_cast at h2
    exact h2

/-- **Worked use site.** The literal reward statement
`∃ c > 0, ∀ᶠ k in atTop, (Erdos1095.g k : ℝ) ≥ exp (c * k / log k)`, reached from an explicit
covering: a family of bounds `N k` together with, for all large `k` and every `t` below `N k`, a
prime `p ≤ k` and a digit position at which adding `k` and `t` in base `p` carries. This is the
shape that a sieve argument for the conjecture produces. Both hypotheses are eventual, so a sieve
controlling only large `k` suffices; `lower_conjecture_iff_covering` shows the hypotheses are
exactly equivalent to the conclusion, so nothing has been given away. -/
theorem lower_conjecture_of_covering (N : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hN : ∀ᶠ k : ℕ in atTop, exp (c * k / log k) ≤ N k)
    (hcov : ∀ᶠ k : ℕ in atTop, ∀ t : ℕ, 1 < t → k + t < N k →
      ∃ p ≤ k, p.Prime ∧ ∃ i, p ≤ k / p ^ i % p + t / p ^ i % p) :
    ∃ c > 0, ∀ᶠ k : ℕ in atTop, (Erdos1095.g k : ℝ) ≥ exp (c * k / log k) := by
  refine ⟨c, hc, ?_⟩
  filter_upwards [hN, hcov] with k hNk hcovk
  have h1 : N k ≤ Erdos1095.g k := by
    refine le_g_iff.mpr fun t ht1 ht2 hnc => ?_
    obtain ⟨p, hpk, hp, i, hi⟩ := hcovk t ht1 ht2
    exact absurd (hnc p hpk hp i) (by omega)
  rw [ge_iff_le]
  calc exp (c * k / log k) ≤ (N k : ℝ) := hNk
    _ ≤ (Erdos1095.g k : ℝ) := Nat.cast_le.mpr h1

/--
**The covering data is equivalent to the reward statement.** The hypotheses of
`lower_conjecture_of_covering` are not stronger than what they prove: given the conjecture, the
bound `N = Erdos1095.g` itself supplies the covering (by `le_g_iff`, no `t` with `1 < t` and
`k + t < g k` is carry-free). So the use site is a lossless reformulation, and the remaining task
is genuinely the analytic one of producing an explicit `N k` of size `exp (c * k / log k)` and a
carrying prime for every `t` below it.
-/
theorem lower_conjecture_iff_covering :
    (∃ c > 0, ∀ᶠ k : ℕ in atTop, (Erdos1095.g k : ℝ) ≥ exp (c * k / log k)) ↔
      ∃ (N : ℕ → ℕ) (c : ℝ), 0 < c ∧ (∀ᶠ k : ℕ in atTop, exp (c * k / log k) ≤ N k) ∧
        ∀ᶠ k : ℕ in atTop, ∀ t : ℕ, 1 < t → k + t < N k →
          ∃ p ≤ k, p.Prime ∧ ∃ i, p ≤ k / p ^ i % p + t / p ^ i % p := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨Erdos1095.g, c, hc, ?_, .of_forall fun k t ht1 ht2 => ?_⟩
    · filter_upwards [h] with k hk
      exact hk
    · have hnc : ¬ NoCarry k t := le_g_iff.mp le_rfl t ht1 ht2
      by_contra hcon
      push_neg at hcon
      exact hnc fun p hpk hp i => hcon p hpk hp i
  · rintro ⟨N, c, hc, hN, hcov⟩
    exact lower_conjecture_of_covering N c hc hN hcov

end Contribution.Erdos1095Shift
