import Mathlib
import FormalConjectures.ErdosProblems.«699»

/-!
# Erdős 699: a base-`p` carry criterion for `p ∣ gcd (n.choose i) (n.choose j)`

Target: `Erdos699.erdos_699`, whose statement is
`True ↔ ∀ n i j, 1 ≤ i → i < j → j ≤ n / 2 →
  ∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)`.

## The obstacle

The reward obligation asks for a *prime dividing a gcd of two binomial coefficients*. Nothing in
Mathlib produces such a prime: the available divisibility criteria are `Nat.Prime.dvd_choose`
(which needs both `k < p` **and** `n - k < p`, so it is useless in the regime `i < j ≤ n / 2`
where `p` is tiny compared with `n`), `Nat.Prime.dvd_choose_pow` (only for `n` a prime power) and
Kummer's theorem in the form `Nat.factorization_choose`, which computes the `p`-adic valuation as
the cardinality of a `Finset.filter` over `Finset.Ico 1 b` whose predicate
`p ^ t ≤ k % p ^ t + (n - k) % p ^ t` is a *carry* condition, not a divisibility statement. So a
solver must, every single time, unfold `Nat.gcd` into two divisibilities, turn each into a
`factorization` inequality, choose a bound `b`, and translate the carry predicate back into
something usable. Worse, the problem is tagged as falsifiable by a finite counterexample, but a
search cannot evaluate `Nat.choose n i` for the relevant `n`.

## What is proved here

* `mod_lt_mod_iff_le_add_mod` and `add_mod_lt_iff` convert Kummer's carry predicate into the
  arithmetic form `n % q < k % q`, which is what one actually reasons with.
* `prime_dvd_choose_iff_exists_mod_pow_lt` is the resulting criterion:
  `p ∣ n.choose k ↔ ∃ t, 0 < t ∧ n % p ^ t < k % p ^ t` (for `k ≤ n`), i.e. Kummer's theorem
  packaged as a divisibility test. `prime_dvd_choose_of_mod_pow_lt` is the hypothesis-free
  sufficient half, and `prime_dvd_choose_iff_exists_le_log` bounds the search to
  `Finset.Icc 1 (Nat.log p n)`, making the criterion a *finite, `decide`-able check* that never
  evaluates the binomial coefficient.
* `prime_dvd_choose_iff_mod_lt`: for `k < p` the criterion collapses to a single congruence,
  `p ∣ n.choose k ↔ n % p < k`. Hence `prime_dvd_gcd_choose_iff_mod_lt`: for a prime `p > j`,
  `p ∣ Nat.gcd (n.choose i) (n.choose j) ↔ n % p < i`. The gcd, both binomial coefficients and
  the factorials disappear.
* `exists_prime_ge_dvd_gcd_choose_iff` is the reformulation a prover wants: the target's
  existential is equivalent to a disjunction, an `rcases`-friendly split into the *bounded* search
  `i ≤ p ≤ j` and the purely modular condition `∃ p prime, j < p ∧ n % p < i`.
  `le_mod_of_not_exists_prime_ge_dvd` is the contrapositive: a counterexample `(n, i, j)` must
  satisfy `i ≤ n % p` for **every** prime `p > j`, which is the shape a search needs, and
  `erdos_699_of_prime_dvd` disposes of every `n` having a prime factor above `j`.
* `div_gcd_dvd_choose : n / Nat.gcd n k ∣ n.choose k` (for `0 < n`) is the classical sharpening of
  `n ∣ k * n.choose k` coming from `Nat.add_one_mul_choose_eq`; it is not in Mathlib. With it,
  `erdos_699_index_one` settles the whole `i = 1` case of the target: for `1 < j ≤ n / 2` there
  really is a prime dividing `Nat.gcd (n.choose 1) (n.choose j)`.
* `gcd_choose_ten` and `gcd_choose_twentyEight` are checked computations (the second confirms the
  value `2 ^ 3 * 3 ^ 3 * 5` recorded on erdosproblems.com). They give two checked obstructions,
  `not_exists_prime_gt_dvd_gcd_choose_ten` and `not_exists_prime_gt_dvd_gcd_choose_twentyEight`:
  by `mem_of_forall_exists_prime_gt`, both `(10, 3, 5)` and `(28, 5, 14)` — the latter being the
  only exception with `i ≥ 4` known in the literature — belong to *every* exceptional set `E`
  admissible in `Erdos699.erdos_szekeres_strengthening`. Meanwhile
  `exists_prime_ge_dvd_gcd_choose_ten` and `exists_prime_ge_dvd_gcd_choose_twentyEight` show the
  weaker bound `i ≤ p` of `Erdos699.erdos_699` does hold at both triples. So the `≤` of `i ≤ p`
  cannot be strengthened to `<`, and the two open theorems of the target file,
  `Erdos699.erdos_699` and `Erdos699.erdos_szekeres_strengthening`, are genuinely different.

A later solver can use declaration
`Contribution.Erdos699Carries.exists_prime_ge_dvd_gcd_choose_iff` to discharge or simplify
obligation `∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)` in target
`Erdos699.erdos_699`, replacing it by the disjunction "a prime in `[i, j]` divides the gcd, or
some prime `p > j` has `n % p < i`"; `erdos_699_of_split` packages that reduction for the whole
statement, and the final section contains worked use sites stated with the reward theorem's own
binders.

*References:*
- [erdosproblems.com/699](https://www.erdosproblems.com/699)
- Erdős, P. and Szekeres, G., *Some number theoretic problems on binomial coefficients*,
  Austral. Math. Soc. Gaz. 5 (1978), 97-99.
- Guy, R. K., *Unsolved Problems in Number Theory*, 3rd ed., Springer (2004), problem B31.
- Kummer, E. E., *Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen*,
  J. Reine Angew. Math. 44 (1852), 93-146.
-/

namespace Contribution.Erdos699Carries

open Finset

/- ### Carries in base `p`, written with `%` -/

/-- A carry occurs when adding `a` and `b` in a single base-`q` digit exactly when the resulting
digit drops below `a`. -/
theorem add_mod_lt_iff {q a b : ℕ} (ha : a < q) (hb : b < q) : (a + b) % q < a ↔ q ≤ a + b := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    rw [Nat.mod_eq_of_lt hcon] at h
    omega
  · intro h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The dictionary between Kummer's carry predicate, as it appears in
`Nat.factorization_choose`, and the arithmetic condition `n % q < k % q`. -/
theorem mod_lt_mod_iff_le_add_mod {q n k : ℕ} (hq : 0 < q) (hkn : k ≤ n) :
    n % q < k % q ↔ q ≤ k % q + (n - k) % q := by
  have h1 : n % q = (k % q + (n - k) % q) % q := by
    conv_lhs => rw [← Nat.add_sub_cancel' hkn, Nat.add_mod]
  rw [h1]
  exact add_mod_lt_iff (Nat.mod_lt _ hq) (Nat.mod_lt _ hq)

/-- Carries between `k` and `n` can only happen among the base-`p` digits that `n` actually has:
this is what makes the criterion below a finite check. -/
theorem le_log_of_mod_pow_lt {p n k t : ℕ} (hp : 1 < p) (hkn : k ≤ n)
    (h : n % p ^ t < k % p ^ t) : t ≤ Nat.log p n := by
  by_contra hcon
  push_neg at hcon
  have hn : n < p ^ t := Nat.lt_pow_of_log_lt hp hcon
  rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (lt_of_le_of_lt hkn hn)] at h
  omega

/- ### Kummer's theorem as a divisibility criterion -/

/-- **Kummer's theorem, as a divisibility test.** For a prime `p` and `k ≤ n`, `p` divides
`n.choose k` exactly when some base-`p` truncation of `n` is smaller than the corresponding
truncation of `k`. Mathlib only offers the valuation formula `Nat.factorization_choose`, whose
carry predicate is stated as `p ^ t ≤ k % p ^ t + (n - k) % p ^ t`. -/
theorem prime_dvd_choose_iff_exists_mod_pow_lt {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    p ∣ n.choose k ↔ ∃ t, 0 < t ∧ n % p ^ t < k % p ^ t := by
  have hne : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hcard : p ∣ n.choose k ↔
      1 ≤ #{t ∈ Finset.Ico 1 (Nat.log p n + 1) | p ^ t ≤ k % p ^ t + (n - k) % p ^ t} := by
    rw [hp.dvd_iff_one_le_factorization hne, Nat.factorization_choose hp hkn (Nat.lt_add_one _)]
  rw [hcard]
  constructor
  · intro h
    obtain ⟨t, ht, hcarry⟩ := Finset.filter_nonempty_iff.mp (Finset.card_pos.mp h)
    rw [Finset.mem_Ico] at ht
    exact ⟨t, ht.1, (mod_lt_mod_iff_le_add_mod (pow_pos hp.pos t) hkn).mpr hcarry⟩
  · rintro ⟨t, ht, hlt⟩
    have hlog := le_log_of_mod_pow_lt hp.one_lt hkn hlt
    exact Finset.card_pos.mpr (Finset.filter_nonempty_iff.mpr
      ⟨t, Finset.mem_Ico.mpr ⟨ht, by omega⟩,
        (mod_lt_mod_iff_le_add_mod (pow_pos hp.pos t) hkn).mp hlt⟩)

/-- **The finite form of the criterion.** Only the `Nat.log p n` lowest base-`p` digits can carry,
so `p ∣ n.choose k` is decided by a bounded search that never evaluates `n.choose k`. This is the
test a counterexample search for `Erdos699.erdos_699` needs. -/
theorem prime_dvd_choose_iff_exists_le_log {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    p ∣ n.choose k ↔ ∃ t ∈ Finset.Icc 1 (Nat.log p n), n % p ^ t < k % p ^ t := by
  rw [prime_dvd_choose_iff_exists_mod_pow_lt hp hkn]
  constructor
  · rintro ⟨t, ht, hlt⟩
    exact ⟨t, Finset.mem_Icc.mpr ⟨ht, le_log_of_mod_pow_lt hp.one_lt hkn hlt⟩, hlt⟩
  · rintro ⟨t, ht, hlt⟩
    exact ⟨t, (Finset.mem_Icc.mp ht).1, hlt⟩

/-- The sufficient half of `prime_dvd_choose_iff_exists_mod_pow_lt`, with no side condition:
one carry in base `p` already forces `p ∣ n.choose k`. -/
theorem prime_dvd_choose_of_mod_pow_lt {p n k t : ℕ} (hp : p.Prime) (ht : 0 < t)
    (h : n % p ^ t < k % p ^ t) : p ∣ n.choose k := by
  rcases le_or_gt k n with hkn | hkn
  · exact (prime_dvd_choose_iff_exists_mod_pow_lt hp hkn).mpr ⟨t, ht, h⟩
  · simp [Nat.choose_eq_zero_of_lt hkn]

/-- For `k < p` the carry criterion collapses to a single congruence condition on `n`:
`p ∣ n.choose k ↔ n % p < k`. This is the workhorse for primes above the top index. -/
theorem prime_dvd_choose_iff_mod_lt {p n k : ℕ} (hp : p.Prime) (hkp : k < p) :
    p ∣ n.choose k ↔ n % p < k := by
  rcases le_or_gt k n with hkn | hkn
  · rw [prime_dvd_choose_iff_exists_mod_pow_lt hp hkn]
    constructor
    · rintro ⟨t, ht, hlt⟩
      have hk : k % p ^ t = k := Nat.mod_eq_of_lt (hkp.trans_le (Nat.le_self_pow ht.ne' p))
      rw [hk] at hlt
      have hmm : n % p ^ t % p = n % p := Nat.mod_mod_of_dvd _ (dvd_pow_self p ht.ne')
      rw [← hmm, Nat.mod_eq_of_lt (hlt.trans hkp)]
      exact hlt
    · intro h
      exact ⟨1, one_pos, by simpa [Nat.mod_eq_of_lt hkp] using h⟩
  · rw [Nat.choose_eq_zero_of_lt hkn]
    simp only [dvd_zero, true_iff]
    exact lt_of_le_of_lt (Nat.mod_le n p) hkn

/- ### The reward statement's existential -/

/-- For a prime `p` strictly above the larger index `j`, membership of `p` in the reward
statement's conclusion is a purely modular condition on `n`. -/
theorem prime_dvd_gcd_choose_iff_mod_lt {p n i j : ℕ} (hp : p.Prime) (hij : i ≤ j) (hjp : j < p) :
    p ∣ Nat.gcd (n.choose i) (n.choose j) ↔ n % p < i := by
  rw [Nat.dvd_gcd_iff, prime_dvd_choose_iff_mod_lt hp (lt_of_le_of_lt hij hjp),
    prime_dvd_choose_iff_mod_lt hp hjp]
  exact ⟨fun h => h.1, fun h => ⟨h, h.trans_le hij⟩⟩

/-- **The reformulation.** The conclusion of `Erdos699.erdos_699` splits into a bounded search
over primes in `[i, j]` and a purely modular condition on the primes above `j`. -/
theorem exists_prime_ge_dvd_gcd_choose_iff {n i j : ℕ} (hij : i ≤ j) :
    (∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)) ↔
      (∃ p, p.Prime ∧ i ≤ p ∧ p ≤ j ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)) ∨
      (∃ p, p.Prime ∧ j < p ∧ n % p < i) := by
  constructor
  · rintro ⟨p, hp, hip, hdvd⟩
    rcases le_or_gt p j with h | h
    · exact Or.inl ⟨p, hp, hip, h, hdvd⟩
    · exact Or.inr ⟨p, hp, h, (prime_dvd_gcd_choose_iff_mod_lt hp hij h).mp hdvd⟩
  · rintro (⟨p, hp, hip, _, hdvd⟩ | ⟨p, hp, hjp, hmod⟩)
    · exact ⟨p, hp, hip, hdvd⟩
    · exact ⟨p, hp, hij.trans hjp.le, (prime_dvd_gcd_choose_iff_mod_lt hp hij hjp).mpr hmod⟩

/-- The shape of a counterexample: if `(n, i, j)` fails the reward statement then `n` is at least
`i` modulo *every* prime above `j`. -/
theorem le_mod_of_not_exists_prime_ge_dvd {n i j : ℕ} (hij : i ≤ j)
    (h : ¬ ∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)) :
    ∀ p, p.Prime → j < p → i ≤ n % p := by
  intro p hp hjp
  by_contra hcon
  push_neg at hcon
  exact h ((exists_prime_ge_dvd_gcd_choose_iff hij).mpr (Or.inr ⟨p, hp, hjp, hcon⟩))

/-- A ready-made sufficient condition: any prime factor of `n` exceeding `j` witnesses the reward
statement's conclusion at `(n, i, j)`. -/
theorem erdos_699_of_prime_dvd {n i j p : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hij : i ≤ j)
    (hjp : j < p) (hdvd : p ∣ n) :
    ∃ q, q.Prime ∧ i ≤ q ∧ q ∣ Nat.gcd (n.choose i) (n.choose j) := by
  refine (exists_prime_ge_dvd_gcd_choose_iff hij).mpr (Or.inr ⟨p, hp, hjp, ?_⟩)
  obtain ⟨c, rfl⟩ := hdvd
  rw [Nat.mul_mod_right]
  omega

/- ### The case `i = 1`, in full -/

/-- The classical divisibility `n / gcd (n, k) ∣ n.choose k`, which is not in Mathlib. It is the
sharp form of `n ∣ k * n.choose k`. -/
theorem div_gcd_dvd_choose {n k : ℕ} (hn : 0 < n) : n / Nat.gcd n k ∣ n.choose k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Nat.div_self hn]
  have hdvd : n ∣ k * n.choose k := by
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨n.choose k, by rw [Nat.add_one_mul_choose_eq, mul_comm]⟩
  have hd0 : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left k hn
  have hcop : Nat.Coprime (n / Nat.gcd n k) (k / Nat.gcd n k) := Nat.coprime_div_gcd_div_gcd hd0
  refine hcop.dvd_of_dvd_mul_left ?_
  refine (mul_dvd_mul_iff_left hd0.ne').mp ?_
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left n k), ← mul_assoc,
    Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)]
  exact hdvd

/-- **The case `i = 1` of `Erdos699.erdos_699`, proved.** For `1 < j ≤ n / 2` there is a prime
dividing `Nat.gcd (n.choose 1) (n.choose j)`; the witness is any prime factor of
`n / gcd (n, j) ≥ 2`. -/
theorem erdos_699_index_one {n j : ℕ} (hj : 1 < j) (hjn : j ≤ n / 2) :
    ∃ p, p.Prime ∧ 1 ≤ p ∧ p ∣ Nat.gcd (n.choose 1) (n.choose j) := by
  have h2j : 2 * j ≤ n := by omega
  have hn : 0 < n := by omega
  have hd0 : 0 < Nat.gcd n j := Nat.gcd_pos_of_pos_left j hn
  have hdj : Nat.gcd n j ≤ j := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right n j)
  have hmul : n / Nat.gcd n j * Nat.gcd n j = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n j)
  have hm : 2 ≤ n / Nat.gcd n j := by
    refine Nat.le_of_mul_le_mul_right ?_ hd0
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show n / Nat.gcd n j ≠ 1 by omega)
  refine ⟨p, hp, hp.one_lt.le, ?_⟩
  rw [Nat.choose_one_right]
  exact hpd.trans (Nat.dvd_gcd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n j)) (div_gcd_dvd_choose hn))

/- ### Two checked exceptions for the Erdős–Szekeres strengthening -/

/-- A checked computation: `gcd (choose 10 3, choose 10 5) = 12`. -/
theorem gcd_choose_ten : Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) = 12 := by
  have h1 : Nat.choose 10 3 = 120 := by rfl
  have h2 : Nat.choose 10 5 = 252 := by rfl
  rw [h1, h2]
  norm_num

/-- A checked computation confirming the value `2 ^ 3 * 3 ^ 3 * 5` recorded on
[erdosproblems.com/699](https://www.erdosproblems.com/699) for the triple `(28, 5, 14)`. The large
coefficient is evaluated through `Nat.choose_eq_descFactorial_div_factorial` rather than by
unfolding Pascal's rule. -/
theorem gcd_choose_twentyEight :
    Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 2 ^ 3 * 3 ^ 3 * 5 := by
  have h1 : Nat.choose 28 5 = 98280 := by rfl
  have h2 : Nat.choose 28 14 = 40116600 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    rfl
  rw [h1, h2]
  norm_num

/-- At `(n, i, j) = (10, 3, 5)` no prime *strictly* above `i` divides
`gcd (n.choose i) (n.choose j) = 12`. -/
theorem not_exists_prime_gt_dvd_gcd_choose_ten :
    ¬ ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) := by
  rintro ⟨p, hp, hp3, hdvd⟩
  rw [gcd_choose_ten] at hdvd
  have hle : p ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases p <;> revert hp hdvd <;> norm_num

/-- At `(n, i, j) = (28, 5, 14)` no prime *strictly* above `i` divides
`gcd (n.choose i) (n.choose j) = 2 ^ 3 * 3 ^ 3 * 5`. This is the only exception with `i ≥ 4`
known in the literature. -/
theorem not_exists_prime_gt_dvd_gcd_choose_twentyEight :
    ¬ ∃ p : ℕ, p.Prime ∧ 5 < p ∧ p ∣ Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) := by
  rintro ⟨p, hp, hp5, hdvd⟩
  rw [gcd_choose_twentyEight] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
      omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

/-- The bound `i ≤ p` of `Erdos699.erdos_699` *is* attained at `(10, 3, 5)`, by `p = i = 3`. -/
theorem exists_prime_ge_dvd_gcd_choose_ten :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ Nat.gcd (Nat.choose 10 3) (Nat.choose 10 5) := by
  refine ⟨3, by norm_num, le_rfl, ?_⟩
  rw [gcd_choose_ten]
  norm_num

/-- The bound `i ≤ p` of `Erdos699.erdos_699` *is* attained at `(28, 5, 14)`, by `p = i = 5`. -/
theorem exists_prime_ge_dvd_gcd_choose_twentyEight :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) := by
  refine ⟨5, by norm_num, le_rfl, ?_⟩
  rw [gcd_choose_twentyEight]
  norm_num

/-- Consequently every exceptional set `E` admissible in
`Erdos699.erdos_szekeres_strengthening` contains both `(10, 3, 5)` and `(28, 5, 14)`. -/
theorem mem_of_forall_exists_prime_gt {E : Finset (ℕ × ℕ × ℕ)}
    (hE : ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → (n, i, j) ∉ E →
      ∃ p, p.Prime ∧ i < p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j)) :
    ((10, 3, 5) : ℕ × ℕ × ℕ) ∈ E ∧ ((28, 5, 14) : ℕ × ℕ × ℕ) ∈ E := by
  constructor
  · by_contra h
    exact not_exists_prime_gt_dvd_gcd_choose_ten
      (hE 10 3 5 (by norm_num) (by norm_num) (by norm_num) h)
  · by_contra h
    exact not_exists_prime_gt_dvd_gcd_choose_twentyEight
      (hE 28 5 14 (by norm_num) (by norm_num) (by norm_num) h)

/- ### Use sites against the reward statement -/

/-- **The reduction.** To prove the reward statement it suffices to prove, for every admissible
triple, the `rcases`-friendly disjunction of `exists_prime_ge_dvd_gcd_choose_iff`. -/
theorem erdos_699_of_split
    (h : ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
      (∃ p, p.Prime ∧ i ≤ p ∧ p ≤ j ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)) ∨
      (∃ p, p.Prime ∧ j < p ∧ n % p < i)) :
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
      ∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := fun n i j h1 hij hj =>
  (exists_prime_ge_dvd_gcd_choose_iff hij.le).mpr (h n i j h1 hij hj)

/-- Worked use site: the full statement of `Erdos699.erdos_699`, discharged from the split form.
This is literally the reward theorem's type, whose left-hand side elaborates to `True`. -/
example (h : ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
      (∃ p, p.Prime ∧ i ≤ p ∧ p ≤ j ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)) ∨
      (∃ p, p.Prime ∧ j < p ∧ n % p < i)) :
    True ↔ ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
      ∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) :=
  ⟨fun _ => erdos_699_of_split h, fun _ => trivial⟩

/-- Worked use site: inside the reward theorem's own binders, the case `i = 1` is already settled
by `erdos_699_index_one`, and on the remaining range a solver may additionally assume the
counterexample structure `∀ p prime, j < p → i ≤ n % p` handed over by
`le_mod_of_not_exists_prime_ge_dvd`. Only the bounded range `i ≤ p ≤ j` is left to work on. -/
example (n i j : ℕ) (h1 : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2)
    (hsmall : 2 ≤ i → (∀ p, p.Prime → j < p → i ≤ n % p) →
      ∃ p, p.Prime ∧ i ≤ p ∧ p ≤ j ∧ p ∣ Nat.gcd (n.choose i) (n.choose j)) :
    ∃ p, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (n.choose i) (n.choose j) := by
  rcases eq_or_lt_of_le h1 with hi | hi
  · subst hi
    exact erdos_699_index_one hij hj
  · by_contra hcon
    exact hcon ((exists_prime_ge_dvd_gcd_choose_iff hij.le).mpr
      (Or.inl (hsmall hi (le_mod_of_not_exists_prime_ge_dvd hij.le hcon))))

/-- Worked use site for the second base-`p` digit, the mechanism that separates
`Erdos699.erdos_699` (which allows `p = i`) from `Erdos699.erdos_szekeres_strengthening` (which
does not): if `i` is itself a prime `p` and `n % p ^ 2 < p`, then `p ∣ n.choose i`. At
`(n, i, j) = (10, 3, 5)` this is precisely the divisibility `3 ∣ Nat.choose 10 3` behind
`exists_prime_ge_dvd_gcd_choose_ten`. -/
example (p n : ℕ) (hp : p.Prime) (h : n % p ^ 2 < p) : p ∣ n.choose p := by
  refine prime_dvd_choose_of_mod_pow_lt hp two_pos ?_
  have h2 := hp.two_le
  rwa [Nat.mod_eq_of_lt (show p < p ^ 2 by nlinarith)]

/-- Worked use site for the finite criterion: neither `7` nor `13` divides `Nat.choose 28 14`,
each by a `decide` over `Finset.Icc 1 (Nat.log p 28)` that never evaluates the coefficient. These
are the two primes above `5` that do divide `Nat.choose 28 5`, so this is the computational core
of `not_exists_prime_gt_dvd_gcd_choose_twentyEight`. -/
example : ¬ (7 ∣ Nat.choose 28 14) ∧ ¬ (13 ∣ Nat.choose 28 14) := by
  have h7 : Nat.log 7 28 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have h13 : Nat.log 13 28 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  constructor
  · rw [prime_dvd_choose_iff_exists_le_log (by norm_num) (by norm_num), h7]
    decide
  · rw [prime_dvd_choose_iff_exists_le_log (by norm_num) (by norm_num), h13]
    decide

end Contribution.Erdos699Carries
