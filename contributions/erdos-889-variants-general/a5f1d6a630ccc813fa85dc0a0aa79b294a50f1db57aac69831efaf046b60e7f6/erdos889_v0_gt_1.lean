/-
Copyright 2026 The Contribution Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Erdős Problem 889 (1967): `v₀(n) > 1` Outside `{0, 1, 2, 3, 4, 7, 8, 16}`

Complete self-contained Lean 4 proof of the Erdős–Selfridge (1967) variant
`Erdos889.erdos_889.variants.v0_gt_1`: for every `n ∉ {0, 1, 2, 3, 4, 7, 8, 16}`,
there exists `k : ℕ` such that `n + k` has at least two prime factors dividing none
of `n, n + 1, ..., n + k - 1`, hence `1 < v₀ n`.

For `n ≥ 17`, either `n` or `n + 1` has at least two prime factors (`k = 0` or `k = 1`),
or `n` and `n + 1` are prime powers with one equal to `2 ^ a` (`a ≥ 5`), in which case
congruences modulo `16` and `5` produce two distinct odd prime factors of `2 ^ m + 1`
in `n + 1` or `n + 2`.
-/

namespace Contribution.Erdos889

/--
`v n k` counts the prime factors of `n + k` that do not divide `n + i` for any `0 ≤ i < k`.
Matches `Erdos889.v` definitionally.
-/
def v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ Finset.range k, ¬ p ∣ n + i)).card

/--
`v₀ n` is the supremum over `k` of `(v n k : ℕ∞)`.
Matches `Erdos889.v₀` definitionally.
-/
noncomputable def v₀ (n : ℕ) : ℕ∞ :=
  ⨆ k, (v n k : ℕ∞)

private lemma one_lt_v0_of_two_le_v {n k : ℕ} (hk : 2 ≤ v n k) : 1 < v₀ n := by
  have h12 : (1 : ℕ∞) < (2 : ℕ) := by decide
  have h2v : ((2 : ℕ) : ℕ∞) ≤ (v n k : ℕ∞) := Nat.cast_le.mpr hk
  exact lt_of_lt_of_le (lt_of_lt_of_le h12 h2v) (le_iSup (fun j => (v n j : ℕ∞)) k)

private lemma two_le_v_of_two_primes {n k p q : ℕ} (hnk : n + k ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpd : p ∣ n + k) (hqd : q ∣ n + k)
    (hpnd : ∀ i ∈ Finset.range k, ¬ p ∣ n + i)
    (hqnd : ∀ i ∈ Finset.range k, ¬ q ∣ n + i) : 2 ≤ v n k := by
  unfold v
  have hp_mem : p ∈ (n + k).primeFactors.filter (fun r => ∀ i ∈ Finset.range k, ¬ r ∣ n + i) :=
    Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpd, hnk⟩, hpnd⟩
  have hq_mem : q ∈ (n + k).primeFactors.filter (fun r => ∀ i ∈ Finset.range k, ¬ r ∣ n + i) :=
    Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqd, hnk⟩, hqnd⟩
  exact Finset.one_lt_card.mpr ⟨p, hp_mem, q, hq_mem, hpq⟩

private lemma prime_pow_of_primeFactors_subset {m p : ℕ} (hm : 1 ≤ m)
    (hsub : ∀ q ∈ m.primeFactors, q = p) : ∃ e : ℕ, m = p ^ e := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_lt_of_le hm with rfl | hm2
    · exact ⟨0, by simp⟩
    · have hm0 : m ≠ 0 := by omega
      let q := m.minFac
      have hq_prime : q.Prime := Nat.minFac_prime (by omega)
      have hq_dvd : q ∣ m := Nat.minFac_dvd m
      have hqp : q = p := hsub q (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, hm0⟩)
      subst hqp
      have hq_ge : 2 ≤ q := hq_prime.two_le
      have hm_div_lt : m / q < m := Nat.div_lt_self (by omega) (by omega)
      have hm_div_pos : 1 ≤ m / q := Nat.div_pos (Nat.le_of_dvd (by omega) hq_dvd) (by omega)
      have hsub_div : ∀ r ∈ (m / q).primeFactors, r = q := by
        intro r hr
        have hr' := Nat.mem_primeFactors.mp hr
        exact hsub r (Nat.mem_primeFactors.mpr ⟨hr'.1, dvd_trans hr'.2.1 (Nat.div_dvd_of_dvd hq_dvd), hm0⟩)
      obtain ⟨e, he⟩ := ih (m / q) hm_div_lt hm_div_pos hsub_div
      refine ⟨e + 1, ?_⟩
      calc
        m = q * (m / q) := (Nat.mul_div_cancel' hq_dvd).symm
        _ = q * q ^ e := by rw [he]
        _ = q ^ (e + 1) := by ring

private lemma three_pow_four_mul_mod_16 (q : ℕ) : (3 ^ (4 * q)) % 16 = 1 := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, Nat.mul_mod, ih]
    decide

private lemma three_pow_four_mul_mod_5 (q : ℕ) : (3 ^ (4 * q)) % 5 = 1 := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, Nat.mul_mod, ih]
    decide

private lemma two_pow_add_one_ne_three_pow {a b : ℕ} (ha : 4 ≤ a) : 2 ^ a + 1 ≠ 3 ^ b := by
  intro h
  have h16_dvd : 16 ∣ 2 ^ a := by
    simpa using Nat.pow_dvd_pow 2 ha
  have hmod16 : (3 ^ b) % 16 = 1 := by
    rw [← h, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp h16_dvd]
  have hb_div : 4 * (b / 4) + b % 4 = b := Nat.div_add_mod b 4
  have hr : (3 ^ (b % 4)) % 16 = 1 := by
    have hpow : 3 ^ b = 3 ^ (4 * (b / 4)) * 3 ^ (b % 4) := by
      conv_lhs => rw [← hb_div, pow_add]
    rw [hpow, Nat.mul_mod, three_pow_four_mul_mod_16] at hmod16
    simpa [Nat.mod_mod] using hmod16
  have hr_lt : b % 4 < 4 := Nat.mod_lt b (by decide)
  have hbmod4 : b % 4 = 0 := by
    interval_cases hrem : b % 4 <;> simp_all
  have hb4 : b = 4 * (b / 4) := by omega
  have hmod5 : (3 ^ b) % 5 = 1 := by
    rw [hb4, three_pow_four_mul_mod_5]
  have h2a_mod5 : (2 ^ a) % 5 = 0 := by
    have hpow_mod : (2 ^ a + 1) % 5 = 1 := by rw [h, hmod5]
    omega
  have h5_dvd_2 : 5 ∣ 2 := (by decide : Nat.Prime 5).dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h2a_mod5)
  omega

private lemma three_dvd_two_pow_odd_add_one {a : ℕ} (ha : Odd a) : 3 ∣ 2 ^ a + 1 := by
  obtain ⟨m, rfl⟩ := ha
  have hmod : (2 ^ (2 * m + 1) + 1) % 3 = 0 := by
    induction m with
    | zero => decide
    | succ m ih =>
      have hstep : 2 ^ (2 * (m + 1) + 1) + 1 = 4 * (2 ^ (2 * m + 1) + 1) - 3 := by
        have hpos : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_pow _ 2 (by decide)
        ring_nf
        omega
      omega
  exact Nat.dvd_of_mod_eq_zero hmod

private lemma odd_two_pow_add_one_two_odd_primes {a : ℕ} (ha : 5 ≤ a) (hodd : Odd a) :
    ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ≠ 2 ∧ q ≠ 2 ∧ p ∣ 2 ^ a + 1 ∧ q ∣ 2 ^ a + 1 := by
  have h3_dvd : 3 ∣ 2 ^ a + 1 := three_dvd_two_pow_odd_add_one hodd
  have hnot_all_3 : ¬ ∀ q ∈ (2 ^ a + 1).primeFactors, q = 3 := by
    intro hall
    obtain ⟨b, hb⟩ := prime_pow_of_primeFactors_subset (Nat.le_add_left 1 _) hall
    exact two_pow_add_one_ne_three_pow (by omega) hb
  push Not at hnot_all_3
  obtain ⟨q, hq_mem, hq_ne3⟩ := hnot_all_3
  have hq_info := Nat.mem_primeFactors.mp hq_mem
  have heven : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
  have hodd_val : ¬ 2 ∣ 2 ^ a + 1 := by
    intro h2
    have h1 := (Nat.dvd_add_right heven).mp h2
    omega
  have hq_ne2 : q ≠ 2 := by
    rintro rfl
    exact hodd_val hq_info.2.1
  exact ⟨3, q, by decide, hq_info.1, hq_ne3.symm, by decide, hq_ne2, h3_dvd, hq_info.2.1⟩

private lemma eq_two_pow_of_even_primeFactors_lt_two {m : ℕ} (hm : 2 ≤ m) (heven : 2 ∣ m)
    (hcard : m.primeFactors.card < 2) : ∃ a ≥ 1, m = 2 ^ a := by
  have h2_mem : 2 ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, heven, by omega⟩
  have hall : ∀ q ∈ m.primeFactors, q = 2 := by
    intro q hq
    by_contra hq2
    have h2 : 2 ≤ m.primeFactors.card := Finset.one_lt_card.mpr ⟨q, hq, 2, h2_mem, hq2⟩
    omega
  obtain ⟨a, ha⟩ := prime_pow_of_primeFactors_subset (by omega) hall
  have ha1 : a ≥ 1 := by
    by_contra h0
    have ha0 : a = 0 := by omega
    subst ha0
    omega
  exact ⟨a, ha1, ha⟩

private lemma one_lt_v0_small_k0 {n p q : ℕ} (hn : n ≠ 0)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpn : p ∣ n) (hqn : q ∣ n) :
    1 < v₀ n :=
  one_lt_v0_of_two_le_v (two_le_v_of_two_primes (k := 0) hn hp hq hpq hpn hqn (by simp) (by simp))

private lemma one_lt_v0_small_k1 {n p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpn : p ∣ n + 1) (hqn : q ∣ n + 1) :
    1 < v₀ n := by
  have hnot : ∀ r : ℕ, r.Prime → r ∣ n + 1 → ∀ i ∈ Finset.range 1, ¬ r ∣ n + i := by
    intro r hr hrd i hi hri
    rw [Finset.mem_range] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact hr.ne_one (Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hri).mp hrd))
  exact one_lt_v0_of_two_le_v (two_le_v_of_two_primes (k := 1) (by omega) hp hq hpq hpn hqn
    (hnot p hp hpn) (hnot q hq hqn))

/--
For every `n ∉ {0, 1, 2, 3, 4, 7, 8, 16}`, `1 < v₀ n`.
Discharges `Erdos889.erdos_889.variants.v0_gt_1`.
-/
theorem erdos_889_v0_gt_1 :
    ∀ n : ℕ, n ∉ ({0, 1, 2, 3, 4, 7, 8, 16} : Finset ℕ) → 1 < v₀ n := by
  intro n hn
  by_cases h17 : n < 17
  · interval_cases n
    all_goals
      try (simp at hn; done)
    · exact one_lt_v0_small_k1 (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k0 (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k1 (p := 2) (q := 5) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k0 (p := 2) (q := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k1 (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k0 (p := 2) (q := 3) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k1 (p := 2) (q := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k0 (p := 2) (q := 7) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact one_lt_v0_small_k0 (p := 3) (q := 5) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have hn_ge : 17 ≤ n := by omega
    by_cases hc0 : 2 ≤ n.primeFactors.card
    · have hv0 : v n 0 = n.primeFactors.card := by simp [v]
      exact one_lt_v0_of_two_le_v (k := 0) (hv0 ▸ hc0)
    · by_cases hc1 : 2 ≤ (n + 1).primeFactors.card
      · have hfilt : (n + 1).primeFactors.filter (fun p => ∀ i ∈ Finset.range 1, ¬ p ∣ n + i) =
            (n + 1).primeFactors := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
          refine ⟨fun h => h.1, fun h => ⟨h, fun i hi hdiv => ?_⟩⟩
          have hi0 : i = 0 := by omega
          subst hi0
          have hdvd1 : p ∣ 1 := (Nat.dvd_add_right hdiv).mp h.2.1
          exact h.1.ne_one (Nat.eq_one_of_dvd_one hdvd1)
        have hv1 : v n 1 = (n + 1).primeFactors.card := by unfold v; rw [hfilt]
        exact one_lt_v0_of_two_le_v (k := 1) (hv1 ▸ hc1)
      · rcases Nat.mod_two_eq_zero_or_one n with hn_even | hn_odd
        · have h2_n : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn_even
          obtain ⟨a, _, ha_eq⟩ := eq_two_pow_of_even_primeFactors_lt_two (by omega) h2_n (by omega)
          have ha_ge5 : 5 ≤ a := by
            by_contra ha_le4
            have : a ≤ 4 := by omega
            have : 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) this
            omega
          rcases Nat.even_or_odd a with ha_even | ha_odd
          · have ha1_ge5 : 5 ≤ a - 1 := by
              obtain ⟨m, hm⟩ := ha_even
              omega
            have ha1_odd : Odd (a - 1) := by
              obtain ⟨m, hm⟩ := ha_even
              exact ⟨m - 1, by omega⟩
            obtain ⟨p, q, hp, hq, hpq, hp2, hq2, hpd, hqd⟩ :=
              odd_two_pow_add_one_two_odd_primes ha1_ge5 ha1_odd
            have hfac : n + 2 = 2 * (2 ^ (a - 1) + 1) := by
              rw [ha_eq]
              have : 2 ^ a = 2 * 2 ^ (a - 1) := by
                conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_add, pow_one]
                ring
              omega
            have hpd2 : p ∣ n + 2 := hfac ▸ dvd_mul_of_dvd_right hpd 2
            have hqd2 : q ∣ n + 2 := hfac ▸ dvd_mul_of_dvd_right hqd 2
            have hnot0 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ n + 2 → ∀ i ∈ Finset.range 2, ¬ r ∣ n + i := by
              intro r hr hr2 hrd2 i hi hri
              rw [Finset.mem_range] at hi
              have hi01 : i = 0 ∨ i = 1 := by omega
              rcases hi01 with rfl | rfl
              · have hrd : r ∣ 2 ^ a := ha_eq ▸ hri
                exact hr2 (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp
                  (hr.dvd_of_dvd_pow hrd)).resolve_left hr.ne_one)
              · have hdvd1 : r ∣ 1 := by
                  have hsub : n + 2 = (n + 1) + 1 := by omega
                  rw [hsub] at hrd2
                  exact (Nat.dvd_add_right hri).mp hrd2
                exact hr.ne_one (Nat.eq_one_of_dvd_one hdvd1)
            exact one_lt_v0_of_two_le_v (two_le_v_of_two_primes (by omega) hp hq hpq hpd2 hqd2
              (hnot0 p hp hp2 hpd2) (hnot0 q hq hq2 hqd2))
          · obtain ⟨p, q, hp, hq, hpq, _, _, hpd, hqd⟩ :=
              odd_two_pow_add_one_two_odd_primes ha_ge5 ha_odd
            have hpd1 : p ∣ n + 1 := ha_eq ▸ hpd
            have hqd1 : q ∣ n + 1 := ha_eq ▸ hqd
            have hnot0 : ∀ r : ℕ, r.Prime → r ∣ n + 1 → ∀ i ∈ Finset.range 1, ¬ r ∣ n + i := by
              intro r hr hrd1 i hi hri
              rw [Finset.mem_range] at hi
              have hi0 : i = 0 := by omega
              subst hi0
              exact hr.ne_one (Nat.eq_one_of_dvd_one ((Nat.dvd_add_right hri).mp hrd1))
            exact one_lt_v0_of_two_le_v (two_le_v_of_two_primes (by omega) hp hq hpq hpd1 hqd1
              (hnot0 p hp hpd1) (hnot0 q hq hqd1))
        · have h2_n1 : 2 ∣ n + 1 := by omega
          obtain ⟨a, _, ha_eq⟩ := eq_two_pow_of_even_primeFactors_lt_two (by omega) h2_n1 (by omega)
          have ha_ge5 : 5 ≤ a := by
            by_contra ha_le4
            have : a ≤ 4 := by omega
            have : 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) this
            omega
          rcases Nat.even_or_odd a with ha_even | ha_odd
          · obtain ⟨m, hm⟩ := ha_even
            have hm3 : 3 ≤ m := by omega
            have h2m_ge : 8 ≤ 2 ^ m := by
              calc
                8 = 2 ^ 3 := by decide
                _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm3
            have hprod : n = (2 ^ m - 1) * (2 ^ m + 1) := by
              have ha2m : a = 2 * m := by omega
              have hsq : 2 ^ a = (2 ^ m) ^ 2 := by rw [ha2m, pow_mul']
              have h2a_pos : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by omega)
              zify [show 1 ≤ 2 ^ m by omega, h2a_pos]
              have : (n : ℤ) = (2 ^ m : ℤ) ^ 2 - 1 := by
                have hz : (n : ℤ) + 1 = (2 ^ a : ℤ) := by exact_mod_cast ha_eq
                have hs : (2 ^ a : ℤ) = (2 ^ m : ℤ) ^ 2 := by exact_mod_cast hsq
                omega
              linarith
            let p := (2 ^ m - 1).minFac
            let q := (2 ^ m + 1).minFac
            have hp : p.Prime := Nat.minFac_prime (by omega)
            have hq : q.Prime := Nat.minFac_prime (by omega)
            have hp_dvd : p ∣ n := hprod ▸ dvd_mul_of_dvd_left (Nat.minFac_dvd _) _
            have hq_dvd : q ∣ n := hprod ▸ dvd_mul_of_dvd_right (Nat.minFac_dvd _) _
            have hpq : p ≠ q := by
              intro hpeq
              have hdiv_sub : p ∣ (2 ^ m + 1) - (2 ^ m - 1) := by
                have hp_sub : p ∣ 2 ^ m - 1 := Nat.minFac_dvd _
                have hp_add : p ∣ 2 ^ m + 1 := hpeq ▸ Nat.minFac_dvd (2 ^ m + 1)
                exact Nat.dvd_sub hp_add hp_sub
              have hsub2 : (2 ^ m + 1) - (2 ^ m - 1) = 2 := by omega
              rw [hsub2] at hdiv_sub
              have hp2 : p = 2 := ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv_sub).resolve_left hp.ne_one
              have h2_odd : 2 ∣ 2 ^ m - 1 := by
                have hp_min : p ∣ 2 ^ m - 1 := Nat.minFac_dvd (2 ^ m - 1)
                exact hp2 ▸ hp_min
              have h2_pow : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
              have h2_1 : 2 ∣ 1 := by
                have := Nat.dvd_sub h2_pow h2_odd
                rwa [show 2 ^ m - (2 ^ m - 1) = 1 by omega] at this
              omega
            have hcard2 : 2 ≤ n.primeFactors.card := Finset.one_lt_card.mpr
              ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, by omega⟩,
               q, Nat.mem_primeFactors.mpr ⟨hq, hq_dvd, by omega⟩, hpq⟩
            omega
          · obtain ⟨p, q, hp, hq, hpq, hp2, hq2, hpd, hqd⟩ :=
              odd_two_pow_add_one_two_odd_primes ha_ge5 ha_odd
            have hn2_eq : n + 2 = 2 ^ a + 1 := by omega
            have hpd2 : p ∣ n + 2 := hn2_eq ▸ hpd
            have hqd2 : q ∣ n + 2 := hn2_eq ▸ hqd
            have hnot0 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ n + 2 → ∀ i ∈ Finset.range 2, ¬ r ∣ n + i := by
              intro r hr hr2 hrd2 i hi hri
              rw [Finset.mem_range] at hi
              have hi01 : i = 0 ∨ i = 1 := by omega
              rcases hi01 with rfl | rfl
              · have hdvd2 : r ∣ 2 := by
                  have := Nat.dvd_sub hrd2 hri
                  simpa using this
                exact hr2 (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdvd2).resolve_left hr.ne_one)
              · exact hr2 (((Nat.dvd_prime (by decide : Nat.Prime 2)).mp
                  (hr.dvd_of_dvd_pow (ha_eq ▸ hri))).resolve_left hr.ne_one)
            exact one_lt_v0_of_two_le_v (two_le_v_of_two_primes (by omega) hp hq hpq hpd2 hqd2
              (hnot0 p hp hp2 hpd2) (hnot0 q hq hq2 hqd2))

end Contribution.Erdos889
