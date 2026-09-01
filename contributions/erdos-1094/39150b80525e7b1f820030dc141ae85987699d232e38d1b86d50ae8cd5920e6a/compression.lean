import Mathlib.Data.Nat.Choose.Factorization

open Finset

namespace Contribution.Erdos1094.Compression

/-- The least common multiple of the positive integers at most `k`. -/
def uptoLcm : ℕ → ℕ
  | 0 => 1
  | k + 1 => Nat.lcm (uptoLcm k) (k + 1)

lemma uptoLcm_ne_zero (k : ℕ) : uptoLcm k ≠ 0 := by
  induction k with
  | zero => simp [uptoLcm]
  | succ k ih => simpa [uptoLcm] using Nat.lcm_ne_zero ih (Nat.succ_ne_zero k)

lemma dvd_uptoLcm {m k : ℕ} (hm : 0 < m) (hmk : m ≤ k) : m ∣ uptoLcm k := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hmk' : m ≤ k
      · exact (ih hmk').trans (Nat.dvd_lcm_left _ _)
      · have hmeq : m = k + 1 := by omega
        rw [uptoLcm, hmeq]
        exact Nat.dvd_lcm_right _ _

lemma prime_le_of_dvd_factorial {p : ℕ} (hp : p.Prime) :
    ∀ {n : ℕ}, p ∣ Nat.factorial n → p ≤ n := by
  intro n hpn
  induction n with
  | zero =>
      simp only [Nat.factorial_zero, Nat.dvd_one] at hpn
      exact (hp.ne_one hpn).elim
  | succ n ih =>
      rw [Nat.factorial_succ] at hpn
      rcases hp.dvd_mul.mp hpn with hps | hpf
      · exact Nat.le_of_dvd (Nat.succ_pos n) hps
      · exact (ih hpf).trans (Nat.le_succ n)

lemma prime_le_of_dvd_choose_support
    {p d k r : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hrk : r < k)
    (hpd : p ∣ d) (hsupport : d ∣ k * (k - 1).choose r) :
    p ≤ k := by
  have hpA : p ∣ k * (k - 1).choose r := hpd.trans hsupport
  rcases hp.dvd_mul.mp hpA with hpk | hpchoose
  · exact Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hk) hpk
  · have hrle : r ≤ k - 1 := by omega
    have hchoose_factorial : (k - 1).choose r ∣ Nat.factorial (k - 1) := by
      refine ⟨Nat.factorial r * Nat.factorial (k - 1 - r), ?_⟩
      simpa [Nat.mul_assoc] using (Nat.choose_mul_factorial_mul_factorial hrle).symm
    have hpfactorial : p ∣ Nat.factorial (k - 1) := hpchoose.trans hchoose_factorial
    exact (prime_le_of_dvd_factorial hp hpfactorial).trans (Nat.sub_le k 1)

/-- If all prime divisors of `m` are at most `k`, but none of those primes
divide `choose (m+r) k`, every maximal prime-power component of `m` is at
most `k`. Therefore `m` divides `lcm(1,...,k)`. -/
theorem multiplicand_lcm_compression
    {m k r : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) (hrk : r < k) (hkm : k ≤ m)
    (hsupport : ∀ p, p.Prime → p ∣ m → p ≤ k)
    (hprime : ∀ p, p.Prime → p ≤ k → ¬p ∣ (m + r).choose k) :
    m ∣ uptoLcm k := by
  have hLne : uptoLcm k ≠ 0 := uptoLcm_ne_zero k
  rw [← Nat.factorization_le_iff_dvd hm hLne]
  intro p
  by_cases hp : p.Prime
  · let e := m.factorization p
    by_cases he : e = 0
    · simp [e, he]
    have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hpowm : p ^ e ∣ m := (hp.pow_dvd_iff_le_factorization hm).2 (by simp [e])
    have hpm : p ∣ m := (dvd_pow_self p he).trans hpowm
    have hpk : p ≤ k := hsupport p hp hpm
    have hpowle : p ^ e ≤ k := by
      by_contra hnot
      have hkpow : k < p ^ e := Nat.lt_of_not_ge hnot
      have hrpow : r < p ^ e := hrk.trans hkpow
      have hnmod : (m + r) % p ^ e = r := by
        rw [Nat.add_mod]
        have hmmod : m % p ^ e = 0 := Nat.dvd_iff_mod_eq_zero.mp hpowm
        simp [hmmod, Nat.mod_eq_of_lt hrpow]
      have hkn : k ≤ m + r := hkm.trans (Nat.le_add_right m r)
      have hn0 : m + r ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_of_ne_zero hk) hkn)
      have hcarry : p ^ e ≤ k % p ^ e + (m + r - k) % p ^ e := by
        by_contra hcarry
        have hsum : k % p ^ e + (m + r - k) % p ^ e < p ^ e :=
          Nat.lt_of_not_ge hcarry
        have htop : (m + r) % p ^ e =
            k % p ^ e + (m + r - k) % p ^ e := by
          conv_lhs => rw [← Nat.add_sub_of_le hkn]
          rw [Nat.add_mod, Nat.mod_eq_of_lt hsum]
        have hkle : k ≤ (m + r) % p ^ e := by
          rw [htop, Nat.mod_eq_of_lt hkpow]
          exact Nat.le_add_right _ _
        rw [hnmod] at hkle
        exact (Nat.not_le_of_gt hrk) hkle
      have hein : e ∈ Finset.Ico 1 (m + r + 1) := by
        simp only [mem_Ico]
        refine ⟨hepos, Nat.lt_succ_of_le ?_⟩
        have hepow : e ≤ p ^ e :=
          e.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le e)
        calc
          e ≤ p ^ e := hepow
          _ ≤ m := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hm) hpowm
          _ ≤ m + r := Nat.le_add_right _ _
      have hfac := Nat.factorization_choose hp hkn
        ((Nat.log_lt_self p hn0).trans (Nat.lt_succ_self (m + r)))
      have hmem : e ∈ {i ∈ Finset.Ico 1 (m + r + 1) |
          p ^ i ≤ k % p ^ i + (m + r - k) % p ^ i} := by
        simp only [mem_filter]
        exact ⟨hein, hcarry⟩
      have hpos : 0 < ((m + r).choose k).factorization p := by
        rw [hfac]
        exact card_pos.mpr ⟨e, hmem⟩
      have hpchoose : p ∣ (m + r).choose k := by
        apply (hp.dvd_iff_one_le_factorization (Nat.ne_of_gt (Nat.choose_pos hkn))).2
        exact hpos
      exact (hprime p hp hpk) hpchoose
    have hpowL : p ^ e ∣ uptoLcm k := dvd_uptoLcm (pow_pos hp.pos e) hpowle
    exact (hp.pow_dvd_iff_le_factorization hLne).1 hpowL
  · simp [Nat.factorization_eq_zero_of_not_prime m hp]

/-- Whole-multiplicand strengthening of quotient-supported lcm compression. -/
theorem whole_multiplicand_compression
    {d k r : ℕ} (hd : d ≠ 0) (hk : k ≠ 0) (hrk : r < k)
    (hsupport : d ∣ k * (k - 1).choose r)
    (hprime : ∀ p, p.Prime → p ≤ k → ¬p ∣ (d * k + r).choose k) :
    d * k ∣ uptoLcm k := by
  apply multiplicand_lcm_compression (Nat.mul_ne_zero hd hk) hk hrk
  · have hdpos : 0 < d := Nat.zero_lt_of_ne_zero hd
    nlinarith
  · intro p hp hpm
    rcases hp.dvd_mul.mp hpm with hpd | hpk
    · exact prime_le_of_dvd_choose_support hp hk hrk hpd hsupport
    · exact Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hk) hpk
  · simpa only using hprime

end Contribution.Erdos1094.Compression
