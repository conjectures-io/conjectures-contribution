import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.ModEq

open Finset

namespace Contribution.Erdos1094.Quotient

/-- The valuation-counting core of the ELS93 quotient transfer. At every
prime-power level in `m`, equality contributes to `k-r` and strict inequality
contributes a Kummer carry to `choose k r`. -/
theorem quotient_transfer_of_mod_le
    {m k r : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) (hrk : r < k)
    (hmod : ∀ p, p.Prime → ∀ a ∈ Icc 1 (m.factorization p),
      k % p ^ a ≤ r % p ^ a) :
    m ∣ (k - r) * k.choose r := by
  have hsub : k - r ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hrk)
  have hchoose : k.choose r ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hrk.le)
  rw [← Nat.factorization_le_iff_dvd hm (Nat.mul_ne_zero hsub hchoose)]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul hsub hchoose]
    change m.factorization p ≤ (k - r).factorization p + (k.choose r).factorization p
    let D := (Icc 1 (m.factorization p)).filter fun a => p ^ a ∣ k - r
    let C := (Icc 1 (m.factorization p)).filter fun a =>
      p ^ a ≤ r % p ^ a + (k - r) % p ^ a
    have hcover : Icc 1 (m.factorization p) ⊆ D ∪ C := by
      intro a ha
      have hle := hmod p hp a ha
      rcases hle.eq_or_lt with heq | hlt
      · apply mem_union_left C
        simp only [D, mem_filter]
        refine ⟨ha, (Nat.modEq_iff_dvd' hrk.le).mp ?_⟩
        exact heq.symm
      · apply mem_union_right D
        simp only [C, mem_filter]
        refine ⟨ha, ?_⟩
        by_contra hcarry
        have hsum : r % p ^ a + (k - r) % p ^ a < p ^ a := Nat.lt_of_not_ge hcarry
        have hkmod : k % p ^ a = r % p ^ a + (k - r) % p ^ a := by
          conv_lhs => rw [← Nat.add_sub_of_le hrk.le]
          rw [Nat.add_mod, Nat.mod_eq_of_lt hsum]
        have hrle : r % p ^ a ≤ k % p ^ a := by
          rw [hkmod]
          exact Nat.le_add_right _ _
        exact (Nat.not_lt_of_ge hrle) hlt
    have hD : D.card ≤ (k - r).factorization p := by
      rw [Nat.factorization_eq_card_pow_dvd (k - r) hp]
      apply card_le_card
      intro a ha
      simp only [D, mem_filter, mem_Icc] at ha
      simp only [mem_filter, mem_Ico]
      refine ⟨⟨ha.1.1, ?_⟩, ha.2⟩
      exact Nat.lt_of_pow_dvd_right hsub hp.two_le ha.2
    have hC : C.card ≤ (k.choose r).factorization p := by
      rw [Nat.factorization_choose hp hrk.le
        ((Nat.log_lt_self p hk).trans (Nat.lt_succ_self k))]
      apply card_le_card
      intro a ha
      simp only [C, mem_filter, mem_Icc] at ha
      simp only [mem_filter, mem_Ico]
      refine ⟨⟨ha.1.1, ?_⟩, ha.2⟩
      have hpak : p ^ a ≤ k := by
        by_contra hnot
        have hka : k < p ^ a := Nat.lt_of_not_ge hnot
        have hra : r < p ^ a := hrk.trans hka
        have hsuba : k - r < p ^ a := (Nat.sub_le k r).trans_lt hka
        have hcarry := ha.2
        rw [Nat.mod_eq_of_lt hra, Nat.mod_eq_of_lt hsuba,
          Nat.add_sub_of_le hrk.le] at hcarry
        exact (Nat.not_lt_of_ge hcarry) hka
      have hapow : a ≤ p ^ a :=
        a.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le a)
      exact Nat.lt_succ_of_le (hapow.trans hpak)
    calc
      m.factorization p = (Icc 1 (m.factorization p)).card := by simp
      _ ≤ (D ∪ C).card := card_le_card hcover
      _ ≤ D.card + C.card := card_union_le D C
      _ ≤ (k - r).factorization p + (k.choose r).factorization p := Nat.add_le_add hD hC
  · simp [Nat.factorization_eq_zero_of_not_prime m hp]

/-- Absence of a prime divisor of `choose n k` forces the residue inequality
used by `quotient_transfer_of_mod_le`. -/
theorem mod_le_of_no_prime_divisor
    {n m k r p a : ℕ} (hn : n = m * k + r) (hm : m ≠ 0) (hk : k ≠ 0)
    (hp : p.Prime) (ha : a ∈ Icc 1 (m.factorization p))
    (hnodiv : ¬p ∣ n.choose k) :
    k % p ^ a ≤ r % p ^ a := by
  have hmone : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have hkn : k ≤ n := by
    rw [hn]
    nlinarith
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_of_ne_zero hk) hkn)
  have ha' : 1 ≤ a ∧ a ≤ m.factorization p := by
    simpa only [mem_Icc] using ha
  have hpowdvd : p ^ a ∣ m := by
    apply (hp.pow_dvd_iff_le_factorization hm).2
    exact ha'.2
  have hnmod : n % p ^ a = r % p ^ a := by
    rw [hn, Nat.add_mod, Nat.mul_mod]
    have hpm : m % p ^ a = 0 := Nat.dvd_iff_mod_eq_zero.mp hpowdvd
    simp [hpm]
  by_contra hnot
  have hlt : r % p ^ a < k % p ^ a := Nat.lt_of_not_ge hnot
  have hnlt : n % p ^ a < k % p ^ a := hnmod.trans_lt hlt
  have hcarry : p ^ a ≤ k % p ^ a + (n - k) % p ^ a := by
    by_contra hcarry
    have hsum : k % p ^ a + (n - k) % p ^ a < p ^ a := Nat.lt_of_not_ge hcarry
    have hnmod' : n % p ^ a = k % p ^ a + (n - k) % p ^ a := by
      conv_lhs => rw [← Nat.add_sub_of_le hkn]
      rw [Nat.add_mod, Nat.mod_eq_of_lt hsum]
    have hkle : k % p ^ a ≤ n % p ^ a := by
      rw [hnmod']
      exact Nat.le_add_right _ _
    exact (Nat.not_lt_of_ge hkle) hnlt
  have hapow : a ≤ p ^ a :=
    a.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hp.two_le a)
  have hpown : p ^ a ≤ n := by
    calc
      p ^ a ≤ m := Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hm) hpowdvd
      _ ≤ m * k := by
        exact Nat.le_mul_of_pos_right m (Nat.zero_lt_of_ne_zero hk)
      _ ≤ n := by omega
  have hain : a ∈ Ico 1 (n + 1) := by
    simp only [mem_Ico]
    exact ⟨ha'.1, Nat.lt_succ_of_le (hapow.trans hpown)⟩
  have hfac0 : (n.choose k).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hnodiv
  have hfac := Nat.factorization_choose hp hkn
    ((Nat.log_lt_self p hn0).trans (Nat.lt_succ_self n))
  rw [hfac0] at hfac
  have hmem : a ∈ {i ∈ Ico 1 (n + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
    simp only [mem_filter]
    exact ⟨hain, hcarry⟩
  have hcardpos : 0 < #{i ∈ Ico 1 (n + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} :=
    card_pos.mpr ⟨a, hmem⟩
  exact (Nat.ne_of_gt hcardpos) hfac.symm

theorem quotient_transfer_of_no_prime_divisors
    {n m k r : ℕ} (hn : n = m * k + r) (hm : m ≠ 0) (hk : k ≠ 0)
    (hrk : r < k)
    (hprime : ∀ p, p.Prime → p ∣ m → ¬p ∣ n.choose k) :
    m ∣ (k - r) * k.choose r := by
  apply quotient_transfer_of_mod_le hm hk hrk
  intro p hp a ha
  apply mod_le_of_no_prime_divisor hn hm hk hp ha
  apply hprime p hp
  have ha' : 1 ≤ a ∧ a ≤ m.factorization p := by
    simpa only [mem_Icc] using ha
  exact (dvd_pow_self p (Nat.ne_of_gt ha'.1)).trans
    ((hp.pow_dvd_iff_le_factorization hm).2 ha'.2)

/-- Target-facing quotient transfer: every exceptional pair has quotient
`n / k` dividing a smaller binomial product determined by the remainder. -/
theorem quotient_transfer_of_large_minFac
    {n k : ℕ} (hk : 0 < k) (h2k : 2 * k ≤ n)
    (hlarge : max (n / k) k < (n.choose k).minFac) :
    n / k ∣ (k - n % k) * k.choose (n % k) := by
  have hkn : k ≤ n := by omega
  have hmpos : 0 < n / k := Nat.div_pos hkn hk
  have hdecomp : n = n / k * k + n % k := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod n k).symm
  apply quotient_transfer_of_no_prime_divisors (n := n) (m := n / k) (k := k)
    (r := n % k) hdecomp hmpos.ne' hk.ne' (Nat.mod_lt n hk)
  intro p hp hpm hpdvd
  have hpmle : p ≤ n / k := Nat.le_of_dvd hmpos hpm
  have hminle : (n.choose k).minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpdvd
  have hpmax : p ≤ max (n / k) k := hpmle.trans (le_max_left _ _)
  omega

end Contribution.Erdos1094.Quotient
