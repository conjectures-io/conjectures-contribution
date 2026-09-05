import Mathlib

/-! Structural reductions for Erdős 727. No infinitude claim is proved here. -/
namespace Contribution.Subb727

theorem factorial_square_iff_choose (n : ℕ) :
    (n+2).factorial ^ 2 ∣ (2*n).factorial ↔
      (n+1)^2 * (n+2)^2 ∣ (2*n).choose n := by
  have hfac : (2*n).factorial = n.factorial^2 * (2*n).choose n := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
    have he : 2*n-n = n := by omega
    rw [he] at h
    nlinarith only [h]
  have hleft : (n+2).factorial^2 = n.factorial^2 * ((n+1)^2*(n+2)^2) := by
    rw [show n+2 = (n+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    ring
  rw [hfac, hleft]
  exact Nat.mul_dvd_mul_iff_left (pow_pos (Nat.factorial_pos n) 2)

theorem central_choose_valuation_le_one {n p : ℕ} (hp : p.Prime)
    (hlarge : 2*n < p^2) : padicValNat p ((2*n).choose n) ≤ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (2*n) < 2 := by
    exact Nat.log_lt_of_lt_pow' (by norm_num) hlarge
  rw [padicValNat_choose (by omega : n ≤ 2*n) hlog]
  exact le_trans (Finset.card_filter_le _ _) (by decide)

theorem prime_factor_square_bound {n p : ℕ} (hp : p.Prime)
    (hs : (n+2).factorial^2 ∣ (2*n).factorial)
    (hd : p ∣ n+1 ∨ p ∣ n+2) : p^2 ≤ 2*n := by
  letI : Fact p.Prime := ⟨hp⟩
  have hb := (factorial_square_iff_choose n).mp hs
  have hp2 : p^2 ∣ (2*n).choose n := by
    apply dvd_trans _ hb
    rcases hd with h | h
    · exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd h 2) _
    · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd h 2) _
  have hv : 2 ≤ padicValNat p ((2*n).choose n) :=
    (padicValNat_dvd_iff_le (Nat.choose_ne_zero (by omega))).mp hp2
  by_contra h
  have := central_choose_valuation_le_one hp (by omega : 2*n < p^2)
  omega

theorem arbitrarily_large_failures_in_every_residue (q r B : ℕ) (hq : 0 < q) :
    ∃ n, B < n ∧ Nat.ModEq q n r ∧
      ¬ (n+2).factorial^2 ∣ (2*n).factorial := by
  let g := Nat.gcd (r+2) q
  have hg : 0 < g := Nat.gcd_pos_of_pos_right (r+2) hq
  have hgq : g ∣ q := Nat.gcd_dvd_right (r+2) q
  have hgr : g ∣ r+2 := Nat.gcd_dvd_left (r+2) q
  have hqrep : g * (q/g) = q := Nat.mul_div_cancel' hgq
  have hrrep : g * ((r+2)/g) = r+2 := Nat.mul_div_cancel' hgr
  have hquot : q/g ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hqrep
    omega
  have hcop : ((r+2)/g).Coprime (q/g) := Nat.coprime_div_gcd_div_gcd hg
  obtain ⟨p, hpbig, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (B + 2*g + 2) hquot hcop
  have hgp : 2 ≤ g*p := by nlinarith [hp.two_le]
  have hnrep : g*p-2+2 = g*p := by omega
  refine ⟨g*p-2, ?_, ?_, ?_⟩
  · nlinarith
  · have hm := hmod.mul_left' g
    rw [hqrep, hrrep] at hm
    apply Nat.ModEq.add_right_cancel' 2
    simpa only [hnrep] using hm
  · intro hs
    have hd : p ∣ (g*p-2)+2 := by
      rw [hnrep]
      exact dvd_mul_left p g
    have hb := prime_factor_square_bound hp hs (Or.inr hd)
    nlinarith

end Contribution.Subb727
