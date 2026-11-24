import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Module.NatInt

/-!
# Obláth's Theorem on Five Integers in Arithmetic Progression (Erdős Problem #672, k = 5, l = 2)

Proves unconditionally that the product of five positive integers in coprime arithmetic
progression `n * (n + d) * (n + 2*d) * (n + 3*d) * (n + 4*d)` (`n, d > 0`, `Nat.Coprime n d`)
is never a perfect square, discharging the `Erdos672With 5 2` conjunct of
`Erdos672.erdos_672.variants.oblath` as well as `Erdos672With 5 (2 * m)` for all `m > 0`.

Combines canonical `{1, 2, 3, 6}` square-free splitting from `p`-adic valuation divisibility
for primes `p ≥ 5` with a kernel-decidable mod-8 and mod-9 filter (`checkAll5`) reducing all
`4^5 = 1024` tuples to `(1, 1, 1, 1, 1)`, `(6, 1, 2, 3, 1)`, and `(1, 3, 2, 1, 6)`, each closed
by the four-term square-product exclusion theorem (`no_prod_four_ap_sq`).
-/

namespace Contribution.Erdos672OblathK5L2

private theorem nat_coprime_mul_eq_sq_left {u v y : ℕ} (hcop : Nat.Coprime u v)
    (heq : u * v = y ^ 2) : ∃ a : ℕ, u = a ^ 2 := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · exact ⟨0, by simp⟩
  have hiz : (u : ℤ) * (v : ℤ) = (y : ℤ) ^ 2 := by exact_mod_cast heq
  have hgcd : Int.gcd (u : ℤ) (v : ℤ) = 1 := by simpa using hcop
  obtain ⟨a0, ha0 | ha0⟩ := Int.sq_of_gcd_eq_one hgcd hiz
  · refine ⟨a0.natAbs, ?_⟩
    have h1 : (u : ℤ) = (a0.natAbs : ℤ) ^ 2 := by rw [Int.natAbs_sq, ha0]
    exact_mod_cast h1
  · exfalso
    have hneg : -a0 ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg a0)
    have hpos : (0 : ℤ) < u := Int.natCast_pos.mpr hu
    omega

private theorem nat_coprime_mul_eq_sq {u v y : ℕ} (hcop : Nat.Coprime u v) (heq : u * v = y ^ 2) :
    ∃ a b : ℕ, u = a ^ 2 ∧ v = b ^ 2 := by
  obtain ⟨a, ha⟩ := nat_coprime_mul_eq_sq_left hcop heq
  obtain ⟨b, hb⟩ := nat_coprime_mul_eq_sq_left hcop.symm (mul_comm u v ▸ heq)
  exact ⟨a, b, ha, hb⟩

private theorem nat_coprime_mul_eq_prime_mul_sq {p u v q : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime u v) (heq : u * v = p * q ^ 2) :
    (∃ a b : ℕ, u = p * a ^ 2 ∧ v = b ^ 2) ∨ (∃ a b : ℕ, u = a ^ 2 ∧ v = p * b ^ 2) := by
  have hdvd : p ∣ u * v := ⟨q ^ 2, heq⟩
  rcases hp.dvd_mul.mp hdvd with hpu | hpv
  · left
    obtain ⟨u', rfl⟩ := hpu
    have heq' : u' * v = q ^ 2 := by
      have : p * (u' * v) = p * q ^ 2 := by linear_combination heq
      exact Nat.mul_left_cancel hp.pos this
    have hcop' : Nat.Coprime u' v := hcop.coprime_dvd_left ⟨p, mul_comm p u'⟩
    obtain ⟨a, b, ha, hb⟩ := nat_coprime_mul_eq_sq hcop' heq'
    exact ⟨a, b, by rw [ha], hb⟩
  · right
    obtain ⟨v', rfl⟩ := hpv
    have heq' : u * v' = q ^ 2 := by
      have : p * (u * v') = p * q ^ 2 := by linear_combination heq
      exact Nat.mul_left_cancel hp.pos this
    have hcop' : Nat.Coprime u v' := hcop.coprime_dvd_right ⟨p, mul_comm p v'⟩
    obtain ⟨a, b, ha, hb⟩ := nat_coprime_mul_eq_sq hcop' heq'
    exact ⟨a, b, ha, by rw [hb]⟩

private theorem not_sum_sq_mod_four_two {x y z : ℕ} (hx : x % 2 = 1) (hy : y % 2 = 1) :
    x ^ 2 + y ^ 2 ≠ z ^ 2 := by
  intro heq
  have hlhs : (x ^ 2 + y ^ 2) % 4 = 2 := by
    rw [← Nat.div_add_mod x 2, ← Nat.div_add_mod y 2, hx, hy]
    ring_nf
    omega
  rcases Nat.mod_two_eq_zero_or_one z with hz | hz
  · have hrhs : z ^ 2 % 4 = 0 := by
      rw [← Nat.div_add_mod z 2, hz]; ring_nf; omega
    omega
  · have hrhs : z ^ 2 % 4 = 1 := by
      rw [← Nat.div_add_mod z 2, hz]; ring_nf; omega
    omega

private theorem coprime_sq_add_sq_and_four {g h : ℕ} (hcop : Nat.Coprime g h) :
    Nat.Coprime (g ^ 2 + h ^ 2) (g ^ 2 + 4 * h ^ 2) := by
  refine Nat.coprime_of_dvd' fun p hp hp1 hp2 => ?_
  have hp3 : p ∣ 3 * h ^ 2 := by
    have heq : g ^ 2 + 4 * h ^ 2 = (g ^ 2 + h ^ 2) + 3 * h ^ 2 := by ring
    rw [heq] at hp2
    exact (Nat.dvd_add_right hp1).mp hp2
  rcases hp.dvd_mul.mp hp3 with hp_three | hp_hsq
  · have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp_three
    subst hp_eq
    by_cases hg3 : 3 ∣ g
    · have hhsq : 3 ∣ h ^ 2 := (Nat.dvd_add_right (dvd_pow hg3 (by decide))).mp hp1
      have hh3 : 3 ∣ h := Nat.prime_three.dvd_of_dvd_pow hhsq
      exact hcop ▸ Nat.dvd_gcd hg3 hh3
    · exfalso
      have hh3 : ¬ 3 ∣ h := fun hh =>
        hg3 (Nat.prime_three.dvd_of_dvd_pow ((Nat.dvd_add_left (dvd_pow hh (by decide))).mp hp1))
      have hgm : g % 3 = 1 ∨ g % 3 = 2 := by omega
      have hhm : h % 3 = 1 ∨ h % 3 = 2 := by omega
      have hmod1 : (g ^ 2 + h ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd hp1
      rw [← Nat.div_add_mod g 3, ← Nat.div_add_mod h 3] at hmod1
      rcases hgm with hgm | hgm <;> rcases hhm with hhm | hhm <;>
        rw [hgm, hhm] at hmod1 <;> ring_nf at hmod1 <;> omega
  · have hph : p ∣ h := hp.dvd_of_dvd_pow hp_hsq
    have hpg : p ∣ g := hp.dvd_of_dvd_pow ((Nat.dvd_add_left (dvd_pow hph (by decide))).mp hp1)
    exact hcop ▸ Nat.dvd_gcd hpg hph

private theorem coprime_sq_sub_mul_nat {a b : ℕ} (hcop : Nat.Coprime a b) (hba : b ≤ a) :
    Nat.Coprime (a ^ 2 - b ^ 2) (a * b) := by
  refine Nat.coprime_of_dvd' fun r hr hr1 hr2 => ?_
  have hle : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hba 2
  rcases hr.dvd_mul.mp hr2 with hra | hrb
  · have hr_bsq : r ∣ b ^ 2 := by
      have hsub : a ^ 2 - (a ^ 2 - b ^ 2) = b ^ 2 := Nat.sub_sub_self hle
      rw [← hsub]
      exact Nat.dvd_sub (dvd_pow hra (by decide)) hr1
    exact hcop ▸ Nat.dvd_gcd hra (hr.dvd_of_dvd_pow hr_bsq)
  · have hr_asq : r ∣ a ^ 2 := by
      have hadd := Nat.dvd_add hr1 (dvd_pow hrb (by decide : 2 ≠ 0))
      rwa [Nat.sub_add_cancel hle] at hadd
    exact hcop ▸ Nat.dvd_gcd (hr.dvd_of_dvd_pow hr_asq) hrb

private theorem eq_of_coprime_sq_mul_eq {A B X Y : ℕ} (hAB : Nat.Coprime A B)
    (hXY : Nat.Coprime X Y) (heq : A ^ 2 * X = B ^ 2 * Y) : A ^ 2 = Y ∧ B ^ 2 = X := by
  have hA2B2 : Nat.Coprime (A ^ 2) (B ^ 2) := (hAB.pow_left 2).pow_right 2
  have hd1 : A ^ 2 ∣ B ^ 2 * Y := ⟨X, heq.symm⟩
  have h1 : A ^ 2 ∣ Y := hA2B2.dvd_of_dvd_mul_left hd1
  have h2 : Y ∣ A ^ 2 := hXY.symm.dvd_of_dvd_mul_left ⟨B ^ 2, by
    calc X * A ^ 2 = A ^ 2 * X := by ring
      _ = B ^ 2 * Y := heq
      _ = Y * B ^ 2 := by ring⟩
  have hAY : A ^ 2 = Y := Nat.dvd_antisymm h1 h2
  have h3 : B ^ 2 ∣ X := hA2B2.symm.dvd_of_dvd_mul_left ⟨Y, heq⟩
  have h4 : X ∣ B ^ 2 := hXY.dvd_of_dvd_mul_left ⟨A ^ 2, by
    calc Y * B ^ 2 = B ^ 2 * Y := by ring
      _ = A ^ 2 * X := heq.symm
      _ = X * A ^ 2 := by ring⟩
  exact ⟨hAY, Nat.dvd_antisymm h3 h4⟩

/-- No positive coprime integers `x, y` satisfy `x^2 + y^2 = z^2` and `x^2 + 4*y^2 = w^2`
simultaneously (Fermat-style infinite descent on `z + w`). -/
private theorem no_sim_pyth : ∀ S x y z w : ℕ,
    0 < x → 0 < y → 0 < z → 0 < w → z + w = S →
    Nat.Coprime x y → x ^ 2 + y ^ 2 = z ^ 2 → x ^ 2 + 4 * y ^ 2 = w ^ 2 → False := by
  intro S
  induction S using Nat.strong_induction_on with
  | h S ih =>
    intro x y z w hx hy hz hw hsum hcop heq1 heq2
    by_cases hx2 : 2 ∣ x
    · obtain ⟨x', rfl⟩ := hx2
      have hx' : 0 < x' := by omega
      have hcop' : Nat.Coprime y x' := hcop.symm.coprime_dvd_right ⟨2, mul_comm 2 x'⟩
      have hw_even : 2 ∣ w := by
        have h2w2 : 2 ∣ w ^ 2 := ⟨2 * (x' ^ 2 + y ^ 2), by
          calc w ^ 2 = (2 * x') ^ 2 + 4 * y ^ 2 := heq2.symm
            _ = 2 * (2 * (x' ^ 2 + y ^ 2)) := by ring⟩
        exact Nat.prime_two.dvd_of_dvd_pow h2w2
      obtain ⟨w', rfl⟩ := hw_even
      have hw' : 0 < w' := by omega
      have h4w : 4 * (y ^ 2 + x' ^ 2) = 4 * w' ^ 2 := by
        calc 4 * (y ^ 2 + x' ^ 2) = (2 * x') ^ 2 + 4 * y ^ 2 := by ring
          _ = (2 * w') ^ 2 := heq2
          _ = 4 * w' ^ 2 := by ring
      have heq1' : y ^ 2 + x' ^ 2 = w' ^ 2 := by omega
      have heq2' : y ^ 2 + 4 * x' ^ 2 = z ^ 2 := by
        calc y ^ 2 + 4 * x' ^ 2 = (2 * x') ^ 2 + y ^ 2 := by ring
          _ = z ^ 2 := heq1
      exact ih (w' + z) (by omega) y x' w' z hy hx' hw' hz rfl hcop' heq1' heq2'
    · have hx_odd : x % 2 = 1 := by omega
      have hy2 : 2 ∣ y := by
        by_contra hy_ndvd
        exact not_sum_sq_mod_four_two hx_odd (by omega) heq1
      have hw_odd : w % 2 = 1 := by
        by_contra hw_even
        obtain ⟨k, rfl⟩ := (by omega : 2 ∣ w)
        have hx2sq : 2 ∣ x ^ 2 := by
          have hle : y ^ 2 ≤ k ^ 2 := by nlinarith only [heq2]
          have : x ^ 2 = 2 * (2 * k ^ 2 - 2 * y ^ 2) := by
            zify [Nat.mul_le_mul_left 2 hle]
            have hz2 : (x : ℤ) ^ 2 + 4 * (y : ℤ) ^ 2 = (2 * (k : ℤ)) ^ 2 := by exact_mod_cast heq2
            linarith only [hz2]
          exact ⟨2 * k ^ 2 - 2 * y ^ 2, this⟩
        exact hx2 (Nat.prime_two.dvd_of_dvd_pow hx2sq)
      have hxw : x < w := by nlinarith only [heq2, hx, hy, hw]
      set u := (w + x) / 2
      set v := (w - x) / 2
      have hu2 : 2 * u = w + x := by omega
      have hv2 : 2 * v = w - x := by omega
      have hu_pos : 0 < u := by omega
      have hv_pos : 0 < v := by omega
      have hvu : v < u := by omega
      have huv_eq : u * v = y ^ 2 := by
        have h4 : 4 * (u * v) = 4 * y ^ 2 := by
          zify [le_of_lt hxw] at hu2 hv2 heq2 ⊢
          nlinarith only [hu2, hv2, heq2]
        omega
      have hcop_uv : Nat.Coprime u v := by
        refine Nat.coprime_of_dvd' fun r hr hru hrv => ?_
        have hrx : r ∣ x := by rw [show x = u - v by omega]; exact Nat.dvd_sub hru hrv
        have hry : r ∣ y := hr.dvd_of_dvd_pow (huv_eq ▸ dvd_mul_of_dvd_left hru v)
        exact hcop ▸ Nat.dvd_gcd hrx hry
      obtain ⟨p, q, hu_sq, hv_sq⟩ := nat_coprime_mul_eq_sq hcop_uv huv_eq
      have hqp : q < p := by nlinarith only [hu_sq, hv_sq, hvu]
      have hq_pos : 0 < q := by nlinarith only [hv_sq, hv_pos]
      have hp_pos : 0 < p := by omega
      have hcop_pq : Nat.Coprime p q := by
        refine Nat.coprime_of_dvd' fun r _ hrp hrq => ?_
        exact hcop_uv ▸ Nat.dvd_gcd (hu_sq ▸ dvd_pow hrp (by decide)) (hv_sq ▸ dvd_pow hrq (by decide))
      have hx_pq : x = p ^ 2 - q ^ 2 := by omega
      have hy_pq : y = p * q := by
        have hsq : (p * q) ^ 2 = y ^ 2 := by
          calc (p * q) ^ 2 = p ^ 2 * q ^ 2 := by ring
            _ = u * v := by rw [← hu_sq, ← hv_sq]
            _ = y ^ 2 := huv_eq
        rcases lt_trichotomy (p * q) y with hlt | heq | hgt
        · exact absurd (Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)) (by omega)
        · exact heq.symm
        · exact absurd (Nat.pow_lt_pow_left hgt (by decide : 2 ≠ 0)) (by omega)
      have hw_pq : w = p ^ 2 + q ^ 2 := by omega
      have hx_z : (x : ℤ) = (p : ℤ) ^ 2 - (q : ℤ) ^ 2 := by
        zify [Nat.pow_le_pow_left (le_of_lt hqp) 2] at hx_pq
        exact hx_pq
      have hy_z : (y : ℤ) = (p : ℤ) * (q : ℤ) := by exact_mod_cast hy_pq
      have hpyth : PythagoreanTriple ((p : ℤ) ^ 2 - (q : ℤ) ^ 2) ((p : ℤ) * (q : ℤ)) (z : ℤ) := by
        dsimp [PythagoreanTriple]
        rw [← hx_z, ← hy_z]
        exact_mod_cast (by linear_combination heq1 : x * x + y * y = z * z)
      have hcop_z : Int.gcd ((p : ℤ) ^ 2 - (q : ℤ) ^ 2) ((p : ℤ) * (q : ℤ)) = 1 := by
        rw [← hx_z, ← hy_z]
        simpa using hcop
      have hpar_z : ((p : ℤ) ^ 2 - (q : ℤ) ^ 2) % 2 = 1 := by
        rw [← hx_z]; omega
      obtain ⟨m, n, hm_eq, hn_eq, hz_eq, hcop_mn, _, hm_nonneg⟩ :=
        hpyth.coprime_classification' hcop_z hpar_z (Int.natCast_pos.mpr hz)
      have hm_pos_z : 0 < m := by
        by_contra hm0
        have hmz : m = 0 := by omega
        subst hmz
        have : p * q = 0 := by exact_mod_cast (by linarith only [hn_eq] : (p : ℤ) * (q : ℤ) = 0)
        nlinarith only [hp_pos, hq_pos, this]
      have hn_pos_z : 0 < n := by
        have hpq_z : (0 : ℤ) < (p : ℤ) * (q : ℤ) := by positivity
        nlinarith only [hpq_z, hn_eq, hm_pos_z]
      set m' := m.natAbs
      set n' := n.natAbs
      have hm'_pos : 0 < m' := Int.natAbs_pos.mpr hm_pos_z.ne'
      have hn'_pos : 0 < n' := Int.natAbs_pos.mpr hn_pos_z.ne'
      have hm'_cast : (m' : ℤ) = m := Int.natAbs_of_nonneg hm_nonneg
      have hn'_cast : (n' : ℤ) = n := Int.natAbs_of_nonneg (le_of_lt hn_pos_z)
      have hm'_eq : p ^ 2 + n' ^ 2 = m' ^ 2 + q ^ 2 := by
        zify; rw [hm'_cast, hn'_cast]; linear_combination hm_eq
      have hpq' : p * q = 2 * m' * n' := by
        zify; rw [hm'_cast, hn'_cast]; exact hn_eq
      have hz' : z = m' ^ 2 + n' ^ 2 := by
        zify; rw [hm'_cast, hn'_cast]; exact hz_eq
      set g := Nat.gcd p m'
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left m' hp_pos
      set A := p / g
      set B := m' / g
      have hp_gA : p = g * A := (Nat.mul_div_cancel' (Nat.gcd_dvd_left p m')).symm
      have hm'_gB : m' = g * B := (Nat.mul_div_cancel' (Nat.gcd_dvd_right p m')).symm
      have hA_pos : 0 < A := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hp_gA; omega
      have hB_pos : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hm'_gB; omega
      have hcop_AB : Nat.Coprime A B := Nat.coprime_div_gcd_div_gcd hg_pos
      have hAq : A * q = 2 * B * n' := by
        have : g * (A * q) = g * (2 * B * n') := by
          calc g * (A * q) = (g * A) * q := by ring
            _ = p * q := by rw [← hp_gA]
            _ = 2 * m' * n' := hpq'
            _ = 2 * (g * B) * n' := by rw [hm'_gB]
            _ = g * (2 * B * n') := by ring
        exact Nat.mul_left_cancel hg_pos this
      by_cases hA2 : 2 ∣ A
      · obtain ⟨A', hA'eq⟩ := hA2
        have hA'_pos : 0 < A' := by omega
        have hcop_A'B : Nat.Coprime A' B := hcop_AB.coprime_dvd_left ⟨2, by rw [hA'eq, mul_comm]⟩
        have hA'q : A' * q = B * n' := by
          have h2 : 2 * (A' * q) = 2 * (B * n') := by
            calc 2 * (A' * q) = (2 * A') * q := by ring
              _ = A * q := by rw [← hA'eq]
              _ = 2 * B * n' := hAq
              _ = 2 * (B * n') := by ring
          omega
        obtain ⟨h, hh_eq⟩ := hcop_A'B.dvd_of_dvd_mul_left ⟨q, by rw [← hA'q, mul_comm]⟩
        have hq_Bh : q = B * h := by
          have : A' * q = A' * (B * h) := by
            calc A' * q = B * n' := hA'q
              _ = B * (A' * h) := by rw [hh_eq]
              _ = A' * (B * h) := by ring
          exact Nat.mul_left_cancel hA'_pos this
        have hh_pos : 0 < h := by
          rw [hq_Bh] at hq_pos
          exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hq_pos
        have hcop_hg : Nat.Coprime h g := by
          refine Nat.coprime_of_dvd' fun r _ hrh hrg => ?_
          have hrp : r ∣ p := hp_gA ▸ dvd_mul_of_dvd_left hrg A
          have hrq : r ∣ q := by rw [hq_Bh]; exact dvd_mul_of_dvd_right hrh B
          exact hcop_pq ▸ Nat.dvd_gcd hrp hrq
        have hrel : A' ^ 2 * (h ^ 2 + 4 * g ^ 2) = B ^ 2 * (h ^ 2 + g ^ 2) := by
          have hsub : (g * (2 * A')) ^ 2 + (A' * h) ^ 2 = (g * B) ^ 2 + (B * h) ^ 2 := by
            rw [← hA'eq, ← hp_gA, ← hm'_gB, ← hh_eq, ← hq_Bh]; exact hm'_eq
          calc A' ^ 2 * (h ^ 2 + 4 * g ^ 2) = (g * (2 * A')) ^ 2 + (A' * h) ^ 2 := by ring
            _ = (g * B) ^ 2 + (B * h) ^ 2 := hsub
            _ = B ^ 2 * (h ^ 2 + g ^ 2) := by ring
        obtain ⟨hA'sq, hBsq⟩ :=
          eq_of_coprime_sq_mul_eq hcop_A'B (coprime_sq_add_sq_and_four hcop_hg).symm hrel
        have hlt : A' + B < S := by
          have hp_lt : p < w := by nlinarith only [hw_pq, hq_pos, hp_pos]
          have hm_lt : m' < z := by nlinarith only [hz', hn'_pos, hm'_pos]
          have hA_eq : p = g * (2 * A') := by rw [← hA'eq]; exact hp_gA
          have hA'p : A' < p := by nlinarith only [hA_eq, hg_pos, hA'_pos]
          have hBm : B ≤ m' := by nlinarith only [hm'_gB, hg_pos]
          omega
        exact ih (A' + B) hlt h g A' B hh_pos hg_pos hA'_pos hB_pos rfl hcop_hg hA'sq.symm hBsq.symm
      · have hcop_A2B : Nat.Coprime A (2 * B) :=
          (Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr hA2)).mul_right hcop_AB
        obtain ⟨h, hh_eq⟩ := hcop_A2B.dvd_of_dvd_mul_left ⟨q, by rw [← hAq, mul_comm]⟩
        have hq_2Bh : q = 2 * B * h := by
          have : A * q = A * (2 * B * h) := by
            calc A * q = 2 * B * n' := hAq
              _ = 2 * B * (A * h) := by rw [hh_eq]
              _ = A * (2 * B * h) := by ring
          exact Nat.mul_left_cancel hA_pos this
        have hh_pos : 0 < h := by
          rw [hq_2Bh] at hq_pos
          exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hq_pos
        have hcop_gh : Nat.Coprime g h := by
          refine Nat.coprime_of_dvd' fun r _ hrg hrh => ?_
          have hrp : r ∣ p := hp_gA ▸ dvd_mul_of_dvd_left hrg A
          have hrq : r ∣ q := by rw [hq_2Bh]; exact dvd_mul_of_dvd_right hrh (2 * B)
          exact hcop_pq ▸ Nat.dvd_gcd hrp hrq
        have hrel : A ^ 2 * (g ^ 2 + h ^ 2) = B ^ 2 * (g ^ 2 + 4 * h ^ 2) := by
          have hsub : (g * A) ^ 2 + (A * h) ^ 2 = (g * B) ^ 2 + (2 * B * h) ^ 2 := by
            rw [← hp_gA, ← hm'_gB, ← hh_eq, ← hq_2Bh]; exact hm'_eq
          calc A ^ 2 * (g ^ 2 + h ^ 2) = (g * A) ^ 2 + (A * h) ^ 2 := by ring
            _ = (g * B) ^ 2 + (2 * B * h) ^ 2 := hsub
            _ = B ^ 2 * (g ^ 2 + 4 * h ^ 2) := by ring
        obtain ⟨hAsq, hBsq⟩ :=
          eq_of_coprime_sq_mul_eq hcop_AB (coprime_sq_add_sq_and_four hcop_gh) hrel
        have hlt : B + A < S := by
          have hp_lt : p < w := by nlinarith only [hw_pq, hq_pos, hp_pos]
          have hm_lt : m' < z := by nlinarith only [hz', hn'_pos, hm'_pos]
          have hAp : A ≤ p := by nlinarith only [hp_gA, hg_pos]
          have hBm : B ≤ m' := by nlinarith only [hm'_gB, hg_pos]
          omega
        exact ih (B + A) hlt g h B A hg_pos hh_pos hB_pos hA_pos rfl hcop_gh hBsq.symm hAsq.symm

/-- Corollary of `no_sim_pyth`: `p^4 + q^4 = c^2 + p^2 * q^2` has no coprime solutions `0 < q < p`. -/
private theorem no_biquad_sub {p q c : ℕ} (hqp : q < p) (hq : 0 < q) (hcop : Nat.Coprime p q)
    (heq : p ^ 4 + q ^ 4 = c ^ 2 + p ^ 2 * q ^ 2) : False := by
  have hq2p2 : q ^ 2 < p ^ 2 := by nlinarith only [hqp, hq]
  have hx : 0 < p ^ 2 - q ^ 2 := Nat.sub_pos_of_lt hq2p2
  have hy : 0 < p * q := by nlinarith only [hqp, hq]
  have hc : 0 < c := by
    have hp_pos : 0 < p := by omega
    have hpq4 : p ^ 2 * q ^ 2 < p ^ 4 := by
      calc p ^ 2 * q ^ 2 < p ^ 2 * p ^ 2 := Nat.mul_lt_mul_of_pos_left hq2p2 (Nat.pow_pos hp_pos)
        _ = p ^ 4 := by ring
    have hpos : 0 < c ^ 2 := by linarith only [heq, hpq4, Nat.zero_le (q ^ 4)]
    exact Nat.pos_of_ne_zero fun h0 => by simp [h0] at hpos
  have hw : 0 < p ^ 2 + q ^ 2 := by nlinarith only [hq]
  have hcop_xy : Nat.Coprime (p ^ 2 - q ^ 2) (p * q) := coprime_sq_sub_mul_nat hcop (le_of_lt hqp)
  have h1 : (p ^ 2 - q ^ 2) ^ 2 + (p * q) ^ 2 = c ^ 2 := by
    zify [Nat.pow_le_pow_left (le_of_lt hqp) 2]
    have heqz : (p : ℤ) ^ 4 + (q : ℤ) ^ 4 = (c : ℤ) ^ 2 + (p : ℤ) ^ 2 * (q : ℤ) ^ 2 := by
      exact_mod_cast heq
    linear_combination heqz
  have h2 : (p ^ 2 - q ^ 2) ^ 2 + 4 * (p * q) ^ 2 = (p ^ 2 + q ^ 2) ^ 2 := by
    zify [Nat.pow_le_pow_left (le_of_lt hqp) 2]
    ring
  exact no_sim_pyth (c + (p ^ 2 + q ^ 2)) (p ^ 2 - q ^ 2) (p * q) c (p ^ 2 + q ^ 2)
    hx hy hc hw rfl hcop_xy h1 h2

private theorem coprime_of_sq_ap {a c e : ℕ} (hac : Nat.Coprime a c)
    (heq : a ^ 2 + e ^ 2 = 2 * c ^ 2) :
    a % 2 = 1 ∧ c % 2 = 1 ∧ e % 2 = 1 ∧ Nat.Coprime a e ∧ Nat.Coprime c e := by
  have ha_odd : a % 2 = 1 := by
    by_contra ha2
    obtain ⟨ka, rfl⟩ := (by omega : 2 ∣ a)
    have h2esq : 2 ∣ e ^ 2 := by
      have : 2 ∣ (2 * ka) ^ 2 + e ^ 2 := heq ▸ dvd_mul_right 2 (c ^ 2)
      exact (Nat.dvd_add_right ⟨2 * ka ^ 2, by ring⟩).mp this
    obtain ⟨ke, rfl⟩ := Nat.prime_two.dvd_of_dvd_pow h2esq
    have hc2eq : 2 * c ^ 2 = 2 * (2 * (ka ^ 2 + ke ^ 2)) := by linear_combination -heq
    have h2csq : 2 ∣ c ^ 2 := ⟨ka ^ 2 + ke ^ 2, by omega⟩
    have hc2 : 2 ∣ c := Nat.prime_two.dvd_of_dvd_pow h2csq
    exact Nat.prime_two.not_dvd_one (hac ▸ Nat.dvd_gcd ⟨ka, rfl⟩ hc2)
  have he_odd : e % 2 = 1 := by
    by_contra he2
    obtain ⟨ke, rfl⟩ := (by omega : 2 ∣ e)
    have h2asq : 2 ∣ a ^ 2 := by
      have : 2 ∣ a ^ 2 + (2 * ke) ^ 2 := heq ▸ dvd_mul_right 2 (c ^ 2)
      exact (Nat.dvd_add_left ⟨2 * ke ^ 2, by ring⟩).mp this
    have h2a := Nat.prime_two.dvd_of_dvd_pow h2asq
    omega
  have hc_odd : c % 2 = 1 := by
    by_contra hc2
    obtain ⟨kc, rfl⟩ := (by omega : 2 ∣ c)
    have hmod : (a ^ 2 + e ^ 2) % 4 = 2 := by
      rw [← Nat.div_add_mod a 2, ← Nat.div_add_mod e 2, ha_odd, he_odd]; ring_nf; omega
    have h4 : (2 * (2 * kc) ^ 2) % 4 = 0 := by ring_nf; omega
    omega
  have hcop_ae : Nat.Coprime a e := by
    refine Nat.coprime_of_dvd' fun r hr hra hre => ?_
    have hr_ne2 : r ≠ 2 := fun h2 => by subst h2; omega
    have hr2c : r ∣ 2 * c ^ 2 := heq ▸ Nat.dvd_add (dvd_pow hra (by decide)) (dvd_pow hre (by decide))
    have hr_not2 : Nat.Coprime r 2 :=
      hr.coprime_iff_not_dvd.mpr fun h => hr_ne2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
    have hr_c : r ∣ c := hr.dvd_of_dvd_pow (hr_not2.dvd_of_dvd_mul_left hr2c)
    exact hac ▸ Nat.dvd_gcd hra hr_c
  have hcop_ce : Nat.Coprime c e := by
    refine Nat.coprime_of_dvd' fun r hr hrc hre => ?_
    have hr_ne2 : r ≠ 2 := fun h2 => by subst h2; omega
    have hle : e ^ 2 ≤ 2 * c ^ 2 := by linarith only [heq, Nat.zero_le (a ^ 2)]
    have hr_asq : r ∣ a ^ 2 := by
      have : a ^ 2 = 2 * c ^ 2 - e ^ 2 := by omega
      rw [this]
      exact Nat.dvd_sub (dvd_mul_of_dvd_right (dvd_pow hrc (by decide)) 2) (dvd_pow hre (by decide))
    exact hac ▸ Nat.dvd_gcd (hr.dvd_of_dvd_pow hr_asq) hrc
  exact ⟨ha_odd, hc_odd, he_odd, hcop_ae, hcop_ce⟩

/-- Four distinct positive integers in arithmetic progression cannot all be squares (Fermat 1640). -/
private theorem no_four_sq_ap {a c e b : ℕ} (ha : 0 < a) (hac : a < c) (hce : c < e) (heb : e < b)
    (hcop : Nat.Coprime a c) (heq1 : a ^ 2 + e ^ 2 = 2 * c ^ 2)
    (heq2 : c ^ 2 + b ^ 2 = 2 * e ^ 2) : False := by
  obtain ⟨ha_odd, hc_odd, he_odd, hcop_ae, hcop_ce⟩ := coprime_of_sq_ap hcop heq1
  obtain ⟨_, _, hb_odd, _, _⟩ := coprime_of_sq_ap hcop_ce heq2
  have hcop_bc : Nat.Coprime b c := by
    refine Nat.coprime_of_dvd' fun r hr hrb hrc => ?_
    have hr_ne2 : r ≠ 2 := fun h2 => by subst h2; omega
    have hr2e : r ∣ 2 * e ^ 2 := heq2 ▸ Nat.dvd_add (dvd_pow hrc (by decide)) (dvd_pow hrb (by decide))
    have hr_not2 : Nat.Coprime r 2 :=
      hr.coprime_iff_not_dvd.mpr fun h => hr_ne2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
    have hr_e : r ∣ e := hr.dvd_of_dvd_pow (hr_not2.dvd_of_dvd_mul_left hr2e)
    exact hcop_ce ▸ Nat.dvd_gcd hrc hr_e
  set u := (e + a) / 2
  set v := (e - a) / 2
  set U := (b + c) / 2
  set V := (b - c) / 2
  have hu2 : 2 * u = e + a := by omega
  have hv2 : 2 * v = e - a := by omega
  have hU2 : 2 * U = b + c := by omega
  have hV2 : 2 * V = b - c := by omega
  have hv_pos : 0 < v := by omega
  have hV_pos : 0 < V := by omega
  have hu_pos : 0 < u := by omega
  have hU_pos : 0 < U := by omega
  have huU : u < U := by omega
  have huv_e : u + v = e := by omega
  have huv_c2 : u ^ 2 + v ^ 2 = c ^ 2 := by
    have h4 : 4 * (u ^ 2 + v ^ 2) = 4 * c ^ 2 := by
      zify [le_of_lt (lt_trans hac hce)] at hu2 hv2 heq1 ⊢
      nlinarith only [hu2, hv2, heq1]
    omega
  have hUV_e2 : U ^ 2 + V ^ 2 = e ^ 2 := by
    have h4 : 4 * (U ^ 2 + V ^ 2) = 4 * e ^ 2 := by
      zify [le_of_lt (lt_trans hce heb)] at hU2 hV2 heq2 ⊢
      nlinarith only [hU2, hV2, heq2]
    omega
  have huv_UV : u * v = U * V := by
    have h4 : 4 * (u * v) = 4 * (U * V) := by
      zify [le_of_lt (lt_trans hac hce), le_of_lt (lt_trans hce heb)] at hu2 hv2 hU2 hV2 heq1 heq2 ⊢
      nlinarith only [hu2, hv2, hU2, hV2, heq1, heq2]
    omega
  have hcop_uv : Nat.Coprime u v := by
    refine Nat.coprime_of_dvd' fun r _ hru hrv => ?_
    have hre : r ∣ e := huv_e ▸ Nat.dvd_add hru hrv
    have hra : r ∣ a := by rw [show a = u - v by omega]; exact Nat.dvd_sub hru hrv
    exact hcop_ae ▸ Nat.dvd_gcd hra hre
  have hcop_UV : Nat.Coprime U V := by
    refine Nat.coprime_of_dvd' fun r _ hrU hrV => ?_
    have hrb : r ∣ b := by rw [show b = U + V by omega]; exact Nat.dvd_add hrU hrV
    have hrc : r ∣ c := by rw [show c = U - V by omega]; exact Nat.dvd_sub hrU hrV
    exact hcop_bc ▸ Nat.dvd_gcd hrb hrc
  set g := Nat.gcd u U
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left U hu_pos
  set A := u / g
  set B := U / g
  have hu_gA : u = g * A := (Nat.mul_div_cancel' (Nat.gcd_dvd_left u U)).symm
  have hU_gB : U = g * B := (Nat.mul_div_cancel' (Nat.gcd_dvd_right u U)).symm
  have hA_pos : 0 < A := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hu_gA; omega
  have hB_pos : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hU_gB; omega
  have hcop_AB : Nat.Coprime A B := Nat.coprime_div_gcd_div_gcd hg_pos
  have hAB : A < B := by nlinarith only [hu_gA, hU_gB, huU, hg_pos]
  have hAv_BV : A * v = B * V := by
    have : g * (A * v) = g * (B * V) := by
      calc g * (A * v) = (g * A) * v := by ring
        _ = u * v := by rw [← hu_gA]
        _ = U * V := huv_UV
        _ = (g * B) * V := by rw [← hU_gB]
        _ = g * (B * V) := by ring
    exact Nat.mul_left_cancel hg_pos this
  obtain ⟨h, hh_eq⟩ := hcop_AB.symm.dvd_of_dvd_mul_left ⟨V, hAv_BV⟩
  have hV_Ah : V = A * h := by
    have : B * V = B * (A * h) := by
      calc B * V = A * v := hAv_BV.symm
        _ = A * (B * h) := by rw [hh_eq]
        _ = B * (A * h) := by ring
    exact Nat.mul_left_cancel hB_pos this
  have hh_pos : 0 < h := by nlinarith only [hh_eq, hv_pos, hB_pos]
  have hcop_gh : Nat.Coprime g h := by
    refine Nat.coprime_of_dvd' fun r _ hrg hrh => ?_
    have hru : r ∣ u := by rw [hu_gA]; exact dvd_mul_of_dvd_left hrg A
    have hrv : r ∣ v := by rw [hh_eq]; exact dvd_mul_of_dvd_right hrh B
    exact hcop_uv ▸ Nat.dvd_gcd hru hrv
  have hkey_int : ((g : ℤ) ^ 2 - (h : ℤ) ^ 2) * ((B : ℤ) ^ 2 - (A : ℤ) ^ 2) =
      2 * ((g : ℤ) * (h : ℤ)) * ((A : ℤ) * (B : ℤ)) := by
    have h1 : (U : ℤ) ^ 2 + (V : ℤ) ^ 2 = ((u : ℤ) + (v : ℤ)) ^ 2 := by
      have h1_nat : U ^ 2 + V ^ 2 = (u + v) ^ 2 := by rw [hUV_e2, huv_e]
      exact_mod_cast h1_nat
    have hug : (u : ℤ) = (g : ℤ) * (A : ℤ) := by exact_mod_cast hu_gA
    have hUg : (U : ℤ) = (g : ℤ) * (B : ℤ) := by exact_mod_cast hU_gB
    have hvg : (v : ℤ) = (B : ℤ) * (h : ℤ) := by exact_mod_cast hh_eq
    have hVg : (V : ℤ) = (A : ℤ) * (h : ℤ) := by exact_mod_cast hV_Ah
    rw [hug, hUg, hvg, hVg] at h1
    linear_combination h1
  have hhg : h < g := by
    have hBA_pos : (0 : ℤ) < (B : ℤ) ^ 2 - (A : ℤ) ^ 2 := by nlinarith only [hAB]
    have hrhs_pos : (0 : ℤ) < 2 * ((g : ℤ) * (h : ℤ)) * ((A : ℤ) * (B : ℤ)) := by positivity
    have hlhs_pos : (0 : ℤ) < (g : ℤ) ^ 2 - (h : ℤ) ^ 2 := by nlinarith only [hkey_int, hBA_pos, hrhs_pos]
    nlinarith only [hlhs_pos]
  have hkey : (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) = 2 * (g * h) * (A * B) := by
    zify [Nat.pow_le_pow_left (le_of_lt hhg) 2, Nat.pow_le_pow_left (le_of_lt hAB) 2]
    exact hkey_int
  have hcop_gh_diff : Nat.Coprime (g ^ 2 - h ^ 2) (g * h) :=
    coprime_sq_sub_mul_nat hcop_gh (le_of_lt hhg)
  have hcop_BA_diff : Nat.Coprime (B ^ 2 - A ^ 2) (A * B) := by
    simpa [mul_comm A B] using coprime_sq_sub_mul_nat hcop_AB.symm (le_of_lt hAB)
  have hpar_gh_or_BA : (g ^ 2 - h ^ 2) % 2 = 1 ∨ (B ^ 2 - A ^ 2) % 2 = 1 := by
    have huv_opp : (u % 2 = 0 ∧ v % 2 = 1) ∨ (u % 2 = 1 ∧ v % 2 = 0) := by
      rcases Nat.mod_two_eq_zero_or_one u with hu2' | hu2' <;>
        rcases Nat.mod_two_eq_zero_or_one v with hv2' | hv2'
      · exfalso; exact Nat.prime_two.not_dvd_one (hcop_uv ▸ Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hu2') (Nat.dvd_of_mod_eq_zero hv2'))
      · left; exact ⟨hu2', hv2'⟩
      · right; exact ⟨hu2', hv2'⟩
      · exfalso; exact not_sum_sq_mod_four_two hu2' hv2' huv_c2
    have h_parity : ∀ x y : ℕ, x < y → (x + y) % 2 = 1 → (y ^ 2 - x ^ 2) % 2 = 1 := by
      intro x y hxy hsum
      have hle : x ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hxy.le 2
      have hadd : (y ^ 2 - x ^ 2) + x ^ 2 = y ^ 2 := Nat.sub_add_cancel hle
      have hxsq : x ^ 2 % 2 = x % 2 := by
        rw [Nat.pow_mod]
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
      have hysq : y ^ 2 % 2 = y % 2 := by
        rw [Nat.pow_mod]
        rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [h]
      have hmod := congrArg (· % 2) hadd
      rw [Nat.add_mod, hxsq, hysq] at hmod
      omega
    by_cases hgh2 : (h + g) % 2 = 1
    · left; exact h_parity h g hhg hgh2
    · by_cases hAB2 : (A + B) % 2 = 1
      · right; exact h_parity A B hAB hAB2
      · exfalso
        have hg_odd : g % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one g with hg2 | hg2
          · exfalso
            have hh2 : h % 2 = 0 := by omega
            exact Nat.prime_two.not_dvd_one
              (hcop_gh ▸ Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hg2) (Nat.dvd_of_mod_eq_zero hh2))
          · exact hg2
        have hh_odd : h % 2 = 1 := by omega
        have hA_odd : A % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one A with hA2 | hA2
          · exfalso
            have hB2 : B % 2 = 0 := by omega
            exact Nat.prime_two.not_dvd_one
              (hcop_AB ▸ Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hA2) (Nat.dvd_of_mod_eq_zero hB2))
          · exact hA2
        have hB_odd : B % 2 = 1 := by omega
        have hu1 : u % 2 = 1 := by rw [hu_gA, Nat.mul_mod, hg_odd, hA_odd]
        have hv1 : v % 2 = 1 := by rw [hh_eq, Nat.mul_mod, hB_odd, hh_odd]
        omega
  rcases hpar_gh_or_BA with hgh_odd | hBA_odd
  · have hcop1 : Nat.Coprime (g ^ 2 - h ^ 2) (2 * (g * h)) :=
      (Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).mul_right hcop_gh_diff
    have hd1 : g ^ 2 - h ^ 2 ∣ A * B := hcop1.dvd_of_dvd_mul_left ⟨B ^ 2 - A ^ 2, hkey.symm⟩
    have hd2 : A * B ∣ g ^ 2 - h ^ 2 :=
      hcop_BA_diff.symm.dvd_of_dvd_mul_left ⟨2 * (g * h), by
        calc (B ^ 2 - A ^ 2) * (g ^ 2 - h ^ 2) = (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) := by ring
          _ = 2 * (g * h) * (A * B) := hkey
          _ = A * B * (2 * (g * h)) := by ring⟩
    have h_eq1 : g ^ 2 - h ^ 2 = A * B := Nat.dvd_antisymm hd1 hd2
    have h_eq2 : B ^ 2 - A ^ 2 = 2 * (g * h) := by
      have : (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) = (g ^ 2 - h ^ 2) * (2 * (g * h)) := by
        calc (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) = 2 * (g * h) * (A * B) := hkey
          _ = 2 * (g * h) * (g ^ 2 - h ^ 2) := by rw [← h_eq1]
          _ = (g ^ 2 - h ^ 2) * (2 * (g * h)) := by ring
      exact Nat.mul_left_cancel (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hhg (by decide))) this
    have h2_sum : 2 ∣ B ^ 2 + A ^ 2 := by
      have hsub2 : 2 ∣ B ^ 2 - A ^ 2 := ⟨g * h, h_eq2⟩
      have hleBA : A ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left (le_of_lt hAB) 2
      have : B ^ 2 + A ^ 2 = (B ^ 2 - A ^ 2) + 2 * A ^ 2 := by omega
      rw [this]; exact Nat.dvd_add hsub2 (dvd_mul_right 2 _)
    set Z := (B ^ 2 + A ^ 2) / 2
    have hZ2 : 2 * Z = B ^ 2 + A ^ 2 := by omega
    have hbi : g ^ 4 + h ^ 4 = Z ^ 2 + g ^ 2 * h ^ 2 := by
      have h4 : 4 * (g ^ 4 + h ^ 4) = 4 * (Z ^ 2 + g ^ 2 * h ^ 2) := by
        zify [Nat.pow_le_pow_left (le_of_lt hhg) 2, Nat.pow_le_pow_left (le_of_lt hAB) 2]
          at h_eq1 h_eq2 hZ2 ⊢
        nlinarith only [h_eq1, h_eq2, hZ2]
      omega
    exact no_biquad_sub hhg hh_pos hcop_gh hbi
  · have hcop1 : Nat.Coprime (B ^ 2 - A ^ 2) (2 * (A * B)) :=
      (Nat.coprime_comm.mp (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).mul_right hcop_BA_diff
    have hd1 : B ^ 2 - A ^ 2 ∣ g * h :=
      hcop1.dvd_of_dvd_mul_left ⟨g ^ 2 - h ^ 2, by
        calc 2 * (A * B) * (g * h) = 2 * (g * h) * (A * B) := by ring
          _ = (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) := hkey.symm
          _ = (B ^ 2 - A ^ 2) * (g ^ 2 - h ^ 2) := by ring⟩
    have hd2 : g * h ∣ B ^ 2 - A ^ 2 :=
      hcop_gh_diff.symm.dvd_of_dvd_mul_left ⟨2 * (A * B), by
        calc (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) = 2 * (g * h) * (A * B) := hkey
          _ = g * h * (2 * (A * B)) := by ring⟩
    have h_eq1 : B ^ 2 - A ^ 2 = g * h := Nat.dvd_antisymm hd1 hd2
    have h_eq2 : g ^ 2 - h ^ 2 = 2 * (A * B) := by
      have : (B ^ 2 - A ^ 2) * (g ^ 2 - h ^ 2) = (B ^ 2 - A ^ 2) * (2 * (A * B)) := by
        calc (B ^ 2 - A ^ 2) * (g ^ 2 - h ^ 2) = (g ^ 2 - h ^ 2) * (B ^ 2 - A ^ 2) := by ring
          _ = 2 * (g * h) * (A * B) := hkey
          _ = 2 * (B ^ 2 - A ^ 2) * (A * B) := by rw [← h_eq1]
          _ = (B ^ 2 - A ^ 2) * (2 * (A * B)) := by ring
      exact Nat.mul_left_cancel (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hAB (by decide))) this
    have h2_sum : 2 ∣ g ^ 2 + h ^ 2 := by
      have hsub2 : 2 ∣ g ^ 2 - h ^ 2 := ⟨A * B, h_eq2⟩
      have hlegh : h ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left (le_of_lt hhg) 2
      have : g ^ 2 + h ^ 2 = (g ^ 2 - h ^ 2) + 2 * h ^ 2 := by omega
      rw [this]; exact Nat.dvd_add hsub2 (dvd_mul_right 2 _)
    set Z := (g ^ 2 + h ^ 2) / 2
    have hZ2 : 2 * Z = g ^ 2 + h ^ 2 := by omega
    have hbi : B ^ 4 + A ^ 4 = Z ^ 2 + B ^ 2 * A ^ 2 := by
      have h4 : 4 * (B ^ 4 + A ^ 4) = 4 * (Z ^ 2 + B ^ 2 * A ^ 2) := by
        zify [Nat.pow_le_pow_left (le_of_lt hAB) 2, Nat.pow_le_pow_left (le_of_lt hhg) 2]
          at h_eq1 h_eq2 hZ2 ⊢
        nlinarith only [h_eq1, h_eq2, hZ2]
      omega
    exact no_biquad_sub hAB hA_pos hcop_AB.symm hbi

private theorem sq_mod_three_ne_two (x : ℕ) : x ^ 2 % 3 ≠ 2 := by
  have hx : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rw [← Nat.div_add_mod x 3]
  rcases hx with h | h | h <;> rw [h] <;> ring_nf <;> omega

private theorem odd_sq_sub_odd_sq_mod_four {a b d : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hd : d % 2 = 1) (heq : a ^ 2 + 2 * d = b ^ 2) : False := by
  have ha4 : a ^ 2 % 4 = 1 := by rw [← Nat.div_add_mod a 2, ha]; ring_nf; omega
  have hb4 : b ^ 2 % 4 = 1 := by rw [← Nat.div_add_mod b 2, hb]; ring_nf; omega
  omega

private theorem ap_div3_split {n d u0 : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n d)
    (h3n : 3 ∣ n) (hAu : n * (n + 3 * d) = 2 * u0 ^ 2) :
    (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = 3 * a ^ 2 ∧ n + 3 * d = 6 * b ^ 2 ∧ Nat.Coprime a b) ∨
    (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n = 6 * a ^ 2 ∧ n + 3 * d = 3 * b ^ 2 ∧ Nat.Coprime b a) := by
  obtain ⟨n0, hn0_eq⟩ := h3n
  have hn0_pos : 0 < n0 := by omega
  have hcop_n0d : Nat.Coprime n0 (n0 + d) := by
    refine Nat.coprime_of_dvd' fun r _ hr1 hr2 => ?_
    have hrd : r ∣ d := (Nat.dvd_add_right hr1).mp hr2
    have hrn : r ∣ n := hn0_eq ▸ dvd_mul_of_dvd_right hr1 3
    exact hcop ▸ Nat.dvd_gcd hrn hrd
  have hA9 : 9 * (n0 * (n0 + d)) = 2 * u0 ^ 2 := by
    have : n * (n + 3 * d) = 9 * (n0 * (n0 + d)) := by rw [hn0_eq]; ring
    linarith only [hAu, this]
  have h3u0 : 3 ∣ u0 := by
    have : 3 ∣ 2 * u0 ^ 2 := ⟨3 * (n0 * (n0 + d)), by linarith only [hA9]⟩
    have h3sq : 3 ∣ u0 ^ 2 := (Nat.prime_three.coprime_iff_not_dvd.mpr (by decide)).dvd_of_dvd_mul_left this
    exact Nat.prime_three.dvd_of_dvd_pow h3sq
  obtain ⟨u1, hu1_eq⟩ := h3u0
  have hn0_eq_2u1 : n0 * (n0 + d) = 2 * u1 ^ 2 := by
    have h2 : 2 * u0 ^ 2 = 9 * (2 * u1 ^ 2) := by rw [hu1_eq]; ring
    linarith only [hA9, h2]
  rcases nat_coprime_mul_eq_prime_mul_sq Nat.prime_two hcop_n0d hn0_eq_2u1 with
      ⟨a, b, ha_eq, hb_eq⟩ | ⟨a, b, ha_eq, hb_eq⟩
  · have ha_pos : 0 < a := by nlinarith only [hn0_pos, ha_eq]
    have hb_pos : 0 < b := by nlinarith only [hn0_pos, hb_eq]
    have hcop_ba : Nat.Coprime b a := by
      refine Nat.coprime_of_dvd' fun r _ hrb hra => ?_
      have h1 : r ∣ n0 := ha_eq ▸ dvd_mul_of_dvd_right (dvd_pow hra (by decide)) 2
      have h2 : r ∣ n0 + d := hb_eq ▸ dvd_pow hrb (by decide)
      exact hcop_n0d ▸ Nat.dvd_gcd h1 h2
    refine Or.inr ⟨a, b, ha_pos, hb_pos, ?_, ?_, hcop_ba⟩
    · rw [hn0_eq, ha_eq]; ring
    · rw [hn0_eq, show 3 * n0 + 3 * d = 3 * (n0 + d) by ring, hb_eq]
  · have ha_pos : 0 < a := by nlinarith only [hn0_pos, ha_eq]
    have hb_pos : 0 < b := by nlinarith only [hn0_pos, hb_eq]
    have hcop_ab : Nat.Coprime a b := by
      refine Nat.coprime_of_dvd' fun r _ hra hrb => ?_
      have h1 : r ∣ n0 := ha_eq ▸ dvd_pow hra (by decide)
      have h2 : r ∣ n0 + d := hb_eq ▸ dvd_mul_of_dvd_right (dvd_pow hrb (by decide)) 2
      exact hcop_n0d ▸ Nat.dvd_gcd h1 h2
    refine Or.inl ⟨a, b, ha_pos, hb_pos, ?_, ?_, hcop_ab⟩
    · rw [hn0_eq, ha_eq]
    · rw [hn0_eq, show 3 * n0 + 3 * d = 3 * (n0 + d) by ring, hb_eq]; ring

private theorem ap_not3_coprime {n d : ℕ} (hcop : Nat.Coprime n d) (h3n : ¬ 3 ∣ n) :
    Nat.Coprime n (n + 3 * d) := by
  refine Nat.coprime_of_dvd' fun r hr hrn hrn3d => ?_
  have hr3d : r ∣ 3 * d := (Nat.dvd_add_right hrn).mp hrn3d
  rcases hr.dvd_mul.mp hr3d with hr3 | hrd
  · exfalso
    have : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp hr3
    exact h3n (this ▸ hrn)
  · exact hcop ▸ Nat.dvd_gcd hrn hrd

/-- Euler's Theorem: No four positive integers in coprime AP have a square product. -/
private theorem no_prod_four_ap_sq {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime n d) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) ≠ q ^ 2 := by
  intro heq
  set A := n * (n + 3 * d)
  set B := (n + d) * (n + 2 * d)
  have hAB_eq : A * B = q ^ 2 := by
    calc A * B = n * (n + d) * (n + 2 * d) * (n + 3 * d) := by dsimp [A, B]; ring
      _ = q ^ 2 := heq
  have hcop_n_d1 : Nat.Coprime n (n + d) := by
    refine Nat.coprime_of_dvd' fun r _ hrn hrnd => ?_
    exact hcop ▸ Nat.dvd_gcd hrn ((Nat.dvd_add_right hrn).mp hrnd)
  have hcop_12 : Nat.Coprime (n + d) (n + 2 * d) := by
    refine Nat.coprime_of_dvd' fun r _ hr1 hr2 => ?_
    have hrd : r ∣ d := (Nat.dvd_add_right hr1).mp (show r ∣ (n + d) + d by
      have : (n + d) + d = n + 2 * d := by ring
      rwa [this])
    exact hcop ▸ Nat.dvd_gcd ((Nat.dvd_add_left hrd).mp hr1) hrd
  have hcop_Ad : Nat.Coprime A d := by
    refine Nat.Coprime.mul_left hcop ?_
    refine Nat.coprime_of_dvd' fun r _ hrn3d hrd => ?_
    exact hcop ▸ Nat.dvd_gcd ((Nat.dvd_add_left (dvd_mul_of_dvd_right hrd 3)).mp hrn3d) hrd
  have hB_eq : B = A + 2 * d ^ 2 := by dsimp [A, B]; ring
  have hgcd_AB_dvd_2 : Nat.gcd A B ∣ 2 := by
    have hg2d2 : Nat.gcd A B ∣ 2 * d ^ 2 := by
      have hgB : Nat.gcd A B ∣ A + 2 * d ^ 2 := hB_eq ▸ Nat.gcd_dvd_right A B
      exact (Nat.dvd_add_right (Nat.gcd_dvd_left A B)).mp hgB
    exact ((hcop_Ad.coprime_dvd_left (Nat.gcd_dvd_left A B)).pow_right 2).dvd_of_dvd_mul_right hg2d2
  by_cases hd2 : 2 ∣ d
  · have hn_odd : ¬ 2 ∣ n := fun h2n => Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd h2n hd2)
    have hA_odd : ¬ 2 ∣ A := by
      intro h2A
      rcases Nat.prime_two.dvd_mul.mp h2A with h2n | h2n3
      · exact hn_odd h2n
      · exact hn_odd ((Nat.dvd_add_left (dvd_mul_of_dvd_right hd2 3)).mp h2n3)
    have hcop_AB : Nat.Coprime A B := by
      refine Nat.coprime_of_dvd' fun r hr hrA hrB => ?_
      exfalso
      have hr2 : r ∣ 2 := dvd_trans (Nat.dvd_gcd hrA hrB) hgcd_AB_dvd_2
      have hreq2 : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hr2
      exact hA_odd (hreq2 ▸ hrA)
    obtain ⟨u, v, hu_sq, hv_sq⟩ := nat_coprime_mul_eq_sq hcop_AB hAB_eq
    obtain ⟨c, e, hce1, hce2⟩ := nat_coprime_mul_eq_sq hcop_12 hv_sq
    by_cases h3n : 3 ∣ n
    · have h3nd : ¬ 3 ∣ d := fun h3d => Nat.prime_three.not_dvd_one (hcop ▸ Nat.dvd_gcd h3n h3d)
      rcases (by omega : d % 3 = 1 ∨ d % 3 = 2) with hd3 | hd3
      · exact sq_mod_three_ne_two e (by rw [← hce2]; omega)
      · exact sq_mod_three_ne_two c (by rw [← hce1]; omega)
    · obtain ⟨a, b, ha_sq, hb_sq⟩ := nat_coprime_mul_eq_sq (ap_not3_coprime hcop h3n) hu_sq
      have ha_pos : 0 < a := by nlinarith only [hn, ha_sq]
      have hac : a < c := by nlinarith only [ha_sq, hce1, hd]
      have hce : c < e := by nlinarith only [hce1, hce2, hd]
      have heb : e < b := by nlinarith only [hce2, hb_sq, hd]
      have hcop_ac : Nat.Coprime a c := by
        refine Nat.coprime_of_dvd' fun r _ hra hrc => ?_
        exact hcop_n_d1 ▸ Nat.dvd_gcd (ha_sq ▸ dvd_pow hra (by decide))
          (hce1 ▸ dvd_pow hrc (by decide))
      exact no_four_sq_ap ha_pos hac hce heb hcop_ac
        (by linarith only [ha_sq, hce1, hce2]) (by linarith only [hce1, hce2, hb_sq])
  · have hd_odd : d % 2 = 1 := by omega
    have h2A : 2 ∣ A := by
      dsimp [A]
      rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2
      · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero hn2) _
      · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
    have h2B : 2 ∣ B := by rw [hB_eq]; exact Nat.dvd_add h2A ⟨d ^ 2, rfl⟩
    have hgcd_AB : Nat.gcd A B = 2 := Nat.dvd_antisymm hgcd_AB_dvd_2 (Nat.dvd_gcd h2A h2B)
    obtain ⟨A', hA'⟩ := h2A
    obtain ⟨B', hB'⟩ := h2B
    have hcop_A'B' : Nat.Coprime A' B' := by
      have := Nat.coprime_div_gcd_div_gcd (by omega : 0 < Nat.gcd A B)
      rwa [hgcd_AB, show A / 2 = A' by omega, show B / 2 = B' by omega] at this
    obtain ⟨q', hq'⟩ := Nat.prime_two.dvd_of_dvd_pow (⟨2 * (A' * B'), by
      calc q ^ 2 = A * B := hAB_eq.symm
        _ = (2 * A') * (2 * B') := by rw [hA', hB']
        _ = 2 * (2 * (A' * B')) := by ring⟩ : 2 ∣ q ^ 2)
    have hA'B'_sq : A' * B' = q' ^ 2 := by
      have h4 : 4 * (A' * B') = 4 * q' ^ 2 := by nlinarith only [hAB_eq, hA', hB', hq']
      omega
    obtain ⟨u0, v0, hu0_sq, hv0_sq⟩ := nat_coprime_mul_eq_sq hcop_A'B' hA'B'_sq
    have hAu : n * (n + 3 * d) = 2 * u0 ^ 2 := by rw [← show A = n * (n + 3 * d) from rfl, hA', hu0_sq]
    have hBv : (n + d) * (n + 2 * d) = 2 * v0 ^ 2 := by rw [← show B = (n + d) * (n + 2 * d) from rfl, hB', hv0_sq]
    rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2
    · obtain ⟨c, e, hc_pos, he_pos, hcd_eq, he_eq⟩ :
          ∃ c e : ℕ, 0 < c ∧ 0 < e ∧ n + d = c ^ 2 ∧ n + 2 * d = 2 * e ^ 2 := by
        rcases nat_coprime_mul_eq_prime_mul_sq Nat.prime_two hcop_12 hBv with
            ⟨c, e, hc_eq, he_eq⟩ | ⟨c, e, hc_eq, he_eq⟩
        · exfalso; have : 2 ∣ n + d := hc_eq ▸ dvd_mul_right 2 _; omega
        · exact ⟨c, e, by nlinarith only [hn, hc_eq], by nlinarith only [hn, he_eq], hc_eq, he_eq⟩
      by_cases h3n : 3 ∣ n
      · rcases ap_div3_split hn hcop h3n hAu with
            ⟨a, b, _, _, _, hnb, _⟩ | ⟨a, b, ha_pos, hb_pos, hna, hnb, hcop_ba⟩
        · exfalso
          have : 2 ∣ n + 3 * d := hnb ▸ dvd_mul_of_dvd_left (by decide : 2 ∣ 6) (b ^ 2)
          omega
        · have h1 : b ^ 2 + a ^ 2 = e ^ 2 := by linarith only [hna, hnb, he_eq]
          have h2 : b ^ 2 + 4 * a ^ 2 = c ^ 2 := by linarith only [hna, hnb, hcd_eq]
          exact no_sim_pyth (e + c) b a e c hb_pos ha_pos he_pos hc_pos rfl hcop_ba h1 h2
      · rcases nat_coprime_mul_eq_prime_mul_sq Nat.prime_two (ap_not3_coprime hcop h3n) hAu with
            ⟨a, b, _, hb_eq⟩ | ⟨a, b, _, hb_eq⟩
        · have hc_odd : c % 2 = 1 := by
            by_contra hc2; have : 2 ∣ c ^ 2 := dvd_pow (by omega : 2 ∣ c) (by decide)
            rw [← hcd_eq] at this; omega
          have hb_odd : b % 2 = 1 := by
            by_contra hb2; have : 2 ∣ b ^ 2 := dvd_pow (by omega : 2 ∣ b) (by decide)
            rw [← hb_eq] at this; omega
          exact odd_sq_sub_odd_sq_mod_four hc_odd hb_odd hd_odd (by linarith only [hcd_eq, hb_eq])
        · exfalso; have : 2 ∣ n + 3 * d := hb_eq ▸ dvd_mul_right 2 _; omega
    · obtain ⟨c, e, hc_pos, he_pos, hcd_eq, he_eq⟩ :
          ∃ c e : ℕ, 0 < c ∧ 0 < e ∧ n + d = 2 * c ^ 2 ∧ n + 2 * d = e ^ 2 := by
        rcases nat_coprime_mul_eq_prime_mul_sq Nat.prime_two hcop_12 hBv with
            ⟨c, e, hc_eq, he_eq⟩ | ⟨c, e, _, he_eq⟩
        · exact ⟨c, e, by nlinarith only [hn, hc_eq], by nlinarith only [hn, he_eq], hc_eq, he_eq⟩
        · exfalso; have : 2 ∣ n + 2 * d := he_eq ▸ dvd_mul_right 2 _; omega
      by_cases h3n : 3 ∣ n
      · rcases ap_div3_split hn hcop h3n hAu with
            ⟨a, b, ha_pos, hb_pos, hna, hnb, hcop_ab⟩ | ⟨a, b, _, _, hna, _, _⟩
        · have h1 : a ^ 2 + b ^ 2 = c ^ 2 := by linarith only [hna, hnb, hcd_eq]
          have h2 : a ^ 2 + 4 * b ^ 2 = e ^ 2 := by linarith only [hna, hnb, he_eq]
          exact no_sim_pyth (c + e) a b c e ha_pos hb_pos hc_pos he_pos rfl hcop_ab h1 h2
        · exfalso
          have : 2 ∣ n := hna ▸ dvd_mul_of_dvd_left (by decide : 2 ∣ 6) (a ^ 2)
          omega
      · rcases nat_coprime_mul_eq_prime_mul_sq Nat.prime_two (ap_not3_coprime hcop h3n) hAu with
            ⟨a, b, ha_eq, _⟩ | ⟨a, b, ha_eq, _⟩
        · exfalso; have : 2 ∣ n := ha_eq ▸ dvd_mul_right 2 _; omega
        · have ha_odd : a % 2 = 1 := by
            by_contra ha2; have : 2 ∣ a ^ 2 := dvd_pow (by omega : 2 ∣ a) (by decide)
            rw [← ha_eq] at this; omega
          have he_odd : e % 2 = 1 := by
            by_contra he2; have : 2 ∣ e ^ 2 := dvd_pow (by omega : 2 ∣ e) (by decide)
            rw [← he_eq] at this; omega
          exact odd_sq_sub_odd_sq_mod_four ha_odd he_odd hd_odd (by linarith only [ha_eq, he_eq])

/-- For `Nat.Coprime n d` and `i < j`, `Nat.gcd (n + i * d) (n + j * d)` divides `j - i`,
independent of `n` and `d`. -/
private theorem ap_pairwise_gcd_dvd {n d i j : ℕ} (hcop : Nat.Coprime n d) (hij : i < j) :
    Nat.gcd (n + i * d) (n + j * d) ∣ (j - i) := by
  set g := Nat.gcd (n + i * d) (n + j * d)
  have hgi : g ∣ n + i * d := Nat.gcd_dvd_left _ _
  have hgj : g ∣ n + j * d := Nat.gcd_dvd_right _ _
  have hdiff : n + j * d = (n + i * d) + (j - i) * d := by
    have hle : i ≤ j := Nat.le_of_lt hij
    calc
      n + j * d = n + (i + (j - i)) * d := by rw [Nat.add_sub_cancel' hle]
      _ = (n + i * d) + (j - i) * d := by ring
  have hgd : g ∣ (j - i) * d := by
    rw [hdiff] at hgj
    exact (Nat.dvd_add_right hgi).mp hgj
  have hcop_gd : Nat.Coprime g d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hc_n : Nat.gcd g d ∣ n :=
      (Nat.dvd_add_left (dvd_mul_of_dvd_right (Nat.gcd_dvd_right g d) i)).mp
        (dvd_trans (Nat.gcd_dvd_left g d) hgi)
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hc_n (Nat.gcd_dvd_right g d))
  exact hcop_gd.dvd_of_dvd_mul_right hgd

/-- Any prime `p ≥ k` divides at most one term among `n + 0*d, ..., n + (k-1)*d`. -/
private theorem ap_prime_unique_term {n d k p i j : ℕ} (hcop : Nat.Coprime n d) (hp : p.Prime)
    (hpk : k ≤ p) (hi : i < k) (hj : j < k)
    (hpi : p ∣ n + i * d) (hpj : p ∣ n + j * d) : i = j := by
  have _ := hp.pos
  by_contra hne
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · have hpd : p ∣ j - i :=
      dvd_trans (Nat.dvd_gcd hpi hpj) (ap_pairwise_gcd_dvd hcop hij)
    have hle : p ≤ j - i := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hpd
    omega
  · exact hne rfl
  · have hpd : p ∣ i - j :=
      dvd_trans (Nat.dvd_gcd hpj hpi) (ap_pairwise_gcd_dvd hcop hji)
    have hle : p ≤ i - j := Nat.le_of_dvd (Nat.sub_pos_of_lt hji) hpd
    omega

private theorem padicValNat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    {p : ℕ} [Fact p.Prime] (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ x ∈ s, f x ≠ 0 := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have hprod0 : ∏ x ∈ s, f x ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul ha0 hprod0, ih hs0]

/-- If `∏_{j < k} (n + j * d) = q ^ l` with `Nat.Coprime n d` and `n > 0`, then for every
prime `p ≥ k` and every `i < k`, `l ∣ padicValNat p (n + i * d)`. -/
private theorem ap_padicValNat_dvd_of_prod_eq_pow {n d k l q p i : ℕ}
    (hn : 0 < n) (hcop : Nat.Coprime n d) (hp : p.Prime) (hpk : k ≤ p) (hi : i < k)
    (hprod : ∏ j ∈ Finset.range k, (n + j * d) = q ^ l) :
    l ∣ padicValNat p (n + i * d) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hdiv : p ∣ n + i * d
  · have hne : ∀ j ∈ Finset.range k, n + j * d ≠ 0 := fun j _ => by omega
    have hsum : ∑ j ∈ Finset.range k, padicValNat p (n + j * d) = padicValNat p (n + i * d) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j hj hji
        have hjlt : j < k := Finset.mem_range.mp hj
        have hnot : ¬ p ∣ n + j * d := by
          intro hdj
          exact hji (ap_prime_unique_term hcop hp hpk hjlt hi hdj hdiv)
        exact padicValNat.eq_zero_of_not_dvd hnot
      · intro hi_mem
        exact absurd (Finset.mem_range.mpr hi) hi_mem
    have hpow : padicValNat p (∏ j ∈ Finset.range k, (n + j * d)) = l * padicValNat p q := by
      rw [hprod, padicValNat.pow]
    rw [padicValNat_finset_prod (Finset.range k) (fun j => n + j * d) hne, hsum] at hpow
    exact ⟨padicValNat p q, hpow⟩
  · rw [padicValNat.eq_zero_of_not_dvd hdiv]
    exact dvd_zero l



theorem ap5_sq_splitting {n d q i : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n d)
    (hi : i < 5) (hprod : ∏ j ∈ Finset.range 5, (n + j * d) = q ^ 2) :
    ∃ a x : ℕ, 0 < x ∧ a ∈ ([1, 2, 3, 6] : List ℕ) ∧ n + i * d = a * x ^ 2 := by
  classical
  set m := n + i * d
  have hm0 : m ≠ 0 := by omega
  set a := 2 ^ (m.factorization 2 % 2) * 3 ^ (m.factorization 3 % 2)
  set x := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)
  have hx_pos : 0 < x :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have ha_mem : a ∈ ([1, 2, 3, 6] : List ℕ) := by
    rcases Nat.mod_two_eq_zero_or_one (m.factorization 2) with h2 | h2 <;>
      rcases Nat.mod_two_eq_zero_or_one (m.factorization 3) with h3 | h3 <;>
      simp [a, h2, h3]
  have ha_prod : ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 2) = a := by
    let f : ℕ → ℕ := fun p => p ^ (m.factorization p % 2)
    change ∏ p ∈ m.primeFactors, f p = a
    have h1 : ∏ p ∈ m.primeFactors, f p = ∏ p ∈ m.primeFactors ∩ ({2, 3} : Finset ℕ), f p := by
      symm
      refine Finset.prod_subset Finset.inter_subset_left fun p hp_mem hp_not => ?_
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hp_n23 : p ∉ ({2, 3} : Finset ℕ) :=
        fun hmem => hp_not (Finset.mem_inter.mpr ⟨hp_mem, hmem⟩)
      have hp2 : p ≠ 2 := fun h => hp_n23 (by simp [h])
      have hp3 : p ≠ 3 := fun h => hp_n23 (by simp [h])
      have hp4 : p ≠ 4 := fun h => by rw [h] at hp; exact (by decide : ¬Nat.Prime 4) hp
      have hpk : 5 ≤ p := by have := hp.two_le; omega
      have hdvd : 2 ∣ padicValNat p m :=
        ap_padicValNat_dvd_of_prod_eq_pow hn hcop hp hpk hi hprod
      have hmod : m.factorization p % 2 = 0 := by
        rw [Nat.factorization_def m hp]
        exact Nat.mod_eq_zero_of_dvd hdvd
      simp [f, hmod]
    have h2 : ∏ p ∈ m.primeFactors ∩ ({2, 3} : Finset ℕ), f p = ∏ p ∈ ({2, 3} : Finset ℕ), f p := by
      refine Finset.prod_subset Finset.inter_subset_right fun p hp_23 hp_not => ?_
      have hp_nm : p ∉ m.primeFactors := fun hmem => hp_not (Finset.mem_inter.mpr ⟨hmem, hp_23⟩)
      have hzero : m.factorization p = 0 := by
        by_contra hne
        exact hp_nm (Nat.support_factorization m ▸ Finsupp.mem_support_iff.mpr hne)
      simp [f, hzero]
    have h3 : ∏ p ∈ ({2, 3} : Finset ℕ), f p = a := by
      rw [Finset.prod_pair (by decide : (2 : ℕ) ≠ 3)]
    exact h1.trans (h2.trans h3)
  have hm_eq : n + i * d = a * x ^ 2 := by
    calc n + i * d = m := rfl
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p) :=
        Nat.prod_primeFactors_pow_factorization hm0
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 2 + 2 * (m.factorization p / 2)) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Nat.mod_add_div]
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 2) * (p ^ (m.factorization p / 2)) ^ 2 := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [pow_add, mul_comm 2 (m.factorization p / 2), pow_mul]
      _ = (∏ p ∈ m.primeFactors, p ^ (m.factorization p % 2)) *
            (∏ p ∈ m.primeFactors, (p ^ (m.factorization p / 2)) ^ 2) :=
        Finset.prod_mul_distrib
      _ = a * x ^ 2 := by rw [ha_prod, Finset.prod_pow]
  exact ⟨a, x, hx_pos, ha_mem, hm_eq⟩

private def anyLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | k + 1, f => f k || anyLt k f

private theorem anyLt_sound {k : ℕ} {f : ℕ → Bool} {i : ℕ} (hi : i < k) (hfi : f i = true) :
    anyLt k f = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [anyLt, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · right; exact ih hlt
    · left; exact hfi

private def res8Fast (a r : ℕ) : Bool :=
  if a == 1 then (r == 0 || r == 1 || r == 4)
  else if a == 2 then (r == 0 || r == 2)
  else if a == 3 then (r == 0 || r == 3 || r == 4)
  else (r == 0 || r == 6)

private theorem res8Fast_sound {a x : ℕ} (ha : a ∈ ([1, 2, 3, 6] : List ℕ)) :
    res8Fast a ((a * x ^ 2) % 8) = true := by
  have hmod : (a * x ^ 2) % 8 = (a * ((x % 8) * (x % 8))) % 8 := by
    simp [sq, Nat.mul_mod]
  rw [hmod]
  set rx := x % 8
  have hrx : rx < 8 := Nat.mod_lt x (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    · rcases (by omega : rx = 0 ∨ rx = 1 ∨ rx = 2 ∨ rx = 3 ∨ rx = 4 ∨ rx = 5 ∨ rx = 6 ∨ rx = 7)
        with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

private def res9Fast (a r : ℕ) : Bool :=
  if a == 1 then (r == 0 || r == 1 || r == 4 || r == 7)
  else if a == 2 then (r == 0 || r == 2 || r == 5 || r == 8)
  else if a == 3 then (r == 0 || r == 3)
  else (r == 0 || r == 6)

private theorem res9Fast_sound {a x : ℕ} (ha : a ∈ ([1, 2, 3, 6] : List ℕ)) :
    res9Fast a ((a * x ^ 2) % 9) = true := by
  have hmod : (a * x ^ 2) % 9 = (a * ((x % 9) * (x % 9))) % 9 := by
    simp [sq, Nat.mul_mod]
  rw [hmod]
  set rx := x % 9
  have hrx : rx < 9 := Nat.mod_lt x (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    · rcases (by omega : rx = 0 ∨ rx = 1 ∨ rx = 2 ∨ rx = 3 ∨ rx = 4 ∨ rx = 5 ∨ rx = 6 ∨ rx = 7 ∨ rx = 8)
        with h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

private def ok8Fast (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  anyLt 8 fun n => anyLt 8 fun d =>
    (n % 2 == 1 || d % 2 == 1) &&
    res8Fast a0 (n % 8) && res8Fast a1 ((n + d) % 8) &&
    res8Fast a2 ((n + 2 * d) % 8) && res8Fast a3 ((n + 3 * d) % 8) &&
    res8Fast a4 ((n + 4 * d) % 8)

private def ok9Fast (a0 a1 a2 a3 a4 : ℕ) : Bool :=
  anyLt 9 fun n => anyLt 9 fun d =>
    (!(n % 3 == 0 && d % 3 == 0)) &&
    res9Fast a0 (n % 9) && res9Fast a1 ((n + d) % 9) &&
    res9Fast a2 ((n + 2 * d) % 9) && res9Fast a3 ((n + 3 * d) % 9) &&
    res9Fast a4 ((n + 4 * d) % 9)

private def isSq89 (p : ℕ) : Bool := anyLt 89 (fun s => s * s == p)

private def checkAll5 : Bool :=
  let vals : List ℕ := [1, 2, 3, 6]
  vals.all fun a0 => vals.all fun a1 => vals.all fun a2 => vals.all fun a3 => vals.all fun a4 =>
    !(isSq89 (a0 * a1 * a2 * a3 * a4) && ok8Fast a0 a1 a2 a3 a4 && ok9Fast a0 a1 a2 a3 a4) ||
    ((a0 == 1 && a1 == 1 && a2 == 1 && a3 == 1 && a4 == 1) ||
     (a0 == 6 && a1 == 1 && a2 == 2 && a3 == 3 && a4 == 1) ||
     (a0 == 1 && a1 == 3 && a2 == 2 && a3 == 1 && a4 == 6))

private theorem checkAll5_true : checkAll5 = true := by decide

private theorem ok8Fast_sound {n d a0 a1 a2 a3 a4 x0 x1 x2 x3 x4 : ℕ}
    (hcop : Nat.Coprime n d)
    (ha0 : a0 ∈ ([1, 2, 3, 6] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 3, 6] : List ℕ)) (ha3 : a3 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha4 : a4 ∈ ([1, 2, 3, 6] : List ℕ))
    (h0 : n = a0 * x0 ^ 2) (h1 : n + d = a1 * x1 ^ 2) (h2 : n + 2 * d = a2 * x2 ^ 2)
    (h3 : n + 3 * d = a3 * x3 ^ 2) (h4 : n + 4 * d = a4 * x4 ^ 2) :
    ok8Fast a0 a1 a2 a3 a4 = true := by
  refine anyLt_sound (Nat.mod_lt n (by decide)) ?_
  refine anyLt_sound (Nat.mod_lt d (by decide)) ?_
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  have hpar : (n % 8) % 2 = 1 ∨ (d % 8) % 2 = 1 := by
    by_contra hboth
    have hn2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have hd2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
    exact Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd hn2 hd2)
  have r0 : res8Fast a0 ((n % 8) % 8) = true := by
    rw [Nat.mod_mod, h0]; exact res8Fast_sound ha0
  have r1 : res8Fast a1 ((n % 8 + d % 8) % 8) = true := by
    have : (n % 8 + d % 8) % 8 = (n + d) % 8 := by simp [Nat.add_mod]
    rw [this, h1]; exact res8Fast_sound ha1
  have r2 : res8Fast a2 ((n % 8 + 2 * (d % 8)) % 8) = true := by
    have : (n % 8 + 2 * (d % 8)) % 8 = (n + 2 * d) % 8 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h2]; exact res8Fast_sound ha2
  have r3 : res8Fast a3 ((n % 8 + 3 * (d % 8)) % 8) = true := by
    have : (n % 8 + 3 * (d % 8)) % 8 = (n + 3 * d) % 8 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h3]; exact res8Fast_sound ha3
  have r4 : res8Fast a4 ((n % 8 + 4 * (d % 8)) % 8) = true := by
    have : (n % 8 + 4 * (d % 8)) % 8 = (n + 4 * d) % 8 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h4]; exact res8Fast_sound ha4
  exact ⟨⟨⟨⟨⟨hpar, r0⟩, r1⟩, r2⟩, r3⟩, r4⟩

private theorem ok9Fast_sound {n d a0 a1 a2 a3 a4 x0 x1 x2 x3 x4 : ℕ}
    (hcop : Nat.Coprime n d)
    (ha0 : a0 ∈ ([1, 2, 3, 6] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 3, 6] : List ℕ)) (ha3 : a3 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha4 : a4 ∈ ([1, 2, 3, 6] : List ℕ))
    (h0 : n = a0 * x0 ^ 2) (h1 : n + d = a1 * x1 ^ 2) (h2 : n + 2 * d = a2 * x2 ^ 2)
    (h3 : n + 3 * d = a3 * x3 ^ 2) (h4 : n + 4 * d = a4 * x4 ^ 2) :
    ok9Fast a0 a1 a2 a3 a4 = true := by
  refine anyLt_sound (Nat.mod_lt n (by decide)) ?_
  refine anyLt_sound (Nat.mod_lt d (by decide)) ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  have hmod3 : n % 3 ≠ 0 ∨ d % 3 ≠ 0 := by
    by_contra hboth
    rcases not_or.mp hboth with ⟨hn0, hd0⟩
    have hn3 : 3 ∣ n := Nat.dvd_of_mod_eq_zero (not_not.mp hn0)
    have hd3 : 3 ∣ d := Nat.dvd_of_mod_eq_zero (not_not.mp hd0)
    exact Nat.prime_three.not_dvd_one (hcop ▸ Nat.dvd_gcd hn3 hd3)
  have r0 : res9Fast a0 ((n % 9) % 9) = true := by
    rw [Nat.mod_mod, h0]; exact res9Fast_sound ha0
  have r1 : res9Fast a1 ((n % 9 + d % 9) % 9) = true := by
    have : (n % 9 + d % 9) % 9 = (n + d) % 9 := by simp [Nat.add_mod]
    rw [this, h1]; exact res9Fast_sound ha1
  have r2 : res9Fast a2 ((n % 9 + 2 * (d % 9)) % 9) = true := by
    have : (n % 9 + 2 * (d % 9)) % 9 = (n + 2 * d) % 9 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h2]; exact res9Fast_sound ha2
  have r3 : res9Fast a3 ((n % 9 + 3 * (d % 9)) % 9) = true := by
    have : (n % 9 + 3 * (d % 9)) % 9 = (n + 3 * d) % 9 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h3]; exact res9Fast_sound ha3
  have r4 : res9Fast a4 ((n % 9 + 4 * (d % 9)) % 9) = true := by
    have : (n % 9 + 4 * (d % 9)) % 9 = (n + 4 * d) % 9 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h4]; exact res9Fast_sound ha4
  refine ⟨⟨⟨⟨⟨?_, r0⟩, r1⟩, r2⟩, r3⟩, r4⟩
  rcases hmod3 with h | h
  · left; simpa [Nat.mod_mod_of_dvd n (by decide : 3 ∣ 9)] using h
  · right; simpa [Nat.mod_mod_of_dvd d (by decide : 3 ∣ 9)] using h

private theorem le_six_of_mem {a : ℕ} (ha : a ∈ ([1, 2, 3, 6] : List ℕ)) : a ≤ 6 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  omega

private theorem isSq89_sound {a0 a1 a2 a3 a4 X q : ℕ}
    (ha0 : a0 ∈ ([1, 2, 3, 6] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 3, 6] : List ℕ)) (ha3 : a3 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha4 : a4 ∈ ([1, 2, 3, 6] : List ℕ))
    (hX : 0 < X) (hprod : (a0 * a1 * a2 * a3 * a4) * X ^ 2 = q ^ 2) :
    isSq89 (a0 * a1 * a2 * a3 * a4) = true := by
  have hdvd_sq : X ^ 2 ∣ q ^ 2 := ⟨a0 * a1 * a2 * a3 * a4, by
    calc q ^ 2 = (a0 * a1 * a2 * a3 * a4) * X ^ 2 := hprod.symm
      _ = X ^ 2 * (a0 * a1 * a2 * a3 * a4) := by ring⟩
  have hX_dvd_q : X ∣ q :=
    Int.natCast_dvd_natCast.mp ((Int.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
      (Int.natCast_dvd_natCast.mpr hdvd_sq))
  obtain ⟨s, hs⟩ := hX_dvd_q
  have hs_sq : a0 * a1 * a2 * a3 * a4 = s ^ 2 := by
    have hX2 : 0 < X ^ 2 := Nat.pow_pos hX
    have heq : X ^ 2 * (a0 * a1 * a2 * a3 * a4) = X ^ 2 * s ^ 2 := by
      calc X ^ 2 * (a0 * a1 * a2 * a3 * a4) = (a0 * a1 * a2 * a3 * a4) * X ^ 2 := by ring
        _ = q ^ 2 := hprod
        _ = (X * s) ^ 2 := by rw [hs]
        _ = X ^ 2 * s ^ 2 := by ring
    exact Nat.mul_left_cancel hX2 heq
  have hle0 := le_six_of_mem ha0
  have hle1 := le_six_of_mem ha1
  have hle2 := le_six_of_mem ha2
  have hle3 := le_six_of_mem ha3
  have hle4 := le_six_of_mem ha4
  have h01234 : a0 * a1 * a2 * a3 * a4 ≤ 36 * 36 * 6 := by
    have h01 : a0 * a1 ≤ 36 := Nat.mul_le_mul hle0 hle1
    have h23 : a2 * a3 ≤ 36 := Nat.mul_le_mul hle2 hle3
    have h0123 : a0 * a1 * a2 * a3 ≤ 36 * 36 := by
      calc a0 * a1 * a2 * a3 = (a0 * a1) * (a2 * a3) := by ring
        _ ≤ 36 * 36 := Nat.mul_le_mul h01 h23
    exact Nat.mul_le_mul h0123 hle4
  have hsq_lt : s ^ 2 < 89 * 89 := by linarith only [hs_sq, h01234]
  have hs_lt : s < 89 := by nlinarith only [hsq_lt]
  refine anyLt_sound hs_lt ?_
  simp [hs_sq, sq]

private theorem checkAll5_elim {a0 a1 a2 a3 a4 : ℕ}
    (ha0 : a0 ∈ ([1, 2, 3, 6] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 3, 6] : List ℕ)) (ha3 : a3 ∈ ([1, 2, 3, 6] : List ℕ))
    (ha4 : a4 ∈ ([1, 2, 3, 6] : List ℕ))
    (hsq : isSq89 (a0 * a1 * a2 * a3 * a4) = true)
    (hok8 : ok8Fast a0 a1 a2 a3 a4 = true)
    (hok9 : ok9Fast a0 a1 a2 a3 a4 = true) :
    (a0 = 1 ∧ a1 = 1 ∧ a2 = 1 ∧ a3 = 1 ∧ a4 = 1) ∨
    (a0 = 6 ∧ a1 = 1 ∧ a2 = 2 ∧ a3 = 3 ∧ a4 = 1) ∨
    (a0 = 1 ∧ a1 = 3 ∧ a2 = 2 ∧ a3 = 1 ∧ a4 = 6) := by
  have hc := checkAll5_true
  simp only [checkAll5, List.all_eq_true] at hc
  have hrow := hc a0 ha0 a1 ha1 a2 ha2 a3 ha3 a4 ha4
  simpa [hsq, hok8, hok9, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc, or_assoc] using hrow

/-- Obláth's theorem: no five positive integers in coprime arithmetic progression
have a perfect square product. -/
theorem no_prod_five_ap_sq {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime n d) :
    n * (n + d) * (n + 2 * d) * (n + 3 * d) * (n + 4 * d) ≠ q ^ 2 := by
  intro heq
  have hprod : ∏ j ∈ Finset.range 5, (n + j * d) = q ^ 2 := by
    calc ∏ j ∈ Finset.range 5, (n + j * d)
        = n * (n + d) * (n + 2 * d) * (n + 3 * d) * (n + 4 * d) := by
          simp [Finset.prod_range_succ, mul_assoc]
      _ = q ^ 2 := heq
  obtain ⟨a0, x0, hx0, ha0, h0⟩ := ap5_sq_splitting hn hcop (by decide : 0 < 5) hprod
  obtain ⟨a1, x1, hx1, ha1, h1⟩ := ap5_sq_splitting hn hcop (by decide : 1 < 5) hprod
  obtain ⟨a2, x2, hx2, ha2, h2⟩ := ap5_sq_splitting hn hcop (by decide : 2 < 5) hprod
  obtain ⟨a3, x3, hx3, ha3, h3⟩ := ap5_sq_splitting hn hcop (by decide : 3 < 5) hprod
  obtain ⟨a4, x4, hx4, ha4, h4⟩ := ap5_sq_splitting hn hcop (by decide : 4 < 5) hprod
  simp only [zero_mul, add_zero] at h0
  simp only [one_mul] at h1
  have hX_pos : 0 < x0 * x1 * x2 * x3 * x4 := by positivity
  have hprod_split : (a0 * a1 * a2 * a3 * a4) * (x0 * x1 * x2 * x3 * x4) ^ 2 = q ^ 2 := by
    calc (a0 * a1 * a2 * a3 * a4) * (x0 * x1 * x2 * x3 * x4) ^ 2
        = (a0 * x0 ^ 2) * (a1 * x1 ^ 2) * (a2 * x2 ^ 2) * (a3 * x3 ^ 2) * (a4 * x4 ^ 2) := by ring
      _ = n * (n + d) * (n + 2 * d) * (n + 3 * d) * (n + 4 * d) := by rw [← h0, ← h1, ← h2, ← h3, ← h4]
      _ = q ^ 2 := heq
  have hsq : isSq89 (a0 * a1 * a2 * a3 * a4) = true :=
    isSq89_sound ha0 ha1 ha2 ha3 ha4 hX_pos hprod_split
  have hok8 : ok8Fast a0 a1 a2 a3 a4 = true :=
    ok8Fast_sound hcop ha0 ha1 ha2 ha3 ha4 h0 h1 h2 h3 h4
  have hok9 : ok9Fast a0 a1 a2 a3 a4 = true :=
    ok9Fast_sound hcop ha0 ha1 ha2 ha3 ha4 h0 h1 h2 h3 h4
  rcases checkAll5_elim ha0 ha1 ha2 ha3 ha4 hsq hok8 hok9 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · apply no_prod_four_ap_sq hn hd hcop (q := x0 * x1 * x2 * x3)
    calc n * (n + d) * (n + 2 * d) * (n + 3 * d)
        = (1 * x0 ^ 2) * (1 * x1 ^ 2) * (1 * x2 ^ 2) * (1 * x3 ^ 2) := by rw [← h0, ← h1, ← h2, ← h3]
      _ = (x0 * x1 * x2 * x3) ^ 2 := by ring
  · apply no_prod_four_ap_sq hn hd hcop (q := 6 * x0 * x1 * x2 * x3)
    calc n * (n + d) * (n + 2 * d) * (n + 3 * d)
        = (6 * x0 ^ 2) * (1 * x1 ^ 2) * (2 * x2 ^ 2) * (3 * x3 ^ 2) := by rw [← h0, ← h1, ← h2, ← h3]
      _ = (6 * x0 * x1 * x2 * x3) ^ 2 := by ring
  · have hn1 : 0 < n + d := by omega
    have hcop1 : Nat.Coprime (n + d) d := by
      refine Nat.coprime_of_dvd' fun r _ hr1 hr2 => ?_
      exact hcop ▸ Nat.dvd_gcd ((Nat.dvd_add_left hr2).mp hr1) hr2
    apply no_prod_four_ap_sq hn1 hd hcop1 (q := 6 * x1 * x2 * x3 * x4)
    have ht1 : n + d + d = n + 2 * d := by ring
    have ht2 : n + d + 2 * d = n + 3 * d := by ring
    have ht3 : n + d + 3 * d = n + 4 * d := by ring
    rw [ht1, ht2, ht3]
    calc (n + d) * (n + 2 * d) * (n + 3 * d) * (n + 4 * d)
        = (3 * x1 ^ 2) * (2 * x2 ^ 2) * (1 * x3 ^ 2) * (6 * x4 ^ 2) := by rw [← h1, ← h2, ← h3, ← h4]
      _ = (6 * x1 * x2 * x3 * x4) ^ 2 := by ring

private theorem finset_ap_prod_five {s : Finset ℕ} {n d : ℕ} (hd : 0 < d)
    (hap : ENat.card (s : Set ℕ) = (5 : ℕ∞) ∧
      (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (5 : ℕ∞))}) :
    ∏ x ∈ s, x = n * (n + d) * (n + 2 * d) * (n + 3 * d) * (n + 4 * d) := by
  have hs_eq : s = (Finset.range 5).image (fun i => n + i * d) := by
    ext x
    have hmem : x ∈ (s : Set ℕ) ↔ ∃ i : ℕ, (i : ℕ∞) < (5 : ℕ∞) ∧ n + i • d = x := by
      rw [hap.2]; simp only [Set.mem_ofPred_eq, exists_prop]
    rw [Finset.mem_coe] at hmem
    rw [hmem, Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, Finset.mem_range.mpr (ENat.natCast_lt_natCast.mp hi), by simp [smul_eq_mul]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, ENat.natCast_lt_natCast.mpr (Finset.mem_range.mp hi), by simp [smul_eq_mul]⟩
  rw [hs_eq, Finset.prod_image]
  · simp [Finset.prod_range_succ]
  · intro i _ j _ hij
    exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)

/-- Bridge theorem matching the `Erdos672With 5 2` conjunct of
`Erdos672.erdos_672.variants.oblath` definitionally. -/
theorem oblath_k5_l2_bridge :
    ∀ (s : Finset ℕ), s.card = 5 → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
      (ENat.card (s : Set ℕ) = (5 : ℕ∞) ∧
        (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (5 : ℕ∞))}) →
      ∀ q, ∏ i ∈ s, i ≠ q ^ 2 := by
  intro s _ n hn d hd hcop hap q heq
  rw [finset_ap_prod_five hd hap] at heq
  exact no_prod_five_ap_sq hn hd hcop heq

/-- Generalization of Obláth's `k = 5, l = 2` theorem to all even exponents
`l = 2 * m` (`m ≥ 1`). -/
theorem oblath_k5_even_l_bridge {m : ℕ} (_hm : 0 < m) :
    ∀ (s : Finset ℕ), s.card = 5 → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
      (ENat.card (s : Set ℕ) = (5 : ℕ∞) ∧
        (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (5 : ℕ∞))}) →
      ∀ q, ∏ i ∈ s, i ≠ q ^ (2 * m) := by
  intro s hs n hn d hd hcop hap q heq
  apply oblath_k5_l2_bridge s hs n hn d hd hcop hap (q ^ m)
  rw [heq, pow_mul']

end Contribution.Erdos672OblathK5L2
