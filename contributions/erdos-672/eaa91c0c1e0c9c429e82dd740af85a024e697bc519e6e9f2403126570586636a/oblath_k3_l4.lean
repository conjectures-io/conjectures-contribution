import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
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
# Obláth's Theorem on Three Integers in AP and Fourth Powers (Erdős Problem #672, k = 3, l = 4)

Proves unconditionally that the product of three positive integers in coprime arithmetic
progression `n * (n + d) * (n + 2 * d)` (`n, d > 0`, `Nat.Coprime n d`) is never a fourth
power, discharging the `Erdos672With 3 4` conjunct of `Erdos672.erdos_672.variants.oblath`
as well as `Erdos672With 3 (4 * m)` for all `m > 0`.

Combines canonical `{1, 2, 4, 8}` splitting for primes `p ≥ 3` and a kernel-decidable
mod-16 filter (`checkAll3Fourths`) reducing all tuples to `(1, 1, 1)`, `(2, 1, 8)`, and
`(8, 1, 2)`, each closed by Fermat descent on `V ^ 4 + W ^ 2 = U ^ 4`.
-/

namespace Contribution.Erdos672OblathK3L4

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

private theorem nat_coprime_mul_eq_fourth {u v z : ℕ} (hcop : Nat.Coprime u v)
    (heq : u * v = z ^ 4) : ∃ a b : ℕ, u = a ^ 4 ∧ v = b ^ 4 := by
  have heq2 : u * v = (z ^ 2) ^ 2 := by rw [heq]; ring
  obtain ⟨A, B, hA, hB⟩ := nat_coprime_mul_eq_sq hcop heq2
  have hcopAB : Nat.Coprime A B := by
    refine Nat.coprime_of_dvd' fun r _ hrA hrB => ?_
    exact hcop ▸ Nat.dvd_gcd (hA ▸ dvd_pow hrA (by decide : 2 ≠ 0))
      (hB ▸ dvd_pow hrB (by decide : 2 ≠ 0))
  have hABz : A * B = z ^ 2 := by
    rcases lt_trichotomy (A * B) (z ^ 2) with hlt | heq' | hgt
    · have h4 : (A * B) ^ 2 < (z ^ 2) ^ 2 := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)
      have h5 : (A * B) ^ 2 = (z ^ 2) ^ 2 := by rw [mul_pow, ← hA, ← hB, heq]; ring
      omega
    · exact heq'
    · have h4 : (z ^ 2) ^ 2 < (A * B) ^ 2 := Nat.pow_lt_pow_left hgt (by decide : 2 ≠ 0)
      have h5 : (A * B) ^ 2 = (z ^ 2) ^ 2 := by rw [mul_pow, ← hA, ← hB, heq]; ring
      omega
  obtain ⟨a, b, ha, hb⟩ := nat_coprime_mul_eq_sq hcopAB hABz
  exact ⟨a, b, by rw [hA, ha]; ring, by rw [hB, hb]; ring⟩

private theorem nat_coprime_mul_eq_prime_mul_sq {p u v q : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime u v) (heq : u * v = p * q ^ 2) :
    (∃ a b : ℕ, u = p * a ^ 2 ∧ v = b ^ 2) ∨ (∃ a b : ℕ, u = a ^ 2 ∧ v = p * b ^ 2) := by
  have hdvd : p ∣ u * v := ⟨q ^ 2, heq⟩
  rcases hp.dvd_mul.mp hdvd with hpu | hpv
  · left
    obtain ⟨u', rfl⟩ := hpu
    have heq' : u' * v = q ^ 2 := by
      have : p * (u' * v) = p * q ^ 2 := by
        calc p * (u' * v) = p * u' * v := by ring
          _ = p * q ^ 2 := heq
      exact Nat.mul_left_cancel hp.pos this
    have hcop' : Nat.Coprime u' v := hcop.coprime_dvd_left ⟨p, mul_comm p u'⟩
    obtain ⟨a, b, ha, hb⟩ := nat_coprime_mul_eq_sq hcop' heq'
    exact ⟨a, b, by rw [ha], hb⟩
  · right
    obtain ⟨v', rfl⟩ := hpv
    have heq' : u * v' = q ^ 2 := by
      have : p * (u * v') = p * q ^ 2 := by
        calc p * (u * v') = u * (p * v') := by ring
          _ = p * q ^ 2 := heq
      exact Nat.mul_left_cancel hp.pos this
    have hcop' : Nat.Coprime u v' := hcop.coprime_dvd_right ⟨p, mul_comm p v'⟩
    obtain ⟨a, b, ha, hb⟩ := nat_coprime_mul_eq_sq hcop' heq'
    exact ⟨a, b, ha, by rw [hb]⟩

/-- Fermat's infinite descent on `V^4 + W^2 = U^4` for positive `U, V, W` with `Nat.Coprime U V`. -/
theorem no_fourth_sub_fourth_eq_sq : ∀ S U V W : ℕ,
    0 < U → 0 < V → 0 < W → U = S → Nat.Coprime U V → V ^ 4 + W ^ 2 = U ^ 4 → False := by
  intro S
  induction S using Nat.strong_induction_on with
  | h S ih =>
    intro U V W hU hV hW hUS hcop heq
    subst hUS
    have hU_odd : U % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one U with hU2 | hU2
      · exfalso
        have hV_odd : V % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one V with hV2 | hV2
          · exact False.elim (Nat.prime_two.not_dvd_one
              (hcop ▸ Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hU2) (Nat.dvd_of_mod_eq_zero hV2)))
          · exact hV2
        have hU4 : U ^ 4 % 4 = 0 := by
          have : 4 ∣ U ^ 4 := by
            obtain ⟨U', rfl⟩ := Nat.dvd_of_mod_eq_zero hU2
            exact ⟨4 * U' ^ 4, by ring⟩
          exact Nat.mod_eq_zero_of_dvd this
        have hV4 : V ^ 4 % 4 = 1 := by
          obtain ⟨V', hV'⟩ : ∃ V', V = 2 * V' + 1 := ⟨V / 2, by omega⟩
          have : V ^ 4 = 4 * (4 * V' ^ 4 + 8 * V' ^ 3 + 6 * V' ^ 2 + 2 * V') + 1 := by rw [hV']; ring
          omega
        have hW4 : W ^ 2 % 4 = 0 ∨ W ^ 2 % 4 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one W with hW2 | hW2
          · obtain ⟨W', rfl⟩ := Nat.dvd_of_mod_eq_zero hW2
            left; have : (2 * W') ^ 2 = 4 * W' ^ 2 := by ring
            omega
          · obtain ⟨W', hW'⟩ : ∃ W', W = 2 * W' + 1 := ⟨W / 2, by omega⟩
            right; have : W ^ 2 = 4 * (W' ^ 2 + W') + 1 := by rw [hW']; ring
            omega
        have hmod := congrArg (· % 4) heq
        rw [Nat.add_mod, hV4, hU4] at hmod
        rcases hW4 with hW0 | hW1 <;> omega
      · exact hU2
    have hcop_V2W : Nat.Coprime (V ^ 2) W := by
      refine Nat.coprime_of_dvd' fun p hp hpV hpW => ?_
      have hpV1 : p ∣ V := hp.dvd_of_dvd_pow hpV
      have hpU4 : p ∣ U ^ 4 := heq ▸ Nat.dvd_add (dvd_pow hpV1 (by decide : 4 ≠ 0)) (dvd_pow hpW (by decide : 2 ≠ 0))
      have hpU : p ∣ U := hp.dvd_of_dvd_pow hpU4
      exact hcop ▸ Nat.dvd_gcd hpU hpV1
    rcases Nat.mod_two_eq_zero_or_one V with hV2 | hV2
    · obtain ⟨V', rfl⟩ := Nat.dvd_of_mod_eq_zero hV2
      have hV' : 0 < V' := by omega
      have hW_odd : W % 2 = 1 := by
        have hU4_mod : U ^ 4 % 2 = 1 := by rw [Nat.pow_mod, hU_odd]
        have hV4_mod : (2 * V') ^ 4 % 2 = 0 := by
          have : 2 ∣ (2 * V') ^ 4 := ⟨8 * V' ^ 4, by ring⟩
          exact Nat.mod_eq_zero_of_dvd this
        have hW2_mod : W ^ 2 % 2 = 1 := by
          have hmod := congrArg (· % 2) heq
          rw [Nat.add_mod, hV4_mod, hU4_mod] at hmod
          omega
        rcases Nat.mod_two_eq_zero_or_one W with h | h
        · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero h
          have : (2 * k) ^ 2 % 2 = 0 := by have : 2 ∣ (2 * k) ^ 2 := ⟨2 * k ^ 2, by ring⟩; exact Nat.mod_eq_zero_of_dvd this
          omega
        · exact h
      have hpyth : PythagoreanTriple (W : ℤ) (((2 * V') ^ 2 : ℕ) : ℤ) ((U ^ 2 : ℕ) : ℤ) := by
        dsimp [PythagoreanTriple]
        exact_mod_cast (by calc W * W + (2 * V') ^ 2 * (2 * V') ^ 2 = (2 * V') ^ 4 + W ^ 2 := by ring
          _ = U ^ 4 := heq
          _ = U ^ 2 * U ^ 2 := by ring)
      have hcop_z : Int.gcd (W : ℤ) (((2 * V') ^ 2 : ℕ) : ℤ) = 1 := by
        exact_mod_cast hcop_V2W.symm
      have hpar_z : (W : ℤ) % 2 = 1 := by exact_mod_cast hW_odd
      have hU2_pos : (0 : ℤ) < (U ^ 2 : ℕ) := by exact_mod_cast Nat.pow_pos hU
      obtain ⟨r, s, _, hs_eq, hU2_eq, hcop_rs, _, hr_nn⟩ :=
        hpyth.coprime_classification' hcop_z hpar_z hU2_pos
      have hr_pos : 0 < r := by
        apply lt_of_le_of_ne hr_nn
        intro hr0
        rw [← hr0] at hs_eq
        have hpos : (0 : ℤ) < (((2 * V') ^ 2 : ℕ) : ℤ) := by positivity
        linarith only [hs_eq, hpos]
      have hs_pos : 0 < s := by
        have hpos : (0 : ℤ) < 2 * r * s := by
          rw [← hs_eq]; positivity
        nlinarith only [hpos, hr_pos]
      set rN := r.natAbs
      set sN := s.natAbs
      have hrN_pos : 0 < rN := Int.natAbs_pos.mpr hr_pos.ne'
      have hsN_pos : 0 < sN := Int.natAbs_pos.mpr hs_pos.ne'
      have hcop_rsN : Nat.Coprime rN sN := hcop_rs
      have hrN_z : (rN : ℤ) = r := Int.natAbs_of_nonneg hr_pos.le
      have hsN_z : (sN : ℤ) = s := Int.natAbs_of_nonneg hs_pos.le
      have hrs_mul : rN * sN = 2 * V' ^ 2 := by
        have h1 : (2 : ℤ) * (rN : ℤ) * (sN : ℤ) = (2 * V') ^ 2 := by
          rw [hrN_z, hsN_z, ← hs_eq]; push_cast; ring
        have h1N : 2 * rN * sN = (2 * V') ^ 2 := by exact_mod_cast h1
        have h2N : 2 * (rN * sN) = 2 * (2 * V' ^ 2) := by
          calc 2 * (rN * sN) = 2 * rN * sN := by ring
            _ = (2 * V') ^ 2 := h1N
            _ = 2 * (2 * V' ^ 2) := by ring
        omega
      have hU2_sum : rN ^ 2 + sN ^ 2 = U ^ 2 := by
        have h1 : (rN : ℤ) ^ 2 + (sN : ℤ) ^ 2 = (U ^ 2 : ℕ) := by
          rw [hrN_z, hsN_z, ← hU2_eq]
        exact_mod_cast h1
      obtain ⟨a, b, ha_pos, hb_pos, hcop_ab, hab_eq⟩ :
          ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ a ^ 4 + 4 * b ^ 4 = U ^ 2 := by
        rcases nat_coprime_mul_eq_prime_mul_sq Nat.prime_two hcop_rsN hrs_mul with
            ⟨b, a, hr_eq, hs_eq'⟩ | ⟨a, b, hr_eq, hs_eq'⟩
        · have hb_pos : 0 < b := by nlinarith only [hr_eq, hrN_pos]
          have ha_pos : 0 < a := by nlinarith only [hs_eq', hsN_pos]
          have hcop_ab : Nat.Coprime a b := by
            refine Nat.coprime_of_dvd' fun q _ hqa hqb => ?_
            exact hcop_rsN ▸ Nat.dvd_gcd (hr_eq ▸ dvd_mul_of_dvd_right (dvd_pow hqb (by decide)) 2)
              (hs_eq' ▸ dvd_pow hqa (by decide))
          have hab_eq : a ^ 4 + 4 * b ^ 4 = U ^ 2 := by
            calc a ^ 4 + 4 * b ^ 4 = (a ^ 2) ^ 2 + (2 * b ^ 2) ^ 2 := by ring
              _ = sN ^ 2 + rN ^ 2 := by rw [← hs_eq', ← hr_eq]
              _ = U ^ 2 := by linarith only [hU2_sum]
          exact ⟨a, b, ha_pos, hb_pos, hcop_ab, hab_eq⟩
        · have ha_pos : 0 < a := by nlinarith only [hr_eq, hrN_pos]
          have hb_pos : 0 < b := by nlinarith only [hs_eq', hsN_pos]
          have hcop_ab : Nat.Coprime a b := by
            refine Nat.coprime_of_dvd' fun q _ hqa hqb => ?_
            exact hcop_rsN ▸ Nat.dvd_gcd (hr_eq ▸ dvd_pow hqa (by decide))
              (hs_eq' ▸ dvd_mul_of_dvd_right (dvd_pow hqb (by decide)) 2)
          have hab_eq : a ^ 4 + 4 * b ^ 4 = U ^ 2 := by
            calc a ^ 4 + 4 * b ^ 4 = (a ^ 2) ^ 2 + (2 * b ^ 2) ^ 2 := by ring
              _ = rN ^ 2 + sN ^ 2 := by rw [← hr_eq, ← hs_eq']
              _ = U ^ 2 := hU2_sum
          exact ⟨a, b, ha_pos, hb_pos, hcop_ab, hab_eq⟩
      have ha_odd : a % 2 = 1 := by
        have hU2_mod : U ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hU_odd]
        have h4b : 4 * b ^ 4 % 2 = 0 := by
          have : 2 ∣ 4 * b ^ 4 := ⟨2 * b ^ 4, by ring⟩
          exact Nat.mod_eq_zero_of_dvd this
        have ha4_mod : a ^ 4 % 2 = 1 := by
          have hmod := congrArg (· % 2) hab_eq
          rw [Nat.add_mod, h4b, hU2_mod] at hmod
          omega
        rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2
        · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero ha2
          have : (2 * k) ^ 4 % 2 = 0 := by have : 2 ∣ (2 * k) ^ 4 := ⟨8 * k ^ 4, by ring⟩; exact Nat.mod_eq_zero_of_dvd this
          omega
        · exact ha2
      have ha2_lt_U : a ^ 2 < U := by
        have h4pos : 0 < 4 * b ^ 4 := by positivity
        have hsq_lt : (a ^ 2) ^ 2 < U ^ 2 := by nlinarith only [hab_eq, h4pos]
        nlinarith only [hsq_lt]
      set A := (U + a ^ 2) / 2
      set B := (U - a ^ 2) / 2
      have ha2_odd : a ^ 2 % 2 = 1 := by rw [Nat.pow_mod, ha_odd]
      have hA2 : 2 * A = U + a ^ 2 := by omega
      have hB2 : 2 * B = U - a ^ 2 := by omega
      have hA_pos : 0 < A := by omega
      have hB_pos : 0 < B := by omega
      have hAB_mul : A * B = b ^ 4 := by
        have h4 : 4 * (A * B) = 4 * b ^ 4 := by
          zify [le_of_lt ha2_lt_U] at hA2 hB2 hab_eq ⊢
          nlinarith only [hA2, hB2, hab_eq]
        omega
      have hcop_AB : Nat.Coprime A B := by
        refine Nat.coprime_of_dvd' fun p hp hpA hpB => ?_
        have hp_sum : p ∣ U := by
          rw [show U = A + B by omega]
          exact Nat.dvd_add hpA hpB
        have hp_diff : p ∣ a ^ 2 := by
          rw [show a ^ 2 = A - B by omega]
          exact Nat.dvd_sub hpA hpB
        have hpa : p ∣ a := hp.dvd_of_dvd_pow hp_diff
        have hpb4 : p ∣ b ^ 4 := hAB_mul ▸ dvd_mul_of_dvd_left hpA B
        have hpb : p ∣ b := hp.dvd_of_dvd_pow hpb4
        exact hcop_ab ▸ Nat.dvd_gcd hpa hpb
      obtain ⟨u, v, hu_eq, hv_eq⟩ := nat_coprime_mul_eq_fourth hcop_AB hAB_mul
      have hu_pos : 0 < u := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hu_eq; omega
      have hv_pos : 0 < v := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hv_eq; omega
      have hcop_uv : Nat.Coprime u v := by
        refine Nat.coprime_of_dvd' fun q _ hqu hqv => ?_
        exact hcop_AB ▸ Nat.dvd_gcd (hu_eq ▸ dvd_pow hqu (by decide)) (hv_eq ▸ dvd_pow hqv (by decide))
      have heq' : v ^ 4 + a ^ 2 = u ^ 4 := by
        have hsub : A - B = a ^ 2 := by omega
        have hle : v ^ 4 ≤ u ^ 4 := by rw [← hu_eq, ← hv_eq]; omega
        rw [← hu_eq, ← hv_eq]; omega
      have hu_lt_U : u < U := by
        have hu_le : u ≤ u ^ 4 := Nat.le_self_pow (by decide : 4 ≠ 0) u
        have hA_lt_U : A < U := by omega
        omega
      exact ih u hu_lt_U u v a hu_pos hv_pos ha_pos rfl hcop_uv heq'
    · have hW_even : W % 2 = 0 := by
        have hU4_mod : U ^ 4 % 2 = 1 := by rw [Nat.pow_mod, hU_odd]
        have hV4_mod : V ^ 4 % 2 = 1 := by rw [Nat.pow_mod, hV2]
        have hW2_mod : W ^ 2 % 2 = 0 := by
          have hmod := congrArg (· % 2) heq
          rw [Nat.add_mod, hV4_mod, hU4_mod] at hmod
          omega
        rcases Nat.mod_two_eq_zero_or_one W with h | h
        · exact h
        · have : W ^ 2 % 2 = 1 := by rw [Nat.pow_mod, h]
          omega
      have hpyth : PythagoreanTriple ((V ^ 2 : ℕ) : ℤ) (W : ℤ) ((U ^ 2 : ℕ) : ℤ) := by
        dsimp [PythagoreanTriple]
        exact_mod_cast (by calc V ^ 2 * V ^ 2 + W * W = V ^ 4 + W ^ 2 := by ring
          _ = U ^ 4 := heq
          _ = U ^ 2 * U ^ 2 := by ring)
      have hcop_z : Int.gcd ((V ^ 2 : ℕ) : ℤ) (W : ℤ) = 1 := by exact_mod_cast hcop_V2W
      have hV2_odd : V ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hV2]
      have hpar_z : ((V ^ 2 : ℕ) : ℤ) % 2 = 1 := by exact_mod_cast hV2_odd
      have hU2_pos : (0 : ℤ) < (U ^ 2 : ℕ) := by exact_mod_cast Nat.pow_pos hU
      obtain ⟨r, s, hr_eq, _, hU2_eq, hcop_rs, _, hr_nn⟩ :=
        hpyth.coprime_classification' hcop_z hpar_z hU2_pos
      have hs_nz : s ≠ 0 := by
        intro hs0
        have heq_W : (W : ℤ) = 0 := by
          have h1 : (W : ℤ) ^ 2 + ((V ^ 2 : ℕ) : ℤ) ^ 2 = ((U ^ 2 : ℕ) : ℤ) ^ 2 := by
            exact_mod_cast (by
              calc W ^ 2 + (V ^ 2) ^ 2 = V ^ 4 + W ^ 2 := by ring
                _ = U ^ 4 := heq
                _ = (U ^ 2) ^ 2 := by ring)
          have hrU : ((V ^ 2 : ℕ) : ℤ) = ((U ^ 2 : ℕ) : ℤ) := by
            rw [hr_eq, hU2_eq, hs0]; ring
          nlinarith only [h1, hrU]
        exact hW.ne' (by exact_mod_cast heq_W)
      have hr_pos : 0 < r := by
        apply lt_of_le_of_ne hr_nn
        intro hr0
        rw [← hr0] at hr_eq
        have hpos : (0 : ℤ) < ((V ^ 2 : ℕ) : ℤ) := by positivity
        nlinarith only [hr_eq, hpos]
      set rN := r.natAbs
      set sN := s.natAbs
      have hrN_pos : 0 < rN := Int.natAbs_pos.mpr hr_pos.ne'
      have hsN_pos : 0 < sN := Int.natAbs_pos.mpr hs_nz
      have hcop_rsN : Nat.Coprime rN sN := hcop_rs
      have hr_sq_z : (rN : ℤ) ^ 2 = r ^ 2 := Int.natAbs_sq r
      have hs_sq_z : (sN : ℤ) ^ 2 = s ^ 2 := Int.natAbs_sq s
      have hV2_z : (rN : ℤ) ^ 2 - (sN : ℤ) ^ 2 = ((V ^ 2 : ℕ) : ℤ) := by
        rw [hr_sq_z, hs_sq_z, ← hr_eq]
      have hs_lt_r : sN < rN := by
        have hpos : (0 : ℤ) < (V ^ 2 : ℕ) := by positivity
        have : (sN : ℤ) ^ 2 < (rN : ℤ) ^ 2 := by linarith only [hV2_z, hpos]
        nlinarith only [this, hrN_pos, hsN_pos]
      have hV2_eq : rN ^ 2 - sN ^ 2 = V ^ 2 := by
        zify [Nat.pow_le_pow_left (le_of_lt hs_lt_r) 2]
        exact hV2_z
      have hU2_sum : rN ^ 2 + sN ^ 2 = U ^ 2 := by
        have h1 : (rN : ℤ) ^ 2 + (sN : ℤ) ^ 2 = (U ^ 2 : ℕ) := by
          rw [hr_sq_z, hs_sq_z, ← hU2_eq]
        exact_mod_cast h1
      have heq' : sN ^ 4 + (U * V) ^ 2 = rN ^ 4 := by
        zify [Nat.pow_le_pow_left (le_of_lt hs_lt_r) 2] at hV2_eq ⊢
        have hU2z : (rN : ℤ) ^ 2 + (sN : ℤ) ^ 2 = (U : ℤ) ^ 2 := by exact_mod_cast hU2_sum
        calc (sN : ℤ) ^ 4 + ((U : ℤ) * (V : ℤ)) ^ 2
            = (sN : ℤ) ^ 4 + (U : ℤ) ^ 2 * (V : ℤ) ^ 2 := by ring
          _ = (sN : ℤ) ^ 4 + ((rN : ℤ) ^ 2 + (sN : ℤ) ^ 2) * ((rN : ℤ) ^ 2 - (sN : ℤ) ^ 2) := by
              rw [← hU2z, ← hV2_eq]
          _ = (rN : ℤ) ^ 4 := by ring
      have hrN_lt_U : rN < U := by
        have hsq : rN ^ 2 < U ^ 2 := by nlinarith only [hU2_sum, hsN_pos]
        nlinarith only [hsq]
      exact ih rN hrN_lt_U rN sN (U * V) hrN_pos hsN_pos (Nat.mul_pos hU hV) rfl hcop_rsN heq'

/-- No odd coprime positive `x, y` satisfy `x ^ 4 + 4 * z ^ 4 = y ^ 4` for `z > 0`. -/
theorem no_odd_coprime_fourth_add_four_fourth {x z y : ℕ}
    (hx : 0 < x) (hz : 0 < z) (_hy : 0 < y) (hx_odd : x % 2 = 1) (hy_odd : y % 2 = 1)
    (hcop : Nat.Coprime x y) (heq : x ^ 4 + 4 * z ^ 4 = y ^ 4) : False := by
  have hx_lt_y : x ^ 2 < y ^ 2 := by
    have h4 : 0 < 4 * z ^ 4 := by positivity
    have hsq : (x ^ 2) ^ 2 < (y ^ 2) ^ 2 := by nlinarith only [heq, h4]
    nlinarith only [hsq]
  set A := (y ^ 2 + x ^ 2) / 2
  set B := (y ^ 2 - x ^ 2) / 2
  have hx2_odd : x ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hx_odd]
  have hy2_odd : y ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hy_odd]
  have hA2 : 2 * A = y ^ 2 + x ^ 2 := by omega
  have hB2 : 2 * B = y ^ 2 - x ^ 2 := by omega
  have hA_pos : 0 < A := by omega
  have hB_pos : 0 < B := by omega
  have hAB_mul : A * B = z ^ 4 := by
    have h4 : 4 * (A * B) = 4 * z ^ 4 := by
      zify [le_of_lt hx_lt_y] at hA2 hB2 heq ⊢
      nlinarith only [hA2, hB2, heq]
    omega
  have hcop_AB : Nat.Coprime A B := by
    refine Nat.coprime_of_dvd' fun p hp hpA hpB => ?_
    have hpy : p ∣ y := hp.dvd_of_dvd_pow (by rw [show y ^ 2 = A + B by omega]; exact Nat.dvd_add hpA hpB)
    have hpx : p ∣ x := hp.dvd_of_dvd_pow (by rw [show x ^ 2 = A - B by omega]; exact Nat.dvd_sub hpA hpB)
    exact hcop ▸ Nat.dvd_gcd hpx hpy
  obtain ⟨u, v, hu_eq, hv_eq⟩ := nat_coprime_mul_eq_fourth hcop_AB hAB_mul
  have hu_pos : 0 < u := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hu_eq; omega
  have hv_pos : 0 < v := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hv_eq; omega
  have hcop_uv : Nat.Coprime u v := by
    refine Nat.coprime_of_dvd' fun q _ hqu hqv => ?_
    exact hcop_AB ▸ Nat.dvd_gcd (hu_eq ▸ dvd_pow hqu (by decide)) (hv_eq ▸ dvd_pow hqv (by decide))
  have heq' : v ^ 4 + x ^ 2 = u ^ 4 := by
    have hsub : A - B = x ^ 2 := by omega
    rw [← hu_eq, ← hv_eq]
    omega
  exact no_fourth_sub_fourth_eq_sq u u v x hu_pos hv_pos hx rfl hcop_uv heq'

/-- No three positive odd coprime `x0, x1, x2` with `x0 < x2` satisfy `x0^4 + x2^4 = 2 * x1^4`. -/
theorem no_three_fourth_ap {x0 x1 x2 : ℕ}
    (hx0 : 0 < x0) (hx1 : 0 < x1) (hx2 : 0 < x2) (hlt : x0 < x2)
    (hx0_odd : x0 % 2 = 1) (hx2_odd : x2 % 2 = 1) (hcop : Nat.Coprime x0 x2)
    (heq : x0 ^ 4 + x2 ^ 4 = 2 * x1 ^ 4) : False := by
  have hx_lt : x0 ^ 2 < x2 ^ 2 := by nlinarith only [hlt, hx0]
  set U := (x2 ^ 2 + x0 ^ 2) / 2
  set V := (x2 ^ 2 - x0 ^ 2) / 2
  have hx02_odd : x0 ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hx0_odd]
  have hx22_odd : x2 ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hx2_odd]
  have hU2 : 2 * U = x2 ^ 2 + x0 ^ 2 := by omega
  have hV2 : 2 * V = x2 ^ 2 - x0 ^ 2 := by omega
  have hU_pos : 0 < U := by omega
  have hV_pos : 0 < V := by omega
  have hcop_UV : Nat.Coprime U V := by
    refine Nat.coprime_of_dvd' fun p hp hpU hpV => ?_
    have hp2 : p ∣ x2 := hp.dvd_of_dvd_pow (by rw [show x2 ^ 2 = U + V by omega]; exact Nat.dvd_add hpU hpV)
    have hp0 : p ∣ x0 := hp.dvd_of_dvd_pow (by rw [show x0 ^ 2 = U - V by omega]; exact Nat.dvd_sub hpU hpV)
    exact hcop ▸ Nat.dvd_gcd hp0 hp2
  have hU2V2 : U ^ 2 + V ^ 2 = x1 ^ 4 := by
    have h4 : 4 * (U ^ 2 + V ^ 2) = 4 * x1 ^ 4 := by
      zify [le_of_lt hx_lt] at hU2 hV2 heq ⊢
      nlinarith only [hU2, hV2, heq]
    omega
  have hU2_sub_V2 : U ^ 2 - V ^ 2 = (x0 * x2) ^ 2 := by
    have h4 : 4 * (U ^ 2 - V ^ 2) = 4 * (x0 * x2) ^ 2 := by
      zify [le_of_lt hx_lt, Nat.pow_le_pow_left (by omega : V ≤ U) 2] at hU2 hV2 ⊢
      nlinarith only [hU2, hV2]
    omega
  have hVU_eq : V ^ 4 + (x0 * x2 * x1 ^ 2) ^ 2 = U ^ 4 := by
    have hV_le_U : V ^ 2 ≤ U ^ 2 := Nat.pow_le_pow_left (by omega : V ≤ U) 2
    zify [hV_le_U, Nat.pow_le_pow_left hV_le_U 2] at hU2_sub_V2 ⊢
    have hz1 : (U : ℤ) ^ 2 + (V : ℤ) ^ 2 = (x1 : ℤ) ^ 4 := by exact_mod_cast hU2V2
    calc (V : ℤ) ^ 4 + ((x0 : ℤ) * (x2 : ℤ) * (x1 : ℤ) ^ 2) ^ 2
        = (V : ℤ) ^ 4 + ((x0 : ℤ) * (x2 : ℤ)) ^ 2 * (x1 : ℤ) ^ 4 := by ring
      _ = (V : ℤ) ^ 4 + ((U : ℤ) ^ 2 - (V : ℤ) ^ 2) * ((U : ℤ) ^ 2 + (V : ℤ) ^ 2) := by
          rw [← hU2_sub_V2, ← hz1]
      _ = (U : ℤ) ^ 4 := by ring
  exact no_fourth_sub_fourth_eq_sq U U V (x0 * x2 * x1 ^ 2)
    hU_pos hV_pos (by positivity) rfl hcop_UV hVU_eq

private theorem ap_pairwise_gcd_dvd {n d i j : ℕ} (hcop : Nat.Coprime n d) (hij : i < j) :
    Nat.gcd (n + i * d) (n + j * d) ∣ (j - i) := by
  set g := Nat.gcd (n + i * d) (n + j * d)
  have hgi : g ∣ n + i * d := Nat.gcd_dvd_left _ _
  have hgj : g ∣ n + j * d := Nat.gcd_dvd_right _ _
  have hdiff : n + j * d = (n + i * d) + (j - i) * d := by
    have hle : i ≤ j := Nat.le_of_lt hij
    calc n + j * d = n + (i + (j - i)) * d := by rw [Nat.add_sub_cancel' hle]
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

private theorem ap_prime_unique_term {n d k p i j : ℕ} (hcop : Nat.Coprime n d) (hp : p.Prime)
    (hpk : k ≤ p) (hi : i < k) (hj : j < k)
    (hpi : p ∣ n + i * d) (hpj : p ∣ n + j * d) : i = j := by
  have _ := hp.pos
  by_contra hne
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · have hpd : p ∣ j - i := dvd_trans (Nat.dvd_gcd hpi hpj) (ap_pairwise_gcd_dvd hcop hij)
    have hle : p ≤ j - i := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hpd
    omega
  · exact hne rfl
  · have hpd : p ∣ i - j := dvd_trans (Nat.dvd_gcd hpj hpi) (ap_pairwise_gcd_dvd hcop hji)
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
        have hnot : ¬ p ∣ n + j * d := fun hdj =>
          hji (ap_prime_unique_term hcop hp hpk hjlt hi hdj hdiv)
        exact padicValNat.eq_zero_of_not_dvd hnot
      · intro hi_mem
        exact absurd (Finset.mem_range.mpr hi) hi_mem
    have hpow : padicValNat p (∏ j ∈ Finset.range k, (n + j * d)) = l * padicValNat p q := by
      rw [hprod, padicValNat.pow]
    rw [padicValNat_finset_prod (Finset.range k) (fun j => n + j * d) hne, hsum] at hpow
    exact ⟨padicValNat p q, hpow⟩
  · rw [padicValNat.eq_zero_of_not_dvd hdiv]
    exact dvd_zero l

theorem ap3_fourth_splitting {n d q i : ℕ} (hn : 0 < n) (hcop : Nat.Coprime n d)
    (hi : i < 3) (hprod : ∏ j ∈ Finset.range 3, (n + j * d) = q ^ 4) :
    ∃ a x : ℕ, 0 < x ∧ a ∈ ([1, 2, 4, 8] : List ℕ) ∧ n + i * d = a * x ^ 4 := by
  classical
  set m := n + i * d
  have hm0 : m ≠ 0 := by omega
  set a := 2 ^ (m.factorization 2 % 4)
  set x := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 4)
  have hx_pos : 0 < x :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hmod4 : m.factorization 2 % 4 < 4 := Nat.mod_lt _ (by decide)
  have ha_mem : a ∈ ([1, 2, 4, 8] : List ℕ) := by
    rcases (by omega :
        m.factorization 2 % 4 = 0 ∨ m.factorization 2 % 4 = 1 ∨
        m.factorization 2 % 4 = 2 ∨ m.factorization 2 % 4 = 3)
      with h | h | h | h <;> simp [a, h]
  have ha_prod : ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 4) = a := by
    let f : ℕ → ℕ := fun p => p ^ (m.factorization p % 4)
    change ∏ p ∈ m.primeFactors, f p = a
    have h1 : ∏ p ∈ m.primeFactors, f p = ∏ p ∈ m.primeFactors ∩ ({2} : Finset ℕ), f p := by
      symm
      refine Finset.prod_subset Finset.inter_subset_left fun p hp_mem hp_not => ?_
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hp_ne2 : p ≠ 2 := fun h => hp_not (Finset.mem_inter.mpr ⟨hp_mem, by simp [h]⟩)
      have hpk : 3 ≤ p := by have := hp.two_le; omega
      have hdvd : 4 ∣ padicValNat p m :=
        ap_padicValNat_dvd_of_prod_eq_pow hn hcop hp hpk hi hprod
      have hmod : m.factorization p % 4 = 0 := by
        rw [Nat.factorization_def m hp]
        exact Nat.mod_eq_zero_of_dvd hdvd
      simp [f, hmod]
    have h2 : ∏ p ∈ m.primeFactors ∩ ({2} : Finset ℕ), f p = ∏ p ∈ ({2} : Finset ℕ), f p := by
      refine Finset.prod_subset Finset.inter_subset_right fun p hp_2 hp_not => ?_
      have hp_nm : p ∉ m.primeFactors := fun hmem => hp_not (Finset.mem_inter.mpr ⟨hmem, hp_2⟩)
      have hzero : m.factorization p = 0 := by
        by_contra hne
        exact hp_nm (Nat.support_factorization m ▸ Finsupp.mem_support_iff.mpr hne)
      simp [f, hzero]
    have h3 : ∏ p ∈ ({2} : Finset ℕ), f p = a := by simp [f, a]
    exact h1.trans (h2.trans h3)
  have hm_eq : n + i * d = a * x ^ 4 := by
    calc n + i * d = m := rfl
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p) :=
        Nat.prod_primeFactors_pow_factorization hm0
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 4 + 4 * (m.factorization p / 4)) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Nat.mod_add_div]
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p % 4) * (p ^ (m.factorization p / 4)) ^ 4 := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [pow_add, mul_comm 4 (m.factorization p / 4), pow_mul]
      _ = (∏ p ∈ m.primeFactors, p ^ (m.factorization p % 4)) *
            (∏ p ∈ m.primeFactors, (p ^ (m.factorization p / 4)) ^ 4) :=
        Finset.prod_mul_distrib
      _ = a * x ^ 4 := by rw [ha_prod, Finset.prod_pow]
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

private def res16Fast (a r : ℕ) : Bool :=
  if a == 1 then (r == 0 || r == 1)
  else if a == 2 then (r == 0 || r == 2)
  else if a == 4 then (r == 0 || r == 4)
  else (r == 0 || r == 8)

private theorem res16Fast_sound {a x : ℕ} (ha : a ∈ ([1, 2, 4, 8] : List ℕ)) :
    res16Fast a ((a * x ^ 4) % 16) = true := by
  have hmod : (a * x ^ 4) % 16 = (a * (((x % 16) * (x % 16)) * ((x % 16) * (x % 16)))) % 16 := by
    have hx4 : x ^ 4 = (x * x) * (x * x) := by ring
    simp [hx4, Nat.mul_mod]
  rw [hmod]
  set rx := x % 16
  have hrx : rx < 16 := Nat.mod_lt x (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    · rcases (by omega :
          rx = 0 ∨ rx = 1 ∨ rx = 2 ∨ rx = 3 ∨ rx = 4 ∨ rx = 5 ∨ rx = 6 ∨ rx = 7 ∨
          rx = 8 ∨ rx = 9 ∨ rx = 10 ∨ rx = 11 ∨ rx = 12 ∨ rx = 13 ∨ rx = 14 ∨ rx = 15)
        with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

private def ok16Fast (a0 a1 a2 : ℕ) : Bool :=
  anyLt 16 fun n => anyLt 16 fun d =>
    (n % 2 == 1 || d % 2 == 1) &&
    res16Fast a0 (n % 16) && res16Fast a1 ((n + d) % 16) && res16Fast a2 ((n + 2 * d) % 16)

private def isFourth5 (p : ℕ) : Bool := anyLt 5 (fun s => s * s * s * s == p)

private def checkAll3Fourths : Bool :=
  let vals : List ℕ := [1, 2, 4, 8]
  vals.all fun a0 => vals.all fun a1 => vals.all fun a2 =>
    !(isFourth5 (a0 * a1 * a2) && ok16Fast a0 a1 a2) ||
    ((a0 == 1 && a1 == 1 && a2 == 1) ||
     (a0 == 2 && a1 == 1 && a2 == 8) ||
     (a0 == 8 && a1 == 1 && a2 == 2))

private theorem checkAll3Fourths_true : checkAll3Fourths = true := by decide

private theorem ok16Fast_sound {n d a0 a1 a2 x0 x1 x2 : ℕ}
    (hcop : Nat.Coprime n d)
    (ha0 : a0 ∈ ([1, 2, 4, 8] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 4, 8] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 4, 8] : List ℕ))
    (h0 : n = a0 * x0 ^ 4) (h1 : n + d = a1 * x1 ^ 4) (h2 : n + 2 * d = a2 * x2 ^ 4) :
    ok16Fast a0 a1 a2 = true := by
  refine anyLt_sound (Nat.mod_lt n (by decide)) ?_
  refine anyLt_sound (Nat.mod_lt d (by decide)) ?_
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  have hpar : (n % 16) % 2 = 1 ∨ (d % 16) % 2 = 1 := by
    by_contra hboth
    have hn2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have hd2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
    exact Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd hn2 hd2)
  have r0 : res16Fast a0 ((n % 16) % 16) = true := by
    rw [Nat.mod_mod, h0]; exact res16Fast_sound ha0
  have r1 : res16Fast a1 ((n % 16 + d % 16) % 16) = true := by
    have : (n % 16 + d % 16) % 16 = (n + d) % 16 := by simp [Nat.add_mod]
    rw [this, h1]; exact res16Fast_sound ha1
  have r2 : res16Fast a2 ((n % 16 + 2 * (d % 16)) % 16) = true := by
    have : (n % 16 + 2 * (d % 16)) % 16 = (n + 2 * d) % 16 := by simp [Nat.add_mod, Nat.mul_mod]
    rw [this, h2]; exact res16Fast_sound ha2
  exact ⟨⟨⟨hpar, r0⟩, r1⟩, r2⟩

private theorem le_eight_of_mem {a : ℕ} (ha : a ∈ ([1, 2, 4, 8] : List ℕ)) : a ≤ 8 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  omega

private theorem isFourth5_sound {a0 a1 a2 X q : ℕ}
    (ha0 : a0 ∈ ([1, 2, 4, 8] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 4, 8] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 4, 8] : List ℕ))
    (hX : 0 < X) (hprod : (a0 * a1 * a2) * X ^ 4 = q ^ 4) :
    isFourth5 (a0 * a1 * a2) = true := by
  have hdvd_4 : X ^ 4 ∣ q ^ 4 := ⟨a0 * a1 * a2, by
    calc q ^ 4 = (a0 * a1 * a2) * X ^ 4 := hprod.symm
      _ = X ^ 4 * (a0 * a1 * a2) := by ring⟩
  have hX_dvd_q : X ∣ q :=
    Int.natCast_dvd_natCast.mp ((Int.pow_dvd_pow_iff (by decide : 4 ≠ 0)).mp
      (Int.natCast_dvd_natCast.mpr hdvd_4))
  obtain ⟨s, hs⟩ := hX_dvd_q
  have hs_4 : a0 * a1 * a2 = s ^ 4 := by
    have hX4 : 0 < X ^ 4 := Nat.pow_pos hX
    have heq : X ^ 4 * (a0 * a1 * a2) = X ^ 4 * s ^ 4 := by
      calc X ^ 4 * (a0 * a1 * a2) = (a0 * a1 * a2) * X ^ 4 := by ring
        _ = q ^ 4 := hprod
        _ = (X * s) ^ 4 := by rw [hs]
        _ = X ^ 4 * s ^ 4 := by ring
    exact Nat.mul_left_cancel hX4 heq
  have hle0 := le_eight_of_mem ha0
  have hle1 := le_eight_of_mem ha1
  have hle2 := le_eight_of_mem ha2
  have h4_lt : s ^ 4 < 5 ^ 4 := by
    have hprod_le : a0 * a1 * a2 ≤ 8 * 8 * 8 := Nat.mul_le_mul (Nat.mul_le_mul hle0 hle1) hle2
    linarith only [hs_4, hprod_le]
  have hs_lt : s < 5 := by
    rcases lt_trichotomy s 5 with h | rfl | h
    · exact h
    · omega
    · have : 5 ^ 4 ≤ s ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
  refine anyLt_sound hs_lt ?_
  have hs_mul : s * s * s * s = a0 * a1 * a2 := by rw [hs_4]; ring
  simp [hs_mul]

private theorem checkAll3Fourths_elim {a0 a1 a2 : ℕ}
    (ha0 : a0 ∈ ([1, 2, 4, 8] : List ℕ)) (ha1 : a1 ∈ ([1, 2, 4, 8] : List ℕ))
    (ha2 : a2 ∈ ([1, 2, 4, 8] : List ℕ))
    (hf : isFourth5 (a0 * a1 * a2) = true)
    (hok : ok16Fast a0 a1 a2 = true) :
    (a0 = 1 ∧ a1 = 1 ∧ a2 = 1) ∨
    (a0 = 2 ∧ a1 = 1 ∧ a2 = 8) ∨
    (a0 = 8 ∧ a1 = 1 ∧ a2 = 2) := by
  have hc := checkAll3Fourths_true
  simp only [checkAll3Fourths, List.all_eq_true] at hc
  have hrow := hc a0 ha0 a1 ha1 a2 ha2
  simpa [hf, hok, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc, or_assoc] using hrow

/-- Obláth's theorem (`k = 3, l = 4`): no three positive integers in coprime arithmetic
progression have a product equal to a fourth power. -/
theorem no_prod_three_ap_fourth {n d q : ℕ} (hn : 0 < n) (hd : 0 < d) (hcop : Nat.Coprime n d) :
    n * (n + d) * (n + 2 * d) ≠ q ^ 4 := by
  intro heq
  have hprod : ∏ j ∈ Finset.range 3, (n + j * d) = q ^ 4 := by
    calc ∏ j ∈ Finset.range 3, (n + j * d) = n * (n + d) * (n + 2 * d) := by
          simp [Finset.prod_range_succ, mul_assoc]
      _ = q ^ 4 := heq
  obtain ⟨a0, x0, hx0, ha0, h0⟩ := ap3_fourth_splitting hn hcop (by decide : 0 < 3) hprod
  obtain ⟨a1, x1, hx1, ha1, h1⟩ := ap3_fourth_splitting hn hcop (by decide : 1 < 3) hprod
  obtain ⟨a2, x2, hx2, ha2, h2⟩ := ap3_fourth_splitting hn hcop (by decide : 2 < 3) hprod
  simp only [zero_mul, add_zero] at h0
  simp only [one_mul] at h1
  have hX_pos : 0 < x0 * x1 * x2 := by positivity
  have hprod_split : (a0 * a1 * a2) * (x0 * x1 * x2) ^ 4 = q ^ 4 := by
    calc (a0 * a1 * a2) * (x0 * x1 * x2) ^ 4
        = (a0 * x0 ^ 4) * (a1 * x1 ^ 4) * (a2 * x2 ^ 4) := by ring
      _ = n * (n + d) * (n + 2 * d) := by rw [← h0, ← h1, ← h2]
      _ = q ^ 4 := heq
  have hf := isFourth5_sound ha0 ha1 ha2 hX_pos hprod_split
  have hok := ok16Fast_sound hcop ha0 ha1 ha2 h0 h1 h2
  rcases checkAll3Fourths_elim ha0 ha1 ha2 hf hok with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp only [one_mul] at h0 h1 h2
    have hlt : x0 < x2 := by
      have h4 : x0 ^ 4 < x2 ^ 4 := by omega
      rcases lt_or_ge x0 x2 with h | h
      · exact h
      · have := Nat.pow_le_pow_left h 4; omega
    have heq_ap : x0 ^ 4 + x2 ^ 4 = 2 * x1 ^ 4 := by omega
    have hx0_eq_x2_mod2 : x0 % 2 = x2 % 2 := by
      have hx0_mod : x0 ^ 4 % 2 = x0 % 2 := by
        rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one x0 with h | h <;> simp [h]
      have hx2_mod : x2 ^ 4 % 2 = x2 % 2 := by
        rw [Nat.pow_mod]; rcases Nat.mod_two_eq_zero_or_one x2 with h | h <;> simp [h]
      have hmod := congrArg (· % 2) heq_ap
      rw [Nat.add_mod, hx0_mod, hx2_mod] at hmod
      omega
    have hx0_odd : x0 % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one x0 with hx0_2 | hx0_2
      · exfalso
        have hx2_2 : x2 % 2 = 0 := by omega
        have hn2 : 2 ∣ n := h0 ▸ dvd_pow (Nat.dvd_of_mod_eq_zero hx0_2) (by decide)
        have hn2d : 2 ∣ n + 2 * d := h2 ▸ dvd_pow (Nat.dvd_of_mod_eq_zero hx2_2) (by decide)
        have hx0_16 : 16 ∣ x0 ^ 4 := by
          obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx0_2
          exact ⟨k ^ 4, by ring⟩
        have hx2_16 : 16 ∣ x2 ^ 4 := by
          obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx2_2
          exact ⟨k ^ 4, by ring⟩
        have h2d_16 : 16 ∣ 2 * d := by
          rw [show 2 * d = x2 ^ 4 - x0 ^ 4 by omega]
          exact Nat.dvd_sub hx2_16 hx0_16
        have hd8 : 8 ∣ d := by omega
        have hd2 : 2 ∣ d := dvd_trans (by decide : 2 ∣ 8) hd8
        exact Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd hn2 hd2)
      · exact hx0_2
    have hx2_odd : x2 % 2 = 1 := by omega
    have hcop_x : Nat.Coprime x0 x2 := by
      refine Nat.coprime_of_dvd' fun p hp hp0 hp2 => ?_
      have hpn : p ∣ n := h0 ▸ dvd_pow hp0 (by decide)
      have hpn2d : p ∣ n + 2 * d := h2 ▸ dvd_pow hp2 (by decide)
      have hp2d : p ∣ 2 * d := by rw [show 2 * d = (n + 2 * d) - n by omega]; exact Nat.dvd_sub hpn2d hpn
      rcases hp.dvd_mul.mp hp2d with hp_two | hpd
      · have hp2' : p = 2 := (Nat.dvd_prime Nat.prime_two).mp hp_two |>.resolve_left hp.ne_one
        rw [hp2'] at hp0
        omega
      · exact hcop ▸ Nat.dvd_gcd hpn hpd
    exact no_three_fourth_ap hx0 hx1 hx2 hlt hx0_odd hx2_odd hcop_x heq_ap
  · simp only [one_mul] at h1
    have hd_eq : d = 4 * x2 ^ 4 - x0 ^ 4 := by omega
    have hn_even : 2 ∣ n := h0 ▸ dvd_mul_right 2 (x0 ^ 4)
    have hd_odd : d % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one d with hd2 | hd2
      · exfalso; exact Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd hn_even (Nat.dvd_of_mod_eq_zero hd2))
      · exact hd2
    have hx0_odd : x0 % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one x0 with hx02 | hx02
      · exfalso
        have h4d : x0 ^ 4 ≤ 4 * x2 ^ 4 := by omega
        have hsum_mod : (x0 ^ 4 + d) % 2 = (4 * x2 ^ 4) % 2 := by rw [hd_eq, Nat.add_sub_cancel' h4d]
        have hx04_mod : x0 ^ 4 % 2 = 0 := by
          obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx02
          have : (2 * k) ^ 4 = 2 * (8 * k ^ 4) := by ring
          omega
        omega
      · exact hx02
    have hx1_odd : x1 % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one x1 with hx12 | hx12
      · exfalso
        have hx14_even : (n + d) % 2 = 0 := by
          rw [h1]
          obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx12
          have : (2 * k) ^ 4 = 2 * (8 * k ^ 4) := by ring
          omega
        have hn0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hn_even
        omega
      · exact hx12
    have hcop_x : Nat.Coprime x0 x1 := by
      refine Nat.coprime_of_dvd' fun p _ hp0 hp1 => ?_
      have hpn : p ∣ n := h0 ▸ dvd_mul_of_dvd_right (dvd_pow hp0 (by decide)) 2
      have hpnd : p ∣ n + d := h1 ▸ dvd_pow hp1 (by decide)
      have hpd : p ∣ d := by rw [show d = (n + d) - n by omega]; exact Nat.dvd_sub hpnd hpn
      exact hcop ▸ Nat.dvd_gcd hpn hpd
    have heq' : x0 ^ 4 + 4 * x2 ^ 4 = x1 ^ 4 := by omega
    exact no_odd_coprime_fourth_add_four_fourth hx0 hx2 hx1 hx0_odd hx1_odd hcop_x heq'
  · simp only [one_mul] at h1
    have hd_eq : d = x2 ^ 4 - 4 * x0 ^ 4 := by omega
    have hn_even : 2 ∣ n := by rw [h0]; exact ⟨4 * x0 ^ 4, by ring⟩
    have hd_odd : d % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one d with hd2 | hd2
      · exfalso; exact Nat.prime_two.not_dvd_one (hcop ▸ Nat.dvd_gcd hn_even (Nat.dvd_of_mod_eq_zero hd2))
      · exact hd2
    have hx2_odd : x2 % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one x2 with hx22 | hx22
      · exfalso
        have h4x : 4 * x0 ^ 4 ≤ x2 ^ 4 := by omega
        have hsum_mod : (4 * x0 ^ 4 + d) % 2 = (x2 ^ 4) % 2 := by rw [hd_eq, Nat.add_sub_cancel' h4x]
        have hx24_mod : x2 ^ 4 % 2 = 0 := by
          obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx22
          have : (2 * k) ^ 4 = 2 * (8 * k ^ 4) := by ring
          omega
        omega
      · exact hx22
    have hx1_odd : x1 % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one x1 with hx12 | hx12
      · exfalso
        have hx14_even : (n + d) % 2 = 0 := by
          rw [h1]
          obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hx12
          have : (2 * k) ^ 4 = 2 * (8 * k ^ 4) := by ring
          omega
        have hn0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd hn_even
        omega
      · exact hx12
    have hcop_x : Nat.Coprime x2 x1 := by
      refine Nat.coprime_of_dvd' fun p _ hp2 hp1 => ?_
      have hpn2d : p ∣ n + 2 * d := h2 ▸ dvd_mul_of_dvd_right (dvd_pow hp2 (by decide)) 2
      have hpnd : p ∣ n + d := h1 ▸ dvd_pow hp1 (by decide)
      have hpd : p ∣ d := by rw [show d = (n + 2 * d) - (n + d) by omega]; exact Nat.dvd_sub hpn2d hpnd
      have hpn : p ∣ n := by rw [show n = (n + d) - d by omega]; exact Nat.dvd_sub hpnd hpd
      exact hcop ▸ Nat.dvd_gcd hpn hpd
    have heq' : x2 ^ 4 + 4 * x0 ^ 4 = x1 ^ 4 := by omega
    exact no_odd_coprime_fourth_add_four_fourth hx2 hx0 hx1 hx2_odd hx1_odd hcop_x heq'

private theorem finset_ap_prod_three {s : Finset ℕ} {n d : ℕ} (hd : 0 < d)
    (hap : ENat.card (s : Set ℕ) = (3 : ℕ∞) ∧
      (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (3 : ℕ∞))}) :
    ∏ x ∈ s, x = n * (n + d) * (n + 2 * d) := by
  have hs_eq : s = (Finset.range 3).image (fun i => n + i * d) := by
    ext x
    have hmem : x ∈ (s : Set ℕ) ↔ ∃ i : ℕ, (i : ℕ∞) < (3 : ℕ∞) ∧ n + i • d = x := by
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

/-- Bridge theorem matching the `Erdos672With 3 4` conjunct of
`Erdos672.erdos_672.variants.oblath` definitionally. -/
theorem oblath_k3_l4_bridge :
    ∀ (s : Finset ℕ), s.card = 3 → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
      (ENat.card (s : Set ℕ) = (3 : ℕ∞) ∧
        (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (3 : ℕ∞))}) →
      ∀ q, ∏ i ∈ s, i ≠ q ^ 4 := by
  intro s _ n hn d hd hcop hap q heq
  rw [finset_ap_prod_three hd hap] at heq
  exact no_prod_three_ap_fourth hn hd hcop heq

/-- Generalization of Obláth's `k = 3, l = 4` theorem to all multiples `l = 4 * m` (`m ≥ 1`). -/
theorem oblath_k3_mult4_l_bridge {m : ℕ} (_hm : 0 < m) :
    ∀ (s : Finset ℕ), s.card = 3 → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
      (ENat.card (s : Set ℕ) = (3 : ℕ∞) ∧
        (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (3 : ℕ∞))}) →
      ∀ q, ∏ i ∈ s, i ≠ q ^ (4 * m) := by
  intro s hs n hn d hd hcop hap q heq
  apply oblath_k3_l4_bridge s hs n hn d hd hcop hap (q ^ m)
  rw [heq, pow_mul']

end Contribution.Erdos672OblathK3L4
