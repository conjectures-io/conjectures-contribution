import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Cast.Order
import Init.Data.Nat.Coprime

/-! Algebraic reduction of the length-five case of Erdős 686.
This gives necessary conditions, not an exclusion or a rational-point completeness claim. -/
namespace Contribution.Erdos686Five

def F (t : ℤ) : ℤ := t ^ 5 - 5 * t ^ 3 + 4 * t
def A (R u v : ℤ) : ℤ := v ^ 5 - R * u ^ 5
def B (R u v : ℤ) : ℤ := v ^ 3 - R * u ^ 3
def C (R u v : ℤ) : ℤ := v - R * u
def Q (R u v : ℤ) : ℤ :=
  9 * v ^ 6 + 16 * R * v ^ 5 * u - 50 * R * v ^ 3 * u ^ 3 +
    16 * R * v * u ^ 5 + 9 * R ^ 2 * u ^ 6

theorem centered_product (m : ℤ) :
    (m + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) = F (m + 3) := by
  unfold F
  ring

theorem scaled_identity (R g u v : ℤ) :
    F (g * v) - R * F (g * u) =
      g * (A R u v * g ^ 4 - 5 * B R u v * g ^ 2 + 4 * C R u v) := by
  unfold F A B C
  ring

theorem discriminant_identity (R u v : ℤ) :
    25 * B R u v ^ 2 - 16 * A R u v * C R u v = Q R u v := by
  unfold A B C Q
  ring

/-- The sign of W is chosen explicitly, so recovery uses the plus sign. -/
theorem integral_reduction (R g u v : ℤ) (hg : g ≠ 0)
    (h : F (g * v) = R * F (g * u)) :
    ∃ W : ℤ, W = 2 * A R u v * g ^ 2 - 5 * B R u v ∧
      W ^ 2 = Q R u v ∧
      2 * A R u v * g ^ 2 = 5 * B R u v + W ∧
      g ^ 2 ∣ 4 * C R u v := by
  have hquad : A R u v * g ^ 4 - 5 * B R u v * g ^ 2 + 4 * C R u v = 0 := by
    have hz : g * (A R u v * g ^ 4 - 5 * B R u v * g ^ 2 + 4 * C R u v) = 0 := by
      rw [← scaled_identity, h, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left hg
  refine ⟨2 * A R u v * g ^ 2 - 5 * B R u v, rfl, ?_, ?_, ?_⟩
  · calc
      (2 * A R u v * g ^ 2 - 5 * B R u v) ^ 2 =
          (25 * B R u v ^ 2 - 16 * A R u v * C R u v) +
          4 * A R u v * (A R u v * g ^ 4 - 5 * B R u v * g ^ 2 + 4 * C R u v) := by ring
      _ = Q R u v := by rw [hquad, discriminant_identity]; ring
  · ring
  · refine ⟨5 * B R u v - A R u v * g ^ 2, ?_⟩
    nlinarith only [hquad]

/-- For either ratio, the quadratic leading coefficient does not vanish on primitive pairs. -/
theorem A_ne_zero (R u v : ℕ) (hR : R = 4 ∨ R = 25) (huv : Nat.Coprime u v) :
    A R u v ≠ 0 := by
  intro h
  have he : v ^ 5 = R * u ^ 5 := by
    have hz : (v : ℤ) ^ 5 = R * (u : ℤ) ^ 5 := sub_eq_zero.mp h
    exact_mod_cast hz
  have hd : u ∣ v ^ 5 := by
    rw [he]
    exact dvd_mul_of_dvd_right (dvd_pow_self u (by decide : 5 ≠ 0)) R
  have hu : u = 1 := (huv.pow_right 5).eq_one_of_dvd hd
  rw [hu] at he
  norm_num at he
  have hv : v < 2 := by
    by_contra hh
    have hge : 2 ≤ v := by omega
    have hp : 32 ≤ v ^ 5 := by
      calc
        32 = (2 : ℕ) ^ 5 := by norm_num
        _ ≤ v ^ 5 := Nat.pow_le_pow_left hge 5
    rcases hR with rfl | rfl <;> omega
  have hv_cases : v = 0 ∨ v = 1 := by omega
  rcases hR with rfl | rfl <;> rcases hv_cases with rfl | rfl <;> norm_num at he

/-- The affine rational curve associated with the homogeneous sextic Q. -/
def Curve (R t z : ℚ) : Prop :=
  z ^ 2 = 9 * t ^ 6 + 16 * R * t ^ 5 - 50 * R * t ^ 3 + 16 * R * t + 9 * R ^ 2

theorem rational_point (R u v W : ℤ) (hu : u ≠ 0) (hW : W ^ 2 = Q R u v) :
    Curve R ((v : ℚ) / u) ((W : ℚ) / (u : ℚ) ^ 3) := by
  have huq : (u : ℚ) ≠ 0 := by exact_mod_cast hu
  have ht : (v : ℚ) / u * u = v := div_mul_cancel₀ _ huq
  have hw : (W : ℚ) / (u : ℚ) ^ 3 * (u : ℚ) ^ 3 = W :=
    div_mul_cancel₀ _ (pow_ne_zero 3 huq)
  have hq : (W : ℚ) ^ 2 =
      9 * (v : ℚ) ^ 6 + 16 * R * (v : ℚ) ^ 5 * u -
      50 * R * (v : ℚ) ^ 3 * (u : ℚ) ^ 3 +
      16 * R * v * (u : ℚ) ^ 5 + 9 * (R : ℚ) ^ 2 * (u : ℚ) ^ 6 := by
    unfold Q at hW
    exact_mod_cast hW
  unfold Curve
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show
      (((W : ℚ) / (u : ℚ) ^ 3) ^ 2 -
        (9 * ((v : ℚ) / u) ^ 6 + 16 * R * ((v : ℚ) / u) ^ 5 -
        50 * R * ((v : ℚ) / u) ^ 3 + 16 * R * ((v : ℚ) / u) + 9 * (R : ℚ) ^ 2)) *
        (u : ℚ) ^ 6 = 0 from ?_)).resolve_right (pow_ne_zero 6 huq)
  calc
    _ = ((W : ℚ) / (u : ℚ) ^ 3 * (u : ℚ) ^ 3) ^ 2 -
        (9 * ((v : ℚ) / u * u) ^ 6 + 16 * R * ((v : ℚ) / u * u) ^ 5 * u -
        50 * R * ((v : ℚ) / u * u) ^ 3 * (u : ℚ) ^ 3 +
        16 * R * ((v : ℚ) / u * u) * (u : ℚ) ^ 5 + 9 * (R : ℚ) ^ 2 * (u : ℚ) ^ 6) := by ring
    _ = 0 := by rw [ht, hw, hq, sub_self]

theorem square_recovery (R g u v W : ℤ) (hA : A R u v ≠ 0)
    (hW : 2 * A R u v * g ^ 2 = 5 * B R u v + W) :
    (g : ℚ) ^ 2 = (5 * (B R u v : ℚ) + W) / (2 * (A R u v : ℚ)) := by
  have ha : (A R u v : ℚ) ≠ 0 := by exact_mod_cast hA
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
  have hq : (2 : ℚ) * (A R u v : ℚ) * (g : ℚ) ^ 2 = 5 * (B R u v : ℚ) + W := by
    exact_mod_cast hW
  nlinarith only [hq]

/-- A sextic point with the specified integral recovery reconstructs the product equality.
Positivity and disjointness must still be checked separately. -/
theorem integral_reconstruction (R g u v W : ℤ) (hA : A R u v ≠ 0)
    (hs : W ^ 2 = Q R u v)
    (hr : 2 * A R u v * g ^ 2 = 5 * B R u v + W) :
    F (g * v) = R * F (g * u) := by
  have hw : 2 * A R u v * g ^ 2 - 5 * B R u v = W := by omega
  have hf : 4 * A R u v *
      (A R u v * g ^ 4 - 5 * B R u v * g ^ 2 + 4 * C R u v) = 0 := by
    calc
      _ = (2 * A R u v * g ^ 2 - 5 * B R u v) ^ 2 - Q R u v := by
        rw [← discriminant_identity]
        ring
      _ = 0 := by rw [hw, hs, sub_self]
  have hquad := (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (by norm_num) hA)
  apply sub_eq_zero.mp
  rw [scaled_identity, hquad, mul_zero]

/-- Necessary data retained from a solution, including positivity and the block gap. -/
structure ReductionData (R m n g u v : ℕ) (W : ℤ) : Prop where
  g_pos : 0 < g
  u_pos : 0 < u
  v_pos : 0 < v
  coprime : Nat.Coprime u v
  gcd_eq : g = Nat.gcd (m + 3) (n + 3)
  upper_eq : m + 3 = g * v
  lower_eq : n + 3 = g * u
  lower_bound : 3 ≤ g * u
  gap : g * u + 5 ≤ g * v
  leading_ne_zero : A R u v ≠ 0
  W_eq : W = 2 * A R u v * (g : ℤ) ^ 2 - 5 * B R u v
  sextic : W ^ 2 = Q R u v
  recovery : (g : ℚ) ^ 2 = (5 * (B R u v : ℚ) + W) / (2 * (A R u v : ℚ))
  divisibility : (g : ℤ) ^ 2 ∣ 4 * C R u v
  rational_point : Curve R ((v : ℚ) / u) ((W : ℚ) / (u : ℚ) ^ 3)

/-- Direct bridge from the pinned target's ratio at k = 5 to the sextic curve. -/
theorem length_five_reduction (R m n : ℕ) (hR : R = 4 ∨ R = 25)
    (hgap : n + 5 ≤ m)
    (h : (R : ℚ) = (∏ i ∈ Finset.Icc 1 5, (m + i)) /
      (∏ i ∈ Finset.Icc 1 5, (n + i))) :
    ∃ g u v : ℕ, ∃ W : ℤ, ReductionData R m n g u v W := by
  have hprod : F ((m : ℤ) + 3) = R * F ((n : ℤ) + 3) := by
    norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, Finset.prod_singleton] at h
    have hd : ((n : ℚ) + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5) ≠ 0 := by
      positivity
    have he := (eq_div_iff hd).mp h
    have hz : (R : ℤ) * (((n : ℤ) + 1) * (n + 2) * (n + 3) * (n + 4) * (n + 5)) =
        ((m : ℤ) + 1) * (m + 2) * (m + 3) * (m + 4) * (m + 5) := by
      exact_mod_cast he
    rw [centered_product, centered_product] at hz
    exact hz.symm
  let g := Nat.gcd (m + 3) (n + 3)
  let v := (m + 3) / g
  let u := (n + 3) / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hv : 0 < v := Nat.div_gcd_pos_of_pos_left _ (by omega)
  have hu : 0 < u := Nat.div_gcd_pos_of_pos_right _ (by omega)
  have hc : Nat.Coprime u v := (Nat.coprime_div_gcd_div_gcd hg).symm
  have hx : m + 3 = g * v := by
    dsimp [v, g]
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  have hy : n + 3 = g * u := by
    dsimp [u, g]
    rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
  have hxz : (m : ℤ) + 3 = (g : ℤ) * v := by exact_mod_cast hx
  have hyz : (n : ℤ) + 3 = (g : ℤ) * u := by exact_mod_cast hy
  rw [hxz, hyz] at hprod
  have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hg)
  have huz : (u : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu)
  obtain ⟨W, hW, hs, hr, hd⟩ := integral_reduction R g u v hgz hprod
  have ha := A_ne_zero R u v hR hc
  refine ⟨g, u, v, W, ?_⟩
  exact {
    g_pos := hg
    u_pos := hu
    v_pos := hv
    coprime := hc
    gcd_eq := rfl
    upper_eq := hx
    lower_eq := hy
    lower_bound := by omega
    gap := by omega
    leading_ne_zero := ha
    W_eq := hW
    sextic := hs
    recovery := by simpa only [Int.cast_natCast] using square_recovery R g u v W ha hr
    divisibility := hd
    rational_point := by simpa only [Int.cast_natCast] using rational_point R u v W huz hs
  }

theorem ratio_four_reduction (m n : ℕ) (hgap : n + 5 ≤ m)
    (h : (4 : ℚ) = (∏ i ∈ Finset.Icc 1 5, (m + i)) /
      (∏ i ∈ Finset.Icc 1 5, (n + i))) :
    ∃ g u v : ℕ, ∃ W : ℤ, ReductionData 4 m n g u v W :=
  length_five_reduction 4 m n (Or.inl rfl) hgap h

theorem ratio_twenty_five_reduction (m n : ℕ) (hgap : n + 5 ≤ m)
    (h : (25 : ℚ) = (∏ i ∈ Finset.Icc 1 5, (m + i)) /
      (∏ i ∈ Finset.Icc 1 5, (n + i))) :
    ∃ g u v : ℕ, ∃ W : ℤ, ReductionData 25 m n g u v W :=
  length_five_reduction 25 m n (Or.inr rfl) hgap h

end Contribution.Erdos686Five
