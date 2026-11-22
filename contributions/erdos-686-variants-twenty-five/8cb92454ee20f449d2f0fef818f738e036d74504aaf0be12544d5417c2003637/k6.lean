import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Unconditional Exclusion of k = 6 for Erdős Problem #686 (N = 25)

Proves via scaled polynomial square-completion (`4 * P_6(x) = (2x^3 - 35x)^2 - (189x^2 + 900)`),
Taylor-shift positivity for `n ≥ 54`, and kernel-checked finite bracketing for `0 ≤ n ≤ 53` that
no natural numbers `m, n : ℕ` (even without disjointness) satisfy
`∏ i ∈ Finset.Icc 1 6, (m + i) = 25 * ∏ i ∈ Finset.Icc 1 6, (n + i)` or the corresponding
rational quotient equation `(25 : ℚ) = (∏ i ∈ Finset.Icc 1 6, (m + i)) / (∏ i ∈ Finset.Icc 1 6, (n + i))`.
-/

namespace Contribution.Erdos686SixTwentyFive

def P6 (x : ℕ) : ℕ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25)

def P6Z (x : ℤ) : ℤ := (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25)
def Q6Z (x : ℤ) : ℤ := 2 * x ^ 3 - 35 * x
def R6Z (x : ℤ) : ℤ := -189 * x ^ 2 - 900

private lemma mul_lt_mul_nat {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hd : 0 < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hcd))
    (Nat.mul_lt_mul_of_pos_right hab hd)

private lemma P6_strictMono {a b : ℕ} (ha : 5 ≤ a) (hab : a < b) : P6 a < P6 b := by
  have hb : 5 ≤ b := by omega
  have hab2 : a * a < b * b := mul_lt_mul_nat hab hab (by omega)
  have ha2 : 25 ≤ a * a := Nat.mul_le_mul ha ha
  have hb2 : 25 < b * b := Nat.lt_of_le_of_lt ha2 hab2
  have h1 : a * a - 1 < b * b - 1 := by omega
  have h9 : a * a - 9 < b * b - 9 := by omega
  have h25 : a * a - 25 < b * b - 25 := by omega
  have h12 : (a * a - 1) * (a * a - 9) < (b * b - 1) * (b * b - 9) :=
    mul_lt_mul_nat h1 h9 (by omega)
  exact mul_lt_mul_nat h12 h25 (by omega)

private lemma P6_mono {a b : ℕ} (ha : 5 ≤ a) (hab : a ≤ b) : P6 a ≤ P6 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P6_strictMono ha hlt)

private lemma P6_cast {x : ℕ} (hx : 5 ≤ x) : (P6 x : ℤ) = P6Z (x : ℤ) := by
  have h25 : 25 ≤ x * x := Nat.mul_le_mul hx hx
  have h9 : 9 ≤ x * x := by omega
  have h1 : 1 ≤ x * x := by omega
  dsimp only [P6, P6Z]
  zify [h1, h9, h25]
  ring

private lemma P6Z_strictMono {a b : ℤ} (ha : 5 ≤ a) (hab : a < b) : P6Z a < P6Z b := by
  have hlt : P6 a.toNat < P6 b.toNat := P6_strictMono (by omega) (by omega)
  have hza : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hzb : (b.toNat : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hca := P6_cast (x := a.toNat) (by omega)
  have hcb := P6_cast (x := b.toNat) (by omega)
  rw [← hza, ← hzb, ← hca, ← hcb]
  exact Int.ofNat_lt.mpr hlt

private lemma P6Z_mono {a b : ℤ} (ha : 5 ≤ a) (hab : a ≤ b) : P6Z a ≤ P6Z b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P6Z_strictMono ha hlt)

private lemma prod6_midpoint (m : ℕ) :
    2 ^ 6 * (∏ i ∈ Finset.Icc 1 6, (m + i)) = P6 (2 * m + 7) := by
  have hIcc : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  zify
  rw [P6_cast (by omega)]
  dsimp only [P6Z]
  push_cast
  ring

private lemma prod6_range_eq_Icc (m : ℕ) :
    (∏ i ∈ Finset.range 6, (m + i + 1)) = ∏ i ∈ Finset.Icc 1 6, (m + i) := by
  have hIcc : Finset.Icc 1 6 = (Finset.range 6).image (· + 1) := by decide
  rw [hIcc, Finset.prod_image (fun a _ b _ hab => by omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ### Finite Bracket Verification for 0 ≤ n ≤ 53 -/

def findBracket6 (v : ℕ) : ℕ :=
  let rhs := 25 * P6 v
  let u0 := 2 * ((v * 17099759) / 20000000) + 1
  if P6 u0 < rhs then
    let u1 := u0 + 2
    if P6 u1 < rhs then u1 + 2 else u1
  else
    u0

def check6_v (v : ℕ) : Bool :=
  let rhs := 25 * P6 v
  let u := findBracket6 v
  decide (u ≥ 7 ∧ u % 2 = 1 ∧ P6 (u - 2) < rhs ∧ rhs < P6 u)

def checkBase6 : ℕ → Bool
  | 0 => check6_v 7
  | n + 1 => check6_v (2 * (n + 1) + 7) && checkBase6 n

private lemma check6_v_sound {v : ℕ} (hc : check6_v v = true) :
    ∀ m : ℕ, P6 (2 * m + 7) ≠ 25 * P6 v := by
  simp only [check6_v, decide_eq_true_eq] at hc
  rcases hc with ⟨hu7, hu_odd, hlo, hhi⟩
  intro m heq
  set u := findBracket6 v
  set x := 2 * m + 7
  by_cases hxu : x < u
  · have hle : x ≤ u - 2 := by omega
    have hpm : P6 x ≤ P6 (u - 2) := P6_mono (by omega) hle
    omega
  · have hge : u ≤ x := by omega
    have hpm : P6 u ≤ P6 x := P6_mono (by omega) hge
    omega

private lemma checkBase6_sound {N : ℕ} (h : checkBase6 N = true) :
    ∀ n ≤ N, ∀ m : ℕ, P6 (2 * m + 7) ≠ 25 * P6 (2 * n + 7) := by
  induction N with
  | zero =>
    intro n hn m
    have : n = 0 := by omega
    subst this
    exact check6_v_sound h m
  | succ k ih =>
    simp only [checkBase6, Bool.and_eq_true] at h
    intro n hn m
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · exact check6_v_sound h.1 m
    · exact ih h.2 n (by omega) m

private theorem base6_ok : checkBase6 53 = true := by decide +kernel

/-! ### Asymptotic Exclusion for n ≥ 54 (v ≥ 115) -/

private lemma P6Z_sq (x : ℤ) : 4 * P6Z x = Q6Z x ^ 2 + R6Z x := by
  dsimp only [P6Z, Q6Z, R6Z]
  ring

private lemma Q6Z_pos {v : ℤ} (hv : 7 ≤ v) : 0 < Q6Z v := by
  have ht : 0 ≤ v - 7 := by omega
  have hid : Q6Z v = 2 * (v - 7) ^ 3 + 42 * (v - 7) ^ 2 + 259 * (v - 7) + 441 := by
    dsimp only [Q6Z]; ring
  rw [hid]
  positivity

private lemma Q6Z_odd (k : ℤ) : Q6Z (2 * k + 1) % 2 = 1 := by
  dsimp only [Q6Z]
  have : 2 * (2 * k + 1) ^ 3 - 35 * (2 * k + 1) =
      2 * (8 * k ^ 3 + 12 * k ^ 2 - 29 * k - 17) + 1 := by ring
  rw [this]
  omega

private lemma P6Z_2v_gt {v : ℤ} (hv : 7 ≤ v) : 25 * P6Z v < P6Z (2 * v) := by
  have ht : 0 ≤ v - 7 := by omega
  have hid : P6Z (2 * v) - 25 * P6Z v =
      39 * (v - 7) ^ 6 + 1638 * (v - 7) ^ 5 + 28980 * (v - 7) ^ 4 + 276360 * (v - 7) ^ 3 +
      1491756 * (v - 7) ^ 2 + 4288872 * (v - 7) + 5083515 := by
    dsimp only [P6Z]; ring
  linarith [show 0 < P6Z (2 * v) - 25 * P6Z v by rw [hid]; positivity]

private lemma poly6_pos {v : ℤ} (hv : 115 ≤ v) : 0 < 20 * Q6Z v + 24 * R6Z v - 4 := by
  have ht : 0 ≤ v - 115 := by omega
  have hid : 20 * Q6Z v + 24 * R6Z v - 4 =
      40 * (v - 115) ^ 3 + 9264 * (v - 115) ^ 2 + 543020 * (v - 115) + 744296 := by
    dsimp only [Q6Z, R6Z]; ring
  rw [hid]
  positivity

private lemma asymp6_impossible {m n : ℕ} (hnm : n < m) (hn : 54 ≤ n)
    (heq : P6 (2 * m + 7) = 25 * P6 (2 * n + 7)) : False := by
  set u : ℤ := 2 * (m : ℤ) + 7
  set v : ℤ := 2 * (n : ℤ) + 7
  have hv115 : 115 ≤ v := by omega
  have hv7 : 7 ≤ v := by omega
  have huv : v < u := by omega
  have hu5 : 5 ≤ u := by omega
  have heqZ : P6Z u = 25 * P6Z v := by
    have h1 := P6_cast (x := 2 * m + 7) (by omega)
    have h2 := P6_cast (x := 2 * n + 7) (by omega)
    have h3 : ((P6 (2 * m + 7) : ℕ) : ℤ) = ((25 * P6 (2 * n + 7) : ℕ) : ℤ) := by exact_mod_cast heq
    push_cast at h1 h2 h3
    linarith
  have hu_lt_2v : u < 2 * v := by
    by_contra hge
    push Not at hge
    have hmono := P6Z_mono (by omega) hge
    have h2v := P6Z_2v_gt hv7
    linarith
  have hsq_diff : (5 * Q6Z v) ^ 2 - Q6Z u ^ 2 = -25 * R6Z v + R6Z u := by
    have hsu := P6Z_sq u
    have hsv := P6Z_sq v
    nlinarith
  have hR_pos : 0 < -25 * R6Z v + R6Z u := by
    have h1 : -25 * R6Z v + R6Z u = 189 * (25 * v ^ 2 - u ^ 2) + 21600 := by
      dsimp only [R6Z]; ring
    have h2 : u ^ 2 < (2 * v) ^ 2 := by nlinarith
    rw [h1]
    nlinarith
  have hR_ub : -25 * R6Z v + R6Z u < -24 * R6Z v := by
    have h1 : -25 * R6Z v + R6Z u - (-24 * R6Z v) = -189 * (u ^ 2 - v ^ 2) := by
      dsimp only [R6Z]; ring
    have h2 : v ^ 2 < u ^ 2 := by nlinarith
    linarith
  have hQu_pos : 0 < Q6Z u := Q6Z_pos (by omega)
  have hQv_pos : 0 < Q6Z v := Q6Z_pos hv7
  have hdiff_pos : 0 < 5 * Q6Z v - Q6Z u := by
    have hmul : (5 * Q6Z v - Q6Z u) * (5 * Q6Z v + Q6Z u) = (5 * Q6Z v) ^ 2 - Q6Z u ^ 2 := by ring
    nlinarith
  have hdiff_even : (5 * Q6Z v - Q6Z u) % 2 = 0 := by
    have hov : Q6Z v % 2 = 1 := by
      have : v = 2 * ((n : ℤ) + 3) + 1 := by ring
      rw [this]; exact Q6Z_odd _
    have hou : Q6Z u % 2 = 1 := by
      have : u = 2 * ((m : ℤ) + 3) + 1 := by ring
      rw [this]; exact Q6Z_odd _
    omega
  set d : ℤ := (5 * Q6Z v - Q6Z u) / 2
  have hd_eq : 5 * Q6Z v - Q6Z u = 2 * d := by omega
  have hd_ge1 : 1 ≤ d := by omega
  have hprod_d : 2 * d * (10 * Q6Z v - 2 * d) = -25 * R6Z v + R6Z u := by
    have : 2 * d * (10 * Q6Z v - 2 * d) = (5 * Q6Z v) ^ 2 - Q6Z u ^ 2 := by
      rw [← hd_eq]; ring
    linarith
  have hd_lt : d < 5 * Q6Z v - 1 := by
    have : 2 * d < 5 * Q6Z v := by omega
    linarith
  have hquad_d : 2 * (10 * Q6Z v - 2) ≤ 2 * d * (10 * Q6Z v - 2 * d) := by
    have hid : 2 * d * (10 * Q6Z v - 2 * d) - 2 * (10 * Q6Z v - 2) =
        4 * (d - 1) * (5 * Q6Z v - d - 1) := by ring
    have h1 : 0 ≤ d - 1 := by omega
    have h2 : 0 < 5 * Q6Z v - d - 1 := by omega
    nlinarith
  have hpoly_neg : 20 * Q6Z v + 24 * R6Z v - 4 < 0 := by linarith
  have hpoly_pos : 0 < 20 * Q6Z v + 24 * R6Z v - 4 := poly6_pos hv115
  linarith

/-! ### Main Theorems -/

private lemma prod6_pos (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 6, (n + i) := by
  have hP7 : 0 < P6 7 := by decide
  have hPpos : 0 < P6 (2 * n + 7) := lt_of_lt_of_le hP7 (P6_mono (by omega) (by omega))
  linarith [prod6_midpoint n]

/-- Unconditional length-6 product exclusion for ratio 25 (no disjointness hypothesis needed). -/
theorem length_six (m n : ℕ) :
    (∏ i ∈ Finset.Icc 1 6, (m + i)) ≠ 25 * (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  intro heq
  have hmid : P6 (2 * m + 7) = 25 * P6 (2 * n + 7) := by
    have hm := prod6_midpoint m
    have hn := prod6_midpoint n
    have hmul : 2 ^ 6 * (∏ i ∈ Finset.Icc 1 6, (m + i)) =
        25 * (2 ^ 6 * (∏ i ∈ Finset.Icc 1 6, (n + i))) := by
      calc 2 ^ 6 * (∏ i ∈ Finset.Icc 1 6, (m + i))
          = 2 ^ 6 * (25 * (∏ i ∈ Finset.Icc 1 6, (n + i))) := by rw [heq]
        _ = 25 * (2 ^ 6 * (∏ i ∈ Finset.Icc 1 6, (n + i))) := by ring
    linarith
  have hnm : n < m := by
    by_contra hle
    have hmono : P6 (2 * m + 7) ≤ P6 (2 * n + 7) := P6_mono (by omega) (by omega)
    have hpos : 0 < P6 (2 * n + 7) := by
      have : 0 < ∏ i ∈ Finset.Icc 1 6, (n + i) := prod6_pos n
      linarith [prod6_midpoint n]
    omega
  by_cases hn54 : 54 ≤ n
  · exact asymp6_impossible hnm hn54 hmid
  · exact checkBase6_sound base6_ok n (by omega) m hmid

/-- Exclusion of ratio 25 for length-6 consecutive blocks with `m ≥ n + 6` (`Finset.Icc` form). -/
theorem erdos686_n25_k6_Icc :
    ¬ ∃ (m n : ℕ), m ≥ n + 6 ∧ (∏ i ∈ Finset.Icc 1 6, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  rintro ⟨m, n, _, heq⟩
  exact length_six m n heq

/-- Exclusion of ratio 25 for length-6 consecutive blocks with `m ≥ n + 6` (`Finset.range` form). -/
theorem erdos686_n25_k6_range :
    ¬ ∃ (m n : ℕ), m ≥ n + 6 ∧
      (∏ i ∈ Finset.range 6, (m + i + 1)) = 25 * (∏ i ∈ Finset.range 6, (n + i + 1)) := by
  rintro ⟨m, n, hmn, heq⟩
  rw [prod6_range_eq_Icc m, prod6_range_eq_Icc n] at heq
  exact length_six m n heq

/-- Direct interface to the `k = 6` case of `Erdos686.erdos_686.variants.twenty_five` (no disjointness needed). -/
theorem no_ratio_twenty_five_six (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 6, (m + i)) / (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  intro h
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 6, (n + i) := prod6_pos n
  have hd : ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hz := (eq_div_iff hd).mp h
  have hn : 25 * (∏ i ∈ Finset.Icc 1 6, (n + i)) = ∏ i ∈ Finset.Icc 1 6, (m + i) := by
    exact_mod_cast hz
  exact length_six m n hn.symm

/-- Existential target-shaped exclusion for `k = 6` matching `FormalConjectures.ErdosProblems.«686»`. -/
theorem no_sol_twenty_five_six :
    ¬ ∃ (n : ℕ), ∃ m ≥ n + 6,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 6, (m + i)) / (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  rintro ⟨n, m, _, h⟩
  exact no_ratio_twenty_five_six m n h

end Contribution.Erdos686SixTwentyFive
