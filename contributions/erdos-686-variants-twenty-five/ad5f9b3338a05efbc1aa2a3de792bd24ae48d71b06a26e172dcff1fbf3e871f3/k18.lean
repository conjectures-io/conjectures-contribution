import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Rat.Cast.Order

/-!
# Unconditional Exclusion of k = 18 for Erdős Problem #686 (N = 25)

Proves via scaled polynomial square-completion (`16384 * P_18(x) = Q_18(x)^2 + R_18(x)`, `S = 128`),
modular congruence (`162 ∣ 5 * Q_18(v) - Q_18(u)` for odd `u, v`), 4-zone `d`-pinching (`Base`,
`Zone 2`, `Zone 1B`, `Zone 1A`), Taylor-shift positivity, and a unified kernel check (`cert18_ok`,
`decide +kernel`), that no integers `m ≥ n + 18` satisfy
`∏ i ∈ Finset.range 18, (m + i + 1) = 25 * ∏ i ∈ Finset.range 18, (n + i + 1)`.
-/

namespace Contribution.Erdos686EighteenTwentyFive

def P18 (x : ℕ) : ℕ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) *
    (x2 - 121) * (x2 - 169) * (x2 - 225) * (x2 - 289)

def P18Z (x : ℤ) : ℤ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) *
    (x2 - 121) * (x2 - 169) * (x2 - 225) * (x2 - 289)

def Q18Z (x : ℤ) : ℤ :=
  128 * x ^ 9 - 62016 * x ^ 7 + 9038832 * x ^ 5 - 439659848 * x ^ 3 + 3788405307 * x

def R18Z (x : ℤ) : ℤ :=
  -78397083729792 * x ^ 8 + 16673477276146464 * x ^ 6 - 945705074655002832 * x ^ 4 + 9110023357135451751 * x ^ 2 - 19455213098280960000

def Q18_s10 (X : ℤ) : ℤ :=
  128 * X ^ 9 - 6201600000000000000000000 * X ^ 7 + 90388320000000000000000000000000000000000000000 * X ^ 5 - 439659848000000000000000000000000000000000000000000000000000000000000 * X ^ 3 + 378840530700000000000000000000000000000000000000000000000000000000000000000000000000000000 * X

def negR18_s10 (X : ℤ) : ℤ :=
  78397083729792 * X ^ 8 - 1667347727614646400000000000000000000 * X ^ 6 + 9457050746550028320000000000000000000000000000000000000000 * X ^ 4 - 9110023357135451751000000000000000000000000000000000000000000000000000000000000 * X ^ 2 + 1945521309828096000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private lemma mul_lt_mul_nat {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hd : 0 < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hcd))
    (Nat.mul_lt_mul_of_pos_right hab hd)

private lemma P18_strictMono {a b : ℕ} (ha : 17 ≤ a) (hab : a < b) : P18 a < P18 b := by
  have hb : 17 ≤ b := by omega
  have hab2 : a * a < b * b := mul_lt_mul_nat hab hab (by omega)
  have ha2 : 289 ≤ a * a := Nat.mul_le_mul ha ha
  dsimp only [P18]
  have p1 := mul_lt_mul_nat (by omega : a * a - 1 < b * b - 1) (by omega : a * a - 9 < b * b - 9) (by omega)
  have p2 := mul_lt_mul_nat p1 (by omega : a * a - 25 < b * b - 25) (by omega)
  have p3 := mul_lt_mul_nat p2 (by omega : a * a - 49 < b * b - 49) (by omega)
  have p4 := mul_lt_mul_nat p3 (by omega : a * a - 81 < b * b - 81) (by omega)
  have p5 := mul_lt_mul_nat p4 (by omega : a * a - 121 < b * b - 121) (by omega)
  have p6 := mul_lt_mul_nat p5 (by omega : a * a - 169 < b * b - 169) (by omega)
  have p7 := mul_lt_mul_nat p6 (by omega : a * a - 225 < b * b - 225) (by omega)
  exact mul_lt_mul_nat p7 (by omega : a * a - 289 < b * b - 289) (by omega)

private lemma P18_mono {a b : ℕ} (ha : 17 ≤ a) (hab : a ≤ b) : P18 a ≤ P18 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P18_strictMono ha hlt)

private lemma P18_cast {x : ℕ} (hx : 17 ≤ x) : (P18 x : ℤ) = P18Z (x : ℤ) := by
  have h289 : 289 ≤ x * x := Nat.mul_le_mul hx hx
  dsimp only [P18, P18Z]
  zify [show 1 ≤ x * x by omega, show 9 ≤ x * x by omega, show 25 ≤ x * x by omega,
    show 49 ≤ x * x by omega, show 81 ≤ x * x by omega, show 121 ≤ x * x by omega,
    show 169 ≤ x * x by omega, show 225 ≤ x * x by omega, h289]

private lemma prod18_midpoint (m : ℕ) :
    2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (m + i)) = P18 (2 * m + 19) := by
  have hIcc : Finset.Icc 1 18 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  zify
  rw [P18_cast (by omega)]
  dsimp only [P18Z]
  push_cast
  ring

private lemma prod18_range_eq_Icc (m : ℕ) :
    (∏ i ∈ Finset.range 18, (m + i + 1)) = ∏ i ∈ Finset.Icc 1 18, (m + i) := by
  have hIcc : Finset.Icc 1 18 = (Finset.range 18).image (· + 1) := by decide
  rw [hIcc, Finset.prod_image (fun a _ b _ hab => by omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ## 1. 4-Zone Kernel Certificate Verification -/

def findBracket18 (v : ℕ) : ℕ :=
  let rhs := 25 * P18 v
  let u0 := 2 * ((v * 119581317450040) / 200000000000000) - 1
  if P18 u0 < rhs then
    let u1 := u0 + 2
    if P18 u1 < rhs then
      let u2 := u1 + 2
      if P18 u2 < rhs then u2 + 2 else u2
    else u1
  else
    u0

def check18_v (v : ℕ) : Bool :=
  let rhs := 25 * P18 v
  let u := findBracket18 v
  decide (u ≥ 19 ∧ u % 2 = 1 ∧ P18 (u - 2) < rhs ∧ rhs < P18 u)

def checkBlock (stepFn : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => stepFn (start + k) && checkBlock stepFn start k

def checkGrid (stepFn : ℕ → Bool) (start blockSize : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => checkBlock stepFn (start + b * blockSize) blockSize && checkGrid stepFn start blockSize b

def stepBase18 (n : ℕ) : Bool := check18_v (2 * n + 19)

def c8_hi_18 : ℕ := 1632128882563677
def c6_hi_abs_18 : ℕ := 368083388566156402
def c8_lo_18 : ℕ := 1632129179930663
def c6_lo_abs_18 : ℕ := 368083271457218899

def stepZone2_18 (n : ℕ) : Bool :=
  let v := 2 * n + 19
  let v2 := v * v
  let num_lo := c8_hi_18 * v2 - c6_hi_abs_18
  let den_lo := 1620 * v * (128 * v2 - 62013)
  let num_hi := c8_lo_18 * v2 - c6_lo_abs_18
  let den_hi := 1620 * v * (128 * v2 - 62016)
  if num_lo / den_lo < num_hi / den_hi then check18_v v else true

def C_hi_1A : ℕ := 1632128882550272
def C_lo_1A : ℕ := 1632128883002274
def C_hi_1B : ℕ := 1632128862254384
def C_lo_1B : ℕ := 1632128885195246

def checkPair18 (v_start v_end : ℕ) : Bool :=
  if v_start ≤ v_end then
    check18_v v_start &&
      (if v_start + 2 ≤ v_end then (v_start + 2 == v_end) && check18_v (v_start + 2) else true)
  else true

def stepZone1A_18 (d_idx : ℕ) : Bool :=
  let d_val := d_idx + 1
  let v_lo := C_hi_1A / (207360 * d_val)
  let v_hi := (C_lo_1A * 100000000) / (1620 * 12799999999 * d_val) + 1
  let v_start := 2 * (max 5240201 (v_lo + 1) / 2) + 1
  checkPair18 v_start (v_hi - 1)

def stepZone1B_18 (d_idx : ℕ) : Bool :=
  let d_val := d_idx + 1501
  let v_lo := C_hi_1B / (207360 * d_val)
  let v_hi := (C_lo_1B * 1000000) / (1620 * 127999996 * d_val) + 1
  let v_start := 2 * (max 134625 (v_lo + 1) / 2) + 1
  checkPair18 v_start (v_hi - 1)

theorem cert18_ok :
    (checkGrid stepBase18 0 1000 7 &&
     checkGrid stepZone2_18 7000 1000 61 &&
     checkGrid stepZone1A_18 0 500 3 &&
     checkGrid stepZone1B_18 0 1000 66) = true := by
  decide +kernel

private lemma check18_v_sound {v : ℕ} (hc : check18_v v = true) :
    ∀ m : ℕ, P18 (2 * m + 19) ≠ 25 * P18 v := by
  simp only [check18_v, decide_eq_true_eq] at hc
  rcases hc with ⟨hu19, hu_odd, hlo, hhi⟩
  intro m heq
  set u := findBracket18 v
  set x := 2 * m + 19
  by_cases hxu : x < u
  · have hle : x ≤ u - 2 := by omega
    have hpm : P18 x ≤ P18 (u - 2) := P18_mono (by omega) hle
    omega
  · have hge : u ≤ x := by omega
    have hpm : P18 u ≤ P18 x := P18_mono (by omega) hge
    omega

private lemma checkBlock_sound {f : ℕ → Bool} {start k : ℕ} (h : checkBlock f start k = true) :
    ∀ j < k, f (start + j) = true := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    simp only [checkBlock, Bool.and_eq_true] at h
    intro j hj
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with rfl | hlt
    · exact h.1
    · exact ih h.2 j hlt

private lemma checkGrid_sound {f : ℕ → Bool} {start bs b : ℕ} (h : checkGrid f start bs b = true) :
    ∀ t < b * bs, f (start + t) = true := by
  induction b with
  | zero => intro t ht; simp at ht
  | succ b ih =>
    simp only [checkGrid, Bool.and_eq_true] at h
    intro t ht
    rw [Nat.succ_mul] at ht
    by_cases hlt : t < b * bs
    · exact ih h.2 t hlt
    · have hsub : t - b * bs < bs := by omega
      have hcell := checkBlock_sound h.1 (t - b * bs) hsub
      have heq : start + b * bs + (t - b * bs) = start + t := by omega
      rwa [heq] at hcell

private lemma checkPair18_sound {v_start v_end v : ℕ}
    (h : checkPair18 v_start v_end = true)
    (hs_odd : v_start % 2 = 1) (hv_odd : v % 2 = 1) (hlo : v_start ≤ v) (hhi : v ≤ v_end) :
    check18_v v = true := by
  dsimp only [checkPair18] at h
  have hle_se : v_start ≤ v_end := le_trans hlo hhi
  rw [if_pos hle_se, Bool.and_eq_true] at h
  by_cases h2 : v_start + 2 ≤ v_end
  · rw [if_pos h2, Bool.and_eq_true, beq_iff_eq] at h
    have hcases : v = v_start ∨ v = v_start + 2 := by omega
    rcases hcases with rfl | rfl
    · exact h.1
    · exact h.2.2
  · have hsame : v = v_start := by omega
    rw [hsame]
    exact h.1

private lemma odd_ge_max_start {v0 v_lo v : ℕ} (hv_odd : v % 2 = 1) (hv0 : v0 ≤ v) (hlo : v_lo < v) :
    2 * (max v0 (v_lo + 1) / 2) + 1 ≤ v := by
  have hk : max v0 (v_lo + 1) ≤ v := max_le hv0 (by omega)
  omega

/-! ## 2. Exact Square Completion, Scaling, and Modular Divisibility -/

private lemma P18Z_eq (x : ℤ) : 16384 * P18Z x = Q18Z x ^ 2 + R18Z x := by
  dsimp only [P18Z, Q18Z, R18Z]
  ring

private lemma Q18_s10_eval (x : ℤ) : Q18_s10 (10000000000 * x) = 10000000000 ^ 9 * Q18Z x := by
  dsimp only [Q18_s10, Q18Z]
  ring

private lemma negR18_s10_eval (x : ℤ) :
    negR18_s10 (10000000000 * x) = -(10000000000 ^ 8 * R18Z x) := by
  dsimp only [negR18_s10, R18Z]
  ring

private lemma Q18_s10_shift19 (y : ℤ) :
    Q18_s10 (190000000000 + y) = 128 * y ^ 9 + 218880000000000 * y ^ 8 + 160147200000000000000000000 * y ^ 7 + 65499840000000000000000000000000000000 * y ^ 6 + 16407126240000000000000000000000000000000000000000 * y ^ 5 + 2590534267200000000000000000000000000000000000000000000000000 * y ^ 4 + 255158286424000000000000000000000000000000000000000000000000000000000000 * y ^ 3 + 14891609815920000000000000000000000000000000000000000000000000000000000000000000000 * y ^ 2 + 455926804584300000000000000000000000000000000000000000000000000000000000000000000000000000000 * y + 5307071229657000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  dsimp only [Q18_s10]
  ring

private lemma negR18_s10_shift19 (y : ℤ) :
    negR18_s10 (190000000000 + y) = 78397083729792 * y ^ 8 + 119163567269283840000000000 * y ^ 7 + 77576424506459107200000000000000000000 * y ^ 6 + 28211857039467329472000000000000000000000000000000 * y ^ 5 + 6258338700368375265120000000000000000000000000000000000000000 * y ^ 4 + 865526664800224580256000000000000000000000000000000000000000000000000000 * y ^ 3 + 72717000099942607087257000000000000000000000000000000000000000000000000000000000000 * y ^ 2 + 3385046016093518595349020000000000000000000000000000000000000000000000000000000000000000000000 * y + 66701935378097416484964900000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  dsimp only [negR18_s10]
  ring

private lemma Q18_s10_strictMono {a b : ℤ} (ha : 190000000000 ≤ a) (hab : a < b) :
    Q18_s10 a < Q18_s10 b := by
  set xlo := a - 190000000000
  set xhi := b - 190000000000
  have hx0 : 0 ≤ xlo := by omega
  have hlt : xlo < xhi := by omega
  have h1 := Q18_s10_shift19 xlo
  have h2 := Q18_s10_shift19 xhi
  rw [show 190000000000 + xlo = a by omega] at h1
  rw [show 190000000000 + xhi = b by omega] at h2
  rw [h1, h2]
  have hpow9 : xlo ^ 9 ≤ xhi ^ 9 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 9
  have hm9 : (128 : ℤ) * xlo ^ 9 ≤ (128 : ℤ) * xhi ^ 9 := by linarith only [hpow9]
  have hpow8 : xlo ^ 8 ≤ xhi ^ 8 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 8
  have hm8 : (218880000000000 : ℤ) * xlo ^ 8 ≤ (218880000000000 : ℤ) * xhi ^ 8 := by linarith only [hpow8]
  have hpow7 : xlo ^ 7 ≤ xhi ^ 7 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 7
  have hm7 : (160147200000000000000000000 : ℤ) * xlo ^ 7 ≤ (160147200000000000000000000 : ℤ) * xhi ^ 7 := by linarith only [hpow7]
  have hpow6 : xlo ^ 6 ≤ xhi ^ 6 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 6
  have hm6 : (65499840000000000000000000000000000000 : ℤ) * xlo ^ 6 ≤ (65499840000000000000000000000000000000 : ℤ) * xhi ^ 6 := by linarith only [hpow6]
  have hpow5 : xlo ^ 5 ≤ xhi ^ 5 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 5
  have hm5 : (16407126240000000000000000000000000000000000000000 : ℤ) * xlo ^ 5 ≤ (16407126240000000000000000000000000000000000000000 : ℤ) * xhi ^ 5 := by linarith only [hpow5]
  have hpow4 : xlo ^ 4 ≤ xhi ^ 4 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 4
  have hm4 : (2590534267200000000000000000000000000000000000000000000000000 : ℤ) * xlo ^ 4 ≤ (2590534267200000000000000000000000000000000000000000000000000 : ℤ) * xhi ^ 4 := by linarith only [hpow4]
  have hpow3 : xlo ^ 3 ≤ xhi ^ 3 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 3
  have hm3 : (255158286424000000000000000000000000000000000000000000000000000000000000 : ℤ) * xlo ^ 3 ≤ (255158286424000000000000000000000000000000000000000000000000000000000000 : ℤ) * xhi ^ 3 := by linarith only [hpow3]
  have hpow2 : xlo ^ 2 ≤ xhi ^ 2 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 2
  have hm2 : (14891609815920000000000000000000000000000000000000000000000000000000000000000000000 : ℤ) * xlo ^ 2 ≤ (14891609815920000000000000000000000000000000000000000000000000000000000000000000000 : ℤ) * xhi ^ 2 := by linarith only [hpow2]
  have hlt1 : (455926804584300000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℤ) * xlo < (455926804584300000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℤ) * xhi := by linarith only [hlt]
  linarith only [hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hlt1]

private lemma Q18_s10_mono {a b : ℤ} (ha : 190000000000 ≤ a) (hab : a ≤ b) :
    Q18_s10 a ≤ Q18_s10 b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (Q18_s10_strictMono ha hlt)

private lemma negR18_s10_strictMono {a b : ℤ} (ha : 190000000000 ≤ a) (hab : a < b) :
    negR18_s10 a < negR18_s10 b := by
  set xlo := a - 190000000000
  set xhi := b - 190000000000
  have hx0 : 0 ≤ xlo := by omega
  have hlt : xlo < xhi := by omega
  have h1 := negR18_s10_shift19 xlo
  have h2 := negR18_s10_shift19 xhi
  rw [show 190000000000 + xlo = a by omega] at h1
  rw [show 190000000000 + xhi = b by omega] at h2
  rw [h1, h2]
  have hpow8 : xlo ^ 8 ≤ xhi ^ 8 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 8
  have hm8 : (78397083729792 : ℤ) * xlo ^ 8 ≤ (78397083729792 : ℤ) * xhi ^ 8 := by linarith only [hpow8]
  have hpow7 : xlo ^ 7 ≤ xhi ^ 7 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 7
  have hm7 : (119163567269283840000000000 : ℤ) * xlo ^ 7 ≤ (119163567269283840000000000 : ℤ) * xhi ^ 7 := by linarith only [hpow7]
  have hpow6 : xlo ^ 6 ≤ xhi ^ 6 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 6
  have hm6 : (77576424506459107200000000000000000000 : ℤ) * xlo ^ 6 ≤ (77576424506459107200000000000000000000 : ℤ) * xhi ^ 6 := by linarith only [hpow6]
  have hpow5 : xlo ^ 5 ≤ xhi ^ 5 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 5
  have hm5 : (28211857039467329472000000000000000000000000000000 : ℤ) * xlo ^ 5 ≤ (28211857039467329472000000000000000000000000000000 : ℤ) * xhi ^ 5 := by linarith only [hpow5]
  have hpow4 : xlo ^ 4 ≤ xhi ^ 4 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 4
  have hm4 : (6258338700368375265120000000000000000000000000000000000000000 : ℤ) * xlo ^ 4 ≤ (6258338700368375265120000000000000000000000000000000000000000 : ℤ) * xhi ^ 4 := by linarith only [hpow4]
  have hpow3 : xlo ^ 3 ≤ xhi ^ 3 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 3
  have hm3 : (865526664800224580256000000000000000000000000000000000000000000000000000 : ℤ) * xlo ^ 3 ≤ (865526664800224580256000000000000000000000000000000000000000000000000000 : ℤ) * xhi ^ 3 := by linarith only [hpow3]
  have hpow2 : xlo ^ 2 ≤ xhi ^ 2 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 2
  have hm2 : (72717000099942607087257000000000000000000000000000000000000000000000000000000000000 : ℤ) * xlo ^ 2 ≤ (72717000099942607087257000000000000000000000000000000000000000000000000000000000000 : ℤ) * xhi ^ 2 := by linarith only [hpow2]
  have hlt1 : (3385046016093518595349020000000000000000000000000000000000000000000000000000000000000000000000 : ℤ) * xlo < (3385046016093518595349020000000000000000000000000000000000000000000000000000000000000000000000 : ℤ) * xhi := by linarith only [hlt]
  linarith only [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hlt1]

private lemma negR18_s10_mono {a b : ℤ} (ha : 190000000000 ≤ a) (hab : a ≤ b) :
    negR18_s10 a ≤ negR18_s10 b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (negR18_s10_strictMono ha hlt)

private lemma Q18Z_pos {v : ℤ} (hv : 19 ≤ v) : 0 < Q18Z v := by
  set y := 10000000000 * v - 190000000000
  have hy0 : 0 ≤ y := by omega
  have hsh := Q18_s10_shift19 y
  rw [show 190000000000 + y = 10000000000 * v by omega, Q18_s10_eval v] at hsh
  have hs10 : 0 < 10000000000 ^ 9 * Q18Z v := by
    rw [hsh]
    positivity
  nlinarith only [hs10]

private lemma R18Z_lt_of_lt {v u : ℤ} (hv : 19 ≤ v) (hvu : v < u) : R18Z u < R18Z v := by
  have hmono := negR18_s10_strictMono (by omega : 190000000000 ≤ 10000000000 * v) (by omega : 10000000000 * v < 10000000000 * u)
  rw [negR18_s10_eval v, negR18_s10_eval u] at hmono
  nlinarith only [hmono]

private lemma R18Z_neg {v : ℤ} (hv : 19 ≤ v) : R18Z v < 0 := by
  set y := 10000000000 * v - 190000000000
  have hy0 : 0 ≤ y := by omega
  have hsh := negR18_s10_shift19 y
  rw [show 190000000000 + y = 10000000000 * v by omega, negR18_s10_eval v] at hsh
  have hs10 : 0 < -(10000000000 ^ 8 * R18Z v) := by
    rw [hsh]
    positivity
  nlinarith only [hs10]

private lemma Q18Z_odd (a : ℤ) : ∃ k : ℤ, Q18Z (2 * a + 1) = 2 * k + 1 := by
  refine ⟨32768 * a ^ 9 + 147456 * a ^ 8 - 3674112 * a ^ 7 - 13547520 * a ^ 6 + 124041984 * a ^ 5 + 344317824 * a ^ 4 - 1405725344 * a ^ 3 - 2459777904 * a ^ 2 + 2514186963 * a + 1678861201, ?_⟩
  dsimp only [Q18Z]
  ring

private lemma Q18Z_81_dvd (x : ℤ) : (81 : ℤ) ∣ Q18Z x := by
  set qq := x / 9
  have hr : x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 3 ∨ x % 9 = 4 ∨
      x % 9 = 5 ∨ x % 9 = 6 ∨ x % 9 = 7 ∨ x % 9 = 8 := by omega
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · have hx : x = 9 * qq + 0 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 - 3661982784 * qq ^ 7 + 6589308528 * qq ^ 5 - 3956938632 * qq ^ 3 + 420933923 * qq, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 1 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 612220032 * qq ^ 8 - 3389884992 * qq ^ 7 - 2777664960 * qq ^ 6 + 5651662896 * qq ^ 5 + 3486217968 * qq ^ 4 - 3162882024 * qq ^ 3 - 1229888952 * qq ^ 2 + 279354107 * qq + 41453363, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 2 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 1224440064 * qq ^ 8 - 2573591616 * qq ^ 7 - 5132066688 * qq ^ 6 + 2979813744 * qq ^ 5 + 5956734816 * qq ^ 4 - 1009326600 * qq ^ 3 - 1955937456 * qq ^ 2 - 87988285 * qq + 53591382, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 3 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 1836660096 * qq ^ 8 - 1213102656 * qq ^ 7 - 6639941952 * qq ^ 6 - 1002975696 * qq ^ 5 + 6552613584 * qq ^ 4 + 1852720920 * qq ^ 3 - 1822843944 * qq ^ 2 - 525621445 * qq + 19231193, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 4 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 2448880128 * qq ^ 8 + 691581888 * qq ^ 7 - 6878027520 * qq ^ 6 - 5591266704 * qq ^ 5 + 4728445632 * qq ^ 4 + 4454370936 * qq ^ 3 - 749160288 * qq ^ 2 - 827576413 * qq - 58164948, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 5 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 3061100160 * qq ^ 8 + 3140462016 * qq ^ 7 - 5423060160 * qq ^ 6 - 9797445072 * qq ^ 5 + 409114800 * qq ^ 4 + 5683033368 * qq ^ 3 + 993842280 * qq ^ 2 - 808081477 * qq - 152643265, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 6 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 3673320192 * qq ^ 8 + 6133537728 * qq ^ 7 - 1851776640 * qq ^ 6 - 12351721104 * qq ^ 5 - 5853438432 * qq ^ 4 + 4526273016 * qq ^ 3 + 2772980208 * qq ^ 2 - 382470973 * qq - 222477822, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 7 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 4285540224 * qq ^ 8 + 9670809024 * qq ^ 7 + 4259086272 * qq ^ 6 - 11702129616 * qq ^ 5 - 12723452784 * qq ^ 4 + 385337880 * qq ^ 3 + 3676861944 * qq ^ 2 + 359754875 * qq - 225634843, by dsimp only [Q18Z]; ring⟩
  · have hx : x = 9 * qq + 8 := by omega
    rw [hx]; refine ⟨612220032 * qq ^ 9 + 4897760256 * qq ^ 8 + 13752275904 * qq ^ 7 + 13332791808 * qq ^ 6 - 6014529936 * qq ^ 5 - 17924582016 * qq ^ 4 - 6541639560 * qq ^ 3 + 2715713856 * qq ^ 2 + 1112943395 * qq - 141867432, by dsimp only [Q18Z]; ring⟩

private lemma Q18Z_diff_162_dvd (a b : ℤ) :
    (162 : ℤ) ∣ 5 * Q18Z (2 * b + 1) - Q18Z (2 * a + 1) := by
  obtain ⟨ka, hka⟩ := Q18Z_odd a
  obtain ⟨kb, hkb⟩ := Q18Z_odd b
  obtain ⟨qa, hqa⟩ := Q18Z_81_dvd (2 * a + 1)
  obtain ⟨qb, hqb⟩ := Q18Z_81_dvd (2 * b + 1)
  set Z := 5 * Q18Z (2 * b + 1) - Q18Z (2 * a + 1)
  have h2 : Z = 2 * (5 * kb - ka + 2) := by linarith only [hka, hkb]
  have h81 : Z = 81 * (5 * qb - qa) := by linarith only [hqa, hqb]
  refine ⟨(-40 : ℤ) * (5 * qb - qa) + 1 * (5 * kb - ka + 2), ?_⟩
  calc Z = (-40 * 2 + 1 * 81) * Z := by ring
    _ = -40 * 2 * Z + 81 * Z := by ring
    _ = -40 * 2 * (81 * (5 * qb - qa)) + 81 * (2 * (5 * kb - ka + 2)) := by rw [← h81, ← h2]
    _ = 162 * ((-40 : ℤ) * (5 * qb - qa) + 1 * (5 * kb - ka + 2)) := by ring

/-! ## 3. Taylor Positivity Lemmas Across All Zones -/

private lemma P18Z_prod_scaled10 (u : ℤ) :
    10000000000 ^ 18 * P18Z u =
      ∏ j ∈ Finset.Icc (1 : ℕ) 9, ((10000000000 * u) ^ 2 - 10000000000 ^ 2 * (2 * (j : ℤ) - 1) ^ 2) := by
  have hIcc : Finset.Icc (1 : ℕ) 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  dsimp only [P18Z]
  ring

private lemma P18Z_hom_hi_gt {v : ℤ} (hv : 19 ≤ v) :
    25 * 10000000000 ^ 18 * P18Z v <
      ∏ j ∈ Finset.Icc (1 : ℕ) 9, ((11958131746 * v) ^ 2 - 10000000000 ^ 2 * (2 * (j : ℤ) - 1) ^ 2) := by
  set y := v - 19
  have hy0 : 0 ≤ y := by omega
  have hprod : (∏ j ∈ Finset.Icc (1 : ℕ) 9, ((11958131746 * v) ^ 2 - 10000000000 ^ 2 * (2 * (j : ℤ) - 1) ^ 2)) -
      25 * 10000000000 ^ 18 * P18Z v = 37480040637144810941076344342226955705297576340787683024973124225986004901409728791957975728432978888223910967989625752829239354002972754254613122457114935367227415925620736 * y ^ 18 + 12818173897903525341848109765041618851211771108549387594540808485287213676282127246849627699124078779772577551052452007467599859069016681955077687880333307895591776246562291712 * y ^ 17 + 7284077113163454905332443352692931967309143895950076313264064532601610219792519608841578756542258374406384490434412984773409336944174760658220391876619771684023042738071863819810111488 * y ^ 16 + 2214359022854313163573409323635453301739766998306746969005120056860533911042897527256293734435965535022359703949083249723660599344840673338470320952829634476713615364391282200407424630784 * y ^ 15 + 310743503640349149567429719613313698510865563342388225500354994564497099223750874406081278649341688906513487633900486900873605702098480209493193148018986513826643183928878856779029004943360 * y ^ 14 + 26700921581196824144567492373391021643418791020461505343903088922839033642505651782835711984500300807686511681320808111425717582055668366480875706404953219937703361846737955180644343062986752 * y ^ 13 + 1571134728262148612303858513050147347591203119811806919164685387860783251354334048335283237812089877244563535423325778078011724812169905870385673953555921499586519288116803154936525456092954624 * y ^ 12 + 67073413803234660490964047444126305921858843516891825515054820756550970109227313188662626515933702107049031039793072111047233506606507990702743126607022061341465367109601360817932543427027664896 * y ^ 11 + 2147068775583082077504919346476689184375854794536765325678968795068044225106253073458958937911726493376750448262267941976100897272818476957300721174427925981801345527488437362568487697031097745408 * y ^ 10 + 52517564632770478212583874868242628609547311071385241454062048338455150163824252279370492853921857119993843260335168185459104343013162922982154182555029484875305476593964705480001406937323174625280 * y ^ 9 + 990956718279888582787661901677855544899307097792651226142384499758276016553108554523033763696398586862011980114057594764141696538643675461276219093819408277473341303381950861506424058628226286092288 * y ^ 8 + 14455705965195201508708424322458781064141203509710936134887986602451916928664665584973990788230653673254267047958699268616979540686759136235679218723951159297241916530674176395902586991953672316911616 * y ^ 7 + 162281367530342047899528211779662302228271040617138393365313033749407825290495650382444628063638484087190813302028238941534245765074173611014857986368383089813987375675028800479517139160819868179103744 * y ^ 6 + 1385347499750280599242878999820830294100032845533192316162141882677355224546189621594589289297566961814137243339629599971407996208171005594180699098631406749188877206866039526871460943410266536339832832 * y ^ 5 + 8803023666113639799286732602881745451507112469635128708744026610426047817851657459092363047661846454419443601226449410634492273968872228460071556522023302888392896712775487899562792401712522925163151360 * y ^ 4 + 40186535538774852932453435334266141959192346359426526778778452084195491956747534585130331384243450614845209590338507399432775855124454517763021766523131485030642767082269209158414882035343449487493300224 * y ^ 3 + 124075623097098293011186228334364533631635441700573015730339743191847153591279619520258241796337009203652507488105091281961537822746389893882574511691003999388546017800212451598007961250911038799194882048 * y ^ 2 + 231040016758448055488411422567920734573597893084472130939140094812573204302146809624155095864369009878408263640370693039258338027970337769127153800252468133182367631484137886060104877902036439668788559872 * y + 195066930347678292766507495835297706258753434369019855146328478720149764355157124754279632651636230302331024560046817298872747145434310200472384933405656392152928214752781473978902813963260686317054590976 := by
    have hIcc : Finset.Icc (1 : ℕ) 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
    rw [hIcc]
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
      Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
    have hv_eq : v = 19 + y := by omega
    rw [hv_eq]
    dsimp only [P18Z]
    ring
  have hpos : 0 < (∏ j ∈ Finset.Icc (1 : ℕ) 9, ((11958131746 * v) ^ 2 - 10000000000 ^ 2 * (2 * (j : ℤ) - 1) ^ 2)) -
      25 * 10000000000 ^ 18 * P18Z v := by
    rw [hprod]
    positivity
  omega

private lemma u_lt_a_high18 {u v : ℤ} (hv : 19 ≤ v) (hvu : v < u) (hPeq : P18Z u = 25 * P18Z v) :
    10000000000 * u < 11958131746 * v := by
  by_contra hge
  have hle : 11958131746 * v ≤ 10000000000 * u := by omega
  have hprod_le :
      (∏ j ∈ Finset.Icc (1 : ℕ) 9, ((11958131746 * v) ^ 2 - 10000000000 ^ 2 * (2 * (j : ℤ) - 1) ^ 2)) ≤
        ∏ j ∈ Finset.Icc (1 : ℕ) 9, ((10000000000 * u) ^ 2 - 10000000000 ^ 2 * (2 * (j : ℤ) - 1) ^ 2) := by
    refine Finset.prod_le_prod ?_ ?_
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have h2j : 2 * (j : ℤ) - 1 ≤ 17 := by omega
      have h1 : 0 ≤ 2 * (j : ℤ) - 1 := by omega
      have hsq : (2 * (j : ℤ) - 1) ^ 2 ≤ 289 := by nlinarith
      nlinarith
    · intro j _
      have hsq : (11958131746 * v) ^ 2 ≤ (10000000000 * u) ^ 2 := by nlinarith
      omega
  have hgt := P18Z_hom_hi_gt hv
  rw [← P18Z_prod_scaled10 u] at hprod_le
  linarith only [hPeq, hgt, hprod_le]

private lemma Q18_ub_19 {v : ℤ} (hv : 19 ≤ v) : Q18Z v < 128 * v ^ 9 := by
  set y := v - 19
  have hy0 : 0 ≤ y := by omega
  have heq : 128 * v ^ 9 - Q18Z v = 62016 * y ^ 7 + 8248128 * y ^ 6 + 461104464 * y ^ 5 + 14029182000 * y ^ 4 + 250679026088 * y ^ 3 + 2629799991720 * y ^ 2 + 15005796577389 * y + 35996954086055 := by
    have hv_eq : v = 19 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z]; ring
  have hpos : 0 < 128 * v ^ 9 - Q18Z v := by rw [heq]; positivity
  omega

private lemma d655001_pos {v : ℤ} (hv : 14019 ≤ v) :
    0 < 162 * 655001 * (10 * Q18Z v - 162 * 655001) + 24 * R18Z v := by
  set y := v - 14019
  have hy0 : 0 ≤ y := by omega
  have heq : 162 * 655001 * (10 * Q18Z v - 162 * 655001) + 24 * R18Z v = 135821007360 * y ^ 9 + 15255142310103552 * y ^ 8 + 749938617562525127424 * y ^ 7 + 21079943886889833895107072 * y ^ 6 + 370703946714339471115874991552 * y ^ 5 + 4179460264552372925377609542332352 * y ^ 4 + 29552255157899709220131141315722857440 * y ^ 3 + 120422855110418207233898757115779551764872 * y ^ 2 + 221821037410481245908201292304607840309144012 * y + 33630196236892821523099960713291878271102854520 := by
    have hv_eq : v = 14019 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z, R18Z]; ring
  rw [heq]; positivity

private lemma d67501_pos {v : ℤ} (hv : 136019 ≤ v) :
    0 < 162 * 67501 * (10 * Q18Z v - 162 * 67501) + 24 * R18Z v := by
  set y := v - 136019
  have hy0 : 0 ≤ y := by omega
  have heq : 162 * 67501 * (10 * Q18Z v - 162 * 67501) + 24 * R18Z v = 13997007360 * y ^ 9 + 15253200487383552 * y ^ 8 + 7275204980135255879424 * y ^ 7 + 1984089544711008691099203072 * y ^ 6 + 338522354376358371424105495695552 * y ^ 5 + 37028982148423732307283714121033052352 * y ^ 4 + 2540154114220934421435449108589245548633440 * y ^ 3 + 100413781241262054598276602529199170302196804872 * y ^ 2 + 1793824742630032354919862759931433260797642742662012 * y + 2616158627614315625241620474885619678582100190182268520 := by
    have hv_eq : v = 136019 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z, R18Z]; ring
  rw [heq]; positivity

private lemma rem_hi_z2_pos {v : ℤ} (hv : 14019 ≤ v) :
    10000000000 ^ 8 * v ^ 6 * ((c8_hi_18 : ℤ) * v ^ 2 - (c6_hi_abs_18 : ℤ)) <
      -25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v) := by
  set y := v - 14019
  have hy0 : 0 ≤ y := by omega
  have heq : (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v)) -
      10000000000 ^ 8 * v ^ 6 * ((c8_hi_18 : ℤ) * v ^ 2 - (c6_hi_abs_18 : ℤ)) =
      61433557944775708959654253209944329076519612067523577539050864719292721235263488 * y ^ 8 + 6889896390622485311243143806001676394589827532596904268159632579998117271977270706176 * y ^ 7 + 338063101414842608857895199874619114919171614216012532337599042077332021125472753104584704 * y ^ 6 + 9478613246686257030782908280669216187297311116268641345471349803538986542716005051546345930752 * y ^ 5 + 2336984649398640872930651848060251814453801251449403657957224457258929263472207593522035279504015360 * y ^ 4 + 123597334230924007064600442218593929176880623342369166979190051906788930535568567639668330066693433065472 * y ^ 3 + 2572951167749648261209833610210283189210626143983569732795167400893172791084310710339567159602487619072425984 * y ^ 2 + 23977065756542189831498466780802207953940980096302194942592928770328246921134835148795295406876363980507525677056 * y + 83941967097949601193151376066660921823673050259190366041255964602999338063666284030026077308906568330341875308331008 := by
    have hv_eq : v = 14019 + y := by omega
    rw [hv_eq]; dsimp only [R18Z, negR18_s10, c8_hi_18, c6_hi_abs_18]; ring
  have hpos : 0 < (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v)) -
      10000000000 ^ 8 * v ^ 6 * ((c8_hi_18 : ℤ) * v ^ 2 - (c6_hi_abs_18 : ℤ)) := by
    rw [heq]; positivity
  omega

private lemma q_low_z2_pos {v : ℤ} (hv : 14019 ≤ v) :
    Q18_s10 (11958130390 * v) < 10000000000 ^ 9 * (5 * Q18Z v - 162 * 655000) := by
  set y := v - 14019
  have hy0 : 0 ≤ y := by omega
  have heq : 10000000000 ^ 9 * (5 * Q18Z v - 162 * 655000) - Q18_s10 (11958130390 * v) =
      652678844883806262733641871352141574634778856383953726352592127552167470622848000000000 * y ^ 9 + 82349142537834719975366328550371054613244683088819825607632901325384521935955355008000000000 * y ^ 8 + 4524574184114347623386904029112809808192422535770384214498802804543126452080632487428608000000000 * y ^ 7 + 141903638769684407561218400477346256842263171190761164222919079534750773982009569296277196288000000000 * y ^ 6 + 2791619146413958274781942538838540562866302345818486991627520889027285244969680227946765022142208000000000 * y ^ 5 + 35539340437835272527345880912889334258943740109299413342273567663148825333679785579585698845411613952000000000 * y ^ 4 + 290136117310351334245482286043390926328448466179145095534854424336572271350656513882487941409216943995392000000000 * y ^ 3 + 1440264023350217932166651602225405870858862103648543927632247055576279176333821660364485123406776716230600192000000000 * y ^ 2 + 3809183619298281808929393348523508639694975705302498770845202878986165843988268559015934385331900696209196022912000000000 * y + 3728528563049076402000982888811107714309320502381972847759287983404939461634231869903507912928545317795191005022592000000000 := by
    have hv_eq : v = 14019 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z, Q18_s10]; ring
  have hpos : 0 < 10000000000 ^ 9 * (5 * Q18Z v - 162 * 655000) - Q18_s10 (11958130390 * v) := by
    rw [heq]; positivity
  omega

private lemma rem_lo_z2_pos {v : ℤ} (hv : 14019 ≤ v) :
    (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958130390 * v)) +
        10000000000 ^ 8 * (162 * 655000) ^ 2 <
      10000000000 ^ 8 * v ^ 6 * ((c8_lo_18 : ℤ) * v ^ 2 - (c6_lo_abs_18 : ℤ)) := by
  set y := v - 14019
  have hy0 : 0 ≤ y := by omega
  have heq : 10000000000 ^ 8 * v ^ 6 * ((c8_lo_18 : ℤ) * v ^ 2 - (c6_lo_abs_18 : ℤ)) -
      ((-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958130390 * v)) +
        10000000000 ^ 8 * (162 * 655000) ^ 2) =
      83522786527901563984067999189613784021857325255456769458593033732702195200000000 * y ^ 8 + 9367247554677216203941194245113565105619342742049987608320125919190016596070400000000 * y ^ 7 + 15487574405122233187580492690839284324827243447763326165691917548013936949311088281600000000 * y ^ 6 + 1276948291620560863831593276455130618411834582216078244475435386363624364184784293239500800000000 * y ^ 5 + 42357136810219571568953987674967505667935068885498700955679115550741994043883113758655702144000000000 * y ^ 4 + 708894832974964647707887618650256244184171638141158971805455581710936692655089097426075430685388800000000 * y ^ 3 + 6164674344700363343097119953439562618516593590920232776004739202616754485477012836408075731389232793600000000 * y ^ 2 + 24970679122189231872970976236394826907277849746933911982393954339688198243646663745264918193813044152422400000000 * y + 30352351460790299091192659052079328514132021063362731831808284996390070677783300826044245419883133246601203200000000 := by
    have hv_eq : v = 14019 + y := by omega
    rw [hv_eq]; dsimp only [R18Z, negR18_s10, c8_lo_18, c6_lo_abs_18]; ring
  have hpos : 0 < 10000000000 ^ 8 * v ^ 6 * ((c8_lo_18 : ℤ) * v ^ 2 - (c6_lo_abs_18 : ℤ)) -
      ((-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958130390 * v)) +
        10000000000 ^ 8 * (162 * 655000) ^ 2) := by
    rw [heq]; positivity
  omega

private lemma q_ub_z2_pos {v : ℤ} (hv : 14019 ≤ v) :
    Q18Z v < v ^ 7 * (128 * v ^ 2 - 62013) := by
  set y := v - 14019
  have hy0 : 0 ≤ y := by omega
  have heq : v ^ 7 * (128 * v ^ 2 - 62013) - Q18Z v = 3 * y ^ 7 + 294399 * y ^ 6 + 12372499911 * y ^ 5 + 288661075801155 * y ^ 4 + 4037857507127840033 * y ^ 3 + 33864419954456244504693 * y ^ 2 + 157666560278196770330452218 * y + 314362679672617412823788987448 := by
    have hv_eq : v = 14019 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z]; ring
  have hpos : 0 < v ^ 7 * (128 * v ^ 2 - 62013) - Q18Z v := by rw [heq]; positivity
  omega

private lemma q_lb_z2_pos {v : ℤ} (hv : 14019 ≤ v) :
    10 * v ^ 7 * (128 * v ^ 2 - 62016) < 10 * Q18Z v - 162 * 655000 := by
  set y := v - 14019
  have hy0 : 0 ≤ y := by omega
  have heq : (10 * Q18Z v - 162 * 655000) - 10 * v ^ 7 * (128 * v ^ 2 - 62016) = 90388320 * y ^ 5 + 6335769290400 * y ^ 4 + 177642294967636720 * y ^ 3 + 2490367209879470995440 * y ^ 2 + 17456227661539370361472830 * y + 48943766272043824008230307690 := by
    have hv_eq : v = 14019 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z]; ring
  have hpos : 0 < (10 * Q18Z v - 162 * 655000) - 10 * v ^ 7 * (128 * v ^ 2 - 62016) := by
    rw [heq]; positivity
  omega

private lemma rem_hi_1B_pos {v : ℤ} (hv : 134625 ≤ v) :
    10000000000 ^ 8 * ((C_hi_1B : ℤ) * v ^ 8) <
      -25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v) := by
  set y := v - 134625
  have hy0 : 0 ≤ y := by omega
  have heq : (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v)) -
      10000000000 ^ 8 * ((C_hi_1B : ℤ) * v ^ 8) = 2030929361433557944775708959654253209944329076519612067523577539050864719292721235263488 * y ^ 8 + 2187310922263941906523438549547630707110042415411622196722893009557781302678260770378776576000 * y ^ 7 + 993825226327625487044377134898757728123850970715793575406214679004951507646567396742849787904000000 * y ^ 6 + 247766151714425640227508790921732924602287161531247489873178658223017269037763365973012305393152000000000 * y ^ 5 + 36691070413924777937283488477840941712042516193540306253190222294108298420595646118145977016941360000000000000 * y ^ 4 + 3233150483310232472172956436331467511691805725225369723441552719828521247060189550121121724724584472000000000000000 * y ^ 3 + 157178270823211697320755761871002577170415481602622484274238505152762671516294901659946256095523592271500000000000000000 * y ^ 2 + 3255404267944618744608825958724662937529598655325365162249751068130130732776615880067623718388532459871625000000000000000000 * y + 17126837425814437299266345270375241152274767255263010177724356376106692217942569920467452335301277189453125000000000000000 := by
    have hv_eq : v = 134625 + y := by omega
    rw [hv_eq]; dsimp only [R18Z, negR18_s10, C_hi_1B]; ring
  have hpos : 0 < (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v)) -
      10000000000 ^ 8 * ((C_hi_1B : ℤ) * v ^ 8) := by
    rw [heq]; positivity
  omega

private lemma q_low_1B_pos {v : ℤ} (hv : 134625 ≤ v) :
    Q18_s10 (11958131734 * v) < 10000000000 ^ 9 * (5 * Q18Z v - 162 * 67500) := by
  set y := v - 134625
  have hy0 : 0 ≤ y := by omega
  have heq : 10000000000 ^ 9 * (5 * Q18Z v - 162 * 67500) - Q18_s10 (11958131734 * v) =
      5300422586603110777701884941606888182641416654792353367371859803909419951979551326208 * y ^ 9 + 6422124516492994096033046342374445894292906454362785148741929634911750949317223875616768000 * y ^ 8 + 3365077889894946439344218943648610921931267952634860996674225247527330891877725057019629568000000 * y ^ 7 + 998479473238149524038566332185512194136272935409360585758975355286282342223519183536291138048000000000 * y ^ 6 + 183887527580089880203574435579346362774014182629427181767752556252934893098382916325359791689568000000000000 * y ^ 5 + 21571004080834193331701143480576425077573022841829384848359812839797859827873771620701561956208092000000000000000 * y ^ 4 + 1578696773665845563497992872533547495168178158050264840914080560539965520856960306780965185569676257000000000000000000 * y ^ 3 + 66347186715002857148128872620172695810770037630213102320607139142013755112673329285568466331707571185125000000000000000000 * y ^ 2 + 1261645305559120025049781651968047859880614400609603078330512750285947566624762325237980648882782942699363281250000000000000000 * y + 2266614071181470116284797721920475969443911551458128573457198934021123049095813140872105132507044851211309082031250000000000000000 := by
    have hv_eq : v = 134625 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z, Q18_s10]; ring
  have hpos : 0 < 10000000000 ^ 9 * (5 * Q18Z v - 162 * 67500) - Q18_s10 (11958131734 * v) := by
    rw [heq]; positivity
  omega

private lemma rem_lo_1B_pos {v : ℤ} (hv : 134625 ≤ v) :
    (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131734 * v)) +
        10000000000 ^ 8 * (162 * 67500) ^ 2 <
      10000000000 ^ 8 * ((C_lo_1B : ℤ) * v ^ 8) := by
  set y := v - 134625
  have hy0 : 0 ≤ y := by omega
  have heq : 10000000000 ^ 8 * ((C_lo_1B : ℤ) * v ^ 8) -
      ((-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131734 * v)) +
        10000000000 ^ 8 * (162 * 67500) ^ 2) = 111551888192394633712274906611409778942670149473120994493035632094077630886674432 * y ^ 8 + 120141383583209020508120074420488331921255750982551311068999375765321608464948363264000 * y ^ 7 + 36808395495088361705347856679037397883251697687946927923982173538844481825252988577856915456000000 * y ^ 6 + 29731950977147485791982492396790313847125543193944322590649166967450426298845104774587974486528000000000 * y ^ 5 + 10006657183631651336561048720753976302377681684346773831504416388638487960934998739848632581561040000000000000 * y ^ 4 + 1796194779519578943899108768706728588326322193531200184675426118556556220116442192988897729034124008000000000000000 * y ^ 3 + 181359532229231214063544065212369660448864794308814618230604497656744419980140439062256928385609472288500000000000000000 * y ^ 2 + 9766210515976424460141041639490622451730765088698174001949526212828891973531943056384111770403621487668375000000000000000000 * y + 219129344202522632658518195400688271338961187814331937195032739865697404547360767961387486265815630347169373046875000000000000000 := by
    have hv_eq : v = 134625 + y := by omega
    rw [hv_eq]; dsimp only [R18Z, negR18_s10, C_lo_1B]; ring
  have hpos : 0 < 10000000000 ^ 8 * ((C_lo_1B : ℤ) * v ^ 8) -
      ((-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131734 * v)) +
        10000000000 ^ 8 * (162 * 67500) ^ 2) := by
    rw [heq]; positivity
  omega

private lemma q_lb_1B_pos {v : ℤ} (hv : 134625 ≤ v) :
    10 * 127999996 * v ^ 9 < 1000000 * (10 * Q18Z v - 162 * 67500) := by
  set y := v - 134625
  have hy0 : 0 ≤ y := by omega
  have heq : 1000000 * (10 * Q18Z v - 162 * 67500) - 10 * 127999996 * v ^ 9 = 40 * y ^ 9 + 48465000 * y ^ 8 + 25478242500000 * y ^ 7 + 7613737405312500000 * y ^ 6 + 1419482121270681288750000 * y ^ 5 + 169913733413892078817968750000 * y ^ 4 + 12873172288351113666316096832500000 * y ^ 3 + 578191486120962761107704477366562500000 * y ^ 2 + 12998811482861963512115759792645859710625000 * y + 83989150169139760766765452417945053779765625000 := by
    have hv_eq : v = 134625 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z]; ring
  have hpos : 0 < 1000000 * (10 * Q18Z v - 162 * 67500) - 10 * 127999996 * v ^ 9 := by
    rw [heq]; positivity
  omega

private lemma rem_hi_1A_pos {v : ℤ} (hv : 5240201 ≤ v) :
    10000000000 ^ 8 * ((C_hi_1A : ℤ) * v ^ 8) <
      -25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v) := by
  set y := v - 5240201
  have hy0 : 0 ≤ y := by omega
  have heq : (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v)) -
      10000000000 ^ 8 * ((C_hi_1A : ℤ) * v ^ 8) = 1340561433557944775708959654253209944329076519612067523577539050864719292721235263488 * y ^ 8 + 56198490917534206172918928713418600027865368857181406792948349695042823219496877991720648704 * y ^ 7 + 993911520209322186489740234404230498813608328231727869290198101635040270562562058421823872707723264 * y ^ 6 + 9645059907885716127809936403811068321442027118236446344438630642561721987710517793145799759173768311472128 * y ^ 5 + 55596969349159432959367336387215459777051198969414359627230527140077613897439507386578920912777674849430695772160 * y ^ 4 + 190699330253865316599383257635594342145308325579644781843257298341845468044826103774970534042442742818929265132774883328 * y ^ 3 + 360877442856885009080743655429230537764534971356555389597983739248076011917806141009476114619618507953119977039016038195134464 * y ^ 2 + 290978901661571381788927684543938111229448360579451574572258209757065888040791290884934386596771679848626048093208252104623375253504 * y + 63870160493551460968959935541910086219559813483781173620199286708811622363603239947310913659284713687413269032780585862439453348364288 := by
    have hv_eq : v = 5240201 + y := by omega
    rw [hv_eq]; dsimp only [R18Z, negR18_s10, C_hi_1A]; ring
  have hpos : 0 < (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v)) -
      10000000000 ^ 8 * ((C_hi_1A : ℤ) * v ^ 8) := by
    rw [heq]; positivity
  omega

private lemma q_low_1A_pos {v : ℤ} (hv : 5240201 ≤ v) :
    Q18_s10 (11958131744 * v) < 10000000000 ^ 9 * (5 * Q18Z v - 162 * 1500) := by
  set y := v - 5240201
  have hy0 : 0 ≤ y := by omega
  have heq : 10000000000 ^ 9 * (5 * Q18Z v - 162 * 1500) - Q18_s10 (11958131744 * v) =
      483616667676594652215337106916572265407361734297245615403931059536897386531507929088 * y ^ 9 + 22808236910180030758201155507011960115839301306835446939767654479046782996198149433633800192 * y ^ 8 + 477985747298882049739803353943837832965081255536440023178303169509049049156344555441109093599674368 * y ^ 7 + 5842116556578111282432469486591551407965017006088392303795037563635032064126143845374329064576916853358592 * y ^ 6 + 45893915037864686046725085607658494467411154800667251183305244440641051823767191917625817162987536407829820735488 * y ^ 5 + 240305513239224109269681974899967621898104461381456209475955991151134208455383643770518519013343644871846234447924953088 * y ^ 4 + 838679254495893216749509344047505587293715148957810470180949637439348280396569843349396038753542981085657006400167191397793792 * y ^ 3 + 1881295806329257682336079643983920973984241133100563418013714968291122102359955176809377308942471200039346679669469649941390182842368 * y ^ 2 + 2461213648894730581018625825348351007353877760194316917709768897178474659463029586451969910100342382368805387263381051473130694380189908992 * y + 1430780189246870208053972720116679216493630206455085751237311383809599239159315630185653357490343295241338078288771735233141748646862837921087488 := by
    have hv_eq : v = 5240201 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z, Q18_s10]; ring
  have hpos : 0 < 10000000000 ^ 9 * (5 * Q18Z v - 162 * 1500) - Q18_s10 (11958131744 * v) := by
    rw [heq]; positivity
  omega

private lemma rem_lo_1A_pos {v : ℤ} (hv : 5240201 ≤ v) :
    (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131744 * v)) +
        10000000000 ^ 8 * (162 * 1500) ^ 2 <
      10000000000 ^ 8 * ((C_lo_1A : ℤ) * v ^ 8) := by
  set y := v - 5240201
  have hy0 : 0 ≤ y := by omega
  have heq : 10000000000 ^ 8 * ((C_lo_1A : ℤ) * v ^ 8) -
      ((-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131744 * v)) +
        10000000000 ^ 8 * (162 * 1500) ^ 2) = 183935645112123738625494829057747233019736614397078618909130810701024455003471872 * y ^ 8 + 7710878011617567418152453029785888865738054612001486207089969466930552401069186457010176 * y ^ 7 + 36949761788843811498006721286198537937823693309829151207433688757005886833440823031794239134498816 * y ^ 6 + 1158780733792975936539937765589043605756953677775289808544772304138171994656145480910462407413679660204032 * y ^ 5 + 15170901319804805808810744064005683352578844862949296153932124918185867838465363830562008034239464461351035863040 * y ^ 4 + 105970963069668280491722107709115697258769163220156213958025494147293139639176313365736182193765513527868927584430456832 * y ^ 3 + 416428541033697337262142062502505809744857186355380932503766647300791833182366728448574442037369682107334141098430032160751616 * y ^ 2 + 872803839539972058294395231398847264989161206553066257822842731083469743136671673226279136417611437047866715339352615131086508261376 * y + 762243065393215226194585063106859500672983961572259746505341355930884827806744025648471365893472055855115311069072534545316831459721347072 := by
    have hv_eq : v = 5240201 + y := by omega
    rw [hv_eq]; dsimp only [R18Z, negR18_s10, C_lo_1A]; ring
  have hpos : 0 < 10000000000 ^ 8 * ((C_lo_1A : ℤ) * v ^ 8) -
      ((-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131744 * v)) +
        10000000000 ^ 8 * (162 * 1500) ^ 2) := by
    rw [heq]; positivity
  omega

private lemma q_lb_1A_pos {v : ℤ} (hv : 5240201 ≤ v) :
    10 * 12799999999 * v ^ 9 < 100000000 * (10 * Q18Z v - 162 * 1500) := by
  set y := v - 5240201
  have hy0 : 0 ≤ y := by omega
  have heq : 100000000 * (10 * Q18Z v - 162 * 1500) - 10 * 12799999999 * v ^ 9 = 10 * y ^ 9 + 471618090 * y ^ 8 + 9823478347344360 * y ^ 7 + 118596446380533946104840 * y ^ 6 + 914322943204113107832793009260 * y ^ 5 + 4666303445758907483070488063917261260 * y ^ 4 + 15756018903109554891288156673563042914608840 * y ^ 3 + 33914612015173894238229691122384000955296067704360 * y ^ 2 + 42182709346964211166104601174845996100689798721113744090 * y + 23065357939055118281509478075551428941249778274186280766018010 := by
    have hv_eq : v = 5240201 + y := by omega
    rw [hv_eq]; dsimp only [Q18Z]; ring
  have hpos : 0 < 100000000 * (10 * Q18Z v - 162 * 1500) - 10 * 12799999999 * v ^ 9 := by
    rw [heq]; positivity
  omega

/-! ## 4. Zone Glue (`Zone 2`, `Zone 1B`, `Zone 1A`) -/

/-- Common setup for `n ≥ 7000` (`v ≥ 14019`): produces `d ≥ 1`, `162 * d = 5*Q18Z v - Q18Z u`,
and `10^80 * (-25*R18Z v + R18Z u) > 25*10^80*(-R18Z v) - negR18_s10(11958131746*v)`. -/
private lemma asymp18_common {m n : ℕ} (hmn : m ≥ n + 18) (hn : 7000 ≤ n)
    (hmid : P18 (2 * m + 19) = 25 * P18 (2 * n + 19)) :
    let u : ℤ := ((2 * m + 19 : ℕ) : ℤ)
    let v : ℤ := ((2 * n + 19 : ℕ) : ℤ)
    ∃ d : ℤ, 1 ≤ d ∧ 162 * d = 5 * Q18Z v - Q18Z u ∧
      10000000000 * u < 11958131746 * v ∧
      -25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v) <
        10000000000 ^ 8 * (-25 * R18Z v + R18Z u) := by
  intro u v
  have hv14019 : 14019 ≤ v := by omega
  have hv19 : 19 ≤ v := by omega
  have hvu : v < u := by omega
  have hPeq : P18Z u = 25 * P18Z v := by
    have hzm : (P18 (2 * m + 19) : ℤ) = P18Z u := P18_cast (by omega)
    have hzn : (P18 (2 * n + 19) : ℤ) = P18Z v := P18_cast (by omega)
    have hmidz : (P18 (2 * m + 19) : ℤ) = 25 * (P18 (2 * n + 19) : ℤ) := by exact_mod_cast hmid
    linarith only [hzm, hzn, hmidz]
  have hu_hi := u_lt_a_high18 hv19 hvu hPeq
  have hnegR_mono : negR18_s10 (10000000000 * u) < negR18_s10 (11958131746 * v) :=
    negR18_s10_strictMono (by omega) hu_hi
  rw [negR18_s10_eval u] at hnegR_mono
  have hH_gt : -25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131746 * v) <
      10000000000 ^ 8 * (-25 * R18Z v + R18Z u) := by
    linarith only [hnegR_mono]
  have hrem_hi := rem_hi_z2_pos hv14019
  have hquad_pos : 0 < (c8_hi_18 : ℤ) * v ^ 2 - (c6_hi_abs_18 : ℤ) := by
    dsimp [c8_hi_18, c6_hi_abs_18]
    nlinarith only [hv14019]
  have hv6_pos : 0 < (10000000000 ^ 8 : ℤ) * v ^ 6 := by positivity
  have hR_pos : 0 < -25 * R18Z v + R18Z u := by
    have h1 : 0 < 10000000000 ^ 8 * (-25 * R18Z v + R18Z u) := by
      nlinarith only [hH_gt, hrem_hi, hquad_pos, hv6_pos]
    nlinarith only [h1]
  have hsq_eq : (5 * Q18Z v) ^ 2 - Q18Z u ^ 2 = -25 * R18Z v + R18Z u := by
    linarith only [P18Z_eq u, P18Z_eq v, hPeq]
  have hQu_lt : Q18Z u < 5 * Q18Z v := by
    have hQv_pos := Q18Z_pos hv19
    nlinarith only [hsq_eq, hR_pos, hQv_pos]
  obtain ⟨d, hd⟩ := Q18Z_diff_162_dvd ((m : ℤ) + 9) ((n : ℤ) + 9)
  have hu_eq : 2 * ((m : ℤ) + 9) + 1 = u := by dsimp [u]; ring
  have hv_eq : 2 * ((n : ℤ) + 9) + 1 = v := by dsimp [v]; ring
  rw [hu_eq, hv_eq] at hd
  have hd_pos : 1 ≤ d := by nlinarith only [hd, hQu_lt]
  exact ⟨d, hd_pos, hd.symm, hu_hi, hH_gt⟩

private lemma d_le_D_of_thresh {u v d D : ℤ} (hvu : v < u) (hv19 : 19 ≤ v)
    (hPeq : P18Z u = 25 * P18Z v) (hd : 162 * d = 5 * Q18Z v - Q18Z u)
    (hthresh : 0 < 162 * D * (10 * Q18Z v - 162 * D) + 24 * R18Z v) : d ≤ D - 1 := by
  by_contra hge
  have hDd : 162 * D ≤ 162 * d := by omega
  have hQu_pos : 0 < Q18Z u := Q18Z_pos (by omega)
  have hd_lt5Q : 162 * d < 5 * Q18Z v := by linarith only [hd, hQu_pos]
  have hmono_quad : 162 * D * (10 * Q18Z v - 162 * D) ≤ 162 * d * (10 * Q18Z v - 162 * d) := by
    have hdiff : 162 * d * (10 * Q18Z v - 162 * d) - 162 * D * (10 * Q18Z v - 162 * D) =
        (162 * d - 162 * D) * (10 * Q18Z v - 162 * d - 162 * D) := by ring
    have h1 : 0 ≤ 162 * d - 162 * D := by omega
    have h2 : 0 ≤ 10 * Q18Z v - 162 * d - 162 * D := by linarith only [hd_lt5Q, hDd]
    nlinarith only [hdiff, h1, h2]
  have hquad_eq : 162 * d * (10 * Q18Z v - 162 * d) = -25 * R18Z v + R18Z u := by
    have hsq_eq : Q18Z u ^ 2 + R18Z u = 25 * Q18Z v ^ 2 + 25 * R18Z v := by
      linarith only [P18Z_eq u, P18Z_eq v, hPeq]
    have hsub : Q18Z u = 5 * Q18Z v - 162 * d := by linarith only [hd]
    calc 162 * d * (10 * Q18Z v - 162 * d)
        = 25 * Q18Z v ^ 2 - (5 * Q18Z v - 162 * d) ^ 2 := by ring
      _ = 25 * Q18Z v ^ 2 - Q18Z u ^ 2 := by rw [← hsub]
      _ = -25 * R18Z v + R18Z u := by linarith only [hsq_eq]
  have hRu_lt : R18Z u < R18Z v := R18Z_lt_of_lt hv19 hvu
  linarith only [hthresh, hmono_quad, hquad_eq, hRu_lt]

private lemma zone2_excl {m n : ℕ} (hmn : m ≥ n + 18) (hnlo : 7000 ≤ n) (hnhi : n < 68000)
    (hmid : P18 (2 * m + 19) = 25 * P18 (2 * n + 19)) : False := by
  set u : ℤ := ((2 * m + 19 : ℕ) : ℤ)
  set v : ℤ := ((2 * n + 19 : ℕ) : ℤ)
  have hv14019 : 14019 ≤ v := by omega
  have hv19 : 19 ≤ v := by omega
  have hvu : v < u := by omega
  have hPeq : P18Z u = 25 * P18Z v := by
    have hzm : (P18 (2 * m + 19) : ℤ) = P18Z u := P18_cast (by omega)
    have hzn : (P18 (2 * n + 19) : ℤ) = P18Z v := P18_cast (by omega)
    have hmidz : (P18 (2 * m + 19) : ℤ) = 25 * (P18 (2 * n + 19) : ℤ) := by exact_mod_cast hmid
    linarith only [hzm, hzn, hmidz]
  obtain ⟨d, hd1, hd_eq, _, hH_gt⟩ := asymp18_common hmn hnlo hmid
  have hd_le : d ≤ 655000 := d_le_D_of_thresh hvu hv19 hPeq hd_eq (d655001_pos hv14019)
  have hquad_eq : 162 * d * (10 * Q18Z v - 162 * d) = -25 * R18Z v + R18Z u := by
    have hsq_eq : Q18Z u ^ 2 + R18Z u = 25 * Q18Z v ^ 2 + 25 * R18Z v := by
      linarith only [P18Z_eq u, P18Z_eq v, hPeq]
    have hsub : Q18Z u = 5 * Q18Z v - 162 * d := by linarith only [hd_eq]
    calc 162 * d * (10 * Q18Z v - 162 * d)
        = 25 * Q18Z v ^ 2 - (5 * Q18Z v - 162 * d) ^ 2 := by ring
      _ = 25 * Q18Z v ^ 2 - Q18Z u ^ 2 := by rw [← hsub]
      _ = -25 * R18Z v + R18Z u := by linarith only [hsq_eq]
  have hu_low : 11958130390 * v ≤ 10000000000 * u := by
    by_contra hlt
    have hlt' : 10000000000 * u < 11958130390 * v := by omega
    have hQm := Q18_s10_strictMono (by omega) hlt'
    rw [Q18_s10_eval u] at hQm
    have hql := q_low_z2_pos hv14019
    have hQ_ge : 10000000000 ^ 9 * (5 * Q18Z v - 162 * 655000) ≤ 10000000000 ^ 9 * Q18Z u := by
      have h1 : 5 * Q18Z v - 162 * 655000 ≤ Q18Z u := by linarith only [hd_eq, hd_le]
      nlinarith only [h1]
    linarith only [hQm, hql, hQ_ge]
  have hnegR_low : negR18_s10 (11958130390 * v) ≤ negR18_s10 (10000000000 * u) :=
    negR18_s10_mono (by nlinarith only [hv14019]) hu_low
  rw [negR18_s10_eval u] at hnegR_low
  have hlo_z : (c8_hi_18 : ℤ) * v ^ 2 - (c6_hi_abs_18 : ℤ) < 1620 * v * (128 * v ^ 2 - 62013) * d := by
    have hrem := rem_hi_z2_pos hv14019
    have h1 : 10000000000 ^ 8 * v ^ 6 * ((c8_hi_18 : ℤ) * v ^ 2 - (c6_hi_abs_18 : ℤ)) <
        10000000000 ^ 8 * (162 * d * (10 * Q18Z v - 162 * d)) := by
      linarith only [hrem, hH_gt, hquad_eq]
    have h2 : 162 * d * (10 * Q18Z v - 162 * d) < 1620 * Q18Z v * d := by
      have hd2_pos : 0 < (162 * d) ^ 2 := by nlinarith only [hd1]
      linarith only [hd2_pos]
    have h3 : 1620 * Q18Z v * d < 1620 * (v ^ 7 * (128 * v ^ 2 - 62013)) * d := by
      have hqub := q_ub_z2_pos hv14019
      nlinarith only [hqub, hd1]
    have hv6_pos : 0 < (10000000000 ^ 8 : ℤ) * v ^ 6 := by positivity
    nlinarith only [h1, h2, h3, hv6_pos]
  have hhi_z : 1620 * v * (128 * v ^ 2 - 62016) * d < (c8_lo_18 : ℤ) * v ^ 2 - (c6_lo_abs_18 : ℤ) := by
    have hrem := rem_lo_z2_pos hv14019
    have hdsq : (162 * d) ^ 2 ≤ (162 * 655000) ^ 2 := by nlinarith only [hd1, hd_le]
    have h1 : 10000000000 ^ 8 * (1620 * Q18Z v * d) <
        10000000000 ^ 8 * v ^ 6 * ((c8_lo_18 : ℤ) * v ^ 2 - (c6_lo_abs_18 : ℤ)) := by
      have h1a : 1620 * Q18Z v * d = (-25 * R18Z v + R18Z u) + (162 * d) ^ 2 := by
        linarith only [hquad_eq]
      have h1b : 10000000000 ^ 8 * ((-25 * R18Z v + R18Z u) + (162 * d) ^ 2) ≤
          (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958130390 * v)) +
            10000000000 ^ 8 * (162 * 655000) ^ 2 := by
        nlinarith only [hnegR_low, hdsq]
      linarith only [h1a, h1b, hrem]
    have hqlb := q_lb_z2_pos hv14019
    have hQ_gt : 10 * v ^ 7 * (128 * v ^ 2 - 62016) < 10 * Q18Z v := by linarith only [hqlb]
    have h2 : 1620 * v * (128 * v ^ 2 - 62016) * d * v ^ 6 < 1620 * Q18Z v * d := by
      have heq_mul : 1620 * v * (128 * v ^ 2 - 62016) * d * v ^ 6 = 162 * d * (10 * v ^ 7 * (128 * v ^ 2 - 62016)) := by ring
      have heq_mul2 : 1620 * Q18Z v * d = 162 * d * (10 * Q18Z v) := by ring
      rw [heq_mul, heq_mul2]
      exact mul_lt_mul_of_pos_left hQ_gt (by linarith only [hd1])
    have hv6_pos : 0 < (10000000000 ^ 8 : ℤ) * v ^ 6 := by positivity
    nlinarith only [h1, h2, hv6_pos]
  set vN := 2 * n + 19
  have hcert := cert18_ok
  simp only [Bool.and_eq_true] at hcert
  have hstep := checkGrid_sound hcert.1.1.2 (n - 7000) (by omega)
  rw [show 7000 + (n - 7000) = n by omega] at hstep
  dsimp only [stepZone2_18] at hstep
  set dN : ℕ := d.toNat
  have hdN_eq : (dN : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hvN30 : 30 ≤ vN := by omega
  have hvN_sq : 900 ≤ vN * vN := Nat.mul_le_mul hvN30 hvN30
  have hnum_lo_ge : c6_hi_abs_18 ≤ c8_hi_18 * (vN * vN) := by
    have : (c6_hi_abs_18 : ℤ) ≤ (c8_hi_18 : ℤ) * v ^ 2 := by
      dsimp [c8_hi_18, c6_hi_abs_18]; nlinarith only [hv14019]
    zify; rw [show (vN : ℤ) * (vN : ℤ) = v ^ 2 by dsimp [v, vN]; ring]; exact this
  have hden_lo_ge : 62013 ≤ 128 * (vN * vN) := by
    have : 128 * 900 ≤ 128 * (vN * vN) := Nat.mul_le_mul_left 128 hvN_sq
    omega
  have hnum_hi_ge : c6_lo_abs_18 ≤ c8_lo_18 * (vN * vN) := by
    have : (c6_lo_abs_18 : ℤ) ≤ (c8_lo_18 : ℤ) * v ^ 2 := by
      dsimp [c8_lo_18, c6_lo_abs_18]; nlinarith only [hv14019]
    zify; rw [show (vN : ℤ) * (vN : ℤ) = v ^ 2 by dsimp [v, vN]; ring]; exact this
  have hden_hi_ge : 62016 ≤ 128 * (vN * vN) := by
    have : 128 * 900 ≤ 128 * (vN * vN) := Nat.mul_le_mul_left 128 hvN_sq
    omega
  have hd_gt_div : (c8_hi_18 * (vN * vN) - c6_hi_abs_18) / (1620 * vN * (128 * (vN * vN) - 62013)) < dN := by
    apply Nat.div_lt_of_lt_mul
    zify [hnum_lo_ge, hden_lo_ge]
    rw [hdN_eq, show (vN : ℤ) = v from rfl]
    linarith only [hlo_z]
  have hd_le_div : dN ≤ (c8_lo_18 * (vN * vN) - c6_lo_abs_18) / (1620 * vN * (128 * (vN * vN) - 62016)) := by
    have hmul_lt : dN * (1620 * vN * (128 * (vN * vN) - 62016)) < c8_lo_18 * (vN * vN) - c6_lo_abs_18 := by
      zify [hnum_hi_ge, hden_hi_ge]
      rw [hdN_eq, show (vN : ℤ) = v from rfl]
      linarith only [hhi_z]
    have hpos_v : 0 < vN := by omega
    have hpos_sub : 0 < 128 * (vN * vN) - 62016 := by
      have : 128 * 900 ≤ 128 * (vN * vN) := Nat.mul_le_mul_left 128 hvN_sq
      omega
    have hpos_den : 0 < 1620 * vN * (128 * (vN * vN) - 62016) :=
      Nat.mul_pos (Nat.mul_pos (by decide) hpos_v) hpos_sub
    by_contra hlt_div
    have hle_succ : (c8_lo_18 * (vN * vN) - c6_lo_abs_18) / (1620 * vN * (128 * (vN * vN) - 62016)) + 1 ≤ dN := by omega
    have hmul := Nat.mul_le_mul_right (1620 * vN * (128 * (vN * vN) - 62016)) hle_succ
    have hdiv := Nat.lt_mul_div_succ (c8_lo_18 * (vN * vN) - c6_lo_abs_18) hpos_den
    rw [Nat.mul_comm (1620 * vN * (128 * (vN * vN) - 62016))] at hdiv
    omega
  have htrig : (c8_hi_18 * (vN * vN) - c6_hi_abs_18) / (1620 * vN * (128 * (vN * vN) - 62013)) <
      (c8_lo_18 * (vN * vN) - c6_lo_abs_18) / (1620 * vN * (128 * (vN * vN) - 62016)) := by omega
  rw [if_pos htrig] at hstep
  exact check18_v_sound hstep m hmid

private lemma zone1_excl {m n : ℕ} (hmn : m ≥ n + 18) (hn : 68000 ≤ n)
    (hmid : P18 (2 * m + 19) = 25 * P18 (2 * n + 19)) : False := by
  set u : ℤ := ((2 * m + 19 : ℕ) : ℤ)
  set v : ℤ := ((2 * n + 19 : ℕ) : ℤ)
  have hv136019 : 136019 ≤ v := by omega
  have hv134625 : 134625 ≤ v := by omega
  have hv19 : 19 ≤ v := by omega
  have hvu : v < u := by omega
  have hPeq : P18Z u = 25 * P18Z v := by
    have hzm : (P18 (2 * m + 19) : ℤ) = P18Z u := P18_cast (by omega)
    have hzn : (P18 (2 * n + 19) : ℤ) = P18Z v := P18_cast (by omega)
    have hmidz : (P18 (2 * m + 19) : ℤ) = 25 * (P18 (2 * n + 19) : ℤ) := by exact_mod_cast hmid
    linarith only [hzm, hzn, hmidz]
  obtain ⟨d, hd1, hd_eq, _, hH_gt⟩ := asymp18_common hmn (by omega) hmid
  have hd_le : d ≤ 67500 := d_le_D_of_thresh hvu hv19 hPeq hd_eq (d67501_pos hv136019)
  have hquad_eq : 162 * d * (10 * Q18Z v - 162 * d) = -25 * R18Z v + R18Z u := by
    have hsq_eq : Q18Z u ^ 2 + R18Z u = 25 * Q18Z v ^ 2 + 25 * R18Z v := by
      linarith only [P18Z_eq u, P18Z_eq v, hPeq]
    have hsub : Q18Z u = 5 * Q18Z v - 162 * d := by linarith only [hd_eq]
    calc 162 * d * (10 * Q18Z v - 162 * d)
        = 25 * Q18Z v ^ 2 - (5 * Q18Z v - 162 * d) ^ 2 := by ring
      _ = 25 * Q18Z v ^ 2 - Q18Z u ^ 2 := by rw [← hsub]
      _ = -25 * R18Z v + R18Z u := by linarith only [hsq_eq]
  have hu_low_1B : 11958131734 * v ≤ 10000000000 * u := by
    by_contra hlt
    have hlt' : 10000000000 * u < 11958131734 * v := by omega
    have hQm := Q18_s10_strictMono (by omega) hlt'
    rw [Q18_s10_eval u] at hQm
    have hql := q_low_1B_pos hv134625
    have hQ_ge : 10000000000 ^ 9 * (5 * Q18Z v - 162 * 67500) ≤ 10000000000 ^ 9 * Q18Z u := by
      have h1 : 5 * Q18Z v - 162 * 67500 ≤ Q18Z u := by linarith only [hd_eq, hd_le]
      nlinarith only [h1]
    linarith only [hQm, hql, hQ_ge]
  have hnegR_low_1B : negR18_s10 (11958131734 * v) ≤ negR18_s10 (10000000000 * u) :=
    negR18_s10_mono (by nlinarith only [hv134625]) hu_low_1B
  rw [negR18_s10_eval u] at hnegR_low_1B
  have hC_hi_1B_lt : (C_hi_1B : ℤ) < 207360 * d * v := by
    have hrem := rem_hi_1B_pos hv134625
    have h1 : 10000000000 ^ 8 * ((C_hi_1B : ℤ) * v ^ 8) <
        10000000000 ^ 8 * (162 * d * (10 * Q18Z v - 162 * d)) := by
      linarith only [hrem, hH_gt, hquad_eq]
    have h2 : 162 * d * (10 * Q18Z v - 162 * d) < 1620 * Q18Z v * d := by
      have hd2_pos : 0 < (162 * d) ^ 2 := by nlinarith only [hd1]
      linarith only [hd2_pos]
    have h3 : 1620 * Q18Z v * d < 1620 * (128 * v ^ 9) * d := by
      have hqub := Q18_ub_19 hv19
      nlinarith only [hqub, hd1]
    have h8_pos : 0 < (10000000000 ^ 8 : ℤ) * v ^ 8 := by positivity
    have hmul_v8 : (C_hi_1B : ℤ) * v ^ 8 < (207360 * d * v) * v ^ 8 := by
      have h4 : (C_hi_1B : ℤ) * v ^ 8 < 1620 * (128 * v ^ 9) * d := by
        nlinarith only [h1, h2, h3, show (0 : ℤ) < 10000000000 ^ 8 by positivity]
      linarith only [h4, show (1620 : ℤ) * (128 * v ^ 9) * d = (207360 * d * v) * v ^ 8 by ring]
    nlinarith only [hmul_v8, h8_pos]
  set vN := 2 * n + 19
  set dN : ℕ := d.toNat
  have hdN_eq : (dN : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hcert := cert18_ok
  simp only [Bool.and_eq_true] at hcert
  by_cases hd1500 : d ≤ 1500
  · have hv5240201 : 5240201 ≤ v := by
      have h1 : (C_hi_1B : ℤ) < 207360 * 1500 * v := by nlinarith only [hC_hi_1B_lt, hd1500, hv19]
      dsimp [C_hi_1B] at h1
      omega
    have hC_hi_1A_lt : (C_hi_1A : ℤ) < 207360 * d * v := by
      have hrem := rem_hi_1A_pos hv5240201
      have h1 : 10000000000 ^ 8 * ((C_hi_1A : ℤ) * v ^ 8) < 10000000000 ^ 8 * (1620 * Q18Z v * d) := by
        have hd2_pos : 0 < (162 * d) ^ 2 := by nlinarith only [hd1]
        nlinarith only [hrem, hH_gt, hquad_eq, hd2_pos]
      have hqub := Q18_ub_19 hv19
      have h8_pos : 0 < (10000000000 ^ 8 : ℤ) * v ^ 8 := by positivity
      nlinarith only [h1, hqub, hd1, h8_pos,
        show (1620 : ℤ) * (128 * v ^ 9) * d = (207360 * d * v) * v ^ 8 by ring]
    have hu_low_1A : 11958131744 * v ≤ 10000000000 * u := by
      by_contra hlt
      have hlt' : 10000000000 * u < 11958131744 * v := by omega
      have hQm := Q18_s10_strictMono (by omega) hlt'
      rw [Q18_s10_eval u] at hQm
      have hql := q_low_1A_pos hv5240201
      have hQ_ge : 10000000000 ^ 9 * (5 * Q18Z v - 162 * 1500) ≤ 10000000000 ^ 9 * Q18Z u := by
        have h1 : 5 * Q18Z v - 162 * 1500 ≤ Q18Z u := by linarith only [hd_eq, hd1500]
        nlinarith only [h1]
      linarith only [hQm, hql, hQ_ge]
    have hnegR_low_1A : negR18_s10 (11958131744 * v) ≤ negR18_s10 (10000000000 * u) :=
      negR18_s10_mono (by nlinarith only [hv5240201]) hu_low_1A
    rw [negR18_s10_eval u] at hnegR_low_1A
    have hv_hi_1A_lt : 1620 * 12799999999 * d * v < (C_lo_1A : ℤ) * 100000000 := by
      have hrem := rem_lo_1A_pos hv5240201
      have hdsq : (162 * d) ^ 2 ≤ (162 * 1500) ^ 2 := by nlinarith only [hd1, hd1500]
      have h1 : 10000000000 ^ 8 * (1620 * Q18Z v * d) < 10000000000 ^ 8 * ((C_lo_1A : ℤ) * v ^ 8) := by
        have h1a : 1620 * Q18Z v * d = (-25 * R18Z v + R18Z u) + (162 * d) ^ 2 := by
          linarith only [hquad_eq]
        have h1b : 10000000000 ^ 8 * ((-25 * R18Z v + R18Z u) + (162 * d) ^ 2) ≤
            (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131744 * v)) +
              10000000000 ^ 8 * (162 * 1500) ^ 2 := by
          nlinarith only [hnegR_low_1A, hdsq]
        linarith only [h1a, h1b, hrem]
      have hqlb := q_lb_1A_pos hv5240201
      have hQ_gt : 10 * 12799999999 * v ^ 9 < 100000000 * (10 * Q18Z v) := by linarith only [hqlb]
      have h2 : (1620 * 12799999999 * d * v) * v ^ 8 < (100000000 * (1620 * Q18Z v * d)) := by
        have h2a : (1620 * 12799999999 * d * v) * v ^ 8 = 162 * d * (10 * 12799999999 * v ^ 9) := by ring
        have h2b : 100000000 * (1620 * Q18Z v * d) = 162 * d * (100000000 * (10 * Q18Z v)) := by ring
        rw [h2a, h2b]
        exact mul_lt_mul_of_pos_left hQ_gt (by linarith only [hd1])
      have h8_pos : 0 < (10000000000 ^ 8 : ℤ) * v ^ 8 := by positivity
      have h3 : (1620 * 12799999999 * d * v) * v ^ 8 < ((C_lo_1A : ℤ) * 100000000) * v ^ 8 := by
        have h1' : 1620 * Q18Z v * d < (C_lo_1A : ℤ) * v ^ 8 := by
          nlinarith only [h1, show (0 : ℤ) < 10000000000 ^ 8 by positivity]
        nlinarith only [h2, h1']
      nlinarith only [h3, show 0 < v ^ 8 by positivity]
    have hstep := checkGrid_sound hcert.1.2 (dN - 1) (by omega)
    rw [Nat.zero_add] at hstep
    dsimp only [stepZone1A_18] at hstep
    rw [show dN - 1 + 1 = dN by omega] at hstep
    have hv_lo_nat : C_hi_1A / (207360 * dN) < vN := by
      apply Nat.div_lt_of_lt_mul
      zify
      rw [hdN_eq, show (vN : ℤ) = v from rfl]
      linarith only [hC_hi_1A_lt]
    have hv_hi_nat : vN ≤ (C_lo_1A * 100000000) / (1620 * 12799999999 * dN) := by
      have hmul_lt : vN * (1620 * 12799999999 * dN) < C_lo_1A * 100000000 := by
        zify
        rw [hdN_eq, show (vN : ℤ) = v from rfl]
        linarith only [hv_hi_1A_lt]
      have hpos_den : 0 < 1620 * 12799999999 * dN :=
        Nat.mul_pos (by decide) (by omega)
      by_contra hlt_div
      have hle_succ : (C_lo_1A * 100000000) / (1620 * 12799999999 * dN) + 1 ≤ vN := by omega
      have hmul := Nat.mul_le_mul_right (1620 * 12799999999 * dN) hle_succ
      have hdiv := Nat.lt_mul_div_succ (C_lo_1A * 100000000) hpos_den
      rw [Nat.mul_comm (1620 * 12799999999 * dN)] at hdiv
      omega
    have hstart_le := odd_ge_max_start (v0 := 5240201) (v_lo := C_hi_1A / (207360 * dN))
      (by omega) (by omega) hv_lo_nat
    have hchk := checkPair18_sound hstep (by omega) (by omega) hstart_le (by omega)
    exact check18_v_sound hchk m hmid
  · have hd1501 : 1501 ≤ d := by omega
    have hv_hi_1B_lt : 1620 * 127999996 * d * v < (C_lo_1B : ℤ) * 1000000 := by
      have hrem := rem_lo_1B_pos hv134625
      have hdsq : (162 * d) ^ 2 ≤ (162 * 67500) ^ 2 := by nlinarith only [hd1, hd_le]
      have h1 : 10000000000 ^ 8 * (1620 * Q18Z v * d) < 10000000000 ^ 8 * ((C_lo_1B : ℤ) * v ^ 8) := by
        have h1a : 1620 * Q18Z v * d = (-25 * R18Z v + R18Z u) + (162 * d) ^ 2 := by
          linarith only [hquad_eq]
        have h1b : 10000000000 ^ 8 * ((-25 * R18Z v + R18Z u) + (162 * d) ^ 2) ≤
            (-25 * (10000000000 ^ 8 * R18Z v) - negR18_s10 (11958131734 * v)) +
              10000000000 ^ 8 * (162 * 67500) ^ 2 := by
          nlinarith only [hnegR_low_1B, hdsq]
        linarith only [h1a, h1b, hrem]
      have hqlb := q_lb_1B_pos hv134625
      have hQ_gt : 10 * 127999996 * v ^ 9 < 1000000 * (10 * Q18Z v) := by linarith only [hqlb]
      have h2 : (1620 * 127999996 * d * v) * v ^ 8 < (1000000 * (1620 * Q18Z v * d)) := by
        have h2a : (1620 * 127999996 * d * v) * v ^ 8 = 162 * d * (10 * 127999996 * v ^ 9) := by ring
        have h2b : 1000000 * (1620 * Q18Z v * d) = 162 * d * (1000000 * (10 * Q18Z v)) := by ring
        rw [h2a, h2b]
        exact mul_lt_mul_of_pos_left hQ_gt (by linarith only [hd1])
      have h3 : (1620 * 127999996 * d * v) * v ^ 8 < ((C_lo_1B : ℤ) * 1000000) * v ^ 8 := by
        have h1' : 1620 * Q18Z v * d < (C_lo_1B : ℤ) * v ^ 8 := by
          nlinarith only [h1, show (0 : ℤ) < 10000000000 ^ 8 by positivity]
        nlinarith only [h2, h1']
      nlinarith only [h3, show 0 < v ^ 8 by positivity]
    have hstep := checkGrid_sound hcert.2 (dN - 1501) (by omega)
    rw [Nat.zero_add] at hstep
    dsimp only [stepZone1B_18] at hstep
    rw [show dN - 1501 + 1501 = dN by omega] at hstep
    have hv_lo_nat : C_hi_1B / (207360 * dN) < vN := by
      apply Nat.div_lt_of_lt_mul
      zify
      rw [hdN_eq, show (vN : ℤ) = v from rfl]
      linarith only [hC_hi_1B_lt]
    have hv_hi_nat : vN ≤ (C_lo_1B * 1000000) / (1620 * 127999996 * dN) := by
      have hmul_lt : vN * (1620 * 127999996 * dN) < C_lo_1B * 1000000 := by
        zify
        rw [hdN_eq, show (vN : ℤ) = v from rfl]
        linarith only [hv_hi_1B_lt]
      have hpos_den : 0 < 1620 * 127999996 * dN :=
        Nat.mul_pos (by decide) (by omega)
      by_contra hlt_div
      have hle_succ : (C_lo_1B * 1000000) / (1620 * 127999996 * dN) + 1 ≤ vN := by omega
      have hmul := Nat.mul_le_mul_right (1620 * 127999996 * dN) hle_succ
      have hdiv := Nat.lt_mul_div_succ (C_lo_1B * 1000000) hpos_den
      rw [Nat.mul_comm (1620 * 127999996 * dN)] at hdiv
      omega
    have hstart_le := odd_ge_max_start (v0 := 134625) (v_lo := C_hi_1B / (207360 * dN))
      (by omega) (by omega) hv_lo_nat
    have hchk := checkPair18_sound hstep (by omega) (by omega) hstart_le (by omega)
    exact check18_v_sound hchk m hmid

/-! ## 5. Main Theorems -/

/-- No integers `m ≥ n + 18` satisfy `∏_{i=1}^{18} (m + i) = 25 * ∏_{i=1}^{18} (n + i)`. -/
theorem no_sol_twenty_five_eighteen_Icc :
    ¬ ∃ (m n : ℕ), m ≥ n + 18 ∧
      (∏ i ∈ Finset.Icc 1 18, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 18, (n + i)) := by
  rintro ⟨m, n, hmn, heq⟩
  have hmid : P18 (2 * m + 19) = 25 * P18 (2 * n + 19) := by
    have hm := prod18_midpoint m
    have hn := prod18_midpoint n
    have hmul : 2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (m + i)) =
        25 * (2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (n + i))) := by
      calc 2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (m + i))
          = 2 ^ 18 * (25 * (∏ i ∈ Finset.Icc 1 18, (n + i))) := by rw [heq]
        _ = 25 * (2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (n + i))) := by ring
    linarith only [hm, hn, hmul]
  by_cases hn7000 : n < 7000
  · have hcert := cert18_ok
    simp only [Bool.and_eq_true] at hcert
    have hstep := checkGrid_sound hcert.1.1.1 n hn7000
    simp only [Nat.zero_add, stepBase18] at hstep
    exact check18_v_sound hstep m hmid
  · by_cases hn68000 : n < 68000
    · exact zone2_excl hmn (by omega) hn68000 hmid
    · exact zone1_excl hmn (by omega) hmid

/-- Official `Finset.range 18` formulation matching Erdős #686 (`N = 25`, `k = 18`). -/
theorem no_sol_twenty_five_eighteen :
    ¬ ∃ (m n : ℕ), m ≥ n + 18 ∧
      (∏ i ∈ Finset.range 18, (m + i + 1)) = 25 * (∏ i ∈ Finset.range 18, (n + i + 1)) := by
  rintro ⟨m, n, hmn, heq⟩
  rw [prod18_range_eq_Icc m, prod18_range_eq_Icc n] at heq
  exact no_sol_twenty_five_eighteen_Icc ⟨m, n, hmn, heq⟩

private lemma prod18_pos (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 18, (n + i) := by
  apply Nat.pos_of_ne_zero
  intro h0
  obtain ⟨i, hi, hzi⟩ := Finset.prod_eq_zero_iff.mp h0
  rw [Finset.mem_Icc] at hi
  omega

/-- Full unrestricted length-18 exclusion (`m, n : ℕ`, no disjointness assumption needed). -/
theorem length_eighteen (m n : ℕ) :
    (∏ i ∈ Finset.Icc 1 18, (m + i)) ≠ 25 * (∏ i ∈ Finset.Icc 1 18, (n + i)) := by
  intro heq
  by_cases hmn : m ≥ n + 18
  · exact no_sol_twenty_five_eighteen_Icc ⟨m, n, hmn, heq⟩
  · by_cases hn7000 : n < 7000
    · have hmid : P18 (2 * m + 19) = 25 * P18 (2 * n + 19) := by
        have hm := prod18_midpoint m
        have hn := prod18_midpoint n
        have hmul : 2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (m + i)) =
            25 * (2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (n + i))) := by
          calc 2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (m + i))
              = 2 ^ 18 * (25 * (∏ i ∈ Finset.Icc 1 18, (n + i))) := by rw [heq]
            _ = 25 * (2 ^ 18 * (∏ i ∈ Finset.Icc 1 18, (n + i))) := by ring
        linarith only [hm, hn, hmul]
      have hcert := cert18_ok
      simp only [Bool.and_eq_true] at hcert
      have hstep := checkGrid_sound hcert.1.1.1 n hn7000
      simp only [Nat.zero_add, stepBase18] at hstep
      exact check18_v_sound hstep m hmid
    · have h_pt : ∀ i ∈ Finset.Icc 1 18, 10 * (m + i) ≤ 11 * (n + i) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        omega
      have hprod : ∏ i ∈ Finset.Icc 1 18, (10 * (m + i)) ≤
          ∏ i ∈ Finset.Icc 1 18, (11 * (n + i)) := Finset.prod_le_prod' h_pt
      have hcard : (Finset.Icc 1 18).card = 18 := by simp [Nat.card_Icc]
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
          Finset.prod_mul_distrib, Finset.prod_const, hcard, heq] at hprod
      have hP : 0 < ∏ i ∈ Finset.Icc 1 18, (n + i) := prod18_pos n
      have hpow : 11 ^ 18 < 10 ^ 18 * 25 := by norm_num
      nlinarith

/-- Direct interface to the `k = 18` case of `Erdos686.erdos_686.variants.twenty_five`. -/
theorem no_ratio_twenty_five_eighteen (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 18, (m + i)) / (∏ i ∈ Finset.Icc 1 18, (n + i)) := by
  intro h
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 18, (n + i) := prod18_pos n
  have hd : ((∏ i ∈ Finset.Icc 1 18, (n + i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hz := (eq_div_iff hd).mp h
  have hn : 25 * (∏ i ∈ Finset.Icc 1 18, (n + i)) = ∏ i ∈ Finset.Icc 1 18, (m + i) := by
    exact_mod_cast hz
  exact length_eighteen m n hn.symm

/-- Bridge theorem discharging the `k = 18` branch of `Erdos686.erdos_686.variants.twenty_five`. -/
theorem erdos_686_variants_twenty_five_k18_bridge :
    ¬ ∃ (n : ℕ), ∃ m ≥ n + 18,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 18, (m + i)) / (∏ i ∈ Finset.Icc 1 18, (n + i)) := by
  rintro ⟨n, m, _, h⟩
  exact no_ratio_twenty_five_eighteen m n h

end Contribution.Erdos686EighteenTwentyFive
