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
# Unconditional Exclusion of k = 14 for Erdős Problem #686 (N = 25)

Proves via scaled polynomial square-completion (`256 * P_14(x) = Q_tilde_7(x)^2 + R_tilde_6(x)`),
Taylor-shift positivity, and `d`-pinching (`1 ≤ d ≤ 5000`) together with kernel-checked finite
bracketing that no natural numbers `m, n : ℕ` (even without disjointness) satisfy
`∏ i ∈ Finset.Icc 1 14, (m + i) = 25 * ∏ i ∈ Finset.Icc 1 14, (n + i)` or the corresponding
rational quotient equation `(25 : ℚ) = (∏ i ∈ Finset.Icc 1 14, (m + i)) / (∏ i ∈ Finset.Icc 1 14, (n + i))`.
-/

namespace Contribution.Erdos686FourteenTwentyFive

def P14 (x : ℕ) : ℕ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) * (x2 - 121) * (x2 - 169)

def P14Z (x : ℤ) : ℤ :=
  (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25) * (x ^ 2 - 49) *
    (x ^ 2 - 81) * (x ^ 2 - 121) * (x ^ 2 - 169)

def P14Z_hom (A B : ℤ) : ℤ :=
  (A ^ 2 - B ^ 2) * (A ^ 2 - 9 * B ^ 2) * (A ^ 2 - 25 * B ^ 2) * (A ^ 2 - 49 * B ^ 2) *
    (A ^ 2 - 81 * B ^ 2) * (A ^ 2 - 121 * B ^ 2) * (A ^ 2 - 169 * B ^ 2)

def Q14Z (x : ℤ) : ℤ :=
  16 * x ^ 7 - 3640 * x ^ 5 + 202566 * x ^ 3 - 2656355 * x

def R14Z (x : ℤ) : ℤ :=
  -49 * (26915252 * x ^ 6 - 1894021220 * x ^ 4 + 29702673049 * x ^ 2 + 95406854400)

def Q14Z_hom (A B : ℤ) : ℤ :=
  16 * A ^ 7 - 3640 * A ^ 5 * B ^ 2 + 202566 * A ^ 3 * B ^ 4 - 2656355 * A * B ^ 6

def R14Z_hom (A B : ℤ) : ℤ :=
  -49 * (26915252 * A ^ 6 - 1894021220 * A ^ 4 * B ^ 2 + 29702673049 * A ^ 2 * B ^ 4 + 95406854400 * B ^ 6)

private lemma mul_lt_mul_nat {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hd : 0 < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hcd))
    (Nat.mul_lt_mul_of_pos_right hab hd)

private lemma mul_lt_mul_int {a b c d : ℤ} (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hcd : c < d) :
    a * c < b * d := by nlinarith

private lemma P14_strictMono {a b : ℕ} (ha : 13 ≤ a) (hab : a < b) : P14 a < P14 b := by
  have hb : 13 ≤ b := by omega
  have hab2 : a * a < b * b := mul_lt_mul_nat hab hab (by omega)
  have ha2 : 169 ≤ a * a := Nat.mul_le_mul ha ha
  have hb2 : 169 < b * b := Nat.lt_of_le_of_lt ha2 hab2
  dsimp only [P14]
  have p1 := mul_lt_mul_nat (by omega : a * a - 1 < b * b - 1) (by omega : a * a - 9 < b * b - 9) (by omega)
  have p2 := mul_lt_mul_nat p1 (by omega : a * a - 25 < b * b - 25) (by omega)
  have p3 := mul_lt_mul_nat p2 (by omega : a * a - 49 < b * b - 49) (by omega)
  have p4 := mul_lt_mul_nat p3 (by omega : a * a - 81 < b * b - 81) (by omega)
  have p5 := mul_lt_mul_nat p4 (by omega : a * a - 121 < b * b - 121) (by omega)
  exact mul_lt_mul_nat p5 (by omega : a * a - 169 < b * b - 169) (by omega)

private lemma P14_mono {a b : ℕ} (ha : 13 ≤ a) (hab : a ≤ b) : P14 a ≤ P14 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P14_strictMono ha hlt)

private lemma P14_cast {x : ℕ} (hx : 13 ≤ x) : (P14 x : ℤ) = P14Z (x : ℤ) := by
  have h169 : 169 ≤ x * x := Nat.mul_le_mul hx hx
  have h121 : 121 ≤ x * x := by omega
  have h81  : 81  ≤ x * x := by omega
  have h49  : 49  ≤ x * x := by omega
  have h25  : 25  ≤ x * x := by omega
  have h9   : 9   ≤ x * x := by omega
  have h1   : 1   ≤ x * x := by omega
  dsimp only [P14, P14Z]
  zify [h1, h9, h25, h49, h81, h121, h169]
  ring

private lemma P14Z_hom_mono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 13 * B ≤ A1) (hA : A1 ≤ A2) :
    P14Z_hom A1 B ≤ P14Z_hom A2 B := by
  rcases eq_or_lt_of_le hA with rfl | hlt
  · exact le_rfl
  · have hA1_pos : 0 ≤ A1 := by nlinarith
    have hA2_gt : A1 ^ 2 < A2 ^ 2 := by nlinarith
    have n1 : 0 ≤ A1 ^ 2 - B ^ 2 := by nlinarith
    have n2 : 0 ≤ A1 ^ 2 - 9 * B ^ 2 := by nlinarith
    have n3 : 0 ≤ A1 ^ 2 - 25 * B ^ 2 := by nlinarith
    have n4 : 0 ≤ A1 ^ 2 - 49 * B ^ 2 := by nlinarith
    have n5 : 0 ≤ A1 ^ 2 - 81 * B ^ 2 := by nlinarith
    have n6 : 0 ≤ A1 ^ 2 - 121 * B ^ 2 := by nlinarith
    have n7 : 0 ≤ A1 ^ 2 - 169 * B ^ 2 := by nlinarith
    dsimp only [P14Z_hom]
    have p1 := mul_lt_mul_int n1 (by linarith : A1 ^ 2 - B ^ 2 < A2 ^ 2 - B ^ 2) n2 (by linarith : A1 ^ 2 - 9 * B ^ 2 < A2 ^ 2 - 9 * B ^ 2)
    have p2 := mul_lt_mul_int (mul_nonneg n1 n2) p1 n3 (by linarith : A1 ^ 2 - 25 * B ^ 2 < A2 ^ 2 - 25 * B ^ 2)
    have p3 := mul_lt_mul_int (mul_nonneg (mul_nonneg n1 n2) n3) p2 n4 (by linarith : A1 ^ 2 - 49 * B ^ 2 < A2 ^ 2 - 49 * B ^ 2)
    have p4 := mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) p3 n5 (by linarith : A1 ^ 2 - 81 * B ^ 2 < A2 ^ 2 - 81 * B ^ 2)
    have p5 := mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) n5) p4 n6 (by linarith : A1 ^ 2 - 121 * B ^ 2 < A2 ^ 2 - 121 * B ^ 2)
    have p6 := mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) n5) n6) p5 n7 (by linarith : A1 ^ 2 - 169 * B ^ 2 < A2 ^ 2 - 169 * B ^ 2)
    exact le_of_lt p6

private lemma prod14_midpoint (m : ℕ) :
    2 ^ 14 * (∏ i ∈ Finset.Icc 1 14, (m + i)) = P14 (2 * m + 15) := by
  have hIcc : Finset.Icc 1 14 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  zify
  rw [P14_cast (by omega)]
  dsimp only [P14Z]
  push_cast
  ring

private lemma prod14_range_eq_Icc (m : ℕ) :
    (∏ i ∈ Finset.range 14, (m + i + 1)) = ∏ i ∈ Finset.Icc 1 14, (m + i) := by
  have hIcc : Finset.Icc 1 14 = (Finset.range 14).image (· + 1) := by decide
  rw [hIcc, Finset.prod_image (fun a _ b _ hab => by omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ### Finite Bracket Verification for 0 ≤ n ≤ 9882 and Pinched Odd v for 1 ≤ d ≤ 5000 -/

def findBracket14 (v : ℕ) : ℕ :=
  let rhs := 25 * P14 v
  let u0 := 2 * ((v * 125849895) / 200000000) + 1
  if P14 u0 < rhs then
    let u1 := u0 + 2
    if P14 u1 < rhs then u1 + 2 else u1
  else
    u0

def check14_v (v : ℕ) : Bool :=
  let rhs := 25 * P14 v
  let u := findBracket14 v
  decide (u ≥ 15 ∧ u % 2 = 1 ∧ P14 (u - 2) < rhs ∧ rhs < P14 u)

def c6_h_adj14 : ℕ := 27731413067389039465523372080074334936610900652000000
def c6_l_adj14 : ℕ := 27731427566490472236753410788947887499266631874809772
def den6_14    : ℕ := 1000000000000000000000000000000000000000000

def checkInterval14 (v_cur v_end : ℕ) : ℕ → Bool
  | 0 => decide (v_cur > v_end)
  | fuel + 1 =>
    if v_cur > v_end then true
    else check14_v v_cur && checkInterval14 (v_cur + 2) v_end fuel

def checkD14_d (d_val : ℕ) : Bool :=
  let v_lo := c6_h_adj14 / (320 * d_val * den6_14)
  let v_hi := (c6_l_adj14 * 100000) / (20 * 1599999 * d_val * den6_14) + 1
  let v_start := 2 * (max 19779 (v_lo + 1) / 2) + 1
  checkInterval14 v_start (v_hi - 1) 60

private lemma check14_v_sound {v : ℕ} (hc : check14_v v = true) :
    ∀ m : ℕ, P14 (2 * m + 15) ≠ 25 * P14 v := by
  simp only [check14_v, decide_eq_true_eq] at hc
  rcases hc with ⟨hu15, hu_odd, hlo, hhi⟩
  intro m heq
  set u := findBracket14 v
  set x := 2 * m + 15
  by_cases hxu : x < u
  · have hle : x ≤ u - 2 := by omega
    have hpm : P14 x ≤ P14 (u - 2) := P14_mono (by omega) hle
    omega
  · have hge : u ≤ x := by omega
    have hpm : P14 u ≤ P14 x := P14_mono (by omega) hge
    omega

private lemma checkInterval14_sound :
    ∀ (fuel v_cur v_end v : ℕ),
      checkInterval14 v_cur v_end fuel = true →
      v_cur % 2 = 1 → v % 2 = 1 → v_cur ≤ v → v ≤ v_end →
      check14_v v = true
  | 0, v_cur, v_end, v, hchk, _, _, hle, hle_end => by
    simp only [checkInterval14, decide_eq_true_eq] at hchk
    omega
  | fuel + 1, v_cur, v_end, v, hchk, hco, hvo, hle, hle_end => by
    dsimp only [checkInterval14] at hchk
    split_ifs at hchk with hgt
    · omega
    · simp only [Bool.and_eq_true] at hchk
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact hchk.1
      · exact checkInterval14_sound fuel (v_cur + 2) v_end v hchk.2 (by omega) hvo (by omega) hle_end

private lemma checkD14_d_sound {d v : ℕ} (hc : checkD14_d d = true)
    (hv_odd : v % 2 = 1) (hv_ge : 19779 ≤ v)
    (hv_lo : c6_h_adj14 / (320 * d * den6_14) < v)
    (hv_hi : v < (c6_l_adj14 * 100000) / (20 * 1599999 * d * den6_14) + 1) :
    check14_v v = true := by
  set M := max 19779 (c6_h_adj14 / (320 * d * den6_14) + 1)
  set v_start := 2 * (M / 2) + 1
  have hMv : M ≤ v := by omega
  have hvs_le : v_start ≤ v := by omega
  exact checkInterval14_sound 60 v_start _ v hc (by omega) hv_odd hvs_le (by omega)

private lemma base14_0 : ∀ i : Fin 1000, check14_v (2 * (0    + i) + 15) = true := by decide +kernel
private lemma base14_1 : ∀ i : Fin 1000, check14_v (2 * (1000 + i) + 15) = true := by decide +kernel
private lemma base14_2 : ∀ i : Fin 1000, check14_v (2 * (2000 + i) + 15) = true := by decide +kernel
private lemma base14_3 : ∀ i : Fin 1000, check14_v (2 * (3000 + i) + 15) = true := by decide +kernel
private lemma base14_4 : ∀ i : Fin 1000, check14_v (2 * (4000 + i) + 15) = true := by decide +kernel
private lemma base14_5 : ∀ i : Fin 1000, check14_v (2 * (5000 + i) + 15) = true := by decide +kernel
private lemma base14_6 : ∀ i : Fin 1000, check14_v (2 * (6000 + i) + 15) = true := by decide +kernel
private lemma base14_7 : ∀ i : Fin 1000, check14_v (2 * (7000 + i) + 15) = true := by decide +kernel
private lemma base14_8 : ∀ i : Fin 1000, check14_v (2 * (8000 + i) + 15) = true := by decide +kernel
private lemma base14_9 : ∀ i : Fin 883,  check14_v (2 * (9000 + i) + 15) = true := by decide +kernel

private lemma base14_tile_sound {s M : ℕ}
    (h : ∀ i : Fin M, check14_v (2 * (s + i) + 15) = true) :
    ∀ n, s ≤ n → n < s + M → check14_v (2 * n + 15) = true := by
  intro n hsn hnM
  have hi := h ⟨n - s, by omega⟩
  have heq : s + (n - s) = n := by omega
  simpa [heq] using hi

private lemma base14_ok {n : ℕ} (hn : n ≤ 9882) : check14_v (2 * n + 15) = true := by
  rcases (show n < 1000 ∨ (1000 ≤ n ∧ n < 2000) ∨ (2000 ≤ n ∧ n < 3000) ∨
      (3000 ≤ n ∧ n < 4000) ∨ (4000 ≤ n ∧ n < 5000) ∨ (5000 ≤ n ∧ n < 6000) ∨
      (6000 ≤ n ∧ n < 7000) ∨ (7000 ≤ n ∧ n < 8000) ∨ (8000 ≤ n ∧ n < 9000) ∨
      (9000 ≤ n ∧ n < 9883) by omega) with
    h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact base14_tile_sound base14_0 n (by omega) h0
  · exact base14_tile_sound base14_1 n h1 h2
  · exact base14_tile_sound base14_2 n h1 h2
  · exact base14_tile_sound base14_3 n h1 h2
  · exact base14_tile_sound base14_4 n h1 h2
  · exact base14_tile_sound base14_5 n h1 h2
  · exact base14_tile_sound base14_6 n h1 h2
  · exact base14_tile_sound base14_7 n h1 h2
  · exact base14_tile_sound base14_8 n h1 h2
  · exact base14_tile_sound base14_9 n h1 h2

private lemma d14_0 : ∀ i : Fin 500, checkD14_d (0    + i + 1) = true := by decide +kernel
private lemma d14_1 : ∀ i : Fin 500, checkD14_d (500  + i + 1) = true := by decide +kernel
private lemma d14_2 : ∀ i : Fin 500, checkD14_d (1000 + i + 1) = true := by decide +kernel
private lemma d14_3 : ∀ i : Fin 500, checkD14_d (1500 + i + 1) = true := by decide +kernel
private lemma d14_4 : ∀ i : Fin 500, checkD14_d (2000 + i + 1) = true := by decide +kernel
private lemma d14_5 : ∀ i : Fin 500, checkD14_d (2500 + i + 1) = true := by decide +kernel
private lemma d14_6 : ∀ i : Fin 500, checkD14_d (3000 + i + 1) = true := by decide +kernel
private lemma d14_7 : ∀ i : Fin 500, checkD14_d (3500 + i + 1) = true := by decide +kernel
private lemma d14_8 : ∀ i : Fin 500, checkD14_d (4000 + i + 1) = true := by decide +kernel
private lemma d14_9 : ∀ i : Fin 500, checkD14_d (4500 + i + 1) = true := by decide +kernel

private lemma d14_tile_sound {s M : ℕ}
    (h : ∀ i : Fin M, checkD14_d (s + i + 1) = true) :
    ∀ d, s + 1 ≤ d → d ≤ s + M → checkD14_d d = true := by
  intro d hd1 hdM
  have hi := h ⟨d - s - 1, by omega⟩
  have heq : s + (d - s - 1) + 1 = d := by omega
  simpa [heq] using hi

private lemma d14_ok {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d ≤ 5000) : checkD14_d d = true := by
  rcases (show d ≤ 500 ∨ (501 ≤ d ∧ d ≤ 1000) ∨ (1001 ≤ d ∧ d ≤ 1500) ∨
      (1501 ≤ d ∧ d ≤ 2000) ∨ (2001 ≤ d ∧ d ≤ 2500) ∨ (2501 ≤ d ∧ d ≤ 3000) ∨
      (3001 ≤ d ∧ d ≤ 3500) ∨ (3501 ≤ d ∧ d ≤ 4000) ∨ (4001 ≤ d ∧ d ≤ 4500) ∨
      (4501 ≤ d ∧ d ≤ 5000) by omega) with
    h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact d14_tile_sound d14_0 d hd1 h0
  · exact d14_tile_sound d14_1 d h1 h2
  · exact d14_tile_sound d14_2 d h1 h2
  · exact d14_tile_sound d14_3 d h1 h2
  · exact d14_tile_sound d14_4 d h1 h2
  · exact d14_tile_sound d14_5 d h1 h2
  · exact d14_tile_sound d14_6 d h1 h2
  · exact d14_tile_sound d14_7 d h1 h2
  · exact d14_tile_sound d14_8 d h1 h2
  · exact d14_tile_sound d14_9 d h1 h2

/-! ### Asymptotic Polynomial Square-Completion & d-Pinching for n ≥ 9883 (v ≥ 19779) -/

private lemma P14Z_sq (x : ℤ) : 256 * P14Z x = Q14Z x ^ 2 + R14Z x := by
  dsimp only [P14Z, Q14Z, R14Z]; ring

private lemma P14Z_hom_scale (x B : ℤ) : P14Z_hom (B * x) B = B ^ 14 * P14Z x := by
  dsimp only [P14Z_hom, P14Z]; ring

private lemma Q14Z_hom_scale (x B : ℤ) : Q14Z_hom (B * x) B = B ^ 7 * Q14Z x := by
  dsimp only [Q14Z_hom, Q14Z]; ring

private lemma R14Z_hom_scale (x B : ℤ) : R14Z_hom (B * x) B = B ^ 6 * R14Z x := by
  dsimp only [R14Z_hom, R14Z]; ring

private lemma Q14Z_ge_15 {x : ℤ} (hx : 15 ≤ x) : 613439925 ≤ Q14Z x := by
  have ht : 0 ≤ x - 15 := by omega
  have hid : Q14Z x - 613439925 =
      16 * (x - 15) ^ 7 + 1680 * (x - 15) ^ 6 + 71960 * (x - 15) ^ 5 + 1617000 * (x - 15) ^ 4 +
      20362566 * (x - 15) ^ 3 + 141415470 * (x - 15) ^ 2 + 488450695 * (x - 15) := by
    dsimp only [Q14Z]; ring
  have hnonneg : 0 ≤ Q14Z x - 613439925 := by rw [hid]; positivity
  linarith

private lemma Q14Z_pos_15 {x : ℤ} (hx : 15 ≤ x) : 0 < Q14Z x := by
  linarith [Q14Z_ge_15 hx]

private lemma Q14Z_odd (k : ℤ) : Q14Z (2 * k + 1) % 2 = 1 := by
  dsimp only [Q14Z]
  have : 16 * (2 * k + 1) ^ 7 - 3640 * (2 * k + 1) ^ 5 + 202566 * (2 * k + 1) ^ 3 - 2656355 * (2 * k + 1) =
      2 * (8 * (2 * k + 1) ^ 7 - 1820 * (2 * k + 1) ^ 5 + 101283 * (2 * k + 1) ^ 3 - 2656355 * k - 1328178) + 1 := by ring
  rw [this]
  omega

private lemma Q14Z_hom_strictMono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 15 * B ≤ A1) (hA : A1 < A2) :
    Q14Z_hom A1 B < Q14Z_hom A2 B := by
  set t := A1 - 15 * B
  set h := A2 - A1
  have ht : 0 ≤ t := by omega
  have hh : 0 < h := by omega
  have hid : Q14Z_hom A2 B - Q14Z_hom A1 B =
      112 * t ^ 6 * h + 336 * t ^ 5 * h ^ 2 + 10080 * t ^ 5 * h * B + 560 * t ^ 4 * h ^ 3 +
      25200 * t ^ 4 * h ^ 2 * B + 359800 * t ^ 4 * h * B ^ 2 + 560 * t ^ 3 * h ^ 4 +
      33600 * t ^ 3 * h ^ 3 * B + 719600 * t ^ 3 * h ^ 2 * B ^ 2 + 6468000 * t ^ 3 * h * B ^ 3 +
      336 * t ^ 2 * h ^ 5 + 25200 * t ^ 2 * h ^ 4 * B + 719600 * t ^ 2 * h ^ 3 * B ^ 2 +
      9702000 * t ^ 2 * h ^ 2 * B ^ 3 + 61087698 * t ^ 2 * h * B ^ 4 + 112 * t * h ^ 6 +
      10080 * t * h ^ 5 * B + 359800 * t * h ^ 4 * B ^ 2 + 6468000 * t * h ^ 3 * B ^ 3 +
      61087698 * t * h ^ 2 * B ^ 4 + 282830940 * t * h * B ^ 5 + 16 * h ^ 7 + 1680 * h ^ 6 * B +
      71960 * h ^ 5 * B ^ 2 + 1617000 * h ^ 4 * B ^ 3 + 20362566 * h ^ 3 * B ^ 4 +
      141415470 * h ^ 2 * B ^ 5 + 488450695 * h * B ^ 6 := by
    dsimp only [Q14Z_hom, t, h]; ring
  linarith [show 0 < Q14Z_hom A2 B - Q14Z_hom A1 B by rw [hid]; positivity]

private lemma Q14Z_hom_mono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 15 * B ≤ A1) (hA : A1 ≤ A2) :
    Q14Z_hom A1 B ≤ Q14Z_hom A2 B := by
  rcases eq_or_lt_of_le hA with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (Q14Z_hom_strictMono hB hA1 hlt)

private lemma negR14Z_hom_strictMono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 15 * B ≤ A1) (hA : A1 < A2) :
    -R14Z_hom A1 B < -R14Z_hom A2 B := by
  set t := A1 - 15 * B
  set h := A2 - A1
  have ht : 0 ≤ t := by omega
  have hh : 0 < h := by omega
  have hid : (-R14Z_hom A2 B) - (-R14Z_hom A1 B) =
      7913084088 * t ^ 5 * h + 19782710220 * t ^ 4 * h ^ 2 + 593481306600 * t ^ 4 * h * B +
      26376946960 * t ^ 3 * h ^ 3 + 1186962613200 * t ^ 3 * h ^ 2 * B + 17433211038880 * t ^ 3 * h * B ^ 2 +
      19782710220 * t ^ 2 * h ^ 4 + 1186962613200 * t ^ 2 * h ^ 3 * B + 26149816558320 * t ^ 2 * h ^ 2 * B ^ 2 +
      250361320809600 * t ^ 2 * h * B ^ 3 + 7913084088 * t * h ^ 5 + 593481306600 * t * h ^ 4 * B +
      17433211038880 * t * h ^ 3 * B ^ 2 + 250361320809600 * t * h ^ 2 * B ^ 3 + 1755331264327802 * t * h * B ^ 4 +
      1318847348 * h ^ 6 + 118696261320 * h ^ 5 * B + 4358302759720 * h ^ 4 * B ^ 2 +
      83453773603200 * h ^ 3 * B ^ 3 + 877665632163901 * h ^ 2 * B ^ 4 + 4799766121677030 * h * B ^ 5 := by
    dsimp only [R14Z_hom, t, h]; ring
  linarith [show 0 < (-R14Z_hom A2 B) - (-R14Z_hom A1 B) by rw [hid]; positivity]

private lemma negR14Z_strictMono {a b : ℤ} (ha : 15 ≤ a) (hab : a < b) : -R14Z a < -R14Z b := by
  have := negR14Z_hom_strictMono (A1 := a) (A2 := b) (B := 1) (by omega) (by omega) hab
  rw [show R14Z_hom a 1 = R14Z a from by dsimp only [R14Z_hom, R14Z]; ring,
      show R14Z_hom b 1 = R14Z b from by dsimp only [R14Z_hom, R14Z]; ring] at this
  exact this

private lemma P14Z_3v2_gt {v : ℤ} (hv : 15 ≤ v) : 2 ^ 14 * 25 * P14Z v < P14Z_hom (3 * v) 2 := by
  have ht : 0 ≤ v - 15 := by omega
  have hid : P14Z_hom (3 * v) 2 - 2 ^ 14 * 25 * P14Z v =
      4373369 * (v - 15) ^ 14 + 918407490 * (v - 15) ^ 13 + 88763875655 * (v - 15) ^ 12 +
      5232129984900 * (v - 15) ^ 11 + 210068766700793 * (v - 15) ^ 10 + 6075099224143950 * (v - 15) ^ 9 +
      130445533564160815 * (v - 15) ^ 8 + 2111570494200967800 * (v - 15) ^ 7 +
      25878674697235867507 * (v - 15) ^ 6 + 238801792350897405630 * (v - 15) ^ 5 +
      1632087966676624662205 * (v - 15) ^ 4 + 8005188017681842287300 * (v - 15) ^ 3 +
      26617530470331025010331 * (v - 15) ^ 2 + 53664154431842281074930 * (v - 15) +
      49460387868456156917325 := by
    dsimp only [P14Z_hom, P14Z]; ring
  linarith [show 0 < P14Z_hom (3 * v) 2 - 2 ^ 14 * 25 * P14Z v by rw [hid]; positivity]

private lemma R14Z_3v2_gt {v : ℤ} (hv : 15 ≤ v) : 0 < -25 * 2 ^ 6 * R14Z v + R14Z_hom (3 * v) 2 := by
  have ht : 0 ≤ v - 15 := by omega
  have hid : -25 * 2 ^ 6 * R14Z v + R14Z_hom (3 * v) 2 =
      1148716040108 * (v - 15) ^ 6 + 103384443609720 * (v - 15) ^ 5 +
      3758494852605220 * (v - 15) ^ 4 + 70433025741733200 * (v - 15) ^ 3 +
      714555943737992356 * (v - 15) ^ 2 + 3698716615672030680 * (v - 15) +
      7573470782507966700 := by
    dsimp only [R14Z, R14Z_hom]; ring
  rw [hid]; positivity

private lemma d_ge_5001_impossible {v : ℤ} (hv : 19779 ≤ v) :
    0 < 10002 * (10 * Q14Z v - 10002) + 24 * R14Z v := by
  have ht : 0 ≤ v - 19779 := by omega
  have hid : 10002 * (10 * Q14Z v - 10002) + 24 * R14Z v =
      1600320 * (v - 19779) ^ 7 + 189916768608 * (v - 19779) ^ 6 +
      9390936252701472 * (v - 19779) ^ 5 + 247658822698312835040 * (v - 19779) ^ 4 +
      3673858746822266987079480 * (v - 19779) ^ 3 +
      29066508740705259360913311936 * (v - 19779) ^ 2 +
      95821775001247199044511622187740 * (v - 19779) +
      22764319909492233509609867501400 := by
    dsimp only [Q14Z, R14Z]; ring
  rw [hid]; positivity

private lemma Q14Z_alow_v0 {v : ℤ} (hv : 19779 ≤ v) :
    Q14Z_hom (12584989 * v) 10000000 < 10000000 ^ 7 * (5 * Q14Z v - 10000) := by
  have ht : 0 ≤ v - 19779 := by omega
  have hid : 10000000 ^ 7 * (5 * Q14Z v - 10000) - Q14Z_hom (12584989 * v) 10000000 =
      225343211717380314380297974995074357251074736 * (v - 19779) ^ 7 +
      31199443691906456666895395531993029984483050423408 * (v - 19779) ^ 6 +
      1784193443698146874390671096060524497625270762973760496 * (v - 19779) ^ 5 +
      54392828548973375212136710501829853389572530701430014750640 * (v - 19779) ^ 4 +
      944608772693667427299561494990991499060664143123584261752908560 * (v - 19779) ^ 3 +
      9133619541615002927615728203070608281445553544663239867926467044944 * (v - 19779) ^ 2 +
      43105572276950945878601610417646214795379810639511786309239197227315792 * (v - 19779) +
      63775177192216805197520810026211761044929495283589835069767154565582721424 := by
    dsimp only [Q14Z, Q14Z_hom]; ring
  linarith [show 0 < 10000000 ^ 7 * (5 * Q14Z v - 10000) - Q14Z_hom (12584989 * v) 10000000 by
    rw [hid]; positivity]

private lemma Q14Z_ahigh_15 {v : ℤ} (hv : 15 ≤ v) :
    10000000 ^ 7 * (5 * Q14Z v) < Q14Z_hom (12584990 * v) 10000000 := by
  have ht : 0 ≤ v - 15 := by omega
  have hid : Q14Z_hom (12584990 * v) 10000000 - 10000000 ^ 7 * (5 * Q14Z v) =
      219631333554054755002393017458649519840000000 * (v - 15) ^ 7 +
      23061290023175749275251266833158199583200000000 * (v - 15) ^ 6 +
      67088938752138814229311956260043892118981244000000000 * (v - 15) ^ 5 +
      5031618518507858921762527404152917302974531100000000000 * (v - 15) ^ 4 +
      144857483920507835134411142259459709544617966500000000000 * (v - 15) ^ 3 +
      1990139449588238937640683214701128785901561698500000000000 * (v - 15) ^ 2 +
      12969819329249444250915535913293090179507808492500000000000 * (v - 15) +
      31879672222112611740427804545081483598945303912500000000000 := by
    dsimp only [Q14Z, Q14Z_hom]; ring
  linarith [show 0 < Q14Z_hom (12584990 * v) 10000000 - 10000000 ^ 7 * (5 * Q14Z v) by
    rw [hid]; positivity]

private lemma Q14Z_lt_16v7 {v : ℤ} (hv : 15 ≤ v) : Q14Z v < 16 * v ^ 7 := by
  have ht : 0 ≤ v - 15 := by omega
  have hid : 16 * v ^ 7 - Q14Z v =
      3640 * (v - 15) ^ 5 + 273000 * (v - 15) ^ 4 + 7987434 * (v - 15) ^ 3 +
      113734530 * (v - 15) ^ 2 + 787299305 * (v - 15) + 2120310075 := by
    dsimp only [Q14Z]; ring
  linarith [show 0 < 16 * v ^ 7 - Q14Z v by rw [hid]; positivity]

private lemma Q14Z_gt_eps_v0 {v : ℤ} (hv : 19779 ≤ v) : 1599999 * v ^ 7 < 100000 * Q14Z v := by
  have ht : 0 ≤ v - 19779 := by omega
  have hid : 100000 * Q14Z v - 1599999 * v ^ 7 =
      1 * (v - 19779) ^ 7 + 138453 * (v - 19779) ^ 6 + 7851385661 * (v - 19779) ^ 5 +
      234822408314865 * (v - 19779) ^ 4 + 3932552343696314835 * (v - 19779) ^ 3 +
      35403052811255962032879 * (v - 19779) ^ 2 + 140565432952617252108471247 * (v - 19779) +
      82363069133729171952103342059 := by
    dsimp only [Q14Z]; ring
  linarith [show 0 < 100000 * Q14Z v - 1599999 * v ^ 7 by rw [hid]; positivity]

private lemma Hh14_lb_v0 {v : ℤ} (hv : 19779 ≤ v) :
    (c6_h_adj14 : ℤ) * v ^ 6 < -25 * (den6_14 : ℤ) * R14Z v + R14Z_hom (12584990 * v) 10000000 := by
  have ht : 0 ≤ v - 19779 := by omega
  have hid : (-25 * (den6_14 : ℤ) * R14Z v + R14Z_hom (12584990 * v) 10000000) - (c6_h_adj14 : ℤ) * v ^ 6 =
      6000000000000000000000000000000000000000000000 * (v - 19779) ^ 6 +
      712044000000000000000000000000000000000000000000000 * (v - 19779) ^ 5 +
      33121424757730661389546962329184519780000000000000000000 * (v - 19779) ^ 4 +
      763381921259259006495397471635762466914480000000000000000000 * (v - 19779) ^ 3 +
      8874404410070264724037424136313217749652249880000000000000000000 * (v - 19779) ^ 2 +
      44368353228205512004024590558364250074914566917680000000000000000000 * (v - 19779) +
      39773504396229303828749801560549081689313304766198180000000000000000000 := by
    dsimp only [R14Z, R14Z_hom, c6_h_adj14, den6_14]; ring
  linarith [show 0 < (-25 * (den6_14 : ℤ) * R14Z v + R14Z_hom (12584990 * v) 10000000) - (c6_h_adj14 : ℤ) * v ^ 6 by
    rw [hid]; positivity]

private lemma Hl14_ub_v0 {v : ℤ} (hv : 19779 ≤ v) :
    -25 * (den6_14 : ℤ) * R14Z v + R14Z_hom (12584989 * v) 10000000 < ((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 := by
  have ht : 0 ≤ v - 19779 := by omega
  have hid : ((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 - (-25 * (den6_14 : ℤ) * R14Z v + R14Z_hom (12584989 * v) 10000000) =
      6000000000000000000000000000000000000000000000 * (v - 19779) ^ 6 +
      712044000000000000000000000000000000000000000000000 * (v - 19779) ^ 5 +
      37296166696263846188995161335133017178102000000000000000 * (v - 19779) ^ 4 +
      1093670804468250455088541184190383787062717832000000000000000 * (v - 19779) ^ 3 +
      18673580073394958790633987999338776596470243998692000000000000000 * (v - 19779) ^ 2 +
      173580281727255949124381799182068195239176637366752712000000000000000 * (v - 19779) +
      678694174509263258690839380256521381356534482619250472662000000000000000 := by
    dsimp only [R14Z, R14Z_hom, c6_l_adj14, den6_14]; ring
  linarith [show 0 < ((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 - (-25 * (den6_14 : ℤ) * R14Z v + R14Z_hom (12584989 * v) 10000000) by
    rw [hid]; positivity]

private lemma pinch14_v_gt_lo (v d Qv diffR : ℤ) (hv : 19779 ≤ v) (hd : 1 ≤ d)
    (h1 : (c6_h_adj14 : ℤ) * v ^ 6 < (den6_14 : ℤ) * diffR)
    (hprod : 2 * d * (10 * Qv - 2 * d) = diffR) (hQ7 : Qv < 16 * v ^ 7) :
    (c6_h_adj14 : ℤ) < 320 * d * (den6_14 : ℤ) * v := by
  have h20 : 2 * d * (10 * Qv - 2 * d) < 2 * d * (10 * (16 * v ^ 7)) := by
    have hd2 : 0 < 4 * d ^ 2 := by nlinarith
    have hlt : 10 * Qv - 2 * d < 10 * (16 * v ^ 7) := by nlinarith
    exact mul_lt_mul_of_pos_left hlt (by omega)
  have h2 : diffR < 320 * d * v ^ 7 := by linarith
  have hv6_pos : 0 < v ^ 6 := by positivity
  have hden_pos : (0 : ℤ) < den6_14 := by norm_num [den6_14]
  have hmul : (c6_h_adj14 : ℤ) * v ^ 6 < (320 * d * (den6_14 : ℤ) * v) * v ^ 6 := by
    calc (c6_h_adj14 : ℤ) * v ^ 6
        < (den6_14 : ℤ) * diffR := h1
      _ < (den6_14 : ℤ) * (320 * d * v ^ 7) := mul_lt_mul_of_pos_left h2 hden_pos
      _ = (320 * d * (den6_14 : ℤ) * v) * v ^ 6 := by ring
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hv6_pos)

private lemma pinch14_v_lt_hi (v d Qv diffR : ℤ) (hv : 19779 ≤ v) (hd1 : 1 ≤ d) (hd_ub : d ≤ 5000)
    (h1 : (den6_14 : ℤ) * diffR < ((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6)
    (hprod : 2 * d * (10 * Qv - 2 * d) = diffR) (hQ7 : 1599999 * v ^ 7 < 100000 * Qv) :
    20 * 1599999 * d * (den6_14 : ℤ) * v < (c6_l_adj14 : ℤ) * 100000 := by
  have hprod_eq : 20 * d * Qv - 4 * d ^ 2 = diffR := by rw [← hprod]; ring
  have hd2 : 4 * d ^ 2 < v ^ 6 := by
    have hsq : d ^ 2 ≤ 5000 ^ 2 := by nlinarith
    have hnum : 4 * (5000 : ℤ) ^ 2 < 19779 ^ 6 := by norm_num
    have hv2 : 19779 ^ 2 ≤ v ^ 2 := by nlinarith
    have hv4 : 19779 ^ 4 ≤ v ^ 4 := by nlinarith
    have hv6 : (19779 : ℤ) ^ 6 ≤ v ^ 6 := by nlinarith
    omega
  have hden_pos : (0 : ℤ) < den6_14 := by norm_num [den6_14]
  have hv6_pos : 0 < v ^ 6 := by positivity
  have hstep1 : 20 * d * (1599999 * v ^ 7) < 20 * d * (100000 * Qv) :=
    mul_lt_mul_of_pos_left hQ7 (by omega)
  have hstep2 : (den6_14 : ℤ) * (20 * d * (1599999 * v ^ 7)) < (den6_14 : ℤ) * (20 * d * (100000 * Qv)) :=
    mul_lt_mul_of_pos_left hstep1 hden_pos
  have hstep3 : (den6_14 : ℤ) * (20 * d * Qv) < ((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 + (den6_14 : ℤ) * (4 * d ^ 2) := by
    rw [← hprod_eq, mul_sub] at h1
    linarith
  have hstep4 : 100000 * ((den6_14 : ℤ) * (20 * d * Qv)) <
      100000 * (((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 + (den6_14 : ℤ) * (4 * d ^ 2)) :=
    mul_lt_mul_of_pos_left hstep3 (by norm_num)
  have hstep5 : 100000 * (((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 + (den6_14 : ℤ) * (4 * d ^ 2)) <
      100000 * (((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 + (den6_14 : ℤ) * v ^ 6) := by
    have hdd : (den6_14 : ℤ) * (4 * d ^ 2) < (den6_14 : ℤ) * v ^ 6 := mul_lt_mul_of_pos_left hd2 hden_pos
    linarith
  have hmul : (20 * 1599999 * d * (den6_14 : ℤ) * v) * v ^ 6 < ((c6_l_adj14 : ℤ) * 100000) * v ^ 6 := by
    have hL : (20 * 1599999 * d * (den6_14 : ℤ) * v) * v ^ 6 = (den6_14 : ℤ) * (20 * d * (1599999 * v ^ 7)) := by ring
    have hM : (den6_14 : ℤ) * (20 * d * (100000 * Qv)) = 100000 * ((den6_14 : ℤ) * (20 * d * Qv)) := by ring
    have hR : 100000 * (((c6_l_adj14 : ℤ) - (den6_14 : ℤ)) * v ^ 6 + (den6_14 : ℤ) * v ^ 6) =
        ((c6_l_adj14 : ℤ) * 100000) * v ^ 6 := by ring
    linarith
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hv6_pos)

private lemma asymp14_pinch {m n : ℕ} (hnm : n < m) (hn : 9883 ≤ n)
    (heq : P14 (2 * m + 15) = 25 * P14 (2 * n + 15)) : False := by
  set u : ℤ := 2 * (m : ℤ) + 15
  set v : ℤ := 2 * (n : ℤ) + 15
  have hv19779 : 19779 ≤ v := by omega
  have hv15 : 15 ≤ v := by omega
  have huv : v < u := by omega
  have hu15 : 15 ≤ u := by omega
  have heqZ : P14Z u = 25 * P14Z v := by
    have h1 := P14_cast (x := 2 * m + 15) (by omega)
    have h2 := P14_cast (x := 2 * n + 15) (by omega)
    have h3 : ((P14 (2 * m + 15) : ℕ) : ℤ) = ((25 * P14 (2 * n + 15) : ℕ) : ℤ) := by exact_mod_cast heq
    push_cast at h1 h2 h3
    linarith
  have hu_lt_3v2 : 2 * u < 3 * v := by
    by_contra hge
    push Not at hge
    have hmono := P14Z_hom_mono (A1 := 3 * v) (A2 := 2 * u) (B := 2) (by omega) (by omega) hge
    rw [P14Z_hom_scale u 2] at hmono
    have h3v2 := P14Z_3v2_gt hv15
    linarith
  have hsq_diff : (5 * Q14Z v) ^ 2 - Q14Z u ^ 2 = -25 * R14Z v + R14Z u := by
    have hsu := P14Z_sq u
    have hsv := P14Z_sq v
    nlinarith
  have hR_pos : 0 < -25 * R14Z v + R14Z u := by
    have hmono := negR14Z_hom_strictMono (A1 := 2 * u) (A2 := 3 * v) (B := 2) (by omega) (by omega) hu_lt_3v2
    rw [R14Z_hom_scale u 2] at hmono
    have h3v2 := R14Z_3v2_gt hv15
    linarith
  have hR_ub : -25 * R14Z v + R14Z u < -24 * R14Z v := by
    have h1 := negR14Z_strictMono hv15 huv
    linarith
  have hQv_pos : 0 < Q14Z v := Q14Z_pos_15 hv15
  have hQu_pos : 0 < Q14Z u := Q14Z_pos_15 hu15
  have hdiff_pos : 0 < 5 * Q14Z v - Q14Z u := by
    have hmul : (5 * Q14Z v - Q14Z u) * (5 * Q14Z v + Q14Z u) = (5 * Q14Z v) ^ 2 - Q14Z u ^ 2 := by ring
    nlinarith
  have hdiff_even : (5 * Q14Z v - Q14Z u) % 2 = 0 := by
    have hov : Q14Z v % 2 = 1 := by
      have : v = 2 * ((n : ℤ) + 7) + 1 := by ring
      rw [this]; exact Q14Z_odd _
    have hou : Q14Z u % 2 = 1 := by
      have : u = 2 * ((m : ℤ) + 7) + 1 := by ring
      rw [this]; exact Q14Z_odd _
    omega
  set d : ℤ := (5 * Q14Z v - Q14Z u) / 2
  have hd_eq : 5 * Q14Z v - Q14Z u = 2 * d := by omega
  have hd_pos : 1 ≤ d := by omega
  have hprod_d : 2 * d * (10 * Q14Z v - 2 * d) = -25 * R14Z v + R14Z u := by
    have : 2 * d * (10 * Q14Z v - 2 * d) = (5 * Q14Z v) ^ 2 - Q14Z u ^ 2 := by
      rw [← hd_eq]; ring
    linarith
  have hd_le_5000 : d ≤ 5000 := by
    by_contra hge
    have hd_ge : 5001 ≤ d := by omega
    have hd_lt : d < 5 * Q14Z v - 5001 := by
      have hQge := Q14Z_ge_15 hv15
      linarith [hd_eq, hQu_pos, hQge]
    have hquad : 10002 * (10 * Q14Z v - 10002) ≤ 2 * d * (10 * Q14Z v - 2 * d) := by
      have hid : 2 * d * (10 * Q14Z v - 2 * d) - 10002 * (10 * Q14Z v - 10002) =
          4 * (d - 5001) * (5 * Q14Z v - d - 5001) := by ring
      have h1 : 0 ≤ d - 5001 := by omega
      have h2 : 0 < 5 * Q14Z v - d - 5001 := by omega
      nlinarith
    have himp := d_ge_5001_impossible hv19779
    linarith
  have hu_lb : 12584989 * v < 10000000 * u := by
    have hQ1 : Q14Z_hom (12584989 * v) 10000000 < 10000000 ^ 7 * Q14Z u := by
      have h5Q : 5 * Q14Z v - 10000 ≤ Q14Z u := by omega
      have ha := Q14Z_alow_v0 hv19779
      linarith [show 10000000 ^ 7 * (5 * Q14Z v - 10000) ≤ 10000000 ^ 7 * Q14Z u by gcongr]
    rw [← Q14Z_hom_scale u 10000000] at hQ1
    by_contra hle
    push Not at hle
    have hmono := Q14Z_hom_mono (A1 := 10000000 * u) (A2 := 12584989 * v) (B := 10000000)
      (by omega) (by omega) hle
    linarith
  have hu_ub : 10000000 * u < 12584990 * v := by
    have hQ1 : 10000000 ^ 7 * Q14Z u < Q14Z_hom (12584990 * v) 10000000 := by
      have h5Q : Q14Z u < 5 * Q14Z v := by omega
      have ha := Q14Z_ahigh_15 hv15
      linarith [show 10000000 ^ 7 * Q14Z u < 10000000 ^ 7 * (5 * Q14Z v) by gcongr]
    rw [← Q14Z_hom_scale u 10000000] at hQ1
    by_contra hle
    push Not at hle
    have hmono := Q14Z_hom_mono (A1 := 12584990 * v) (A2 := 10000000 * u) (B := 10000000)
      (by omega) (by omega) hle
    linarith
  have hR_lb_scaled : R14Z_hom (12584990 * v) 10000000 < (den6_14 : ℤ) * R14Z u := by
    have := negR14Z_hom_strictMono (A1 := 10000000 * u) (A2 := 12584990 * v) (B := 10000000)
      (by omega) (by omega) hu_ub
    rw [R14Z_hom_scale u 10000000] at this
    have hden : (den6_14 : ℤ) = 10000000 ^ 6 := by norm_num [den6_14]
    rw [hden]; linarith
  have hR_ub_scaled : (den6_14 : ℤ) * R14Z u < R14Z_hom (12584989 * v) 10000000 := by
    have := negR14Z_hom_strictMono (A1 := 12584989 * v) (A2 := 10000000 * u) (B := 10000000)
      (by omega) (by omega) hu_lb
    rw [R14Z_hom_scale u 10000000] at this
    have hden : (den6_14 : ℤ) = 10000000 ^ 6 := by norm_num [den6_14]
    rw [hden]; linarith
  have hv_gt_lo : (c6_h_adj14 : ℤ) < 320 * d * (den6_14 : ℤ) * v :=
    pinch14_v_gt_lo v d (Q14Z v) (-25 * R14Z v + R14Z u)
      hv19779 hd_pos (by linarith [Hh14_lb_v0 hv19779, hR_lb_scaled]) hprod_d (Q14Z_lt_16v7 hv15)
  have hv_lt_hi : 20 * 1599999 * d * (den6_14 : ℤ) * v < (c6_l_adj14 : ℤ) * 100000 :=
    pinch14_v_lt_hi v d (Q14Z v) (-25 * R14Z v + R14Z u)
      hv19779 hd_pos hd_le_5000 (by linarith [Hl14_ub_v0 hv19779, hR_ub_scaled]) hprod_d (Q14Z_gt_eps_v0 hv19779)
  set dN : ℕ := d.toNat
  have hdN_eq : (dN : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hdN1 : 1 ≤ dN := by omega
  have hdN_le : dN ≤ 5000 := by omega
  set vN : ℕ := 2 * n + 15
  have hvN_eq : (vN : ℤ) = v := by dsimp only [vN, v]; push_cast; ring
  have hvlo_nat : c6_h_adj14 / (320 * dN * den6_14) < vN := by
    apply Nat.div_lt_of_lt_mul
    zify
    rw [hdN_eq, hvN_eq]
    linarith [hv_gt_lo]
  have hvhi_nat : vN < (c6_l_adj14 * 100000) / (20 * 1599999 * dN * den6_14) + 1 := by
    have hlt_mul : vN * (20 * 1599999 * dN * den6_14) < c6_l_adj14 * 100000 := by
      zify
      rw [hdN_eq, hvN_eq]
      linarith [hv_lt_hi]
    have hden_pos : 0 < den6_14 := by norm_num [den6_14]
    have hpos_M : 0 < 20 * 1599999 * dN * den6_14 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hdN1) hden_pos
    by_contra hge
    have hle : (c6_l_adj14 * 100000) / (20 * 1599999 * dN * den6_14) + 1 ≤ vN := by omega
    have hmul_le := Nat.mul_le_mul_right (20 * 1599999 * dN * den6_14) hle
    have hdiv := Nat.lt_mul_div_succ (c6_l_adj14 * 100000) hpos_M
    rw [Nat.mul_comm (20 * 1599999 * dN * den6_14)] at hdiv
    omega
  have hchk := checkD14_d_sound (d14_ok hdN1 hdN_le) (by omega) (by omega) hvlo_nat hvhi_nat
  exact check14_v_sound hchk m heq

/-! ### Main Theorems -/

private lemma prod14_pos (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 14, (n + i) := by
  have hP15 : 0 < P14 15 := by decide
  have hPpos : 0 < P14 (2 * n + 15) := lt_of_lt_of_le hP15 (P14_mono (by omega) (by omega))
  linarith [prod14_midpoint n]

/-- Unconditional length-14 product exclusion for ratio 25 (no disjointness hypothesis needed). -/
theorem length_fourteen (m n : ℕ) :
    (∏ i ∈ Finset.Icc 1 14, (m + i)) ≠ 25 * (∏ i ∈ Finset.Icc 1 14, (n + i)) := by
  intro heq
  have hmid : P14 (2 * m + 15) = 25 * P14 (2 * n + 15) := by
    have hm := prod14_midpoint m
    have hn := prod14_midpoint n
    have hmul : 2 ^ 14 * (∏ i ∈ Finset.Icc 1 14, (m + i)) =
        25 * (2 ^ 14 * (∏ i ∈ Finset.Icc 1 14, (n + i))) := by
      calc 2 ^ 14 * (∏ i ∈ Finset.Icc 1 14, (m + i))
          = 2 ^ 14 * (25 * (∏ i ∈ Finset.Icc 1 14, (n + i))) := by rw [heq]
        _ = 25 * (2 ^ 14 * (∏ i ∈ Finset.Icc 1 14, (n + i))) := by ring
    linarith
  have hnm : n < m := by
    by_contra hle
    have hmono : P14 (2 * m + 15) ≤ P14 (2 * n + 15) := P14_mono (by omega) (by omega)
    have hpos : 0 < P14 (2 * n + 15) := by
      have : 0 < ∏ i ∈ Finset.Icc 1 14, (n + i) := prod14_pos n
      linarith [prod14_midpoint n]
    omega
  by_cases hn9883 : 9883 ≤ n
  · exact asymp14_pinch hnm hn9883 hmid
  · exact check14_v_sound (base14_ok (by omega)) m hmid

/-- Exclusion of ratio 25 for length-14 consecutive blocks with `m ≥ n + 14` (`Finset.Icc` form). -/
theorem erdos686_n25_k14_Icc :
    ¬ ∃ (m n : ℕ), m ≥ n + 14 ∧ (∏ i ∈ Finset.Icc 1 14, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 14, (n + i)) := by
  rintro ⟨m, n, _, heq⟩
  exact length_fourteen m n heq

/-- Exclusion of ratio 25 for length-14 consecutive blocks with `m ≥ n + 14` (`Finset.range` form). -/
theorem erdos686_n25_k14_range :
    ¬ ∃ (m n : ℕ), m ≥ n + 14 ∧
      (∏ i ∈ Finset.range 14, (m + i + 1)) = 25 * (∏ i ∈ Finset.range 14, (n + i + 1)) := by
  rintro ⟨m, n, hmn, heq⟩
  rw [prod14_range_eq_Icc m, prod14_range_eq_Icc n] at heq
  exact length_fourteen m n heq

/-- Direct interface to the `k = 14` case of `Erdos686.erdos_686.variants.twenty_five` (no disjointness needed). -/
theorem no_ratio_twenty_five_fourteen (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 14, (m + i)) / (∏ i ∈ Finset.Icc 1 14, (n + i)) := by
  intro h
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 14, (n + i) := prod14_pos n
  have hd : ((∏ i ∈ Finset.Icc 1 14, (n + i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hz := (eq_div_iff hd).mp h
  have hn : 25 * (∏ i ∈ Finset.Icc 1 14, (n + i)) = ∏ i ∈ Finset.Icc 1 14, (m + i) := by
    exact_mod_cast hz
  exact length_fourteen m n hn.symm

/-- Existential target-shaped exclusion for `k = 14` matching `FormalConjectures.ErdosProblems.«686»`. -/
theorem no_sol_twenty_five_fourteen :
    ¬ ∃ (n : ℕ), ∃ m ≥ n + 14,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 14, (m + i)) / (∏ i ∈ Finset.Icc 1 14, (n + i)) := by
  rintro ⟨n, m, _, h⟩
  exact no_ratio_twenty_five_fourteen m n h

end Contribution.Erdos686FourteenTwentyFive
