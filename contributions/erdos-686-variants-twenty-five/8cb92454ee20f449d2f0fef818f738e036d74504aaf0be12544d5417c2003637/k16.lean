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
# Unconditional Exclusion of k = 16 for Erdős Problem #686 (N = 25)

Proves via exact polynomial square-completion (`P_16(x) = Q_8(x^2)^2 + R_6(x^2)`),
Taylor-shift positivity, and `d`-pinching (`1 ≤ d ≤ 1069`) together with kernel-checked
finite bracketing that no natural numbers `m, n : ℕ` (even without disjointness) satisfy
`∏ i ∈ Finset.Icc 1 16, (m + i) = 25 * ∏ i ∈ Finset.Icc 1 16, (n + i)` or the corresponding
rational quotient equation `(25 : ℚ) = (∏ i ∈ Finset.Icc 1 16, (m + i)) / (∏ i ∈ Finset.Icc 1 16, (n + i))`.
-/

namespace Contribution.Erdos686SixteenTwentyFive

def P16 (x : ℕ) : ℕ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) *
    (x2 - 81) * (x2 - 121) * (x2 - 169) * (x2 - 225)

def P16_X (X : ℤ) : ℤ :=
  (X - 1) * (X - 9) * (X - 25) * (X - 49) *
    (X - 81) * (X - 121) * (X - 169) * (X - 225)

def Q8Z (X : ℤ) : ℤ :=
  X ^ 4 - 340 * X ^ 3 + 31926 * X ^ 2 - 862580 * X - 2167279

def R6Z (X : ℤ) : ℤ :=
  -8388608 * (255 * X ^ 3 - 33439 * X ^ 2 + 1034705 * X + 70127)

def Q8Z_hom (A B : ℤ) : ℤ :=
  A ^ 4 - 340 * A ^ 3 * B + 31926 * A ^ 2 * B ^ 2 - 862580 * A * B ^ 3 - 2167279 * B ^ 4

def R6Z_hom (A B : ℤ) : ℤ :=
  -8388608 * (255 * A ^ 3 - 33439 * A ^ 2 * B + 1034705 * A * B ^ 2 + 70127 * B ^ 3)

private lemma mul_lt_mul_nat {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hd : 0 < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hcd))
    (Nat.mul_lt_mul_of_pos_right hab hd)

private lemma mul_lt_mul_int {a b c d : ℤ} (ha : 0 ≤ a) (hab : a < b) (hc : 0 ≤ c) (hcd : c < d) :
    a * c < b * d := by nlinarith

private lemma P16_strictMono {a b : ℕ} (ha : 15 ≤ a) (hab : a < b) : P16 a < P16 b := by
  have hb : 15 ≤ b := by omega
  have hab2 : a * a < b * b := mul_lt_mul_nat hab hab (by omega)
  have ha2 : 225 ≤ a * a := Nat.mul_le_mul ha ha
  have hb2 : 225 < b * b := Nat.lt_of_le_of_lt ha2 hab2
  dsimp only [P16]
  have p1 := mul_lt_mul_nat (by omega : a * a - 1 < b * b - 1) (by omega : a * a - 9 < b * b - 9) (by omega)
  have p2 := mul_lt_mul_nat p1 (by omega : a * a - 25 < b * b - 25) (by omega)
  have p3 := mul_lt_mul_nat p2 (by omega : a * a - 49 < b * b - 49) (by omega)
  have p4 := mul_lt_mul_nat p3 (by omega : a * a - 81 < b * b - 81) (by omega)
  have p5 := mul_lt_mul_nat p4 (by omega : a * a - 121 < b * b - 121) (by omega)
  have p6 := mul_lt_mul_nat p5 (by omega : a * a - 169 < b * b - 169) (by omega)
  exact mul_lt_mul_nat p6 (by omega : a * a - 225 < b * b - 225) (by omega)

private lemma P16_mono {a b : ℕ} (ha : 15 ≤ a) (hab : a ≤ b) : P16 a ≤ P16 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P16_strictMono ha hlt)

private lemma P16_cast {x : ℕ} (hx : 15 ≤ x) : (P16 x : ℤ) = P16_X ((x : ℤ) ^ 2) := by
  have h225 : 225 ≤ x * x := Nat.mul_le_mul hx hx
  have h169 : 169 ≤ x * x := by omega
  have h121 : 121 ≤ x * x := by omega
  have h81  : 81  ≤ x * x := by omega
  have h49  : 49  ≤ x * x := by omega
  have h25  : 25  ≤ x * x := by omega
  have h9   : 9   ≤ x * x := by omega
  have h1   : 1   ≤ x * x := by omega
  dsimp only [P16, P16_X]
  zify [h1, h9, h25, h49, h81, h121, h169, h225]
  ring

private lemma P16_X_strictMono {A B : ℤ} (hA : 225 ≤ A) (hAB : A < B) : P16_X A < P16_X B := by
  dsimp only [P16_X]
  have n1 : 0 ≤ A - 1 := by omega
  have n2 : 0 ≤ A - 9 := by omega
  have n3 : 0 ≤ A - 25 := by omega
  have n4 : 0 ≤ A - 49 := by omega
  have n5 : 0 ≤ A - 81 := by omega
  have n6 : 0 ≤ A - 121 := by omega
  have n7 : 0 ≤ A - 169 := by omega
  have n8 : 0 ≤ A - 225 := by omega
  have p1 := mul_lt_mul_int n1 (by omega : A - 1 < B - 1) n2 (by omega : A - 9 < B - 9)
  have p2 := mul_lt_mul_int (mul_nonneg n1 n2) p1 n3 (by omega : A - 25 < B - 25)
  have p3 := mul_lt_mul_int (mul_nonneg (mul_nonneg n1 n2) n3) p2 n4 (by omega : A - 49 < B - 49)
  have p4 := mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) p3 n5 (by omega : A - 81 < B - 81)
  have p5 := mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) n5) p4 n6 (by omega : A - 121 < B - 121)
  have p6 := mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) n5) n6) p5 n7 (by omega : A - 169 < B - 169)
  exact mul_lt_mul_int (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg n1 n2) n3) n4) n5) n6) n7) p6 n8 (by omega : A - 225 < B - 225)

private lemma P16_X_mono {A B : ℤ} (hA : 225 ≤ A) (hAB : A ≤ B) : P16_X A ≤ P16_X B := by
  rcases eq_or_lt_of_le hAB with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P16_X_strictMono hA hlt)

private lemma prod16_midpoint (m : ℕ) :
    2 ^ 16 * (∏ i ∈ Finset.Icc 1 16, (m + i)) = P16 (2 * m + 17) := by
  have hIcc : Finset.Icc 1 16 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  zify
  rw [P16_cast (by omega)]
  dsimp only [P16_X]
  push_cast
  ring

private lemma prod16_range_eq_Icc (m : ℕ) :
    (∏ i ∈ Finset.range 16, (m + i + 1)) = ∏ i ∈ Finset.Icc 1 16, (m + i) := by
  have hIcc : Finset.Icc 1 16 = (Finset.range 16).image (· + 1) := by decide
  rw [hIcc, Finset.prod_image (fun a _ b _ hab => by omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ### Finite Bracket Verification for 0 ≤ n ≤ 1088 and Pinched Odd v for 1 ≤ d ≤ 1069 -/

def findBracket16 (v : ℕ) : ℕ :=
  let rhs := 25 * P16 v
  let u0 := 2 * ((v * 12228445) / 20000000) + 1
  if P16 u0 < rhs then
    let u1 := u0 + 2
    if P16 u1 < rhs then u1 + 2 else u1
  else
    u0

def check16_v (v : ℕ) : Bool :=
  let rhs := 25 * P16 v
  let u := findBracket16 v
  decide (u ≥ 17 ∧ u % 2 = 1 ∧ P16 (u - 2) < rhs ∧ rhs < P16 u)

def c3_h_adj16 : ℕ := 46323463164021247836160000
def c3_l_adj16 : ℕ := 46326406659153144479907840
def den3_16    : ℕ := 1000000000000000

def nextOddAbove (V_lo : ℕ) : ℕ :=
  let s := Nat.sqrt V_lo
  if s % 2 = 0 then s + 1 else s + 2

def checkVWindow (v V_hi : ℕ) : ℕ → Bool
  | 0 => decide (v * v ≥ V_hi)
  | fuel + 1 =>
    if v * v ≥ V_hi then true
    else check16_v v && checkVWindow (v + 2) V_hi fuel

def checkD16_d (d : ℕ) : Bool :=
  let V_lo := c3_h_adj16 / (10 * d * den3_16)
  let V_hi := (c3_l_adj16 * 14000) / (10 * 13999 * d * den3_16) + 1
  checkVWindow (nextOddAbove V_lo) V_hi 10

private lemma check16_v_sound {v : ℕ} (hc : check16_v v = true) :
    ∀ m : ℕ, P16 (2 * m + 17) ≠ 25 * P16 v := by
  simp only [check16_v, decide_eq_true_eq] at hc
  rcases hc with ⟨hu17, hu_odd, hlo, hhi⟩
  intro m heq
  set u := findBracket16 v
  set x := 2 * m + 17
  by_cases hxu : x < u
  · have hle : x ≤ u - 2 := by omega
    have hpm : P16 x ≤ P16 (u - 2) := P16_mono (by omega) hle
    omega
  · have hge : u ≤ x := by omega
    have hpm : P16 u ≤ P16 x := P16_mono (by omega) hge
    omega

private lemma nextOddAbove_odd (V_lo : ℕ) : nextOddAbove V_lo % 2 = 1 := by
  dsimp only [nextOddAbove]
  split_ifs <;> omega

private lemma nextOddAbove_sound {V_lo v : ℕ} (hv : v % 2 = 1) (hgt : V_lo < v * v) :
    nextOddAbove V_lo ≤ v := by
  dsimp only [nextOddAbove]
  set s := Nat.sqrt V_lo
  have hs : s * s ≤ V_lo := Nat.sqrt_le V_lo
  have hsv : s < v := by
    by_contra hle
    have hmul : v * v ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
    omega
  split_ifs <;> omega

private lemma checkVWindow_sound :
    ∀ (fuel v_start V_hi v : ℕ),
      checkVWindow v_start V_hi fuel = true →
      v_start % 2 = 1 → v % 2 = 1 → v_start ≤ v → v * v < V_hi →
      check16_v v = true
  | 0, v_start, V_hi, v, hchk, _, _, hle, hlt => by
    simp only [checkVWindow, decide_eq_true_eq] at hchk
    have : v_start * v_start ≤ v * v := Nat.mul_le_mul hle hle
    omega
  | fuel + 1, v_start, V_hi, v, hchk, hso, hvo, hle, hlt => by
    dsimp only [checkVWindow] at hchk
    split_ifs at hchk with hge
    · have : v_start * v_start ≤ v * v := Nat.mul_le_mul hle hle
      omega
    · simp only [Bool.and_eq_true] at hchk
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt_v
      · exact hchk.1
      · have hle2 : v_start + 2 ≤ v := by omega
        exact checkVWindow_sound fuel (v_start + 2) V_hi v hchk.2 (by omega) hvo hle2 hlt

private lemma checkD16_d_sound {d v : ℕ} (hc : checkD16_d d = true)
    (hv : v % 2 = 1)
    (hlo : c3_h_adj16 / (10 * d * den3_16) < v * v)
    (hhi : v * v < (c3_l_adj16 * 14000) / (10 * 13999 * d * den3_16) + 1) :
    check16_v v = true :=
  checkVWindow_sound 10 _ _ v hc (nextOddAbove_odd _) hv (nextOddAbove_sound hv hlo) hhi

private lemma base16_0  : ∀ i : Fin 100, check16_v (2 * (0    + i) + 17) = true := by decide +kernel
private lemma base16_1  : ∀ i : Fin 100, check16_v (2 * (100  + i) + 17) = true := by decide +kernel
private lemma base16_2  : ∀ i : Fin 100, check16_v (2 * (200  + i) + 17) = true := by decide +kernel
private lemma base16_3  : ∀ i : Fin 100, check16_v (2 * (300  + i) + 17) = true := by decide +kernel
private lemma base16_4  : ∀ i : Fin 100, check16_v (2 * (400  + i) + 17) = true := by decide +kernel
private lemma base16_5  : ∀ i : Fin 100, check16_v (2 * (500  + i) + 17) = true := by decide +kernel
private lemma base16_6  : ∀ i : Fin 100, check16_v (2 * (600  + i) + 17) = true := by decide +kernel
private lemma base16_7  : ∀ i : Fin 100, check16_v (2 * (700  + i) + 17) = true := by decide +kernel
private lemma base16_8  : ∀ i : Fin 100, check16_v (2 * (800  + i) + 17) = true := by decide +kernel
private lemma base16_9  : ∀ i : Fin 100, check16_v (2 * (900  + i) + 17) = true := by decide +kernel
private lemma base16_10 : ∀ i : Fin 89,  check16_v (2 * (1000 + i) + 17) = true := by decide +kernel

private lemma base16_tile_sound {s M : ℕ}
    (h : ∀ i : Fin M, check16_v (2 * (s + i) + 17) = true) :
    ∀ n, s ≤ n → n < s + M → check16_v (2 * n + 17) = true := by
  intro n hsn hnM
  have hi := h ⟨n - s, by omega⟩
  have heq : s + (n - s) = n := by omega
  simpa [heq] using hi

private lemma base16_ok {n : ℕ} (hn : n ≤ 1088) : check16_v (2 * n + 17) = true := by
  rcases (show n < 100 ∨ (100 ≤ n ∧ n < 200) ∨ (200 ≤ n ∧ n < 300) ∨
      (300 ≤ n ∧ n < 400) ∨ (400 ≤ n ∧ n < 500) ∨ (500 ≤ n ∧ n < 600) ∨
      (600 ≤ n ∧ n < 700) ∨ (700 ≤ n ∧ n < 800) ∨ (800 ≤ n ∧ n < 900) ∨
      (900 ≤ n ∧ n < 1000) ∨ (1000 ≤ n ∧ n < 1089) by omega) with
    h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact base16_tile_sound base16_0  n (by omega) h0
  · exact base16_tile_sound base16_1  n h1 h2
  · exact base16_tile_sound base16_2  n h1 h2
  · exact base16_tile_sound base16_3  n h1 h2
  · exact base16_tile_sound base16_4  n h1 h2
  · exact base16_tile_sound base16_5  n h1 h2
  · exact base16_tile_sound base16_6  n h1 h2
  · exact base16_tile_sound base16_7  n h1 h2
  · exact base16_tile_sound base16_8  n h1 h2
  · exact base16_tile_sound base16_9  n h1 h2
  · exact base16_tile_sound base16_10 n h1 h2

private lemma d16_0  : ∀ i : Fin 100, checkD16_d (0    + i + 1) = true := by decide +kernel
private lemma d16_1  : ∀ i : Fin 100, checkD16_d (100  + i + 1) = true := by decide +kernel
private lemma d16_2  : ∀ i : Fin 100, checkD16_d (200  + i + 1) = true := by decide +kernel
private lemma d16_3  : ∀ i : Fin 100, checkD16_d (300  + i + 1) = true := by decide +kernel
private lemma d16_4  : ∀ i : Fin 100, checkD16_d (400  + i + 1) = true := by decide +kernel
private lemma d16_5  : ∀ i : Fin 100, checkD16_d (500  + i + 1) = true := by decide +kernel
private lemma d16_6  : ∀ i : Fin 100, checkD16_d (600  + i + 1) = true := by decide +kernel
private lemma d16_7  : ∀ i : Fin 100, checkD16_d (700  + i + 1) = true := by decide +kernel
private lemma d16_8  : ∀ i : Fin 100, checkD16_d (800  + i + 1) = true := by decide +kernel
private lemma d16_9  : ∀ i : Fin 100, checkD16_d (900  + i + 1) = true := by decide +kernel
private lemma d16_10 : ∀ i : Fin 69,  checkD16_d (1000 + i + 1) = true := by decide +kernel

private lemma d16_tile_sound {s M : ℕ}
    (h : ∀ i : Fin M, checkD16_d (s + i + 1) = true) :
    ∀ d, s + 1 ≤ d → d ≤ s + M → checkD16_d d = true := by
  intro d hd1 hdM
  have hi := h ⟨d - s - 1, by omega⟩
  have heq : s + (d - s - 1) + 1 = d := by omega
  simpa [heq] using hi

private lemma d16_ok {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d ≤ 1069) : checkD16_d d = true := by
  rcases (show d ≤ 100 ∨ (101 ≤ d ∧ d ≤ 200) ∨ (201 ≤ d ∧ d ≤ 300) ∨
      (301 ≤ d ∧ d ≤ 400) ∨ (401 ≤ d ∧ d ≤ 500) ∨ (501 ≤ d ∧ d ≤ 600) ∨
      (601 ≤ d ∧ d ≤ 700) ∨ (701 ≤ d ∧ d ≤ 800) ∨ (801 ≤ d ∧ d ≤ 900) ∨
      (901 ≤ d ∧ d ≤ 1000) ∨ (1001 ≤ d ∧ d ≤ 1069) by omega) with
    h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact d16_tile_sound d16_0  d hd1 h0
  · exact d16_tile_sound d16_1  d h1 h2
  · exact d16_tile_sound d16_2  d h1 h2
  · exact d16_tile_sound d16_3  d h1 h2
  · exact d16_tile_sound d16_4  d h1 h2
  · exact d16_tile_sound d16_5  d h1 h2
  · exact d16_tile_sound d16_6  d h1 h2
  · exact d16_tile_sound d16_7  d h1 h2
  · exact d16_tile_sound d16_8  d h1 h2
  · exact d16_tile_sound d16_9  d h1 h2
  · exact d16_tile_sound d16_10 d h1 h2

/-! ### Asymptotic Polynomial Square-Completion & d-Pinching for n ≥ 1089 (v ≥ 2193, V ≥ 4809249) -/

private lemma P16_X_sq (X : ℤ) : P16_X X = Q8Z X ^ 2 + R6Z X := by
  dsimp only [P16_X, Q8Z, R6Z]
  ring

private lemma Q8Z_hom_scale (X B : ℤ) : Q8Z_hom (B * X) B = B ^ 4 * Q8Z X := by
  dsimp only [Q8Z_hom, Q8Z]; ring

private lemma R6Z_hom_scale (X B : ℤ) : R6Z_hom (B * X) B = B ^ 3 * R6Z X := by
  dsimp only [R6Z_hom, R6Z]; ring

private lemma Q8Z_pos_X0 {X : ℤ} (hX : 4809249 ≤ X) : 0 < Q8Z X := by
  have ht : 0 ≤ X - 4809249 := by omega
  have hid : Q8Z X =
      1 * (X - 4809249) ^ 4 + 19236656 * (X - 4809249) ^ 3 +
      138768350261952 * (X - 4809249) ^ 2 + 444906502872859884544 * (X - 4809249) +
      534907084113404858217709568 := by
    dsimp only [Q8Z]; ring
  rw [hid]; positivity

private lemma Q8Z_hom_strictMono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 289 * B ≤ A1) (hA : A1 < A2) :
    Q8Z_hom A1 B < Q8Z_hom A2 B := by
  set t := A1 - 289 * B
  set h := A2 - A1
  have ht : 0 ≤ t := by omega
  have hh : 0 < h := by omega
  have hid : Q8Z_hom A2 B - Q8Z_hom A1 B =
      4 * t ^ 3 * h + 6 * t ^ 2 * h ^ 2 + 2448 * t ^ 2 * h * B + 4 * t * h ^ 3 +
      2448 * t * h ^ 2 * B + 476544 * t * h * B ^ 2 + 1 * h ^ 4 + 816 * h ^ 3 * B +
      238272 * h ^ 2 * B ^ 2 + 28949504 * h * B ^ 3 := by
    dsimp only [Q8Z_hom, t, h]; ring
  linarith [show 0 < Q8Z_hom A2 B - Q8Z_hom A1 B by rw [hid]; positivity]

private lemma Q8Z_hom_mono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 289 * B ≤ A1) (hA : A1 ≤ A2) :
    Q8Z_hom A1 B ≤ Q8Z_hom A2 B := by
  rcases eq_or_lt_of_le hA with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (Q8Z_hom_strictMono hB hA1 hlt)

private lemma Q8Z_strictMono {A B : ℤ} (hA : 289 ≤ A) (hAB : A < B) : Q8Z A < Q8Z B := by
  have := Q8Z_hom_strictMono (A1 := A) (A2 := B) (B := 1) (by omega) (by omega) hAB
  rw [show Q8Z_hom A 1 = Q8Z A from by dsimp only [Q8Z_hom, Q8Z]; ring,
      show Q8Z_hom B 1 = Q8Z B from by dsimp only [Q8Z_hom, Q8Z]; ring] at this
  exact this

private lemma negR6Z_hom_strictMono {A1 A2 B : ℤ} (hB : 0 < B) (hA1 : 289 * B ≤ A1) (hA : A1 < A2) :
    -R6Z_hom A1 B < -R6Z_hom A2 B := by
  set t := A1 - 289 * B
  set h := A2 - A1
  have ht : 0 ≤ t := by omega
  have hh : 0 < h := by omega
  have hid : (-R6Z_hom A2 B) - (-R6Z_hom A1 B) =
      6417285120 * t ^ 2 * h + 6417285120 * t * h ^ 2 + 3148177473536 * t * h * B +
      2139095040 * h ^ 3 + 1574088736768 * h ^ 2 * B + 382524953985024 * h * B ^ 2 := by
    dsimp only [R6Z_hom, t, h]; ring
  linarith [show 0 < (-R6Z_hom A2 B) - (-R6Z_hom A1 B) by rw [hid]; positivity]

private lemma negR6Z_strictMono {A B : ℤ} (hA : 289 ≤ A) (hAB : A < B) : -R6Z A < -R6Z B := by
  have := negR6Z_hom_strictMono (A1 := A) (A2 := B) (B := 1) (by omega) (by omega) hAB
  rw [show R6Z_hom A 1 = R6Z A from by dsimp only [R6Z_hom, R6Z]; ring,
      show R6Z_hom B 1 = R6Z B from by dsimp only [R6Z_hom, R6Z]; ring] at this
  exact this

private lemma P16_X_2V_gt {V : ℤ} (hV : 289 ≤ V) : 25 * P16_X V < P16_X (2 * V) := by
  have ht : 0 ≤ V - 289 := by omega
  have hid : P16_X (2 * V) - 25 * P16_X V =
      231 * (V - 289) ^ 8 + 464032 * (V - 289) ^ 7 + 405521536 * (V - 289) ^ 6 +
      201369142016 * (V - 289) ^ 5 + 62143690501728 * (V - 289) ^ 4 +
      12204397274227392 * (V - 289) ^ 3 + 1489490979631784432 * (V - 289) ^ 2 +
      103282869253615514960 * (V - 289) + 3115204671770431394273 := by
    dsimp only [P16_X]; ring
  linarith [show 0 < P16_X (2 * V) - 25 * P16_X V by rw [hid]; positivity]

private lemma R6Z_2V_gt {V : ℤ} (hV : 289 ≤ V) : 0 < -25 * R6Z V + R6Z (2 * V) := by
  have ht : 0 ≤ V - 289 := by omega
  have hid : -25 * R6Z V + R6Z (2 * V) =
      36364615680 * (V - 289) ^ 3 + 25637481873408 * (V - 289) ^ 2 +
      5906471220936704 * (V - 289) + 443469597866196992 := by
    dsimp only [R6Z]; ring
  rw [hid]; positivity

private lemma d_ge_1070_impossible {V : ℤ} (hV : 4809249 ≤ V) :
    0 < 1070 * (10 * Q8Z V - 1070) + 24 * R6Z V := by
  have ht : 0 ≤ V - 4809249 := by omega
  have hid : 1070 * (10 * Q8Z V - 1070) + 24 * R6Z V =
      10700 * (V - 4809249) ^ 4 + 154493938240 * (V - 4809249) ^ 3 +
      744132350856999168 * (V - 4809249) ^ 2 + 1198374139291590377590784 * (V - 4809249) +
      13174962723206710121974433724 := by
    dsimp only [Q8Z, R6Z]; ring
  rw [hid]; positivity

private lemma Q8Z_alow_X0 {V : ℤ} (hV : 4809249 ≤ V) :
    Q8Z_hom (149534 * V) 100000 < 100000 ^ 4 * (5 * Q8Z V - 1069) := by
  have ht : 0 ≤ V - 4809249 := by omega
  have hid : 100000 ^ 4 * (5 * Q8Z V - 1069) - Q8Z_hom (149534 * V) 100000 =
      11744609660871664 * (V - 4809249) ^ 4 +
      169614858113929892881344 * (V - 4809249) ^ 3 +
      817331365379798212646062125984 * (V - 4809249) ^ 2 +
      1318027348842250132966583866553617344 * (V - 4809249) +
      18735577156279491654222144139885330503664 := by
    dsimp only [Q8Z, Q8Z_hom]; ring
  linarith [show 0 < 100000 ^ 4 * (5 * Q8Z V - 1069) - Q8Z_hom (149534 * V) 100000 by rw [hid]; positivity]

private lemma Q8Z_ahigh_289 {V : ℤ} (hV : 289 ≤ V) :
    100000 ^ 4 * (5 * Q8Z V) < Q8Z_hom (149535 * V) 100000 := by
  have ht : 0 ≤ V - 289 := by omega
  have hid : Q8Z_hom (149535 * V) 100000 - 100000 ^ 4 * (5 * Q8Z V) =
      1630094978250625 * (V - 289) ^ 4 +
      56315754565812107722500 * (V - 289) ^ 3 +
      40000824587576526572703750 * (V - 289) ^ 2 +
      9312293686165709523590922500 * (V - 289) +
      710524956995091699095756650625 := by
    dsimp only [Q8Z, Q8Z_hom]; ring
  linarith [show 0 < Q8Z_hom (149535 * V) 100000 - 100000 ^ 4 * (5 * Q8Z V) by rw [hid]; positivity]

private lemma Q8Z_lt_X4 {V : ℤ} (hV : 289 ≤ V) : Q8Z V < V ^ 4 := by
  have ht : 0 ≤ V - 289 := by omega
  have hid : V ^ 4 - Q8Z V =
      340 * (V - 289) ^ 3 + 262854 * (V - 289) ^ 2 + 67600772 * (V - 289) + 5791734913 := by
    dsimp only [Q8Z]; ring
  linarith [show 0 < V ^ 4 - Q8Z V by rw [hid]; positivity]

private lemma Q8Z_gt_eps_X0 {V : ℤ} (hV : 4809249 ≤ V) : 13999 * V ^ 4 < 14000 * Q8Z V := by
  have ht : 0 ≤ V - 4809249 := by omega
  have hid : 14000 * Q8Z V - 13999 * V ^ 4 =
      1 * (V - 4809249) ^ 4 + 14476996 * (V - 4809249) ^ 3 +
      70097626908006 * (V - 4809249) ^ 2 + 114654044649173132996 * (V - 4809249) +
      5488428266918766389826001 := by
    dsimp only [Q8Z]; ring
  linarith [show 0 < 14000 * Q8Z V - 13999 * V ^ 4 by rw [hid]; positivity]

private lemma Hh16_lb_X0 {V : ℤ} (hV : 4809249 ≤ V) :
    (c3_h_adj16 : ℤ) * V ^ 3 < -25 * 100000 ^ 3 * R6Z V + R6Z_hom (149535 * V) 100000 := by
  have ht : 0 ≤ V - 4809249 := by omega
  have hid : (-25 * 100000 ^ 3 * R6Z V + R6Z_hom (149535 * V) 100000) - (c3_h_adj16 : ℤ) * V ^ 3 =
      1400000000000000000000 * (V - 4809249) ^ 3 +
      13813412216059696414720000000 * (V - 4809249) ^ 2 +
      35723202822666378964567490560000000 * (V - 4809249) +
      8038612849862133860907908216094720000000 := by
    dsimp only [R6Z, R6Z_hom, c3_h_adj16]; ring
  linarith [show 0 < (-25 * 100000 ^ 3 * R6Z V + R6Z_hom (149535 * V) 100000) - (c3_h_adj16 : ℤ) * V ^ 3 by
    rw [hid]; positivity]

private lemma Hl16_ub_X0 {V : ℤ} (hV : 4809249 ≤ V) :
    -25 * 100000 ^ 3 * R6Z V + R6Z_hom (149534 * V) 100000 < ((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 := by
  have ht : 0 ≤ V - 4809249 := by omega
  have hid : ((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 - (-25 * 100000 ^ 3 * R6Z V + R6Z_hom (149534 * V) 100000) =
      1400000000000000000000 * (V - 4809249) ^ 3 +
      26584287773025020628172800000 * (V - 4809249) ^ 2 +
      158559435797249796396656420454400000 * (V - 4809249) +
      303412646993290562984683641798151372800000 := by
    dsimp only [R6Z, R6Z_hom, c3_l_adj16]; ring
  linarith [show 0 < ((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 - (-25 * 100000 ^ 3 * R6Z V + R6Z_hom (149534 * V) 100000) by
    rw [hid]; positivity]

private lemma pinch16_V_gt_lo (V d QV diffR : ℤ) (hV : 4809249 ≤ V) (hd : 1 ≤ d)
    (h1 : (c3_h_adj16 : ℤ) * V ^ 3 < 100000 ^ 3 * diffR)
    (hprod : d * (10 * QV - d) = diffR) (hQ4 : QV < V ^ 4) :
    (c3_h_adj16 : ℤ) < 10 * d * (den3_16 : ℤ) * V := by
  have h10 : d * (10 * QV - d) < d * (10 * V ^ 4) := by
    have hd2 : 0 < d ^ 2 := by nlinarith
    have hlt : 10 * QV - d < 10 * V ^ 4 := by nlinarith
    exact mul_lt_mul_of_pos_left hlt (by omega)
  have h2 : diffR < 10 * d * V ^ 4 := by linarith
  have hV3_pos : 0 < V ^ 3 := by positivity
  have h100k_pos : (0 : ℤ) < 100000 ^ 3 := by norm_num
  have hden : (den3_16 : ℤ) = 100000 ^ 3 := by norm_num [den3_16]
  have hmul : (c3_h_adj16 : ℤ) * V ^ 3 < (10 * d * (den3_16 : ℤ) * V) * V ^ 3 := by
    calc (c3_h_adj16 : ℤ) * V ^ 3
        < 100000 ^ 3 * diffR := h1
      _ < 100000 ^ 3 * (10 * d * V ^ 4) := mul_lt_mul_of_pos_left h2 h100k_pos
      _ = (10 * d * (den3_16 : ℤ) * V) * V ^ 3 := by rw [hden]; ring
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hV3_pos)

private lemma pinch16_V_lt_hi (V d QV diffR : ℤ) (hV : 4809249 ≤ V) (hd1 : 1 ≤ d) (hd_ub : d ≤ 1069)
    (h1 : 100000 ^ 3 * diffR < ((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3)
    (hprod : d * (10 * QV - d) = diffR) (hQ4 : 13999 * V ^ 4 < 14000 * QV) :
    10 * 13999 * d * (den3_16 : ℤ) * V < (c3_l_adj16 : ℤ) * 14000 := by
  have hprod_eq : 10 * d * QV - d ^ 2 = diffR := by rw [← hprod]; ring
  have hd2 : d ^ 2 < V ^ 3 := by
    have hsq : d ^ 2 ≤ 1069 ^ 2 := by nlinarith
    have hnum : (1069 : ℤ) ^ 2 < 4809249 ^ 3 := by norm_num
    have hV2 : 4809249 ^ 2 ≤ V ^ 2 := by nlinarith
    have hV3 : (4809249 : ℤ) ^ 3 ≤ V ^ 3 := by nlinarith
    omega
  have hden : (den3_16 : ℤ) = 100000 ^ 3 := by norm_num [den3_16]
  have hV3_pos : 0 < V ^ 3 := by positivity
  have h100k_pos : (0 : ℤ) < 100000 ^ 3 := by norm_num
  have hstep1 : 10 * d * (13999 * V ^ 4) < 10 * d * (14000 * QV) :=
    mul_lt_mul_of_pos_left hQ4 (by omega)
  have hstep2 : 100000 ^ 3 * (10 * d * (13999 * V ^ 4)) < 100000 ^ 3 * (10 * d * (14000 * QV)) :=
    mul_lt_mul_of_pos_left hstep1 h100k_pos
  have hstep3 : 100000 ^ 3 * (10 * d * QV) < ((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 + 100000 ^ 3 * d ^ 2 := by
    linarith
  have hstep4 : 14000 * (100000 ^ 3 * (10 * d * QV)) <
      14000 * (((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 + 100000 ^ 3 * d ^ 2) :=
    mul_lt_mul_of_pos_left hstep3 (by norm_num)
  have hstep5 : 14000 * (((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 + 100000 ^ 3 * d ^ 2) <
      14000 * (((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 + 100000 ^ 3 * V ^ 3) := by
    have hdd : 100000 ^ 3 * d ^ 2 < 100000 ^ 3 * V ^ 3 := mul_lt_mul_of_pos_left hd2 h100k_pos
    linarith
  have hmul : (10 * 13999 * d * (den3_16 : ℤ) * V) * V ^ 3 < ((c3_l_adj16 : ℤ) * 14000) * V ^ 3 := by
    have hL : (10 * 13999 * d * (den3_16 : ℤ) * V) * V ^ 3 = 100000 ^ 3 * (10 * d * (13999 * V ^ 4)) := by
      rw [hden]; ring
    have hM : 100000 ^ 3 * (10 * d * (14000 * QV)) = 14000 * (100000 ^ 3 * (10 * d * QV)) := by ring
    have hR : 14000 * (((c3_l_adj16 : ℤ) - 100000 ^ 3) * V ^ 3 + 100000 ^ 3 * V ^ 3) =
        ((c3_l_adj16 : ℤ) * 14000) * V ^ 3 := by ring
    linarith
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hV3_pos)

private lemma asymp16_pinch {m n : ℕ} (hnm : n < m) (hn : 1089 ≤ n)
    (heq : P16 (2 * m + 17) = 25 * P16 (2 * n + 17)) : False := by
  set u : ℕ := 2 * m + 17
  set v : ℕ := 2 * n + 17
  have hv2193 : 2193 ≤ v := by omega
  have huv_nat : v < u := by omega
  set U : ℤ := (u : ℤ) ^ 2
  set V : ℤ := (v : ℤ) ^ 2
  have hVX0 : 4809249 ≤ V := by
    have : (2193 : ℤ) ≤ (v : ℤ) := by omega
    nlinarith
  have hV289 : 289 ≤ V := by omega
  have hUV : V < U := by
    have : (v : ℤ) < (u : ℤ) := by omega
    have : 0 ≤ (v : ℤ) := by omega
    nlinarith
  have hU289 : 289 ≤ U := by omega
  have heqX : P16_X U = 25 * P16_X V := by
    have h1 := P16_cast (x := u) (by omega)
    have h2 := P16_cast (x := v) (by omega)
    have h3 : ((P16 u : ℕ) : ℤ) = ((25 * P16 v : ℕ) : ℤ) := by exact_mod_cast heq
    push_cast at h1 h2 h3
    linarith
  have hU_lt_2V : U < 2 * V := by
    by_contra hge
    push Not at hge
    have hmono := P16_X_mono (by omega) hge
    have h2V := P16_X_2V_gt hV289
    linarith
  have hsq_diff : (5 * Q8Z V) ^ 2 - Q8Z U ^ 2 = -25 * R6Z V + R6Z U := by
    have hsu := P16_X_sq U
    have hsv := P16_X_sq V
    nlinarith
  have hR_pos : 0 < -25 * R6Z V + R6Z U := by
    have h1 : -R6Z U < -R6Z (2 * V) := negR6Z_strictMono hU289 hU_lt_2V
    have h2 : 0 < -25 * R6Z V + R6Z (2 * V) := R6Z_2V_gt hV289
    linarith
  have hR_ub : -25 * R6Z V + R6Z U < -24 * R6Z V := by
    have h1 : -R6Z V < -R6Z U := negR6Z_strictMono hV289 hUV
    linarith
  have hQV_pos : 0 < Q8Z V := Q8Z_pos_X0 hVX0
  have hQU_pos : 0 < Q8Z U := lt_trans hQV_pos (Q8Z_strictMono hV289 hUV)
  set d : ℤ := 5 * Q8Z V - Q8Z U
  have hd_pos : 1 ≤ d := by
    have hmul : d * (5 * Q8Z V + Q8Z U) = (5 * Q8Z V) ^ 2 - Q8Z U ^ 2 := by
      dsimp only [d]; ring
    nlinarith
  have hprod_d : d * (10 * Q8Z V - d) = -25 * R6Z V + R6Z U := by
    have : d * (10 * Q8Z V - d) = (5 * Q8Z V) ^ 2 - Q8Z U ^ 2 := by
      dsimp only [d]; ring
    linarith
  have hd_lt_1070 : d ≤ 1069 := by
    by_contra hge
    have hd_ge : 1070 ≤ d := by omega
    have hd_lt : d < 5 * Q8Z V := by dsimp only [d]; linarith
    have hquad : 1070 * (10 * Q8Z V - 1070) ≤ d * (10 * Q8Z V - d) := by
      have hid : d * (10 * Q8Z V - d) - 1070 * (10 * Q8Z V - 1070) =
          (d - 1070) * (10 * Q8Z V - d - 1070) := by ring
      have h1 : 0 ≤ d - 1070 := by omega
      have h2 : 0 ≤ 10 * Q8Z V - d - 1070 := by linarith
      nlinarith
    have himp := d_ge_1070_impossible hVX0
    linarith
  have hU_lb : 149534 * V < 100000 * U := by
    have hQ1 : Q8Z_hom (149534 * V) 100000 < 100000 ^ 4 * Q8Z U := by
      have h5Q : 5 * Q8Z V - 1069 ≤ Q8Z U := by change 5 * Q8Z V - 1069 ≤ Q8Z (u ^ 2); linarith [show d = 5 * Q8Z V - Q8Z U from rfl]
      have ha := Q8Z_alow_X0 hVX0
      linarith [show 100000 ^ 4 * (5 * Q8Z V - 1069) ≤ 100000 ^ 4 * Q8Z U by gcongr]
    rw [← Q8Z_hom_scale U 100000] at hQ1
    by_contra hle
    push Not at hle
    have hmono := Q8Z_hom_mono (A1 := 100000 * U) (A2 := 149534 * V) (B := 100000)
      (by omega) (by omega) hle
    linarith
  have hU_ub : 100000 * U < 149535 * V := by
    have hQ1 : 100000 ^ 4 * Q8Z U < Q8Z_hom (149535 * V) 100000 := by
      have h5Q : Q8Z U < 5 * Q8Z V := by linarith [show d = 5 * Q8Z V - Q8Z U from rfl]
      have ha := Q8Z_ahigh_289 hV289
      linarith [show 100000 ^ 4 * Q8Z U < 100000 ^ 4 * (5 * Q8Z V) by gcongr]
    rw [← Q8Z_hom_scale U 100000] at hQ1
    by_contra hle
    push Not at hle
    have hmono := Q8Z_hom_mono (A1 := 149535 * V) (A2 := 100000 * U) (B := 100000)
      (by omega) (by omega) hle
    linarith
  have hR_lb_scaled : R6Z_hom (149535 * V) 100000 < 100000 ^ 3 * R6Z U := by
    have := negR6Z_hom_strictMono (A1 := 100000 * U) (A2 := 149535 * V) (B := 100000)
      (by omega) (by omega) hU_ub
    rw [R6Z_hom_scale U 100000] at this
    linarith
  have hR_ub_scaled : 100000 ^ 3 * R6Z U < R6Z_hom (149534 * V) 100000 := by
    have := negR6Z_hom_strictMono (A1 := 149534 * V) (A2 := 100000 * U) (B := 100000)
      (by omega) (by omega) hU_lb
    rw [R6Z_hom_scale U 100000] at this
    linarith
  have hV_gt_lo : (c3_h_adj16 : ℤ) < 10 * d * (den3_16 : ℤ) * V :=
    pinch16_V_gt_lo V d (Q8Z V) (-25 * R6Z V + R6Z U)
      hVX0 hd_pos (by linarith [Hh16_lb_X0 hVX0, hR_lb_scaled]) hprod_d (Q8Z_lt_X4 hV289)
  have hV_lt_hi : 10 * 13999 * d * (den3_16 : ℤ) * V < (c3_l_adj16 : ℤ) * 14000 :=
    pinch16_V_lt_hi V d (Q8Z V) (-25 * R6Z V + R6Z U)
      hVX0 hd_pos hd_lt_1070 (by linarith [Hl16_ub_X0 hVX0, hR_ub_scaled]) hprod_d (Q8Z_gt_eps_X0 hVX0)
  set dN : ℕ := d.toNat
  have hdN_eq : (dN : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hdN1 : 1 ≤ dN := by omega
  have hdN_le : dN ≤ 1069 := by omega
  have hV_nat : V = (v : ℤ) * (v : ℤ) := by dsimp only [V]; ring
  have hVlo_nat : c3_h_adj16 / (10 * dN * den3_16) < v * v := by
    apply Nat.div_lt_of_lt_mul
    zify
    rw [hdN_eq, ← hV_nat]
    linarith [hV_gt_lo]
  have hVhi_nat : v * v < (c3_l_adj16 * 14000) / (10 * 13999 * dN * den3_16) + 1 := by
    have hlt_mul : (v * v) * (10 * 13999 * dN * den3_16) < c3_l_adj16 * 14000 := by
      zify
      rw [hdN_eq, ← hV_nat]
      linarith [hV_lt_hi]
    have hden_pos : 0 < den3_16 := by norm_num [den3_16]
    have hpos_M : 0 < 10 * 13999 * dN * den3_16 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hdN1) hden_pos
    by_contra hge
    have hle : (c3_l_adj16 * 14000) / (10 * 13999 * dN * den3_16) + 1 ≤ v * v := by omega
    have hmul_le := Nat.mul_le_mul_right (10 * 13999 * dN * den3_16) hle
    have hdiv := Nat.lt_mul_div_succ (c3_l_adj16 * 14000) hpos_M
    rw [Nat.mul_comm (10 * 13999 * dN * den3_16)] at hdiv
    omega
  have hchk := checkD16_d_sound (d16_ok hdN1 hdN_le) (by omega) hVlo_nat hVhi_nat
  exact check16_v_sound hchk m heq

/-! ### Main Theorems -/

private lemma prod16_pos (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 16, (n + i) := by
  have hP17 : 0 < P16 17 := by decide
  have hPpos : 0 < P16 (2 * n + 17) := lt_of_lt_of_le hP17 (P16_mono (by omega) (by omega))
  linarith [prod16_midpoint n]

/-- Unconditional length-16 product exclusion for ratio 25 (no disjointness hypothesis needed). -/
theorem length_sixteen (m n : ℕ) :
    (∏ i ∈ Finset.Icc 1 16, (m + i)) ≠ 25 * (∏ i ∈ Finset.Icc 1 16, (n + i)) := by
  intro heq
  have hmid : P16 (2 * m + 17) = 25 * P16 (2 * n + 17) := by
    have hm := prod16_midpoint m
    have hn := prod16_midpoint n
    have hmul : 2 ^ 16 * (∏ i ∈ Finset.Icc 1 16, (m + i)) =
        25 * (2 ^ 16 * (∏ i ∈ Finset.Icc 1 16, (n + i))) := by
      calc 2 ^ 16 * (∏ i ∈ Finset.Icc 1 16, (m + i))
          = 2 ^ 16 * (25 * (∏ i ∈ Finset.Icc 1 16, (n + i))) := by rw [heq]
        _ = 25 * (2 ^ 16 * (∏ i ∈ Finset.Icc 1 16, (n + i))) := by ring
    linarith
  have hnm : n < m := by
    by_contra hle
    have hmono : P16 (2 * m + 17) ≤ P16 (2 * n + 17) := P16_mono (by omega) (by omega)
    have hpos : 0 < P16 (2 * n + 17) := by
      have : 0 < ∏ i ∈ Finset.Icc 1 16, (n + i) := prod16_pos n
      linarith [prod16_midpoint n]
    omega
  by_cases hn1089 : 1089 ≤ n
  · exact asymp16_pinch hnm hn1089 hmid
  · exact check16_v_sound (base16_ok (by omega)) m hmid

/-- Exclusion of ratio 25 for length-16 consecutive blocks with `m ≥ n + 16` (`Finset.Icc` form). -/
theorem erdos686_n25_k16_Icc :
    ¬ ∃ (m n : ℕ), m ≥ n + 16 ∧ (∏ i ∈ Finset.Icc 1 16, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 16, (n + i)) := by
  rintro ⟨m, n, _, heq⟩
  exact length_sixteen m n heq

/-- Exclusion of ratio 25 for length-16 consecutive blocks with `m ≥ n + 16` (`Finset.range` form). -/
theorem erdos686_n25_k16_range :
    ¬ ∃ (m n : ℕ), m ≥ n + 16 ∧
      (∏ i ∈ Finset.range 16, (m + i + 1)) = 25 * (∏ i ∈ Finset.range 16, (n + i + 1)) := by
  rintro ⟨m, n, hmn, heq⟩
  rw [prod16_range_eq_Icc m, prod16_range_eq_Icc n] at heq
  exact length_sixteen m n heq

/-- Direct interface to the `k = 16` case of `Erdos686.erdos_686.variants.twenty_five` (no disjointness needed). -/
theorem no_ratio_twenty_five_sixteen (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 16, (m + i)) / (∏ i ∈ Finset.Icc 1 16, (n + i)) := by
  intro h
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 16, (n + i) := prod16_pos n
  have hd : ((∏ i ∈ Finset.Icc 1 16, (n + i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hz := (eq_div_iff hd).mp h
  have hn : 25 * (∏ i ∈ Finset.Icc 1 16, (n + i)) = ∏ i ∈ Finset.Icc 1 16, (m + i) := by
    exact_mod_cast hz
  exact length_sixteen m n hn.symm

/-- Existential target-shaped exclusion for `k = 16` matching `FormalConjectures.ErdosProblems.«686»`. -/
theorem no_sol_twenty_five_sixteen :
    ¬ ∃ (n : ℕ), ∃ m ≥ n + 16,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 16, (m + i)) / (∏ i ∈ Finset.Icc 1 16, (n + i)) := by
  rintro ⟨n, m, _, h⟩
  exact no_ratio_twenty_five_sixteen m n h

end Contribution.Erdos686SixteenTwentyFive
