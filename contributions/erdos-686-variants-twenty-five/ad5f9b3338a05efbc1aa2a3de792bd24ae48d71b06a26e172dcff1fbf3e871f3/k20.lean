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
# Unconditional Exclusion of k = 20 for Erdős Problem #686 (N = 25)

Proves via exact polynomial square-completion (`P_20(x) = Q_20(x)^2 + R_20(x)`, `S = 1`),
modular congruence (`3200 ∣ Q_20(2*k + 1)`), Taylor-shift positivity at `n_0 = 24596` (`v_0 = 49213`),
and kernel-verified bracketing over `0 ≤ n < 25000` (`25` blocks of `1000`, `decide +kernel`),
that no integers `m ≥ n + 20` satisfy
`∏ i ∈ Finset.range 20, (m + i + 1) = 25 * ∏ i ∈ Finset.range 20, (n + i + 1)`.
-/

namespace Contribution.Erdos686TwentyTwentyFive

def P20 (x : ℕ) : ℕ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) *
    (x2 - 121) * (x2 - 169) * (x2 - 225) * (x2 - 289) * (x2 - 361)

def P20Z (x : ℤ) : ℤ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) *
    (x2 - 121) * (x2 - 169) * (x2 - 225) * (x2 - 289) * (x2 - 361)

def Q20Z (x : ℤ) : ℤ :=
  x ^ 10 - 665 * x ^ 8 + 141778 * x ^ 6 - 11228810 * x ^ 4 + 260432221 * x ^ 2 - 5636490125

def R20Z (x : ℤ) : ℤ :=
  -3229057600000 * x ^ 8 + 1050408889600000 * x ^ 6 - 98738651827200000 * x ^ 4 + 2417704523968000000 * x ^ 2 - 31341350767572160000

def negR20_s5 (t : ℤ) : ℤ :=
  3229057600000 * t ^ 8 + 2712408384000000 * t ^ 7 + 970549858880000000 * t ^ 6 + 192786177024000000000 * t ^ 5 + 23193505265322000000000 * t ^ 4 + 1725793641006120000000000 * t ^ 3 + 77328141481067000000000000 * t ^ 2 + 1901783139253620000000000000 * t + 19613523808657156000000000000

private lemma mul_lt_mul_nat {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hd : 0 < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hcd))
    (Nat.mul_lt_mul_of_pos_right hab hd)

private lemma P20_strictMono {a b : ℕ} (ha : 19 ≤ a) (hab : a < b) : P20 a < P20 b := by
  have hb : 19 ≤ b := by omega
  have hab2 : a * a < b * b := mul_lt_mul_nat hab hab (by omega)
  have ha2 : 361 ≤ a * a := Nat.mul_le_mul ha ha
  dsimp only [P20]
  have p1 := mul_lt_mul_nat (by omega : a * a - 1 < b * b - 1) (by omega : a * a - 9 < b * b - 9) (by omega)
  have p2 := mul_lt_mul_nat p1 (by omega : a * a - 25 < b * b - 25) (by omega)
  have p3 := mul_lt_mul_nat p2 (by omega : a * a - 49 < b * b - 49) (by omega)
  have p4 := mul_lt_mul_nat p3 (by omega : a * a - 81 < b * b - 81) (by omega)
  have p5 := mul_lt_mul_nat p4 (by omega : a * a - 121 < b * b - 121) (by omega)
  have p6 := mul_lt_mul_nat p5 (by omega : a * a - 169 < b * b - 169) (by omega)
  have p7 := mul_lt_mul_nat p6 (by omega : a * a - 225 < b * b - 225) (by omega)
  have p8 := mul_lt_mul_nat p7 (by omega : a * a - 289 < b * b - 289) (by omega)
  exact mul_lt_mul_nat p8 (by omega : a * a - 361 < b * b - 361) (by omega)

private lemma P20_mono {a b : ℕ} (ha : 19 ≤ a) (hab : a ≤ b) : P20 a ≤ P20 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P20_strictMono ha hlt)

private lemma P20_cast {x : ℕ} (hx : 19 ≤ x) : (P20 x : ℤ) = P20Z (x : ℤ) := by
  have h361 : 361 ≤ x * x := Nat.mul_le_mul hx hx
  dsimp only [P20, P20Z]
  zify [show 1 ≤ x * x by omega, show 9 ≤ x * x by omega, show 25 ≤ x * x by omega,
    show 49 ≤ x * x by omega, show 81 ≤ x * x by omega, show 121 ≤ x * x by omega,
    show 169 ≤ x * x by omega, show 225 ≤ x * x by omega, show 289 ≤ x * x by omega, h361]

private lemma prod20_midpoint (m : ℕ) :
    2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (m + i)) = P20 (2 * m + 21) := by
  have hIcc : Finset.Icc 1 20 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  zify
  rw [P20_cast (by omega)]
  dsimp only [P20Z]
  push_cast
  ring

private lemma prod20_range_eq_Icc (m : ℕ) :
    (∏ i ∈ Finset.range 20, (m + i + 1)) = ∏ i ∈ Finset.Icc 1 20, (m + i) := by
  have hIcc : Finset.Icc 1 20 = (Finset.range 20).image (· + 1) := by decide
  rw [hIcc, Finset.prod_image (fun a _ b _ hab => by omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ## 1. Finite Bracket Verification for 0 ≤ n < 25000 -/

def findBracket20 (v : ℕ) : ℕ :=
  let rhs := 25 * P20 v
  let u0 := 2 * ((v * 11746189431) / 20000000000) + 1
  if P20 u0 < rhs then
    let u1 := u0 + 2
    if P20 u1 < rhs then u1 + 2 else u1
  else
    u0

def check20_v (v : ℕ) : Bool :=
  let rhs := 25 * P20 v
  let u := findBracket20 v
  decide (u ≥ 21 ∧ u % 2 = 1 ∧ P20 (u - 2) < rhs ∧ rhs < P20 u)

def stepBase20 (n : ℕ) : Bool := check20_v (2 * n + 21)

def checkBlock (stepFn : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => stepFn (start + k) && checkBlock stepFn start k

def checkGrid (stepFn : ℕ → Bool) (start blockSize : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => checkBlock stepFn (start + b * blockSize) blockSize && checkGrid stepFn start blockSize b

theorem base20_ok : checkGrid stepBase20 0 1000 25 = true := by
  decide +kernel

private lemma check20_v_sound {v : ℕ} (hc : check20_v v = true) :
    ∀ m : ℕ, P20 (2 * m + 21) ≠ 25 * P20 v := by
  simp only [check20_v, decide_eq_true_eq] at hc
  rcases hc with ⟨hu21, hu_odd, hlo, hhi⟩
  intro m heq
  set u := findBracket20 v
  set x := 2 * m + 21
  by_cases hxu : x < u
  · have hle : x ≤ u - 2 := by omega
    have hpm : P20 x ≤ P20 (u - 2) := P20_mono (by omega) hle
    omega
  · have hge : u ≤ x := by omega
    have hpm : P20 u ≤ P20 x := P20_mono (by omega) hge
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

private lemma base20_excl : ∀ n < 25000, ∀ m : ℕ, P20 (2 * m + 21) ≠ 25 * P20 (2 * n + 21) := by
  intro n hn m
  have hcell := checkGrid_sound base20_ok n (by omega)
  simp only [Nat.zero_add, stepBase20] at hcell
  exact check20_v_sound hcell m

/-! ## 2. Exact Square Completion, Modular Divisibility, and Taylor Bounds -/

private lemma P20Z_eq (x : ℤ) : P20Z x = Q20Z x ^ 2 + R20Z x := by
  dsimp only [P20Z, Q20Z, R20Z]
  ring

private lemma Q20Z_shift21 (y : ℤ) :
    Q20Z (21 + y) = y ^ 10 + 210 * y ^ 9 + 19180 * y ^ 8 + 999600 * y ^ 7 + 32771368 * y ^ 6 + 702177840 * y ^ 5 + 9884427520 * y ^ 4 + 89355604800 * y ^ 3 + 489209407456 * y ^ 2 + 1430201572800 * y + 1612852528000 := by
  dsimp only [Q20Z]
  ring

private lemma negR20Z_shift21 (y : ℤ) :
    -R20Z (21 + y) = 3229057600000 * y ^ 8 + 542481676800000 * y ^ 7 + 38821994355200000 * y ^ 6 + 1542289416192000000 * y ^ 5 + 37109608424515200000 * y ^ 4 + 552253965121958400000 * y ^ 3 + 4949001054788288000000 * y ^ 2 + 24342824182446336000000 * y + 50210620950162319360000 := by
  dsimp only [R20Z]
  ring

private lemma Q20Z_pos {v : ℤ} (hv : 21 ≤ v) : 0 < Q20Z v := by
  set y := v - 21
  have hy0 : 0 ≤ y := by omega
  have hsh := Q20Z_shift21 y
  rw [show 21 + y = v by omega] at hsh
  rw [hsh]
  positivity

private lemma R20Z_lt_of_lt {v u : ℤ} (hv : 21 ≤ v) (hvu : v < u) : R20Z u < R20Z v := by
  set xlo := v - 21
  set xhi := u - 21
  have hx0 : 0 ≤ xlo := by omega
  have hlt : xlo < xhi := by omega
  have h1 := negR20Z_shift21 xlo
  have h2 := negR20Z_shift21 xhi
  rw [show 21 + xlo = v by omega] at h1
  rw [show 21 + xhi = u by omega] at h2
  have hneg : -R20Z v < -R20Z u := by
    rw [h1, h2]
    have hpow8 : xlo ^ 8 ≤ xhi ^ 8 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 8
    have hm8 : (3229057600000 : ℤ) * xlo ^ 8 ≤ (3229057600000 : ℤ) * xhi ^ 8 := by linarith only [hpow8]
    have hpow7 : xlo ^ 7 ≤ xhi ^ 7 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 7
    have hm7 : (542481676800000 : ℤ) * xlo ^ 7 ≤ (542481676800000 : ℤ) * xhi ^ 7 := by linarith only [hpow7]
    have hpow6 : xlo ^ 6 ≤ xhi ^ 6 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 6
    have hm6 : (38821994355200000 : ℤ) * xlo ^ 6 ≤ (38821994355200000 : ℤ) * xhi ^ 6 := by linarith only [hpow6]
    have hpow5 : xlo ^ 5 ≤ xhi ^ 5 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 5
    have hm5 : (1542289416192000000 : ℤ) * xlo ^ 5 ≤ (1542289416192000000 : ℤ) * xhi ^ 5 := by linarith only [hpow5]
    have hpow4 : xlo ^ 4 ≤ xhi ^ 4 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 4
    have hm4 : (37109608424515200000 : ℤ) * xlo ^ 4 ≤ (37109608424515200000 : ℤ) * xhi ^ 4 := by linarith only [hpow4]
    have hpow3 : xlo ^ 3 ≤ xhi ^ 3 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 3
    have hm3 : (552253965121958400000 : ℤ) * xlo ^ 3 ≤ (552253965121958400000 : ℤ) * xhi ^ 3 := by linarith only [hpow3]
    have hpow2 : xlo ^ 2 ≤ xhi ^ 2 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 2
    have hm2 : (4949001054788288000000 : ℤ) * xlo ^ 2 ≤ (4949001054788288000000 : ℤ) * xhi ^ 2 := by linarith only [hpow2]
    have hlt1 : (24342824182446336000000 : ℤ) * xlo < (24342824182446336000000 : ℤ) * xhi := by linarith only [hlt]
    linarith only [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hlt1]
  omega

private lemma negR20_s5_strictMono {a b : ℤ} (ha : 0 ≤ a) (hab : a < b) :
    negR20_s5 a < negR20_s5 b := by
  dsimp only [negR20_s5]
  have hpow8 : a ^ 8 ≤ b ^ 8 := pow_le_pow_left₀ ha (le_of_lt hab) 8
  have hm8 : (3229057600000 : ℤ) * a ^ 8 ≤ (3229057600000 : ℤ) * b ^ 8 := by linarith only [hpow8]
  have hpow7 : a ^ 7 ≤ b ^ 7 := pow_le_pow_left₀ ha (le_of_lt hab) 7
  have hm7 : (2712408384000000 : ℤ) * a ^ 7 ≤ (2712408384000000 : ℤ) * b ^ 7 := by linarith only [hpow7]
  have hpow6 : a ^ 6 ≤ b ^ 6 := pow_le_pow_left₀ ha (le_of_lt hab) 6
  have hm6 : (970549858880000000 : ℤ) * a ^ 6 ≤ (970549858880000000 : ℤ) * b ^ 6 := by linarith only [hpow6]
  have hpow5 : a ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ ha (le_of_lt hab) 5
  have hm5 : (192786177024000000000 : ℤ) * a ^ 5 ≤ (192786177024000000000 : ℤ) * b ^ 5 := by linarith only [hpow5]
  have hpow4 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha (le_of_lt hab) 4
  have hm4 : (23193505265322000000000 : ℤ) * a ^ 4 ≤ (23193505265322000000000 : ℤ) * b ^ 4 := by linarith only [hpow4]
  have hpow3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha (le_of_lt hab) 3
  have hm3 : (1725793641006120000000000 : ℤ) * a ^ 3 ≤ (1725793641006120000000000 : ℤ) * b ^ 3 := by linarith only [hpow3]
  have hpow2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha (le_of_lt hab) 2
  have hm2 : (77328141481067000000000000 : ℤ) * a ^ 2 ≤ (77328141481067000000000000 : ℤ) * b ^ 2 := by linarith only [hpow2]
  have hlt1 : (1901783139253620000000000000 : ℤ) * a < (1901783139253620000000000000 : ℤ) * b := by linarith only [hab]
  linarith only [hm8, hm7, hm6, hm5, hm4, hm3, hm2, hlt1]

private lemma negR20_s5_eval (u : ℤ) : -5 ^ 8 * R20Z u = negR20_s5 (5 * u - 105) := by
  dsimp only [R20Z, negR20_s5]
  ring

private lemma Q20Z_128_dvd (a : ℤ) : (128 : ℤ) ∣ Q20Z (2 * a + 1) := by
  set qq := a / 2
  have hr : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hr with h0 | h1
  · have hx : 2 * a + 1 = 4 * qq + 1 := by omega
    rw [hx]
    refine ⟨8192 * qq ^ 10 + 20480 * qq ^ 9 - 317440 * qq ^ 8 - 665600 * qq ^ 7 + 3947776 * qq ^ 6 + 6509440 * qq ^ 5 - 18296960 * qq ^ 4 - 21058400 * qq ^ 3 + 24395932 * qq ^ 2 + 14899830 * qq - 42087075, by dsimp only [Q20Z]; ring⟩
  · have hx : 2 * a + 1 = 4 * qq + 3 := by omega
    rw [hx]
    refine ⟨8192 * qq ^ 10 + 61440 * qq ^ 9 - 133120 * qq ^ 8 - 1628160 * qq ^ 7 - 281344 * qq ^ 6 + 12862080 * qq ^ 5 + 8587520 * qq ^ 4 - 33486240 * qq ^ 3 - 23367748 * qq ^ 2 + 17036130 * qq - 32055325, by dsimp only [Q20Z]; ring⟩

private lemma Q20Z_25_dvd (x : ℤ) : (25 : ℤ) ∣ Q20Z x := by
  set qq := x / 5
  have hr : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
  rcases hr with h0 | h1 | h2 | h3 | h4
  · have hx : x = 5 * qq + 0 := by omega
    rw [hx]; refine ⟨390625 * qq ^ 10 - 10390625 * qq ^ 8 + 88611250 * qq ^ 6 - 280720250 * qq ^ 4 + 260432221 * qq ^ 2 - 225459605, by dsimp only [Q20Z]; ring⟩
  · have hx : x = 5 * qq + 1 := by omega
    rw [hx]; refine ⟨390625 * qq ^ 10 + 781250 * qq ^ 9 - 9687500 * qq ^ 8 - 16250000 * qq ^ 7 + 77105000 * qq ^ 6 + 101710000 * qq ^ 5 - 228712000 * qq ^ 4 - 210584000 * qq ^ 3 + 195167456 * qq ^ 2 + 95358912 * qq - 215485824, by dsimp only [Q20Z]; ring⟩
  · have hx : x = 5 * qq + 2 := by omega
    rw [hx]; refine ⟨390625 * qq ^ 10 + 1562500 * qq ^ 9 - 7578125 * qq ^ 8 - 30250000 * qq ^ 7 + 44161250 * qq ^ 6 + 176435000 * qq ^ 5 - 86337250 * qq ^ 4 - 341611600 * qq ^ 3 + 23787341 * qq ^ 2 + 141790500 * qq - 190620705, by dsimp only [Q20Z]; ring⟩
  · have hx : x = 5 * qq + 3 := by omega
    rw [hx]; refine ⟨390625 * qq ^ 10 + 2343750 * qq ^ 9 - 4062500 * qq ^ 8 - 39750000 * qq ^ 7 - 5495000 * qq ^ 6 + 200970000 * qq ^ 5 + 107344000 * qq ^ 4 - 334862400 * qq ^ 3 - 186941984 * qq ^ 2 + 109031232 * qq - 164123264, by dsimp only [Q20Z]; ring⟩
  · have hx : x = 5 * qq + 4 := by omega
    rw [hx]; refine ⟨390625 * qq ^ 10 + 3125000 * qq ^ 9 + 859375 * qq ^ 8 - 42500000 * qq ^ 7 - 63988750 * qq ^ 6 + 159670000 * qq ^ 5 + 293531750 * qq ^ 4 - 171764000 * qq ^ 3 - 346424419 * qq ^ 2 - 915000 * qq - 152238405, by dsimp only [Q20Z]; ring⟩

private lemma Q20Z_3200_dvd (a : ℤ) : (3200 : ℤ) ∣ Q20Z (2 * a + 1) := by
  obtain ⟨A, hA⟩ := Q20Z_128_dvd a
  obtain ⟨B, hB⟩ := Q20Z_25_dvd (2 * a + 1)
  refine ⟨(-8 : ℤ) * B + 41 * A, ?_⟩
  calc Q20Z (2 * a + 1) = (-8 * 128 + 41 * 25) * Q20Z (2 * a + 1) := by ring
    _ = -8 * 128 * Q20Z (2 * a + 1) + 41 * 25 * Q20Z (2 * a + 1) := by ring
    _ = -8 * 128 * (25 * B) + 41 * 25 * (128 * A) := by rw [← hB, ← hA]
    _ = 3200 * ((-8 : ℤ) * B + 41 * A) := by ring

private lemma P20Z_prod_scaled5 (u : ℤ) :
    5 ^ 20 * P20Z u =
      ∏ j ∈ Finset.Icc (1 : ℕ) 10, ((5 * u) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2) := by
  have hIcc : Finset.Icc (1 : ℕ) 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  dsimp only [P20Z]
  ring

private lemma P20Z_hom65_gt {v : ℤ} (hv : 49213 ≤ v) :
    25 * 5 ^ 20 * P20Z v <
      ∏ j ∈ Finset.Icc (1 : ℕ) 10, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2) := by
  set y := v - 49213
  have hy0 : 0 ≤ y := by omega
  have hprod : (∏ j ∈ Finset.Icc (1 : ℕ) 10, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2)) -
      25 * 5 ^ 20 * P20Z v = 1271972649047351 * y ^ 20 + 1251951799551345695260 * y ^ 19 + 585316886951642111983837860 * y ^ 18 + 172831199623710638599484960908080 * y ^ 17 + 36148552726948334459741110425966109920 * y ^ 16 + 5692731913113880837593519050252306169535872 * y ^ 15 + 700391037868273535774108498261599499807785331840 * y ^ 14 + 68936688147720314774587500410443307457164410798435840 * y ^ 13 + 5512944491372038783223134936385641452491054007602304357120 * y ^ 12 + 361744715320492659924348165495272097157108209750455617106734080 * y ^ 11 + 19582796880574994409655112131147055100093129856424439935404460319744 * y ^ 10 + 876116526812322175892067148152735544794400426888295104622043254758379520 * y ^ 9 + 32337241850380295287986154915647996040946857724173806276526411140776003064320 * y ^ 8 + 979330877824540362225707185899188135245961307871895218640331516736749779593154560 * y ^ 7 + 24097905134987074168463009499106070398673075246290295542017057616124496785410928816640 * y ^ 6 + 474372079827015717427992266184934945433625344822137388515398170795790393262937840062307328 * y ^ 5 + 7295397825419241489225306686329838100245427842456699373056832261946570526184211175782607981520 * y ^ 4 + 84477273214490170707156426289093956159980806118953783490407734028346897592626654462609675699565120 * y ^ 3 + 692896670307102301208936877754920010943457015801721506448582748926218486354294348909486724094606612760 * y ^ 2 + 3589423538937357849449377043983166653468846483773548371035734688588783703586863932059961350978951537741040 * y + 8832314972052873185556645404059858785487847894925104453226813965208070288156083876516675626553682369100122401 := by
    have hIcc : Finset.Icc (1 : ℕ) 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
    rw [hIcc]
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
      Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
    have hv_eq : v = 49213 + y := by omega
    rw [hv_eq]
    dsimp only [P20Z]
    ring
  have hpos : 0 < (∏ j ∈ Finset.Icc (1 : ℕ) 10, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2)) -
      25 * 5 ^ 20 * P20Z v := by
    rw [hprod]
    positivity
  omega

private lemma negR20_s5_upper65 {v : ℤ} (hv : 49213 ≤ v) :
    negR20_s5 (6 * v - 105) < 25 * 5 ^ 8 * (-R20Z v) := by
  set y := v - 49213
  have hy0 : 0 ≤ y := by omega
  have hdiff : 25 * 5 ^ 8 * (-R20Z v) - negR20_s5 (6 * v - 105) =
      26110188815118400000 * y ^ 8 + 10279685777267374553600000 * y ^ 7 + 1770629607515605180001548800000 * y ^ 6 + 174275987971225425816515365068800000 * y ^ 5 + 10720805080961320554470062753306768000000 * y ^ 4 + 422082375746623269338049336882591893107200000 * y ^ 3 + 10385969713893978911074191704529126358309516800000 * y ^ 2 + 146035631967180669423997176890251900662290243942400000 * y + 898356412419933735770536638817588538280362802951406400000 := by
    have hv_eq : v = 49213 + y := by omega
    rw [hv_eq]
    dsimp only [R20Z, negR20_s5]
    ring
  have hpos : 0 < 25 * 5 ^ 8 * (-R20Z v) - negR20_s5 (6 * v - 105) := by
    rw [hdiff]
    positivity
  omega

private lemma thresh_20_pos {v : ℤ} (hv : 49213 ≤ v) :
    0 < 3200 * (10 * Q20Z v - 3200) + 24 * R20Z v := by
  set y := v - 49213
  have hy0 : 0 ≤ y := by omega
  have heq : 3200 * (10 * Q20Z v - 3200) + 24 * R20Z v =
      32000 * y ^ 10 + 15748160000 * y ^ 9 + 3410066487680000 * y ^ 8 + 427178246942901760000 * y ^ 7 + 34162070909834356147456000 * y ^ 6 + 1810554835087840663134369280000 * y ^ 5 + 63645589589140196402645787243520000 * y ^ 4 + 1431886332167423191681310347194480640000 * y ^ 3 + 18718659253118052724617729579993094515712000 * y ^ 2 + 108389876690862438165498966156714482137282560000 * y + 138538480042570024255621593811291960413931520000 := by
    have hv_eq : v = 49213 + y := by omega
    rw [hv_eq]
    dsimp only [Q20Z, R20Z]
    ring
  rw [heq]
  positivity

private lemma asymp20_excl {m n : ℕ} (hmn : m ≥ n + 20) (hn : 24596 ≤ n)
    (hmid : P20 (2 * m + 21) = 25 * P20 (2 * n + 21)) : False := by
  set u : ℤ := ((2 * m + 21 : ℕ) : ℤ)
  set v : ℤ := ((2 * n + 21 : ℕ) : ℤ)
  have hv49213 : 49213 ≤ v := by omega
  have hv21 : 21 ≤ v := by omega
  have hvu : v < u := by omega
  have hPeq : P20Z u = 25 * P20Z v := by
    have hzm : (P20 (2 * m + 21) : ℤ) = P20Z u := P20_cast (by omega)
    have hzn : (P20 (2 * n + 21) : ℤ) = P20Z v := P20_cast (by omega)
    have hmidz : (P20 (2 * m + 21) : ℤ) = 25 * (P20 (2 * n + 21) : ℤ) := by exact_mod_cast hmid
    linarith only [hzm, hzn, hmidz]
  have hu65 : 5 * u < 6 * v := by
    by_contra hge
    have h65 : 6 * v ≤ 5 * u := by omega
    have hprod_le : (∏ j ∈ Finset.Icc (1 : ℕ) 10, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2)) ≤
        ∏ j ∈ Finset.Icc (1 : ℕ) 10, ((5 * u) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        have h2j : 2 * (j : ℤ) - 1 ≤ 19 := by omega
        have h1 : 0 ≤ 2 * (j : ℤ) - 1 := by omega
        have hsq : (2 * (j : ℤ) - 1) ^ 2 ≤ 361 := by nlinarith
        nlinarith
      · intro j _
        have hsq : (6 * v) ^ 2 ≤ (5 * u) ^ 2 := by nlinarith
        omega
    have hgt := P20Z_hom65_gt hv49213
    rw [← P20Z_prod_scaled5 u] at hprod_le
    linarith only [hPeq, hgt, hprod_le]
  have hR_bound : 25 * R20Z v < R20Z u := by
    have hs5_lt : negR20_s5 (5 * u - 105) < negR20_s5 (6 * v - 105) :=
      negR20_s5_strictMono (by omega) (by omega)
    have hup65 := negR20_s5_upper65 hv49213
    rw [← negR20_s5_eval u] at hs5_lt
    linarith only [hs5_lt, hup65]
  have hQu_lt_5Qv : Q20Z u < 5 * Q20Z v := by
    have hsq_eq : Q20Z u ^ 2 + R20Z u = 25 * Q20Z v ^ 2 + 25 * R20Z v := by
      linarith only [P20Z_eq u, P20Z_eq v, hPeq]
    have hsq_lt : Q20Z u ^ 2 < (5 * Q20Z v) ^ 2 := by linarith only [hsq_eq, hR_bound]
    have hQv_pos := Q20Z_pos hv21
    nlinarith only [hsq_lt, hQv_pos]
  obtain ⟨k_v2, hk_v2⟩ := Q20Z_3200_dvd ((n : ℤ) + 10)
  obtain ⟨k_u2, hk_u2⟩ := Q20Z_3200_dvd ((m : ℤ) + 10)
  have hu_eq : 2 * ((m : ℤ) + 10) + 1 = u := by dsimp [u]; ring
  have hv_eq : 2 * ((n : ℤ) + 10) + 1 = v := by dsimp [v]; ring
  rw [hu_eq] at hk_u2
  rw [hv_eq] at hk_v2
  have hdvd : (3200 : ℤ) ∣ 5 * Q20Z v - Q20Z u := ⟨5 * k_v2 - k_u2, by linarith only [hk_v2, hk_u2]⟩
  obtain ⟨d, hd⟩ := hdvd
  have hd_pos : 1 ≤ d := by nlinarith only [hd, hQu_lt_5Qv]
  have hQu_le : Q20Z u ≤ 5 * Q20Z v - 3200 := by nlinarith only [hd, hd_pos]
  have hQu_nonneg : 0 ≤ Q20Z u := le_of_lt (Q20Z_pos (by omega))
  have hsq_le : Q20Z u ^ 2 ≤ (5 * Q20Z v - 3200) ^ 2 := by nlinarith only [hQu_le, hQu_nonneg]
  have hRu_lt : R20Z u < R20Z v := R20Z_lt_of_lt hv21 hvu
  have hsq_eq : Q20Z u ^ 2 + R20Z u = 25 * Q20Z v ^ 2 + 25 * R20Z v := by
    linarith only [P20Z_eq u, P20Z_eq v, hPeq]
  have hneg_t : 3200 * (10 * Q20Z v - 3200) + 24 * R20Z v < 0 := by
    linarith only [hsq_le, hRu_lt, hsq_eq]
  exact absurd (thresh_20_pos hv49213) (not_lt.mpr (le_of_lt hneg_t))

/-! ## 3. Main Theorems -/

/-- No integers `m ≥ n + 20` satisfy `∏_{i=1}^{20} (m + i) = 25 * ∏_{i=1}^{20} (n + i)`. -/
theorem no_sol_twenty_five_twenty_Icc :
    ¬ ∃ (m n : ℕ), m ≥ n + 20 ∧
      (∏ i ∈ Finset.Icc 1 20, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 20, (n + i)) := by
  rintro ⟨m, n, hmn, heq⟩
  have hmid : P20 (2 * m + 21) = 25 * P20 (2 * n + 21) := by
    have hm := prod20_midpoint m
    have hn := prod20_midpoint n
    have hmul : 2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (m + i)) =
        25 * (2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (n + i))) := by
      calc 2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (m + i))
          = 2 ^ 20 * (25 * (∏ i ∈ Finset.Icc 1 20, (n + i))) := by rw [heq]
        _ = 25 * (2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (n + i))) := by ring
    linarith only [hm, hn, hmul]
  by_cases hn25000 : 25000 ≤ n
  · exact asymp20_excl hmn (by omega) hmid
  · exact base20_excl n (by omega) m hmid

/-- Official `Finset.range 20` formulation matching Erdős #686 (`N = 25`, `k = 20`). -/
theorem no_sol_twenty_five_twenty :
    ¬ ∃ (m n : ℕ), m ≥ n + 20 ∧
      (∏ i ∈ Finset.range 20, (m + i + 1)) = 25 * (∏ i ∈ Finset.range 20, (n + i + 1)) := by
  rintro ⟨m, n, hmn, heq⟩
  rw [prod20_range_eq_Icc m, prod20_range_eq_Icc n] at heq
  exact no_sol_twenty_five_twenty_Icc ⟨m, n, hmn, heq⟩

private lemma prod20_pos (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 20, (n + i) := by
  apply Nat.pos_of_ne_zero
  intro h0
  obtain ⟨i, hi, hzi⟩ := Finset.prod_eq_zero_iff.mp h0
  rw [Finset.mem_Icc] at hi
  omega

/-- Full unrestricted length-20 exclusion (`m, n : ℕ`, no disjointness assumption needed). -/
theorem length_twenty (m n : ℕ) :
    (∏ i ∈ Finset.Icc 1 20, (m + i)) ≠ 25 * (∏ i ∈ Finset.Icc 1 20, (n + i)) := by
  intro heq
  by_cases hmn : m ≥ n + 20
  · exact no_sol_twenty_five_twenty_Icc ⟨m, n, hmn, heq⟩
  · by_cases hn25000 : n < 25000
    · have hmid : P20 (2 * m + 21) = 25 * P20 (2 * n + 21) := by
        have hm := prod20_midpoint m
        have hn := prod20_midpoint n
        have hmul : 2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (m + i)) =
            25 * (2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (n + i))) := by
          calc 2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (m + i))
              = 2 ^ 20 * (25 * (∏ i ∈ Finset.Icc 1 20, (n + i))) := by rw [heq]
            _ = 25 * (2 ^ 20 * (∏ i ∈ Finset.Icc 1 20, (n + i))) := by ring
        linarith only [hm, hn, hmul]
      exact base20_excl n hn25000 m hmid
    · have h_pt : ∀ i ∈ Finset.Icc 1 20, 10 * (m + i) ≤ 11 * (n + i) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        omega
      have hprod : ∏ i ∈ Finset.Icc 1 20, (10 * (m + i)) ≤
          ∏ i ∈ Finset.Icc 1 20, (11 * (n + i)) := Finset.prod_le_prod' h_pt
      have hcard : (Finset.Icc 1 20).card = 20 := by simp [Nat.card_Icc]
      rw [Finset.prod_mul_distrib, Finset.prod_const, hcard,
          Finset.prod_mul_distrib, Finset.prod_const, hcard, heq] at hprod
      have hP : 0 < ∏ i ∈ Finset.Icc 1 20, (n + i) := prod20_pos n
      have hpow : 11 ^ 20 < 10 ^ 20 * 25 := by norm_num
      nlinarith

/-- Direct interface to the `k = 20` case of `Erdos686.erdos_686.variants.twenty_five`. -/
theorem no_ratio_twenty_five_twenty (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 20, (m + i)) / (∏ i ∈ Finset.Icc 1 20, (n + i)) := by
  intro h
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 20, (n + i) := prod20_pos n
  have hd : ((∏ i ∈ Finset.Icc 1 20, (n + i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hz := (eq_div_iff hd).mp h
  have hn : 25 * (∏ i ∈ Finset.Icc 1 20, (n + i)) = ∏ i ∈ Finset.Icc 1 20, (m + i) := by
    exact_mod_cast hz
  exact length_twenty m n hn.symm

/-- Bridge theorem discharging the `k = 20` branch of `Erdos686.erdos_686.variants.twenty_five`. -/
theorem erdos_686_variants_twenty_five_k20_bridge :
    ¬ ∃ (n : ℕ), ∃ m ≥ n + 20,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 20, (m + i)) / (∏ i ∈ Finset.Icc 1 20, (n + i)) := by
  rintro ⟨n, m, _, h⟩
  exact no_ratio_twenty_five_twenty m n h

end Contribution.Erdos686TwentyTwentyFive
