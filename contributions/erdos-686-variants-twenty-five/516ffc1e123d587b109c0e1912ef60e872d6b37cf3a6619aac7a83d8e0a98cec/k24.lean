import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Interval.Finset.Nat

/-!
# Unconditional Exclusion of k = 24 for Erdős Problem #686 (N = 25)

Proves via exact polynomial square-completion (`P_24(x) = Q_24(x)^2 + R_24(x)`, `S = 1`),
modular congruence (`21233664 ∣ 5 * Q_24(2*b + 1) - Q_24(2*a + 1)` from `mod 2^18` and `81 ∣ Q_24`),
Taylor-shift positivity at `n_0 = 15000` (`v_0 = 30025`), and kernel-verified bracketing over
`1 ≤ n ≤ 15000` (`15` blocks of `1000`, `decide +kernel`) plus `n = 0` disjointness (`m ≥ 24`),
that no integers `m ≥ n + 24` satisfy
`∏ i ∈ Finset.range 24, (m + i + 1) = 25 * ∏ i ∈ Finset.range 24, (n + i + 1)`
(nor rational quotient `25`).
-/

namespace Contribution.Erdos686TwentyFourTwentyFive

def P24 (x : ℕ) : ℕ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) * (x2 - 121) *
    (x2 - 169) * (x2 - 225) * (x2 - 289) * (x2 - 361) * (x2 - 441) * (x2 - 529)

def P24Z (x : ℤ) : ℤ :=
  let x2 := x * x
  (x2 - 1) * (x2 - 9) * (x2 - 25) * (x2 - 49) * (x2 - 81) * (x2 - 121) *
    (x2 - 169) * (x2 - 225) * (x2 - 289) * (x2 - 361) * (x2 - 441) * (x2 - 529)

def Q24Z (x : ℤ) : ℤ :=
  x ^ 12 - 1150 * x ^ 10 + 463335 * x ^ 8 - 79816900 * x ^ 6 + 5653201855 * x ^ 4 - 147023085150 * x ^ 2 - 6540540635655

def R24Z (x : ℤ) : ℤ :=
  -7057203580108800 * x ^ 10 + 4570482388374650880 * x ^ 8 - 967347850298838220800 * x ^ 6 + 75155627950280722612224 * x ^ 4 - 2044513741960343715840000 * x ^ 2 - 42678667773313061643878400

def negR24_s5 (t : ℤ) : ℤ :=
  7057203580108800 * t ^ 10 + 8821504475136000000 * t ^ 9 + 4847834207554633728000 * t ^ 8 + 1539770029378633728000000 * t ^ 7 + 312434460771589029888000000 * t ^ 6 + 42228959447315644416000000000 * t ^ 5 + 3841236283585655743709184000000 * t ^ 4 + 231574090834450911854592000000000 * t ^ 3 + 8829181299802079232000000000000000 * t ^ 2 + 191657038425384812544000000000000000 * t + 1794520064179540240367616000000000000

private lemma mul_lt_mul_nat {a b c d : ℕ} (hab : a < b) (hcd : c < d) (hd : 0 < d) :
    a * c < b * d :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_lt hcd))
    (Nat.mul_lt_mul_of_pos_right hab hd)

private lemma P24_strictMono {a b : ℕ} (ha : 23 ≤ a) (hab : a < b) : P24 a < P24 b := by
  have hb : 23 ≤ b := by omega
  have hab2 : a * a < b * b := mul_lt_mul_nat hab hab (by omega)
  have ha2 : 529 ≤ a * a := Nat.mul_le_mul ha ha
  dsimp only [P24]
  have p1 := mul_lt_mul_nat (by omega : a * a - 1 < b * b - 1) (by omega : a * a - 9 < b * b - 9) (by omega)
  have p2 := mul_lt_mul_nat p1 (by omega : a * a - 25 < b * b - 25) (by omega)
  have p3 := mul_lt_mul_nat p2 (by omega : a * a - 49 < b * b - 49) (by omega)
  have p4 := mul_lt_mul_nat p3 (by omega : a * a - 81 < b * b - 81) (by omega)
  have p5 := mul_lt_mul_nat p4 (by omega : a * a - 121 < b * b - 121) (by omega)
  have p6 := mul_lt_mul_nat p5 (by omega : a * a - 169 < b * b - 169) (by omega)
  have p7 := mul_lt_mul_nat p6 (by omega : a * a - 225 < b * b - 225) (by omega)
  have p8 := mul_lt_mul_nat p7 (by omega : a * a - 289 < b * b - 289) (by omega)
  have p9 := mul_lt_mul_nat p8 (by omega : a * a - 361 < b * b - 361) (by omega)
  have p10 := mul_lt_mul_nat p9 (by omega : a * a - 441 < b * b - 441) (by omega)
  exact mul_lt_mul_nat p10 (by omega : a * a - 529 < b * b - 529) (by omega)

private lemma P24_mono {a b : ℕ} (ha : 23 ≤ a) (hab : a ≤ b) : P24 a ≤ P24 b := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · exact le_of_lt (P24_strictMono ha hlt)

private lemma P24_cast {x : ℕ} (hx : 23 ≤ x) : (P24 x : ℤ) = P24Z (x : ℤ) := by
  have h529 : 529 ≤ x * x := Nat.mul_le_mul hx hx
  dsimp only [P24, P24Z]
  zify [show 1 ≤ x * x by omega, show 9 ≤ x * x by omega, show 25 ≤ x * x by omega,
    show 49 ≤ x * x by omega, show 81 ≤ x * x by omega, show 121 ≤ x * x by omega,
    show 169 ≤ x * x by omega, show 225 ≤ x * x by omega, show 289 ≤ x * x by omega,
    show 361 ≤ x * x by omega, show 441 ≤ x * x by omega, h529]

private lemma prod24_midpoint (m : ℕ) :
    2 ^ 24 * (∏ i ∈ Finset.Icc 1 24, (m + i)) = P24 (2 * m + 25) := by
  have hIcc : Finset.Icc 1 24 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24} := by
    decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  zify
  rw [P24_cast (by omega)]
  dsimp only [P24Z]
  push_cast
  ring

private lemma prod24_range_eq_Icc (m : ℕ) :
    (∏ i ∈ Finset.range 24, (m + i + 1)) = ∏ i ∈ Finset.Icc 1 24, (m + i) := by
  have hIcc : Finset.Icc 1 24 = (Finset.range 24).image (· + 1) := by decide
  rw [hIcc, Finset.prod_image (fun a _ b _ hab => by omega)]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

/-! ## 1. Finite Bracket Verification for 0 ≤ n ≤ 15000 -/

def findBracket24 (v : ℕ) : ℕ :=
  let rhs := 25 * P24 v
  let u0 := 2 * ((v * 11435298360) / 20000000000) + 1
  if P24 u0 < rhs then
    let u1 := u0 + 2
    if P24 u1 < rhs then u1 + 2 else u1
  else
    u0

def check24_v (v : ℕ) : Bool :=
  let rhs := 25 * P24 v
  let u := findBracket24 v
  decide (u ≥ 25 ∧ u % 2 = 1 ∧ P24 (u - 2) < rhs ∧ rhs < P24 u)

def stepBase24 (n : ℕ) : Bool := check24_v (2 * n + 25)

def checkBlock (stepFn : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => stepFn (start + k) && checkBlock stepFn start k

def checkGrid (stepFn : ℕ → Bool) (start blockSize : ℕ) : ℕ → Bool
  | 0 => true
  | b + 1 => checkBlock stepFn (start + b * blockSize) blockSize && checkGrid stepFn start blockSize b

theorem base24_ok : checkGrid stepBase24 1 1000 15 = true := by
  decide +kernel

private lemma check24_v_sound {v : ℕ} (hc : check24_v v = true) :
    ∀ m : ℕ, P24 (2 * m + 25) ≠ 25 * P24 v := by
  simp only [check24_v, decide_eq_true_eq] at hc
  rcases hc with ⟨hu25, hu_odd, hlo, hhi⟩
  intro m heq
  set u := findBracket24 v
  set x := 2 * m + 25
  by_cases hxu : x < u
  · have hle : x ≤ u - 2 := by omega
    have hpm : P24 x ≤ P24 (u - 2) := P24_mono (by omega) hle
    omega
  · have hge : u ≤ x := by omega
    have hpm : P24 u ≤ P24 x := P24_mono (by omega) hge
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

private lemma base24_excl :
    ∀ n ≤ 15000, ∀ m : ℕ, m ≥ n + 24 → P24 (2 * m + 25) ≠ 25 * P24 (2 * n + 25) := by
  intro n hn m hmn heq
  rcases Nat.eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
  · have hm73 : 73 ≤ 2 * m + 25 := by omega
    have hlt : 25 * P24 25 < P24 73 := by decide
    have hle : P24 73 ≤ P24 (2 * m + 25) := P24_mono (by omega) hm73
    simp only [Nat.mul_zero, Nat.zero_add] at heq
    omega
  · have hcell := checkGrid_sound base24_ok (n - 1) (by omega)
    have hstep : 1 + (n - 1) = n := by omega
    rw [hstep] at hcell
    exact check24_v_sound hcell m heq

/-! ## 2. Exact Square Completion, Modular Divisibility, and Taylor Bounds -/

private lemma P24Z_eq (x : ℤ) : P24Z x = Q24Z x ^ 2 + R24Z x := by
  dsimp only [P24Z, Q24Z, R24Z]
  ring

private lemma Q24Z_shift25 (y : ℤ) :
    Q24Z (25 + y) = y ^ 12 + 300 * y ^ 11 + 40100 * y ^ 10 + 3150000 * y ^ 9 + 161478960 * y ^ 8 + 5670792000 * y ^ 7 + 139278545600 * y ^ 6 + 2397351840000 * y ^ 5 + 28497731092480 * y ^ 4 + 225957109248000 * y ^ 3 + 1118531585433600 * y ^ 2 + 3034192711680000 * y + 3254712845598720 := by
  dsimp only [Q24Z]
  ring

private lemma negR24Z_shift25 (y : ℤ) :
    -R24Z (25 + y) = 7057203580108800 * y ^ 10 + 1764300895027200000 * y ^ 9 + 193913368302185349120 * y ^ 8 + 12318160235029069824000 * y ^ 7 + 499895137234542447820800 * y ^ 6 + 13513267023141006213120000 * y ^ 5 + 245839122149481967597387776 * y ^ 4 + 2964148362680971671738777600 * y ^ 3 + 22602704127493322833920000000 * y ^ 2 + 98128403673797024022528000000 * y + 183758854571984920613643878400 := by
  dsimp only [R24Z]
  ring

private lemma Q24Z_pos {v : ℤ} (hv : 25 ≤ v) : 0 < Q24Z v := by
  set y := v - 25
  have hy0 : 0 ≤ y := by omega
  have hsh := Q24Z_shift25 y
  rw [show 25 + y = v by omega] at hsh
  rw [hsh]
  positivity

private lemma R24Z_lt_of_lt {v u : ℤ} (hv : 25 ≤ v) (hvu : v < u) : R24Z u < R24Z v := by
  set xlo := v - 25
  set xhi := u - 25
  have hx0 : 0 ≤ xlo := by omega
  have hlt : xlo < xhi := by omega
  have h1 := negR24Z_shift25 xlo
  have h2 := negR24Z_shift25 xhi
  rw [show 25 + xlo = v by omega] at h1
  rw [show 25 + xhi = u by omega] at h2
  have hneg : -R24Z v < -R24Z u := by
    rw [h1, h2]
    have hpow10 : xlo ^ 10 ≤ xhi ^ 10 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 10
    have hm10 : (7057203580108800 : ℤ) * xlo ^ 10 ≤ (7057203580108800 : ℤ) * xhi ^ 10 := by linarith only [hpow10]
    have hpow9 : xlo ^ 9 ≤ xhi ^ 9 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 9
    have hm9 : (1764300895027200000 : ℤ) * xlo ^ 9 ≤ (1764300895027200000 : ℤ) * xhi ^ 9 := by linarith only [hpow9]
    have hpow8 : xlo ^ 8 ≤ xhi ^ 8 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 8
    have hm8 : (193913368302185349120 : ℤ) * xlo ^ 8 ≤ (193913368302185349120 : ℤ) * xhi ^ 8 := by linarith only [hpow8]
    have hpow7 : xlo ^ 7 ≤ xhi ^ 7 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 7
    have hm7 : (12318160235029069824000 : ℤ) * xlo ^ 7 ≤ (12318160235029069824000 : ℤ) * xhi ^ 7 := by linarith only [hpow7]
    have hpow6 : xlo ^ 6 ≤ xhi ^ 6 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 6
    have hm6 : (499895137234542447820800 : ℤ) * xlo ^ 6 ≤ (499895137234542447820800 : ℤ) * xhi ^ 6 := by linarith only [hpow6]
    have hpow5 : xlo ^ 5 ≤ xhi ^ 5 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 5
    have hm5 : (13513267023141006213120000 : ℤ) * xlo ^ 5 ≤ (13513267023141006213120000 : ℤ) * xhi ^ 5 := by linarith only [hpow5]
    have hpow4 : xlo ^ 4 ≤ xhi ^ 4 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 4
    have hm4 : (245839122149481967597387776 : ℤ) * xlo ^ 4 ≤ (245839122149481967597387776 : ℤ) * xhi ^ 4 := by linarith only [hpow4]
    have hpow3 : xlo ^ 3 ≤ xhi ^ 3 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 3
    have hm3 : (2964148362680971671738777600 : ℤ) * xlo ^ 3 ≤ (2964148362680971671738777600 : ℤ) * xhi ^ 3 := by linarith only [hpow3]
    have hpow2 : xlo ^ 2 ≤ xhi ^ 2 := pow_le_pow_left₀ hx0 (le_of_lt hlt) 2
    have hm2 : (22602704127493322833920000000 : ℤ) * xlo ^ 2 ≤ (22602704127493322833920000000 : ℤ) * xhi ^ 2 := by linarith only [hpow2]
    have hlt1 : (98128403673797024022528000000 : ℤ) * xlo < (98128403673797024022528000000 : ℤ) * xhi := by linarith only [hlt]
    linarith only [hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hlt1]
  omega

private lemma negR24_s5_strictMono {a b : ℤ} (ha : 0 ≤ a) (hab : a < b) :
    negR24_s5 a < negR24_s5 b := by
  dsimp only [negR24_s5]
  have hpow10 : a ^ 10 ≤ b ^ 10 := pow_le_pow_left₀ ha (le_of_lt hab) 10
  have hm10 : (7057203580108800 : ℤ) * a ^ 10 ≤ (7057203580108800 : ℤ) * b ^ 10 := by linarith only [hpow10]
  have hpow9 : a ^ 9 ≤ b ^ 9 := pow_le_pow_left₀ ha (le_of_lt hab) 9
  have hm9 : (8821504475136000000 : ℤ) * a ^ 9 ≤ (8821504475136000000 : ℤ) * b ^ 9 := by linarith only [hpow9]
  have hpow8 : a ^ 8 ≤ b ^ 8 := pow_le_pow_left₀ ha (le_of_lt hab) 8
  have hm8 : (4847834207554633728000 : ℤ) * a ^ 8 ≤ (4847834207554633728000 : ℤ) * b ^ 8 := by linarith only [hpow8]
  have hpow7 : a ^ 7 ≤ b ^ 7 := pow_le_pow_left₀ ha (le_of_lt hab) 7
  have hm7 : (1539770029378633728000000 : ℤ) * a ^ 7 ≤ (1539770029378633728000000 : ℤ) * b ^ 7 := by linarith only [hpow7]
  have hpow6 : a ^ 6 ≤ b ^ 6 := pow_le_pow_left₀ ha (le_of_lt hab) 6
  have hm6 : (312434460771589029888000000 : ℤ) * a ^ 6 ≤ (312434460771589029888000000 : ℤ) * b ^ 6 := by linarith only [hpow6]
  have hpow5 : a ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ ha (le_of_lt hab) 5
  have hm5 : (42228959447315644416000000000 : ℤ) * a ^ 5 ≤ (42228959447315644416000000000 : ℤ) * b ^ 5 := by linarith only [hpow5]
  have hpow4 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha (le_of_lt hab) 4
  have hm4 : (3841236283585655743709184000000 : ℤ) * a ^ 4 ≤ (3841236283585655743709184000000 : ℤ) * b ^ 4 := by linarith only [hpow4]
  have hpow3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha (le_of_lt hab) 3
  have hm3 : (231574090834450911854592000000000 : ℤ) * a ^ 3 ≤ (231574090834450911854592000000000 : ℤ) * b ^ 3 := by linarith only [hpow3]
  have hpow2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha (le_of_lt hab) 2
  have hm2 : (8829181299802079232000000000000000 : ℤ) * a ^ 2 ≤ (8829181299802079232000000000000000 : ℤ) * b ^ 2 := by linarith only [hpow2]
  have hlt1 : (191657038425384812544000000000000000 : ℤ) * a < (191657038425384812544000000000000000 : ℤ) * b := by linarith only [hab]
  linarith only [hm10, hm9, hm8, hm7, hm6, hm5, hm4, hm3, hm2, hlt1]

private lemma negR24_s5_eval (u : ℤ) : -5 ^ 10 * R24Z u = negR24_s5 (5 * u - 125) := by
  dsimp only [R24Z, negR24_s5]
  ring

private lemma Q24Z_2pow18_mod (a : ℤ) : ∃ k : ℤ, Q24Z (2 * a + 1) = 262144 * k + 131072 := by
  set qq := a / 4
  have hr : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
  rcases hr with h0 | h1 | h2 | h3
  · have hx : 2 * a + 1 = 8 * qq + 1 := by omega
    rw [hx]
    refine ⟨262144 * qq ^ 12 + 393216 * qq ^ 11 - 4440064 * qq ^ 10 - 5775360 * qq ^ 9 + 26373120 * qq ^ 8 + 28555776 * qq ^ 7 - 67084096 * qq ^ 6 - 56655456 * qq ^ 5 + 70127200 * qq ^ 4 + 41098200 * qq ^ 3 - 27902394 * qq ^ 2 - 8297991 * qq - 25489769, by dsimp only [Q24Z]; ring⟩
  · have hx : 2 * a + 1 = 8 * qq + 3 := by omega
    rw [hx]
    refine ⟨262144 * qq ^ 12 + 1179648 * qq ^ 11 - 2277376 * qq ^ 10 - 14622720 * qq ^ 9 + 2411520 * qq ^ 8 + 60691968 * qq ^ 7 + 18055616 * qq ^ 6 - 100603872 * qq ^ 5 - 41684000 * qq ^ 4 + 60048600 * qq ^ 3 + 17186094 * qq ^ 2 - 11599227 * qq - 28461659, by dsimp only [Q24Z]; ring⟩
  · have hx : 2 * a + 1 = 8 * qq + 5 := by omega
    rw [hx]
    refine ⟨262144 * qq ^ 12 + 1966080 * qq ^ 11 + 2048000 * qq ^ 10 - 15360000 * qq ^ 9 - 33346560 * qq ^ 8 + 30067200 * qq ^ 7 + 108017600 * qq ^ 6 + 636000 * qq ^ 5 - 118551680 * qq ^ 4 - 30754200 * qq ^ 3 + 33157350 * qq ^ 2 + 3891375 * qq - 29602058, by dsimp only [Q24Z]; ring⟩
  · have hx : 2 * a + 1 = 8 * qq + 7 := by omega
    rw [hx]
    refine ⟨262144 * qq ^ 12 + 2752512 * qq ^ 11 + 8536064 * qq ^ 10 - 2580480 * qq ^ 9 - 56570880 * qq ^ 8 - 64608768 * qq ^ 7 + 84744896 * qq ^ 6 + 166125792 * qq ^ 5 - 10908800 * qq ^ 4 - 113160600 * qq ^ 3 - 27579906 * qq ^ 2 + 7972587 * qq - 27472244, by dsimp only [Q24Z]; ring⟩

private lemma Q24Z_81_dvd (x : ℤ) : (81 : ℤ) ∣ Q24Z x := by
  set qq := x / 3
  have hr : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases hr with h0 | h1 | h2
  · have hx : x = 3 * qq + 0 := by omega
    rw [hx]
    refine ⟨6561 * qq ^ 12 - 838350 * qq ^ 10 + 37530135 * qq ^ 8 - 718352100 * qq ^ 6 + 5653201855 * qq ^ 4 - 16335898350 * qq ^ 2 - 80747415255, by dsimp only [Q24Z]; ring⟩
  · have hx : x = 3 * qq + 1 := by omega
    rw [hx]
    refine ⟨6561 * qq ^ 12 + 26244 * qq ^ 11 - 790236 * qq ^ 10 - 2741040 * qq ^ 9 + 33378480 * qq ^ 8 + 96375744 * qq ^ 7 - 603756864 * qq ^ 6 - 1359730944 * qq ^ 5 + 4488140800 * qq ^ 4 + 7014092800 * qq ^ 3 - 12698689536 * qq ^ 2 - 10070687744 * qq - 82493702144, by dsimp only [Q24Z]; ring⟩
  · have hx : x = 3 * qq + 2 := by omega
    rw [hx]
    refine ⟨6561 * qq ^ 12 + 52488 * qq ^ 11 - 645894 * qq ^ 10 - 5161320 * qq ^ 9 + 21404655 * qq ^ 8 + 171037008 * qq ^ 7 - 285554196 * qq ^ 6 - 2278202832 * qq ^ 5 + 1367793775 * qq ^ 4 + 11089218600 * qq ^ 3 - 3298353414 * qq ^ 2 - 15631338312 * qq - 86952747999, by dsimp only [Q24Z]; ring⟩

private lemma Q24Z_diff_21233664_dvd (a b : ℤ) :
    (21233664 : ℤ) ∣ 5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1) := by
  obtain ⟨ka, hka⟩ := Q24Z_2pow18_mod a
  obtain ⟨kb, hkb⟩ := Q24Z_2pow18_mod b
  have h2 : (262144 : ℤ) ∣ 5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1) :=
    ⟨5 * kb - ka + 2, by linarith only [hka, hkb]⟩
  obtain ⟨K2, hK2⟩ := h2
  obtain ⟨Ka, hKa⟩ := Q24Z_81_dvd (2 * a + 1)
  obtain ⟨Kb, hKb⟩ := Q24Z_81_dvd (2 * b + 1)
  have h81 : (81 : ℤ) ∣ 5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1) :=
    ⟨5 * Kb - Ka, by linarith only [hKa, hKb]⟩
  obtain ⟨K81, hK81⟩ := h81
  refine ⟨(-26 : ℤ) * K81 + 84145 * K2, ?_⟩
  calc 5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1)
      = (-26 * 262144 + 84145 * 81) * (5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1)) := by ring
    _ = -26 * 262144 * (5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1)) +
          84145 * 81 * (5 * Q24Z (2 * b + 1) - Q24Z (2 * a + 1)) := by ring
    _ = -26 * 262144 * (81 * K81) + 84145 * 81 * (262144 * K2) := by rw [← hK81, ← hK2]
    _ = 21233664 * ((-26 : ℤ) * K81 + 84145 * K2) := by ring

private lemma P24Z_prod_scaled5 (u : ℤ) :
    5 ^ 24 * P24Z u =
      ∏ j ∈ Finset.Icc (1 : ℕ) 12, ((5 * u) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2) := by
  have hIcc : Finset.Icc (1 : ℕ) 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  rw [hIcc]
  simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  dsimp only [P24Z]
  ring

private lemma P24Z_hom65_gt {v : ℤ} (hv : 30025 ≤ v) :
    25 * 5 ^ 24 * P24Z v <
      ∏ j ∈ Finset.Icc (1 : ℕ) 12, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2) := by
  set y := v - 30025
  have hy0 : 0 ≤ y := by omega
  have hprod : (∏ j ∈ Finset.Icc (1 : ℕ) 12, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2)) -
      25 * 5 ^ 24 * P24Z v = 3248265218936851271 * y ^ 24 + 2340699916765895025882600 * y ^ 23 + 808214418369323082404038865000 * y ^ 22 + 177955342861068833306693582685000000 * y ^ 21 + 28051322708196170275772883529347887450000 * y ^ 20 + 3368963788209241130568637178510850814350000000 * y ^ 19 + 320318261307170779492563097562986790678595800000000 * y ^ 18 + 24730857000225710757757279634698941598848882360000000000 * y ^ 17 + 1577905903950426388411034837232696758511551343176418500000000 * y ^ 16 + 84225107243011775312236409391149646358536163482470859900000000000 * y ^ 15 + 3793288092538935518210948288529511332272000847686602083120500000000000 * y ^ 14 + 144955324363838523848198087616137159143672051862956852637175300000000000000 * y ^ 13 + 4714973649458005040063134659003693587259513467250205379903756088515000000000000 * y ^ 12 + 130677300111646134090931556733233112506977206299043716366253260128767000000000000000 * y ^ 11 + 3082817315689404660685479038437374630245660079141923234365274107899755536250000000000000 * y ^ 10 + 61707722176047962168077749312410808924097869393059947827268104641584804109062500000000000000 * y ^ 9 + 1042185496467506112917242962370092395437560356583163002105963839197731457678175150585937500000000 * y ^ 8 + 14725466807631148388322652073108704578364701155956753634367255040187253370145172733242187500000000000 * y ^ 7 + 171940262040070283135097451086691464109553151256351513680787948896756217827369390532207836914062500000000 * y ^ 6 + 1630265018412738400127545063804716854901675709387866247819927509384098467135517918197818138427734375000000000 * y ^ 5 + 12237175603186870030148122931586215410925717465525452379821779899089760406175384717719464947019338989257812500000 * y ^ 4 + 69984982825746342389068659396803526154085172893033750337370919777291380629805307469044043730757353820800781250000000 * y ^ 3 + 286540756807049223599036845147277931994890875521153843308814894638834865047266106656503956121729844807624816894531250000 * y ^ 2 + 748120456814033060708322647320556440364847716610132723228153205271429408760867195795710138425000483730936050415039062500000 * y + 935929752867063885638605658508550655814760226431648652266092424997207802667403128917193319203801923995804227888584136962890625 := by
    have hIcc : Finset.Icc (1 : ℕ) 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
    rw [hIcc]
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton,
      Finset.prod_singleton, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
    have hv_eq : v = 30025 + y := by omega
    rw [hv_eq]
    dsimp only [P24Z]
    ring
  have hpos : 0 < (∏ j ∈ Finset.Icc (1 : ℕ) 12, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2)) -
      25 * 5 ^ 24 * P24Z v := by
    rw [hprod]
    positivity
  omega

private lemma negR24_s5_upper65 {v : ℤ} (hv : 30025 ≤ v) :
    negR24_s5 (6 * v - 125) < 25 * 5 ^ 10 * (-R24Z v) := by
  set y := v - 30025
  have hy0 : 0 ≤ y := by omega
  have hdiff : 25 * 5 ^ 10 * (-R24Z v) - negR24_s5 (6 * v - 125) =
      1296227979057311200051200 * y ^ 10 + 389192450711957687815372800000 * y ^ 9 + 52584764072895339926481497751552000 * y ^ 8 + 4210286628818783437402132628530790400000 * y ^ 7 + 221224236392143727035367545483867717632000000 * y ^ 6 + 7970708677021569527199117716596330384588800000000 * y ^ 5 + 199433755835867965596316696930425543823941697536000000 * y ^ 4 + 3421713078691677389822688784165105547005608434073600000000 * y ^ 3 + 38526345956987891499833543473657336312317009316085760000000000 * y ^ 2 + 257056305503012043670320431506794383742672299361386496000000000000 * y + 771811435224931583582995978851796283880345793860025488384000000000000 := by
    have hv_eq : v = 30025 + y := by omega
    rw [hv_eq]
    dsimp only [R24Z, negR24_s5]
    ring
  have hpos : 0 < 25 * 5 ^ 10 * (-R24Z v) - negR24_s5 (6 * v - 125) := by
    rw [hdiff]
    positivity
  omega

private lemma thresh_24_pos {v : ℤ} (hv : 30025 ≤ v) :
    0 < 21233664 * (10 * Q24Z v - 21233664) + 24 * R24Z v := by
  set y := v - 30025
  have hy0 : 0 ≤ y := by omega
  have heq : 21233664 * (10 * Q24Z v - 21233664) + 24 * R24Z v =
      212336640 * y ^ 12 + 76504891392000 * y ^ 11 + 12464453372136652800 * y ^ 10 + 1213581186784375603200000 * y ^ 9 + 78549469549720423111348715520 * y ^ 8 + 3553459735248652433519913467904000 * y ^ 7 + 114839227119756777957074506533883084800 * y ^ 6 + 2657897614799385482276404989203809566720000 * y ^ 5 + 43362300660744123903660834477954690786395160576 * y ^ 4 + 479289819379500075170402887842017215929130785177600 * y ^ 3 + 3310385530088900315927707357881860326886740385071104000 * y ^ 2 + 11964687824499071110740454946029679115327802266825523200000 * y + 13128384345074008870420335718660614252400221827225771053154304 := by
    have hv_eq : v = 30025 + y := by omega
    rw [hv_eq]
    dsimp only [Q24Z, R24Z]
    ring
  rw [heq]
  positivity

private lemma asymp24_excl {m n : ℕ} (hmn : m ≥ n + 24) (hn : 15000 ≤ n)
    (hmid : P24 (2 * m + 25) = 25 * P24 (2 * n + 25)) : False := by
  set u : ℤ := ((2 * m + 25 : ℕ) : ℤ)
  set v : ℤ := ((2 * n + 25 : ℕ) : ℤ)
  have hv30025 : 30025 ≤ v := by omega
  have hv25 : 25 ≤ v := by omega
  have hvu : v < u := by omega
  have hPeq : P24Z u = 25 * P24Z v := by
    have hzm : (P24 (2 * m + 25) : ℤ) = P24Z u := P24_cast (by omega)
    have hzn : (P24 (2 * n + 25) : ℤ) = P24Z v := P24_cast (by omega)
    have hmidz : (P24 (2 * m + 25) : ℤ) = 25 * (P24 (2 * n + 25) : ℤ) := by exact_mod_cast hmid
    linarith only [hzm, hzn, hmidz]
  have hu65 : 5 * u < 6 * v := by
    by_contra hge
    have h65 : 6 * v ≤ 5 * u := by omega
    have hprod_le : (∏ j ∈ Finset.Icc (1 : ℕ) 12, ((6 * v) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2)) ≤
        ∏ j ∈ Finset.Icc (1 : ℕ) 12, ((5 * u) ^ 2 - 25 * (2 * (j : ℤ) - 1) ^ 2) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        have h2j : 2 * (j : ℤ) - 1 ≤ 23 := by omega
        have h1 : 0 ≤ 2 * (j : ℤ) - 1 := by omega
        have hsq : (2 * (j : ℤ) - 1) ^ 2 ≤ 529 := by nlinarith
        nlinarith
      · intro j _
        have hsq : (6 * v) ^ 2 ≤ (5 * u) ^ 2 := by nlinarith
        omega
    have hgt := P24Z_hom65_gt hv30025
    rw [← P24Z_prod_scaled5 u] at hprod_le
    linarith only [hPeq, hgt, hprod_le]
  have hR_bound : 25 * R24Z v < R24Z u := by
    have hs5_lt : negR24_s5 (5 * u - 125) < negR24_s5 (6 * v - 125) :=
      negR24_s5_strictMono (by omega) (by omega)
    have hup65 := negR24_s5_upper65 hv30025
    rw [← negR24_s5_eval u] at hs5_lt
    linarith only [hs5_lt, hup65]
  have hQu_lt_5Qv : Q24Z u < 5 * Q24Z v := by
    have hsq_eq : Q24Z u ^ 2 + R24Z u = 25 * Q24Z v ^ 2 + 25 * R24Z v := by
      linarith only [P24Z_eq u, P24Z_eq v, hPeq]
    have hsq_lt : Q24Z u ^ 2 < (5 * Q24Z v) ^ 2 := by linarith only [hsq_eq, hR_bound]
    have hQv_pos := Q24Z_pos hv25
    nlinarith only [hsq_lt, hQv_pos]
  obtain ⟨d, hd⟩ := Q24Z_diff_21233664_dvd ((m : ℤ) + 12) ((n : ℤ) + 12)
  have hu_eq : 2 * ((m : ℤ) + 12) + 1 = u := by dsimp [u]; ring
  have hv_eq : 2 * ((n : ℤ) + 12) + 1 = v := by dsimp [v]; ring
  rw [hu_eq, hv_eq] at hd
  have hd_pos : 1 ≤ d := by nlinarith only [hd, hQu_lt_5Qv]
  have hQu_le : Q24Z u ≤ 5 * Q24Z v - 21233664 := by nlinarith only [hd, hd_pos]
  have hQu_nonneg : 0 ≤ Q24Z u := le_of_lt (Q24Z_pos (by omega))
  have hsq_le : Q24Z u ^ 2 ≤ (5 * Q24Z v - 21233664) ^ 2 := by nlinarith only [hQu_le, hQu_nonneg]
  have hRu_lt : R24Z u < R24Z v := R24Z_lt_of_lt hv25 hvu
  have hsq_eq : Q24Z u ^ 2 + R24Z u = 25 * Q24Z v ^ 2 + 25 * R24Z v := by
    linarith only [P24Z_eq u, P24Z_eq v, hPeq]
  have hneg_t : 21233664 * (10 * Q24Z v - 21233664) + 24 * R24Z v < 0 := by
    linarith only [hsq_le, hRu_lt, hsq_eq]
  exact absurd (thresh_24_pos hv30025) (not_lt.mpr (le_of_lt hneg_t))

/-! ## 3. Main Theorems -/

/-- No integers `m ≥ n + 24` satisfy `∏_{i=1}^{24} (m + i) = 25 * ∏_{i=1}^{24} (n + i)`. -/
theorem no_sol_twenty_five_twenty_four_Icc :
    ¬ ∃ (m n : ℕ), m ≥ n + 24 ∧
      (∏ i ∈ Finset.Icc 1 24, (m + i)) = 25 * (∏ i ∈ Finset.Icc 1 24, (n + i)) := by
  rintro ⟨m, n, hmn, heq⟩
  have hmid : P24 (2 * m + 25) = 25 * P24 (2 * n + 25) := by
    have hm := prod24_midpoint m
    have hn := prod24_midpoint n
    have hmul : 2 ^ 24 * (∏ i ∈ Finset.Icc 1 24, (m + i)) =
        25 * (2 ^ 24 * (∏ i ∈ Finset.Icc 1 24, (n + i))) := by
      calc 2 ^ 24 * (∏ i ∈ Finset.Icc 1 24, (m + i))
          = 2 ^ 24 * (25 * (∏ i ∈ Finset.Icc 1 24, (n + i))) := by rw [heq]
        _ = 25 * (2 ^ 24 * (∏ i ∈ Finset.Icc 1 24, (n + i))) := by ring
    linarith only [hm, hn, hmul]
  by_cases hn15000 : 15000 ≤ n
  · exact asymp24_excl hmn hn15000 hmid
  · exact base24_excl n (by omega) m hmn hmid

/-- Official `Finset.range 24` formulation matching Erdős #686 (`N = 25`, `k = 24`). -/
theorem no_sol_twenty_five_twenty_four :
    ¬ ∃ (m n : ℕ), m ≥ n + 24 ∧
      (∏ i ∈ Finset.range 24, (m + i + 1)) = 25 * (∏ i ∈ Finset.range 24, (n + i + 1)) := by
  rintro ⟨m, n, hmn, heq⟩
  rw [prod24_range_eq_Icc m, prod24_range_eq_Icc n] at heq
  exact no_sol_twenty_five_twenty_four_Icc ⟨m, n, hmn, heq⟩

private lemma prod24_pos (n : ℕ) : 0 < ∏ i ∈ Finset.Icc 1 24, (n + i) := by
  apply Nat.pos_of_ne_zero
  intro h0
  obtain ⟨i, hi, hzi⟩ := Finset.prod_eq_zero_iff.mp h0
  rw [Finset.mem_Icc] at hi
  omega

/-- Direct rational-quotient interface to the `k = 24` case of
`Erdos686.erdos_686.variants.twenty_five`. -/
theorem no_ratio_twenty_five_twenty_four (n m : ℕ) (hmn : m ≥ n + 24) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 24, (m + i)) / (∏ i ∈ Finset.Icc 1 24, (n + i)) := by
  intro h
  have hpos : 0 < ∏ i ∈ Finset.Icc 1 24, (n + i) := prod24_pos n
  have hd : ((∏ i ∈ Finset.Icc 1 24, (n + i) : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hz := (eq_div_iff hd).mp h
  have hn : 25 * (∏ i ∈ Finset.Icc 1 24, (n + i)) = ∏ i ∈ Finset.Icc 1 24, (m + i) := by
    exact_mod_cast hz
  exact no_sol_twenty_five_twenty_four_Icc ⟨m, n, hmn, hn.symm⟩

/-- Bridge theorem discharging the `k = 24` branch of `Erdos686.erdos_686.variants.twenty_five`. -/
theorem erdos_686_variants_twenty_five_k24_bridge :
    ¬ ∃ (n : ℕ), ∃ m ≥ n + 24,
      (25 : ℚ) = (∏ i ∈ Finset.Icc 1 24, (m + i)) / (∏ i ∈ Finset.Icc 1 24, (n + i)) := by
  rintro ⟨n, m, hmn, h⟩
  exact no_ratio_twenty_five_twenty_four n m hmn h

end Contribution.Erdos686TwentyFourTwentyFive
