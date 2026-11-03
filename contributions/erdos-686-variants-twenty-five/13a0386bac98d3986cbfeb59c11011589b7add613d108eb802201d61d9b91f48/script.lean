import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős 686: ratio 25, length ten

This is a fixed-length partial result, not the unrestricted conjecture.
The square-gap/cross-multiplication framework extends the author's published
length-eight/twelve contribution. Compact arithmetic bracket hints were also
used in PR 141 (8ab9a0460eea0cf90d844499e005fd9e35744bd9); here a two-index
finite certificate is checked directly by Lean's kernel, using exact integers.
-/

namespace Contribution.Erdos686TenTwentyFive

/-- Integer squares with errors smaller than their positive roots have the same root. -/
lemma square_gap_force (p q c d : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcp : c < p) (hdq : d < q)
    (h : p^2 - q^2 = c-d) : p=q := by
  rcases lt_trichotomy p q with hl | he | hg
  · have hmul := mul_nonneg (show 0 ≤ q-p-1 by omega) (show 0 ≤ q+p by omega)
    nlinarith
  · exact he
  · have hmul := mul_nonneg (show 0 ≤ p-q-1 by omega) (show 0 ≤ p+q by omega)
    nlinarith


def block (n : ℕ) : ℕ := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)*
  (n+6)*(n+7)*(n+8)*(n+9)*(n+10)
def center (n : ℕ) : ℤ := 2*n+11
def poly (q : ℤ) : ℤ := 8*q^5-660*q^3+7887*q
def residual (q : ℤ) : ℤ := 25960*q^4-218295*q^2+2286144
def near (n : ℕ) : ℤ := poly (center n) / 5
def rem (n : ℕ) : ℤ := residual (center n)

lemma poly_dvd (q : ℤ) : 5 ∣ poly q := by
  apply Int.dvd_of_emod_eq_zero
  have hr : q % 5 = 0 ∨ q % 5 = 1 ∨ q % 5 = 2 ∨ q % 5 = 3 ∨ q % 5 = 4 := by omega
  rcases hr with hr | hr | hr | hr | hr <;>
    norm_num [poly, Int.add_emod, Int.sub_emod, Int.mul_emod, pow_succ, hr]

lemma near_spec (n : ℕ) : 5*near n = poly (center n) := by
  dsimp [near]
  exact Int.mul_ediv_cancel' (poly_dvd (center n))

lemma identity (n : ℕ) : 25*(near n)^2-65536*(block n : ℤ)=25*rem n := by
  have hp := near_spec n
  have hs : (5*near n)^2=(poly (center n))^2 := congrArg (fun x : ℤ => x^2) hp
  have hid : (poly (center n))^2-65536*(block n : ℤ)=25*rem n := by
    simp only [poly, center, rem, residual, block, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    ring
  nlinarith only [hs,hid]

lemma center_ge (n : ℕ) : 11 ≤ center n := by dsimp [center]; omega

lemma poly_pos (q : ℤ) (hq : 11 ≤ q) : 0 < poly q := by
  have hz : 0 ≤ q-11 := by omega
  have hid : poly q = 8*(q-11)^5+440*(q-11)^4+9020*(q-11)^3+
      84700*(q-11)^2+353947*(q-11)+496705 := by dsimp [poly]; ring
  rw [hid]
  positivity

lemma near_pos (n : ℕ) : 0 < near n := by
  have hp := poly_pos (center n) (center_ge n)
  have hs := near_spec n
  linarith only [hp,hs]

lemma residual_pos (q : ℤ) (hq : 11 ≤ q) : 0 < residual q := by
  have hq2 : 121 ≤ q^2 := by nlinarith only [hq]
  have hh := mul_nonneg (show 0 ≤ q^2-121 by omega) (sq_nonneg q)
  dsimp [residual]
  nlinarith only [hq2,hh]

lemma rem_pos (n : ℕ) : 0 < rem n := residual_pos (center n) (center_ge n)

lemma cross_pos (u v : ℤ) (hv : 11 ≤ v) (hu : v < u) :
    0 < poly u*residual v-poly v*residual u := by
  let d := u-v
  let z := v-11
  have hd : 0 < d := by dsimp [d]; omega
  have hz : 0 ≤ z := by dsimp [z]; omega
  have hid : poly u*residual v-poly v*residual u = d*(d^4*(207680*z^4 + 9137920*z^3 + 149029320*z^2 + 1067268400*z + 2847622472) + d^3*(830720*z^5 + 45689600*z^4 + 1013573000*z^3 + 11334142600*z^2 + 63749410240*z + 143724774160) + d^2*(1246080*z^6 + 82241280*z^5 + 2295572400*z^4 + 34663886400*z^3 + 297804246540*z^2 + 1373951796360*z + 2643338017980) + d*(830720*z^7 + 63965440*z^6 + 2146543080*z^5 + 40661687000*z^4 + 468109672600*z^3 + 3259506744120*z^2 + 12636158148185*z + 20896251873475) + 207680*z^8 + 18275840*z^7 + 715514360*z^6 + 16264674800*z^5 + 234054836300*z^4 + 2173004496080*z^3 + 12636158148185*z^2 + 41792503746950*z + 59723735059373) := by
    dsimp [poly,residual,d,z]
    ring
  rw [hid]
  positivity

lemma error_small (n : ℕ) (hn : 40600 ≤ n) : 5*rem n < near n := by
  have hq : 81211 ≤ center n := by dsimp [center]; omega
  have hq2 : 121 ≤ (center n)^2 := by nlinarith only [hq]
  have hr : rem n < 25960*(center n)^4 := by
    dsimp [rem,residual]
    nlinarith only [hq2]
  have hprod := mul_nonneg (show 0 ≤ center n-1 by omega)
    (show 0 ≤ (center n)^3 by positivity)
  have hp : (center n)^4*(8*center n-660) < poly (center n) := by
    dsimp [poly]
    nlinarith only [hprod,hq]
  have hprod2 := mul_nonneg (show 0 ≤ 8*center n-660-649000 by omega)
    (show 0 ≤ (center n)^4 by positivity)
  have hs := near_spec n
  nlinarith only [hr,hp,hprod2,hs]

lemma block_strictMono : StrictMono block := by
  intro a b hab
  dsimp [block]
  gcongr

/-- Any length-ten solution has its lower offset below the explicit bound. -/
theorem bound (n m : ℕ) (hmn : n ≤ m) (h : block m = 25*block n) : n < 40600 := by
  by_contra hn
  have hn' : 40600 ≤ n := by omega
  have hm' : 40600 ≤ m := by omega
  have hnid := identity n
  have hmid := identity m
  have hz : (block m : ℤ) = 25*(block n : ℤ) := by exact_mod_cast h
  have hp := near_pos m
  have hq := near_pos n
  have hc := rem_pos m
  have hd := rem_pos n
  have hsm := error_small m hm'
  have hsn := error_small n hn'
  have heq := square_gap_force (near m) (5*near n) (rem m) (25*rem n)
    (le_of_lt hp) (by linarith only [hq]) (le_of_lt hc)
    (by linarith only [hd]) (by linarith only [hc,hsm]) (by linarith only [hsn])
    (by nlinarith only [hnid,hmid,hz])
  have hrem : rem m = 25*rem n := by
    rw [heq] at hmid
    nlinarith only [hnid,hmid,hz]
  have hnm : n < m := by
    have hbp : 0 < block n := by dsimp [block]; positivity
    have hne : n ≠ m := by
      intro he
      rw [← he] at h
      omega
    exact lt_of_le_of_ne hmn hne
  have hcenter : center n < center m := by
    have hnz : (n:ℤ) < m := by exact_mod_cast hnm
    dsimp [center]
    linarith only [hnz]
  have hcross := cross_pos (center m) (center n) (center_ge n) hcenter
  have hpm := near_spec m
  have hpn := near_spec n
  change 0 < poly (center m)*rem n-poly (center n)*rem m at hcross
  rw [← hpm,← hpn,heq,hrem] at hcross
  have hprod := mul_pos hq hd
  nlinarith only [hcross,hprod]

/-- A numerical hint only; exact comparison selects one of two adjacent brackets. -/
def bracket (n : ℕ) : ℕ :=
  let b := (1379729661461*(2*n+11)/1000000000000-11)/2
  if 25*block n < block b then b-1 else b

def row (n : ℕ) : Prop :=
  block (bracket n) < 25*block n ∧ 25*block n < block (bracket n+1)
instance (n : ℕ) : Decidable (row n) := inferInstanceAs (Decidable (_ ∧ _))

/-- Small certificates keep kernel verification memory bounded. -/
lemma checked0 : ∀ i j : Fin 128, row (0+128*i+j) := by decide +kernel
lemma checked1 : ∀ i j : Fin 128, row (16384+128*i+j) := by decide +kernel
lemma checked2 : ∀ i j : Fin 128, row (32768+128*i+j) := by decide +kernel

lemma tile_sound (s n : ℕ) (h : ∀ i j : Fin 128, row (s+128*i+j))
    (hs : s ≤ n) (hn : n < s+16384) : row n := by
  let i : Fin 128 := ⟨(n-s)/128, by omega⟩
  let j : Fin 128 := ⟨(n-s)%128, by omega⟩
  have hr := h i j
  have he : s+128*((n-s)/128)+(n-s)%128=n := by omega
  change row (s+128*((n-s)/128)+(n-s)%128) at hr
  rwa [he] at hr

theorem checked (n : ℕ) (hn : n < 49152) : row n := by
  by_cases h0 : n < 16384
  · exact tile_sound 0 n checked0 (Nat.zero_le n) (by omega)
  by_cases h1 : n < 32768
  · exact tile_sound 16384 n checked1 (by omega) (by omega)
  · exact tile_sound 32768 n checked2 (by omega) (by omega)

theorem finite_check (n m : ℕ) (hn : n < 49152) : block m ≠ 25*block n := by
  intro heq
  obtain ⟨hl,hu⟩ := checked n hn
  by_cases hm : m ≤ bracket n
  · have hb := block_strictMono.monotone hm
    omega
  · have hb := block_strictMono.monotone (show bracket n+1 ≤ m by omega)
    omega

/-- Ratio 25 is impossible at length ten, even without disjointness. -/
theorem length_ten (m n : ℕ) : block m ≠ 25*block n := by
  intro h
  have hmn : n ≤ m := by
    by_contra hn
    have hlt := block_strictMono (show m < n by omega)
    have hp : 0 < block n := by dsimp [block]; positivity
    omega
  have hb := bound n m hmn h
  exact finite_check n m (by omega) h

/-- Direct interface to the length-ten instance of the pinned rational-product target. -/
theorem no_ratio_ten (m n : ℕ) :
    (25 : ℚ) ≠ (∏ i ∈ Finset.Icc 1 10, (m+i))/(∏ i ∈ Finset.Icc 1 10, (n+i)) := by
  norm_num [Finset.prod_Icc_succ_top,Finset.Icc_self,Finset.prod_singleton]
  intro h
  have hd : ((n:ℚ)+1)*(n+2)*(n+3)*(n+4)*(n+5)*(n+6)*(n+7)*(n+8)*(n+9)*(n+10) ≠ 0 := by positivity
  have hz := (eq_div_iff hd).mp h
  have hn : 25*block n = block m := by dsimp [block]; exact_mod_cast hz
  exact length_ten m n hn.symm

end Contribution.Erdos686TenTwentyFive
