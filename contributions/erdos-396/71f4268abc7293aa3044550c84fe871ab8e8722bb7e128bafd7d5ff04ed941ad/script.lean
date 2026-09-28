import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Adjacent quadratic rows and prime valuations for Erdos 396

This file constructs arbitrarily large common endpoints
  N = t * (2*t - 1) = 1 + 2*s * (3*s - 1).
For every block width K >= 2 it pays the COMPLETE K-row demand at each prime
p >= K, p > 2 dividing N or N-1, whenever p^2 > 4*t and p^2 > 12*s.
The other primes and rows remain uncontrolled. This is not a solution of
Erdos 396 or a complete fixed-width special case.

The construction and its carry arguments come from the contributor's
AI-assisted mathematical research. See sources.md for provenance and intended use.
The main entry point is cofinal_adjacent_rows. The generic reusable interface
is scaled_owner_all_width. This file imports only Mathlib.
-/

namespace Contribution.Erdos396AdjacentRows
open Finset

theorem row_owner_unique {p N K j k : ℕ} (hKN : K≤N) (hpK : K≤p)
    (hj : j<K) (hk : k<K) (hdj : p∣N-j) (hdk : p∣N-k) : j=k := by
  have hmod (i : ℕ) (hi : i<K) (hd : p∣N-i) : N%p=i := by
    calc
      N%p = (N-i+i)%p := by rw [Nat.sub_add_cancel (by omega : i≤N)]
      _ = i := by
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add,
          Nat.mod_eq_of_lt (hi.trans_le hpK), Nat.mod_eq_of_lt (hi.trans_le hpK)]
  exact (hmod j hj hdj).symm.trans (hmod k hk hdk)

theorem product_valuation {p : ℕ} (hp : p.Prime) (s : Finset ℕ)
    (f : ℕ→ℕ) (hf : ∀i∈s, f i≠0) :
    padicValNat p (∏i∈s, f i) = ∑i∈s, padicValNat p (f i) := by
  letI : Fact p.Prime := ⟨hp⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi,
      padicValNat.mul (hf i (mem_insert_self _ _))
        (prod_ne_zero_iff.mpr (fun j hj => hf j (mem_insert_of_mem hj))),
      ih (fun j hj => hf j (mem_insert_of_mem hj))]

theorem full_valuation_single_owner {p N K j : ℕ} (hp : p.Prime)
    (hKN : K≤N) (hpK : K≤p) (hj : j<K) (hd : p∣N-j) :
    padicValNat p (N.descFactorial K) = padicValNat p (N-j) := by
  rw [Nat.descFactorial_eq_prod_range,
    product_valuation hp _ _ (by intro i hi; have := mem_range.mp hi; omega)]
  apply sum_eq_single j
  · intro i hi hij
    apply padicValNat.eq_zero_of_not_dvd
    intro hdi
    exact hij (row_owner_unique hKN hpK (mem_range.mp hi) hj hdi hd)
  · intro hn
    exact (hn (mem_range.mpr hj)).elim

theorem supply_of_second_carry (p N : ℕ) (hp : p.Prime)
    (hc : p^2≤N%p^2+N%p^2) : 1≤padicValNat p (Nat.centralBinom N) := by
  letI : Fact p.Prime := ⟨hp⟩
  let b := 3+Nat.log p (N+N)
  have hb : Nat.log p (N+N)<b := by dsimp [b]; omega
  have hk : padicValNat p (Nat.centralBinom N)=
      ((Finset.Ico 1 b).filter (fun i => p^i≤N%p^i+N%p^i)).card := by
    simpa only [Nat.centralBinom, two_mul] using
      (padicValNat_choose' (p:=p) (n:=N) (k:=N) hb)
  rw [hk]
  apply Finset.card_pos.mpr
  exact ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by dsimp [b]; omega⟩, hc⟩⟩

theorem positive_correction_upper (a p B M C : ℕ)
    (ha : 0 < a) (hM : 0 < M) (hsmall : 2 * M < p)
    (hhalf : a ≤ 2 * (B % a)) (hHpos : 0 < B % a)
    (hC : a * C = p * B + M) : p < 2 * (C % p) := by
  let q := B / a
  let H := B % a
  have hHlt : H < a := Nat.mod_lt _ ha
  have he : B = a * q + H := by
    have hd := Nat.mod_add_div B a
    dsimp [q, H]
    omega
  have hrel0 : a * C = a * (p * q) + p * H + M := by
    rw [he] at hC
    nlinarith
  have hbase : p * q ≤ C := by nlinarith
  let R := C - p * q
  have hr : R + p * q = C := Nat.sub_add_cancel hbase
  have hrel : a * R = p * H + M := by nlinarith
  have hHle : H + 1 ≤ a := by omega
  have hbound := Nat.mul_le_mul_left p hHle
  have hrp : R < p := by nlinarith
  have hm : C % p = R := by
    rw [← hr]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hrp]
  rw [hm]
  have hhalf' : a ≤ 2 * H := hhalf
  have hmul := Nat.mul_le_mul_left p hhalf'
  nlinarith

theorem integer_negative (p B M C : ℕ) (hM : 0 < M) (hsmall : 2 * M < p)
    (hC : C + M = p * B) : p < 2 * (C % p) := by
  have hBpos : 0 < B := by
    by_contra h
    have hz : B = 0 := by omega
    simp [hz] at hC
    omega
  have hB : B = (B - 1) + 1 := by omega
  have hbase : p * (B - 1) ≤ C := by nlinarith
  let R := C - p * (B - 1)
  have hr : R + p * (B - 1) = C := Nat.sub_add_cancel hbase
  have hrel : R + M = p := by nlinarith
  have hrp : R < p := by omega
  have hm : C % p = R := by
    rw [← hr]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hrp]
  rw [hm]
  omega

theorem upper_owner_payment {p C N j K : ℕ} (hp : p.Prime)
    (hKN : K≤N) (hpK : K≤p) (hj : j<K)
    (hN : N=j+p*C) (hu : p<2*(C%p)) :
    padicValNat p (N.descFactorial K)=1 ∧
    padicValNat p (N.descFactorial K)≤padicValNat p (Nat.centralBinom N) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hCp : 0<C := by
    by_contra hn
    have hz : C=0 := by omega
    simp [hz] at hu
  have hnd : ¬p∣C := by intro hd; have hz:=Nat.mod_eq_zero_of_dvd hd; rw [hz] at hu; omega
  have hrow : N-j=p*C := by omega
  have hd : p∣N-j := by rw [hrow]; exact dvd_mul_right p C
  have hval : padicValNat p (N.descFactorial K)=1 := by
    rw [full_valuation_single_owner hp hKN hpK hj hd,hrow,
      padicValNat.mul hp.ne_zero hCp.ne',padicValNat_self,
      padicValNat.eq_zero_of_not_dvd hnd]
  refine ⟨hval,?_⟩
  rw [hval]
  apply supply_of_second_carry p N hp
  have hs : C%p<p := Nat.mod_lt _ hp.pos
  have hsmall : p*(C%p)+j<p^2 := by nlinarith
  have he : N=(p*(C%p)+j)+p^2*(C/p) := by
    have hh:=Nat.mod_add_div C p
    nlinarith
  have hm : N%p^2=p*(C%p)+j := by
    rw [he]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hsmall]
  rw [hm]
  nlinarith [Nat.mul_le_mul_left p (show p≤2*(C%p) by omega)]

theorem scaled_cofactor {a A h t p : ℕ}
    (ha : 2≤a) (hA : 0<A) (hh : 0<h) (ht : h≤t)
    (hp : p.Prime) (hAp : ¬p∣A)
    (hdiv : p∣A*t*(a*t-h)) (hsize : 2*A*a*h*t<p^2)
    (hmask : ∀c:ℕ,c∣a*t-h→a≤2*((A*c^2)%a) ∧ 0<(A*c^2)%a) :
    ∃C:ℕ,A*t*(a*t-h)=p*C ∧ p<2*(C%p) := by
  have htpos : 0<t := by omega
  have hat : h≤a*t := by nlinarith
  have hs : 0<a*t-h := Nat.sub_pos_of_lt (by nlinarith)
  have hsub : a*t-h+h=a*t := Nat.sub_add_cancel hat
  have hdiv' : p∣t*(a*t-h) := by
    have hd : p∣A*(t*(a*t-h)) := by simpa [Nat.mul_assoc] using hdiv
    exact (hp.dvd_mul.mp hd).resolve_left hAp
  rcases hp.dvd_mul.mp hdiv' with hl | hr
  · obtain ⟨c,hc⟩:=hl
    have hcpos : 0<c := by nlinarith
    have hbase : 2*A*h*t<p^2 := by
      have hm:=Nat.mul_le_mul_left (2*A*h*t) (show 1≤a by omega)
      nlinarith only [hm,hsize]
    have hsmall : 2*(A*h*c)<p := by
      have hx : p*(2*(A*h*c))<p*p := by
        calc
          p*(2*(A*h*c))=2*A*h*t := by rw [hc]; ring
          _<p*p := by simpa only [pow_two] using hbase
      exact (Nat.mul_lt_mul_left hp.pos).mp hx
    let C:=A*c*(a*t-h)
    have hC : C+A*h*c=p*(A*a*c^2) := by
      dsimp [C]
      nlinarith only [congrArg (A*c*·) hsub,congrArg (A*a*c*·) hc]
    refine ⟨C,?_,integer_negative p (A*a*c^2) (A*h*c) C (by positivity) hsmall hC⟩
    dsimp [C]; rw [hc]; ring
  · obtain ⟨c,hc⟩:=hr
    have hcpos : 0<c := by nlinarith
    have hsmall : 2*(A*h*c)<p := by
      have hm:=Nat.mul_le_mul_left (2*A*h) (show p*c≤a*t by omega)
      have hx : p*(2*(A*h*c))<p*p := by nlinarith only [hm,hsize]
      exact (Nat.mul_lt_mul_left hp.pos).mp hx
    let C:=A*t*c
    have hC : a*C=p*(A*c^2)+A*h*c := by
      dsimp [C]
      nlinarith only [congrArg (A*c*·) hsub,congrArg (A*c*·) hc]
    have hm:=hmask c (by rw [hc]; exact dvd_mul_left c p)
    refine ⟨C,?_,positive_correction_upper a p (A*c^2) (A*h*c) C
      (by omega) (by positivity) hsmall hm.1 hm.2 hC⟩
    dsimp [C]; rw [hc]; ring

theorem scaled_owner_all_width {a A h t N j K p : ℕ}
    (ha : 2≤a) (hA : 0<A) (hh : 0<h) (ht : h≤t)
    (hp : p.Prime) (hAp : ¬p∣A) (hKN : K≤N) (hpK : K≤p) (hj : j<K)
    (hN : N=j+A*t*(a*t-h)) (hdiv : p∣N-j) (hsize : 2*A*a*h*t<p^2)
    (hmask : ∀c:ℕ,c∣a*t-h→a≤2*((A*c^2)%a) ∧ 0<(A*c^2)%a) :
    padicValNat p (N.descFactorial K)=1 ∧
    padicValNat p (N.descFactorial K)≤padicValNat p (Nat.centralBinom N) := by
  have hrow : N-j=A*t*(a*t-h) := by omega
  rw [hrow] at hdiv
  obtain ⟨C,hC,hu⟩:=scaled_cofactor ha hA hh ht hp hAp hdiv hsize hmask
  apply upper_owner_payment hp hKN hpK hj
  · rw [hN,hC]
  · exact hu

theorem triple_slope_mask {t c : ℕ} (ht : 0<t) (hc : c∣3*t-1) :
    3 ≤ 2*((2*c^2)%3) ∧ 0<(2*c^2)%3 := by
  have hn : c%3 ≠ 0 := by
    intro hz
    have hd : 3∣3*t-1 := dvd_trans (Nat.dvd_of_mod_eq_zero hz) hc
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  have hb := Nat.mod_lt c (by decide : 0<3)
  have hm : (2*c^2)%3=2 := by
    have he : c%3=1 ∨ c%3=2 := by omega
    rcases he with he | he <;> norm_num [Nat.mul_mod,Nat.pow_mod,he]
  omega

theorem double_slope_mask {t c : ℕ} (ht : 0<t) (hc : c∣2*t-1) :
    2 ≤ 2*((1*c^2)%2) ∧ 0<(1*c^2)%2 := by
  have hn : c%2 ≠ 0 := by
    intro hz
    have hd : 2∣2*t-1 := dvd_trans (Nat.dvd_of_mod_eq_zero hz) hc
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  have hb := Nat.mod_lt c (by decide : 0<2)
  have he : c%2=1 := by omega
  norm_num [Nat.mul_mod,Nat.pow_mod,he]

def mixedPair : ℕ → ℕ×ℕ
  | 0 => (0,0)
  | k+1 => let z := mixedPair k
           (97*z.1+168*z.2+44,56*z.1+97*z.2+26)

theorem mixedPair_invariant (k : ℕ) :
    2*(mixedPair k).1^2+3*(mixedPair k).1+2*(mixedPair k).2
      =6*(mixedPair k).2^2 := by
  induction k with
  | zero => norm_num [mixedPair]
  | succ k ih =>
    simp only [mixedPair]
    nlinarith only [ih]

theorem mixedPair_growth (k : ℕ) : k≤(mixedPair k).1 := by
  induction k with
  | zero => simp [mixedPair]
  | succ k ih => simp only [mixedPair]; omega

theorem cofinal_mixed_shapes (T : ℕ) :
    ∃N t s:ℕ,T≤N ∧ 4≤N ∧ 0<t ∧ 0<s ∧
      N=t*(2*t-1) ∧ N=1+2*s*(3*s-1) := by
  let u := (mixedPair (T+1)).1
  let s := (mixedPair (T+1)).2
  let t := u+1
  let N := t*(2*t-1)
  have hu : T+1≤u := mixedPair_growth (T+1)
  have hs : 0<s := by dsimp [s]; simp only [mixedPair]; omega
  have ht : 0<t := by dsimp [t]; omega
  have htwo : 2*t-1+1=2*t := Nat.sub_add_cancel (by omega)
  have hthree : 3*s-1+1=3*s := Nat.sub_add_cancel (by omega)
  have hi : 2*u^2+3*u+2*s=6*s^2 := mixedPair_invariant (T+1)
  have hEq : N=1+2*s*(3*s-1) := by
    dsimp [N,t] at *
    nlinarith only [hi,congrArg ((u+1)*·) htwo,congrArg (2*s*·) hthree]
  refine ⟨N,t,s,?_,?_,ht,hs,rfl,hEq⟩
  · dsimp [N,t] at *
    nlinarith only [hu,htwo]
  · dsimp [N,t] at *
    nlinarith only [hu,htwo]

/-- For every width at least two, choose one unbounded endpoint with two
adjacent split rows. The conclusion pays each eligible prime's demand across
the whole block, including multiplicity. It does not assert full divisibility. -/
theorem cofinal_adjacent_rows (K T : ℕ) (hK : 2 ≤ K) :
    ∃ N t s : ℕ, T ≤ N ∧ K ≤ N ∧ 0 < t ∧ 0 < s ∧
      N = t * (2*t-1) ∧ N = 1 + 2*s*(3*s-1) ∧
      ∀ p : ℕ, p.Prime → K ≤ p → 2 < p →
        (p ∣ N ∨ p ∣ N-1) → 4*t < p^2 → 12*s < p^2 →
        padicValNat p (N.descFactorial K) = 1 ∧
        padicValNat p (N.descFactorial K) ≤ padicValNat p (Nat.centralBinom N) := by
  obtain ⟨N,t,s,hB,hN4,ht,hs,h0,h1⟩ := cofinal_mixed_shapes (max T K)
  have hTN : T ≤ N := (le_max_left _ _).trans hB
  have hKN : K ≤ N := (le_max_right _ _).trans hB
  refine ⟨N,t,s,hTN,hKN,ht,hs,h0,h1,?_⟩
  intro p hp hpK hp2 hd hb0 hb1
  rcases hd with hd | hd
  · apply scaled_owner_all_width (a:=2) (A:=1) (h:=1) (t:=t) (j:=0)
      (by decide) (by decide) (by decide) (by omega) hp
      (by simpa using hp.not_dvd_one) hKN hpK (by omega)
      (by simpa using h0) (by simpa using hd) (by nlinarith only [hb0])
    intro c hc
    exact double_slope_mask ht hc
  · apply scaled_owner_all_width (a:=3) (A:=2) (h:=1) (t:=s) (j:=1)
      (by decide) (by decide) (by decide) (by omega) hp
      (Nat.not_dvd_of_pos_of_lt (by decide) hp2) hKN hpK (by omega)
      h1 hd (by nlinarith only [hb1])
    intro c hc
    exact triple_slope_mask hs hc

/-- A small use case: the prime 89 is fully paid in a five-term block at
N=4005=45*89. This does not claim that the whole five-term product divides. -/
theorem example_five_term_prime_payment :
    padicValNat 89 ((4005 : ℕ).descFactorial 5) = 1 ∧
    padicValNat 89 ((4005 : ℕ).descFactorial 5) ≤
      padicValNat 89 (Nat.centralBinom 4005) := by
  apply scaled_owner_all_width (a:=2) (A:=1) (h:=1) (t:=45) (j:=0)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  intro c hc
  exact double_slope_mask (by decide) hc

#print axioms row_owner_unique
#print axioms product_valuation
#print axioms full_valuation_single_owner
#print axioms supply_of_second_carry
#print axioms positive_correction_upper
#print axioms integer_negative
#print axioms upper_owner_payment
#print axioms scaled_cofactor
#print axioms scaled_owner_all_width
#print axioms triple_slope_mask
#print axioms double_slope_mask
#print axioms mixedPair
#print axioms mixedPair_invariant
#print axioms mixedPair_growth
#print axioms cofinal_mixed_shapes
#print axioms cofinal_adjacent_rows
#print axioms example_five_term_prime_payment

end Contribution.Erdos396AdjacentRows
