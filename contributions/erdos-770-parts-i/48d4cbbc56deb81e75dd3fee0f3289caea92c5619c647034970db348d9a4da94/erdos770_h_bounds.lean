import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Order.RelClasses
import Mathlib.Tactic

/-!
# Erdős Problem 770: Textbook Properties of `h(n)`

Self-contained Lean 4 proofs of the two `[textbook]` results in
`FormalConjectures/ErdosProblems/770.lean`:
1. `h_eq_add_one`: for `n > 2`, `h n = n + 1 ↔ (n + 1).Prime`
   (matching `Erdos770.Nat.Prime.h_eq_add_one` definitionally).
2. `erdos_770_odd_h_unbounded`: `Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd))`
   (matching `Erdos770.erdos_770.variants.odd_h_unbounded` definitionally),
   proved via CRT, Dirichlet's theorem on primes in arithmetic progressions, and
   quadratic reciprocity.
-/

namespace Contribution.Erdos770

open Set ENat

/--
Let `h n` be the minimal number `m > 2` such that `2 ^ n - 1, ..., m.toNat ^ n - 1`
are collectively coprime. Matches `Erdos770.h` definitionally.
-/
noncomputable def h (n : ℕ) : ℕ∞ := sInf {m | 2 < m ∧
  ((Finset.Icc 2 m.toNat).image fun i => (i ^ n - 1)).gcd id = 1}

private lemma dvd_pow_sub_one_iff_zmod {r i n : ℕ} (hi : 1 ≤ i) :
    r ∣ i ^ n - 1 ↔ (i : ZMod r) ^ n = 1 := by
  have hpow : 1 ≤ i ^ n := Nat.one_le_pow n i hi
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_one, sub_eq_zero]

private lemma no_prime_dvd_of_all_roots {n r : ℕ} (hn : 1 ≤ n) (hr : r.Prime)
    (hlt : n + 1 < r) (hroots : ∀ i ∈ Finset.Icc 1 (n + 1), (i : ZMod r) ^ n = 1) :
    False := by
  have : Fact r.Prime := ⟨hr⟩
  let Z : Finset (ZMod r) := (Finset.Icc 1 (n + 1)).image (Nat.cast : ℕ → ZMod r)
  have hcard : Z.card = n + 1 := by
    rw [Finset.card_image_of_injOn]
    · rw [Nat.card_Icc]; omega
    · intro a ha b hb hab
      rw [Finset.coe_Icc, Set.mem_Icc] at ha hb
      have hval := congr_arg ZMod.val hab
      rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (lt_of_le_of_lt ha.2 hlt),
        Nat.mod_eq_of_lt (lt_of_le_of_lt hb.2 hlt)] at hval
      exact hval
  let P : Polynomial (ZMod r) := Polynomial.X ^ n - Polynomial.C 1
  have hP_ne : P ≠ 0 := (Polynomial.monic_X_pow_sub_C 1 (by omega)).ne_zero
  have hdeg : P.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hsub : Z.val ⊆ P.roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_image] at hx
    rcases hx with ⟨i, hi, rfl⟩
    rw [Polynomial.mem_roots hP_ne, Polynomial.IsRoot, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, hroots i hi, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hcard, hdeg] at hle
  omega

private lemma not_dvd_self_pow_sub_one {r n : ℕ} (hr : r.Prime) (hn : 1 ≤ n)
    (hdvd : r ∣ r ^ n - 1) : False := by
  have hpow_dvd : r ∣ r ^ n := dvd_pow_self r (by omega)
  have hle : 1 ≤ r ^ n := Nat.one_le_pow n r hr.pos
  have hone : r ∣ r ^ n - (r ^ n - 1) := Nat.dvd_sub hpow_dvd hdvd
  rw [Nat.sub_sub_self hle] at hone
  exact hr.not_dvd_one hone

private lemma gcd_Icc_add_one_eq_one {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.Icc 2 (n + 1)).image fun i => i ^ n - 1).gcd id = 1 := by
  set g := ((Finset.Icc 2 (n + 1)).image fun i => i ^ n - 1).gcd id
  by_contra hg1
  let r := g.minFac
  have hr : r.Prime := Nat.minFac_prime hg1
  have hr_dvd : r ∣ g := Nat.minFac_dvd g
  have hdvd_all : ∀ i ∈ Finset.Icc 2 (n + 1), r ∣ i ^ n - 1 := by
    intro i hi
    exact dvd_trans hr_dvd ((Finset.dvd_gcd_iff.mp dvd_rfl) (i ^ n - 1)
      (Finset.mem_image_of_mem _ hi))
  have hr_gt : n + 1 < r := by
    by_contra hle
    have hle' : r ≤ n + 1 := by omega
    exact not_dvd_self_pow_sub_one hr hn
      (hdvd_all r (Finset.mem_Icc.mpr ⟨hr.two_le, hle'⟩))
  have hroots : ∀ i ∈ Finset.Icc 1 (n + 1), (i : ZMod r) ^ n = 1 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rcases eq_or_lt_of_le hi.1 with rfl | hi2
    · simp
    · exact (dvd_pow_sub_one_iff_zmod hi.1).mp
        (hdvd_all i (Finset.mem_Icc.mpr ⟨hi2, hi.2⟩))
  exact no_prime_dvd_of_all_roots hn hr hr_gt hroots

/--
For `n > 2`, `h n = n + 1` if and only if `n + 1` is prime.
Matches `Erdos770.Nat.Prime.h_eq_add_one` definitionally.
-/
theorem h_eq_add_one {n : ℕ} (hn : 2 < n) : h n = n + 1 ↔ (n + 1).Prime := by
  constructor
  · intro heq
    by_contra hnp
    let a := (n + 1).minFac
    let b := (n + 1) / a
    have ha_prime : a.Prime := Nat.minFac_prime (by omega)
    have ha_dvd : a ∣ n + 1 := Nat.minFac_dvd (n + 1)
    have hab : a * b = n + 1 := Nat.mul_div_cancel' ha_dvd
    have ha_lt : a < n + 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) ha_dvd)
      (fun h => hnp (h ▸ ha_prime))
    have hb_ge2 : 2 ≤ b := by
      by_contra hb1
      have hmul : a * b ≤ a := by
        calc a * b ≤ a * 1 := Nat.mul_le_mul_left a (by omega)
          _ = a := mul_one a
      omega
    have hb_lt : b < n + 1 := by
      calc b < 2 * b := by omega
        _ ≤ a * b := Nat.mul_le_mul_right b ha_prime.two_le
        _ = n + 1 := hab
    have hb_le : b ≤ n := Nat.le_of_lt_succ hb_lt
    have hgcd_n : ((Finset.Icc 2 n).image fun i => i ^ n - 1).gcd id = 1 := by
      set g := ((Finset.Icc 2 n).image fun i => i ^ n - 1).gcd id
      by_contra hg1
      let r := g.minFac
      have hr : r.Prime := Nat.minFac_prime hg1
      have hr_dvd : r ∣ g := Nat.minFac_dvd g
      have hdvd_all : ∀ i ∈ Finset.Icc 2 n, r ∣ i ^ n - 1 := by
        intro i hi
        exact dvd_trans hr_dvd ((Finset.dvd_gcd_iff.mp dvd_rfl) (i ^ n - 1)
          (Finset.mem_image_of_mem _ hi))
      have hr_gt_n : n < r := by
        by_contra hle
        exact not_dvd_self_pow_sub_one hr (by omega)
          (hdvd_all r (Finset.mem_Icc.mpr ⟨hr.two_le, by omega⟩))
      have hr_ne : r ≠ n + 1 := fun h => hnp (h ▸ hr)
      have hr_gt : n + 1 < r := by omega
      have hroots : ∀ i ∈ Finset.Icc 1 (n + 1), (i : ZMod r) ^ n = 1 := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        rcases eq_or_lt_of_le hi.1 with rfl | hi2
        · simp
        · rcases lt_or_eq_of_le hi.2 with hin | rfl
          · exact (dvd_pow_sub_one_iff_zmod hi.1).mp
              (hdvd_all i (Finset.mem_Icc.mpr ⟨hi2, by omega⟩))
          · have ha_le : a ≤ n := Nat.le_of_lt_succ ha_lt
            have ha_root : (a : ZMod r) ^ n = 1 :=
              (dvd_pow_sub_one_iff_zmod ha_prime.pos).mp
                (hdvd_all a (Finset.mem_Icc.mpr ⟨ha_prime.two_le, ha_le⟩))
            have hb_root : (b : ZMod r) ^ n = 1 :=
              (dvd_pow_sub_one_iff_zmod (Nat.le_trans (by decide : 1 ≤ 2) hb_ge2)).mp
                (hdvd_all b (Finset.mem_Icc.mpr ⟨hb_ge2, hb_le⟩))
            calc ((n + 1 : ℕ) : ZMod r) ^ n
                = ((a * b : ℕ) : ZMod r) ^ n := by rw [hab]
              _ = (a : ZMod r) ^ n * (b : ZMod r) ^ n := by push_cast; rw [mul_pow]
              _ = 1 := by rw [ha_root, hb_root, one_mul]
      exact no_prime_dvd_of_all_roots (by omega) hr hr_gt hroots
    have hle_n : h n ≤ (n : ℕ∞) := by
      refine sInf_le ⟨by exact_mod_cast hn, ?_⟩
      simpa using hgcd_n
    rw [heq] at hle_n
    have hcontra : n + 1 ≤ n := by exact_mod_cast hle_n
    omega
  · intro hp
    have hle_succ : h n ≤ (n : ℕ∞) + 1 := by
      refine sInf_le ⟨by exact_mod_cast (by omega : 2 < n + 1), ?_⟩
      have hto : ((n : ℕ∞) + 1).toNat = n + 1 := by
        rw [show (n : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞) by norm_cast, ENat.toNat_natCast]
      rw [hto]
      exact gcd_Icc_add_one_eq_one (by omega)
    have hge_succ : (n : ℕ∞) + 1 ≤ h n := by
      refine le_sInf fun m hm => ?_
      cases m with
      | top => exact le_top
      | coe k =>
        rcases hm with ⟨hk2, hgcd⟩
        have hk2' : 2 < k := by exact_mod_cast hk2
        rw [ENat.toNat_natCast] at hgcd
        by_contra hlt
        have hk_le : k ≤ n := by
          have hlt' : (k : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
            simpa [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hlt
          have : k < n + 1 := by exact_mod_cast hlt'
          omega
        have : Fact (n + 1).Prime := ⟨hp⟩
        have hdiv : ∀ i ∈ Finset.Icc 2 k, (n + 1) ∣ i ^ n - 1 := by
          intro i hi
          rw [Finset.mem_Icc] at hi
          have hne0 : (i : ZMod (n + 1)) ≠ 0 := by
            intro h0
            rw [ZMod.natCast_eq_zero_iff] at h0
            have hle_i : n + 1 ≤ i := Nat.le_of_dvd (by omega) h0
            omega
          have hfermat : (i : ZMod (n + 1)) ^ n = 1 := by
            have hcard : Fintype.card (ZMod (n + 1)) - 1 = n := by
              rw [ZMod.card]; omega
            simpa [hcard] using ZMod.pow_card_sub_one_eq_one hne0
          exact (dvd_pow_sub_one_iff_zmod (by omega : 1 ≤ i)).mpr hfermat
        have hdvd_gcd : n + 1 ∣ ((Finset.Icc 2 k).image fun i => i ^ n - 1).gcd id := by
          rw [Finset.dvd_gcd_iff]
          intro y hy
          rw [Finset.mem_image] at hy
          rcases hy with ⟨i, hi, rfl⟩
          exact hdiv i hi
        rw [hgcd] at hdvd_gcd
        exact hp.not_dvd_one hdvd_gcd
    exact le_antisymm hle_succ hge_succ

/--
For odd `n`, the values of `h n` form an unbounded set.
Matches `Erdos770.erdos_770.variants.odd_h_unbounded` definitionally.
-/
theorem erdos_770_odd_h_unbounded : Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd)) := by
  intro B
  let K := max B 2
  let ps : List ℕ := (List.range (K + 1)).filter fun q => q.Prime ∧ q ≠ 2
  let ms : List ℕ := 8 :: ps
  have hps_spec : ∀ q ∈ ps, q.Prime ∧ q ≠ 2 ∧ q ≤ K := by
    intro q hq
    simp only [ps, List.mem_filter, List.mem_range, decide_eq_true_eq] at hq
    exact ⟨hq.2.1, hq.2.2, by omega⟩
  have hpair : ms.Pairwise Nat.Coprime := by
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro q hq
      have hqs := hps_spec q hq
      have hq_odd : Odd q := hqs.1.odd_of_ne_two hqs.2.1
      have h2q : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by
        rcases hq_odd with ⟨t, ht⟩; omega
      simpa [show (2 ^ 3 : ℕ) = 8 by decide] using h2q.pow_left 3
    · refine (List.nodup_range.filter _).pairwise_of_forall_ne fun q₁ h₁ q₂ h₂ hne => ?_
      exact (Nat.coprime_primes (hps_spec q₁ h₁).1 (hps_spec q₂ h₂).1).mpr hne
  let a : ℕ → ℕ := fun q =>
    if q = 8 then 7
    else if hq : q.Prime ∧ q % 4 = 3 then
      (by
        have : Fact q.Prime := ⟨hq.1⟩
        exact (FiniteField.exists_nonsquare (F := ZMod q)
          (by rw [ZMod.ringChar_zmod_n]; omega)).choose.val)
    else 1
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfList a id ms hpair
  have hprod_ne : ms.prod ≠ 0 := by
    have hlist_nz : ∀ l : List ℕ, (∀ m ∈ l, m ≠ 0) → l.prod ≠ 0 := by
      intro l hl
      induction l with
      | nil => simp
      | cons hd tl ih =>
        rw [List.prod_cons]
        exact mul_ne_zero (hl hd (by simp)) (ih fun m hm => hl m (by simp [hm]))
    refine hlist_nz ms fun m hm => ?_
    rcases List.mem_cons.mp hm with rfl | hmq
    · decide
    · exact (hps_spec m hmq).1.ne_zero
  have hcop_x : x.Coprime ms.prod := by
    rw [Nat.coprime_list_prod_right_iff]
    intro m hm
    have hxm : x ≡ a m [MOD m] := hx m hm
    have hcop_a : (a m).Coprime m := by
      rcases List.mem_cons.mp hm with rfl | hmq
      · simp [a]; decide
      · have hqs := hps_spec m hmq
        have hm8 : m ≠ 8 := by
          intro heq; subst heq; exact (by decide : ¬ Nat.Prime 8) hqs.1
        dsimp only [a]
        rw [if_neg hm8]
        split_ifs with h3
        · have : Fact m.Prime := ⟨h3.1⟩
          have hr_ns := (FiniteField.exists_nonsquare (F := ZMod m)
            (by rw [ZMod.ringChar_zmod_n]; omega)).choose_spec
          set r := (FiniteField.exists_nonsquare (F := ZMod m)
            (by rw [ZMod.ringChar_zmod_n]; omega)).choose
          have hr0 : r ≠ 0 := fun h0 => hr_ns ⟨0, by simp [h0]⟩
          have hr_val_pos : 0 < r.val := by
            by_contra hle
            have hv0 : r.val = 0 := by omega
            exact hr0 (by rw [← ZMod.natCast_zmod_val r, hv0, Nat.cast_zero])
          have hr_lt : r.val < m := ZMod.val_lt r
          exact (h3.1.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hr_val_pos hr_lt)).symm
        · exact Nat.coprime_one_left m
    exact hxm.gcd_eq.trans hcop_a
  obtain ⟨p, hp_gt, hp_prime, hp_mod_prod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max (2 * K + 1) 7) hprod_ne hcop_x
  have h8_dvd : 8 ∣ ms.prod := List.dvd_prod (by simp [ms])
  have hp8 : p % 8 = 7 := by
    have hpx8 : p ≡ x [MOD 8] := hp_mod_prod.of_dvd h8_dvd
    have hx8 : x ≡ 7 [MOD 8] := by simpa [a] using hx 8 (by simp [ms])
    have hmod : p % 8 = 7 % 8 := hpx8.trans hx8
    simpa using hmod
  have hp4 : p % 4 = 3 := by omega
  have hp2 : p ≠ 2 := by omega
  let n := (p - 1) / 2
  have hn_odd : Odd n := by
    refine ⟨(p - 3) / 4, ?_⟩
    omega
  have hn_div : p / 2 = n := by omega
  have hn_gt2 : 2 < n := by omega
  have : Fact p.Prime := ⟨hp_prime⟩
  have hleg : ∀ i : ℕ, 1 ≤ i → i ≤ K → legendreSym p i = 1 := by
    intro i hi1 hiK
    induction i using Nat.strong_induction_on with
    | h i ih =>
      rcases eq_or_lt_of_le hi1 with rfl | hi2
      · simp [legendreSym.at_one]
      · let q := i.minFac
        have hq_prime : q.Prime := Nat.minFac_prime (by omega)
        have hq_dvd : q ∣ i := Nat.minFac_dvd i
        have hiq_eq : q * (i / q) = i := Nat.mul_div_cancel' hq_dvd
        have hlt_i : i / q < i := Nat.div_lt_self (by omega) hq_prime.one_lt
        have hiq_pos : 1 ≤ i / q := Nat.div_pos (Nat.le_of_dvd (by omega) hq_dvd) hq_prime.pos
        have hih : legendreSym p (i / q) = 1 :=
          ih (i / q) hlt_i hiq_pos (le_trans hlt_i.le hiK)
        have hleg_q : legendreSym p q = 1 := by
          by_cases hq2 : q = 2
          · rw [hq2]
            push_cast
            rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
            have hp2' : p % 2 ≠ 0 := by omega
            simp [hp2', hp8]
          · have hq_ps : q ∈ ps := by
              simp only [ps, List.mem_filter, List.mem_range, decide_eq_true_eq]
              have hq_le_i : q ≤ i := Nat.le_of_dvd (by omega) hq_dvd
              exact ⟨by omega, hq_prime, hq2⟩
            have hq_dvd_prod : q ∣ ms.prod := List.dvd_prod (List.mem_cons_of_mem 8 hq_ps)
            have hpq_mod : p ≡ a q [MOD q] := (hp_mod_prod.of_dvd hq_dvd_prod).trans
              (hx q (List.mem_cons_of_mem 8 hq_ps))
            have hq8 : q ≠ 8 := fun h => (by decide : ¬ Nat.Prime 8) (h ▸ hq_prime)
            have : Fact q.Prime := ⟨hq_prime⟩
            have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
              have := hq_prime.eq_two_or_odd; omega
            rcases hq4 with hq1 | hq3
            · rw [legendreSym.quadratic_reciprocity_one_mod_four hq1 hp2]
              have haq : a q = 1 := by simp [a, hq8, hq1]
              rw [haq] at hpq_mod
              have hpq_int : ((p : ℤ) % q) = 1 := by
                have hmod : p % q = 1 % q := hpq_mod
                have h1q : 1 % q = 1 := Nat.mod_eq_of_lt hq_prime.one_lt
                rw [h1q] at hmod
                exact_mod_cast hmod
              rw [legendreSym.mod, hpq_int, legendreSym.at_one]
            · rw [legendreSym.quadratic_reciprocity_three_mod_four hq3 hp4]
              have haq : a q = (FiniteField.exists_nonsquare (F := ZMod q)
                  (by rw [ZMod.ringChar_zmod_n]; omega)).choose.val := by
                simp [a, hq8, hq_prime, hq3]
              set r := (FiniteField.exists_nonsquare (F := ZMod q)
                (by rw [ZMod.ringChar_zmod_n]; omega)).choose
              have hr_ns : ¬ IsSquare r := (FiniteField.exists_nonsquare (F := ZMod q)
                (by rw [ZMod.ringChar_zmod_n]; omega)).choose_spec
              have hpr : (p : ZMod q) = r := by
                rw [← ZMod.natCast_mod, show p % q = r.val % q by rw [← haq]; exact hpq_mod,
                  ZMod.natCast_mod, ZMod.natCast_zmod_val]
              have hneg : legendreSym q p = -1 := by
                rw [legendreSym.eq_neg_one_iff', hpr]
                exact hr_ns
              rw [hneg]
              decide
        calc legendreSym p i = legendreSym p ((q * (i / q) : ℕ) : ℤ) := by rw [hiq_eq]
          _ = legendreSym p q * legendreSym p (i / q) := by
            rw [Nat.cast_mul]; exact legendreSym.mul p (q : ℤ) ((i / q : ℕ) : ℤ)
          _ = 1 := by rw [hleg_q, hih, one_mul]
  have hge_K1 : ((K + 1 : ℕ) : ℕ∞) ≤ h n := by
    refine le_sInf fun m hm => ?_
    cases m with
    | top => exact le_top
    | coe t =>
      rcases hm with ⟨ht2, hgcd⟩
      rw [ENat.toNat_natCast] at hgcd
      by_contra hlt
      have ht_le : t ≤ K := by
        have hlt' : (t : ℕ∞) < ((K + 1 : ℕ) : ℕ∞) := lt_of_not_ge hlt
        have : t < K + 1 := by exact_mod_cast hlt'
        omega
      have hp_dvd : p ∣ 1 := by
        rw [← hgcd, Finset.dvd_gcd_iff]
        intro y hy
        rw [Finset.mem_image] at hy
        rcases hy with ⟨i, hi, rfl⟩
        rw [Finset.mem_Icc] at hi
        have hl := hleg i (by omega) (le_trans hi.2 ht_le)
        have hpow := legendreSym.eq_pow p (i : ℤ)
        rw [hl, hn_div] at hpow
        have hroot : (i : ZMod p) ^ n = 1 := by simpa using hpow.symm
        exact (dvd_pow_sub_one_iff_zmod (by omega : 1 ≤ i)).mpr hroot
      exact hp_prime.not_dvd_one hp_dvd
  have hle_succ : h n ≤ ((n + 1 : ℕ) : ℕ∞) := by
    refine sInf_le ⟨by exact_mod_cast (by omega : 2 < n + 1), ?_⟩
    rw [ENat.toNat_natCast]
    exact gcd_Icc_add_one_eq_one (by omega)
  have hne_top : h n ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top (n + 1)) hle_succ
  have hto_ge : K + 1 ≤ (h n).toNat := by
    have : ((K + 1 : ℕ) : ℕ∞) ≤ ((h n).toNat : ℕ∞) := by
      rwa [ENat.natCast_toNat hne_top]
    exact_mod_cast this
  refine ⟨(h n).toNat, ⟨h n, ⟨n, hn_odd, rfl⟩, rfl⟩, ?_⟩
  omega

end Contribution.Erdos770
