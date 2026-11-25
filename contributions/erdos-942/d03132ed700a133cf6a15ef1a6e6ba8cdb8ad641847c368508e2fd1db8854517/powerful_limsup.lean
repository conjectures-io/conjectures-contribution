/-
Copyright 2026 The Contribution Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 942: Unbounded Powerful Numbers Between Consecutive Squares

Complete self-contained Lean 4 proof of `Erdos942.erdos_942.variants.limsup`:
let `h(n)` count the powerful integers in `[n^2, (n + 1)^2)`. Then
`limsup_{n → ∞} h(n) = ∞`.

Given any `K ≥ 1` and threshold `N₀`, we take `2K` distinct primes `p_0, ..., p_{2K-1}`
and apply Dirichlet simultaneous approximation to `(N / √(p_j^3))_{j < 2K}` (where
`N = N₀ + 2`), finding an integer multiple `d ≥ N₀ + 2` and integers `x_j ≥ 1` with
`|d - x_j √(p_j^3)| < 1`. Squaring places `p_j^3 * x_j^2` inside `[(d - 1)^2, (d + 1)^2)`,
and comparing `padicValNat p_j` parity shows these `2K` powerful numbers are pairwise
distinct, forcing `h(d - 1) ≥ K` or `h(d) ≥ K`.
-/

namespace Contribution.Erdos942

open Nat Filter

/--
A natural number `n` is `k`-full if `p ^ k ∣ n` for every prime factor `p` of `n`.
Matches `Full` in `FormalConjecturesForMathlib` definitionally.
-/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/--
A natural number `n` is powerful (`2`-full) if `p ^ 2 ∣ n` for every prime factor `p` of `n`.
Matches `Powerful` in `FormalConjecturesForMathlib` definitionally.
-/
abbrev Powerful : ℕ → Prop := Full 2

instance Powerful.decide : ∀ n, Decidable (Powerful n) := by
  intro n
  dsimp [Powerful, Full]
  apply Finset.decidableDforallFinset

/--
Let `h(n)` count the number of powerful integers in `[n ^ 2, (n + 1) ^ 2)`.
Matches `Erdos942.erdos_942.h` definitionally.
-/
def erdos_942_h (n : ℕ) : ℕ := ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful).card

private lemma powerful_cube_mul_sq {p : ℕ} (hp : p.Prime) (x : ℕ) : Powerful (p ^ 3 * x ^ 2) := by
  intro q hq
  have hq_info := Nat.mem_primeFactors.mp hq
  rcases hq_info.1.dvd_mul.mp hq_info.2.1 with hqp | hqx
  · have hq_dvd_p : q ∣ p := hq_info.1.dvd_of_dvd_pow hqp
    have hqp_eq : q = p := ((Nat.dvd_prime hp).mp hq_dvd_p).resolve_left hq_info.1.ne_one
    subst hqp_eq
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow q (by decide)) _
  · have hq_dvd_x : q ∣ x := hq_info.1.dvd_of_dvd_pow hqx
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hq_dvd_x 2) _

private lemma cube_mul_sq_ne {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hx : x ≠ 0) (hy : y ≠ 0) : p ^ 3 * x ^ 2 ≠ q ^ 3 * y ^ 2 := by
  intro heq
  have : Fact p.Prime := ⟨hp⟩
  have hval := congrArg (padicValNat p) heq
  have h_not_dvd : ¬ p ∣ q := fun hd =>
    hpq (((Nat.dvd_prime hq).mp hd).resolve_left hp.ne_one)
  have hvpq : padicValNat p q = 0 := padicValNat.eq_zero_of_not_dvd h_not_dvd
  have hp3 : p ^ 3 ≠ 0 := pow_ne_zero 3 hp.ne_zero
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq.ne_zero
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  rw [padicValNat.mul hp3 hx2, padicValNat.mul hq3 hy2,
    padicValNat.pow, padicValNat.pow, padicValNat.pow, padicValNat.pow,
    padicValNat.self hp.one_lt, hvpq] at hval
  omega

private lemma abs_sub_lt_one_of_nat_floor_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ⌊u⌋₊ = ⌊v⌋₊) : |u - v| < 1 := by
  have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
  have h2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  have h3 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv
  have h4 : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
  rw [← h] at h3 h4
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private lemma exists_large_h (K N₀ : ℕ) : ∃ m ≥ N₀, K ≤ erdos_942_h m := by
  by_cases hK : K = 0
  · subst hK
    exact ⟨N₀, le_rfl, Nat.zero_le _⟩
  · have hK_pos : 1 ≤ K := Nat.pos_of_ne_zero hK
    let M : ℕ := 2 * K
    have hM_pos : 1 ≤ M := by omega
    let p : Fin M → ℕ := fun j => Nat.nth Nat.Prime j.1
    have hp_prime : ∀ j : Fin M, (p j).Prime := fun j =>
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j.1
    have hp_strict : StrictMono p := fun i j hij =>
      Nat.nth_strictMono Nat.infinite_setOfPred_prime hij
    let j_last : Fin M := ⟨M - 1, Nat.sub_lt hM_pos Nat.zero_lt_one⟩
    let P : ℕ := p j_last
    have hP_pos : 1 ≤ P := (hp_prime j_last).pos
    have hp_le_P : ∀ j : Fin M, p j ≤ P := fun j =>
      hp_strict.monotone (Fin.mk_le_mk.mpr (Nat.le_pred_of_lt j.isLt))
    let Q : ℕ := P ^ 2 + 1
    have hQ_pos : 0 < Q := Nat.succ_pos _
    let N : ℕ := N₀ + 2
    let α : Fin M → ℝ := fun j => Real.sqrt ((p j : ℝ) ^ 3)
    have hα_pos : ∀ j : Fin M, 0 < α j := fun j => by
      have hp0 : (0 : ℝ) < p j := Nat.cast_pos.mpr (hp_prime j).pos
      exact Real.sqrt_pos.mpr (pow_pos hp0 3)
    have hα_le : ∀ j : Fin M, α j ≤ (P : ℝ) ^ 2 := fun j => by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      have h1 : p j ≤ P := hp_le_P j
      have hnat : p j ^ 3 ≤ P ^ 4 := by
        calc
          p j ^ 3 ≤ P ^ 3 := Nat.pow_le_pow_left h1 3
          _ = P ^ 3 * 1 := (Nat.mul_one _).symm
          _ ≤ P ^ 3 * P := Nat.mul_le_mul_left _ hP_pos
          _ = P ^ 4 := by ring
      have hr : (p j : ℝ) ^ 3 ≤ (P : ℝ) ^ 4 := by exact_mod_cast hnat
      linarith [show ((P : ℝ) ^ 2) ^ 2 = (P : ℝ) ^ 4 by ring]
    let f : Fin (Q ^ M + 1) → (Fin M → Fin Q) := fun t j =>
      ⟨⌊(Q : ℝ) * Int.fract ((N * t.1 : ℝ) / α j)⌋₊, by
        have hfr0 : 0 ≤ Int.fract ((N * t.1 : ℝ) / α j) := Int.fract_nonneg _
        have hfr1 : Int.fract ((N * t.1 : ℝ) / α j) < 1 := Int.fract_lt_one _
        have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
        exact Nat.floor_lt (by positivity) |>.mpr (by nlinarith)⟩
    have hcard : Fintype.card (Fin M → Fin Q) < Fintype.card (Fin (Q ^ M + 1)) := by
      simp [Fintype.card_fin]
    obtain ⟨t1, t2, hne, heq_f⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
    obtain ⟨a, b, hab_lt, hab_f⟩ : ∃ a b : Fin (Q ^ M + 1), a.1 < b.1 ∧ f a = f b := by
      rcases lt_or_gt_of_ne hne with h12 | h21
      · exact ⟨t1, t2, h12, heq_f⟩
      · exact ⟨t2, t1, h21, heq_f.symm⟩
    let d : ℕ := N * (b.1 - a.1)
    have hd_ge_N : N ≤ d := Nat.le_mul_of_pos_right N (Nat.sub_pos_of_lt hab_lt)
    have hd_ge2 : 2 ≤ d := by omega
    have hx_exists : ∀ j : Fin M, ∃ x : ℕ, 1 ≤ x ∧
        ((d - 1) ^ 2 < p j ^ 3 * x ^ 2 ∧ p j ^ 3 * x ^ 2 < (d + 1) ^ 2) := by
      intro j
      let u1 : ℝ := (N * a.1 : ℝ) / α j
      let u2 : ℝ := (N * b.1 : ℝ) / α j
      have hf_eq : ⌊(Q : ℝ) * Int.fract u1⌋₊ = ⌊(Q : ℝ) * Int.fract u2⌋₊ := by
        have := congrFun hab_f j
        simpa [f, Fin.ext_iff, u1, u2] using this
      have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ_pos
      have hQ_fract : |(Q : ℝ) * (Int.fract u2 - Int.fract u1)| < 1 := by
        have hlt := abs_sub_lt_one_of_nat_floor_eq
          (mul_nonneg hQr.le (Int.fract_nonneg u2))
          (mul_nonneg hQr.le (Int.fract_nonneg u1)) hf_eq.symm
        simpa [mul_sub] using hlt
      let z : ℤ := ⌊u2⌋ - ⌊u1⌋
      have hu_diff : (d : ℝ) / α j = u2 - u1 := by
        have hsub : (d : ℝ) = (N : ℝ) * ((b.1 : ℝ) - (a.1 : ℝ)) := by
          dsimp [d]
          push_cast [hab_lt.le]
          ring
        rw [hsub]
        dsimp [u1, u2]
        ring
      have hsub_fract : (d : ℝ) / α j - (z : ℝ) = Int.fract u2 - Int.fract u1 := by
        rw [hu_diff]
        have hf1 := Int.self_sub_fract u1
        have hf2 := Int.self_sub_fract u2
        push_cast [z]
        linarith
      have hQ_eq : (Q : ℝ) * (Int.fract u2 - Int.fract u1) =
          (Q : ℝ) * ((d : ℝ) / α j - (z : ℝ)) := by rw [hsub_fract]
      rw [hQ_eq, abs_mul, abs_of_nonneg hQr.le] at hQ_fract
      have hαp : 0 < α j := hα_pos j
      have hmul_α : |(d : ℝ) - (z : ℝ) * α j| < α j / (Q : ℝ) := by
        have hdiv : |(d : ℝ) / α j - (z : ℝ)| < 1 / (Q : ℝ) := (lt_div_iff₀' hQr).mpr hQ_fract
        have hid : (d : ℝ) - (z : ℝ) * α j = α j * ((d : ℝ) / α j - (z : ℝ)) := by
          field_simp [hαp.ne']
        rw [hid, abs_mul, abs_of_nonneg hαp.le]
        calc
          α j * |(d : ℝ) / α j - (z : ℝ)| < α j * (1 / (Q : ℝ)) :=
            mul_lt_mul_of_pos_left hdiv hαp
          _ = α j / (Q : ℝ) := by ring
      have h_lt1 : |(d : ℝ) - (z : ℝ) * α j| < 1 := by
        have hPQ : α j ≤ (Q : ℝ) - 1 := by
          have : (Q : ℝ) = (P : ℝ) ^ 2 + 1 := by push_cast [Q]; ring
          linarith [hα_le j]
        have hltQ : α j < (Q : ℝ) := by linarith
        exact hmul_α.trans ((div_lt_one hQr).mpr hltQ)
      have h_bounds := abs_lt.mp h_lt1
      have hz_pos : (0 : ℝ) < (z : ℝ) := by
        have h1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_ge2
          linarith
        nlinarith [h_bounds.2, hαp]
      have hz_int_pos : 1 ≤ z := by
        have hz_gt : (0 : ℤ) < z := by exact_mod_cast hz_pos
        omega
      let x : ℕ := z.toNat
      have hx_pos : 1 ≤ x := by omega
      have hx_cast : (x : ℝ) = (z : ℝ) := by
        have := Int.toNat_of_nonneg (by omega : 0 ≤ z)
        exact_mod_cast this
      have h_lo_r : ((d - 1 : ℕ) : ℝ) < (x : ℝ) * α j := by
        have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          simp
        rw [this, hx_cast]
        linarith [h_bounds.2]
      have h_hi_r : (x : ℝ) * α j < ((d + 1 : ℕ) : ℝ) := by
        have : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
        rw [this, hx_cast]
        linarith [h_bounds.1]
      have hsq_eq : ((x : ℝ) * α j) ^ 2 = ((p j ^ 3 * x ^ 2 : ℕ) : ℝ) := by
        have hp0 : (0 : ℝ) ≤ (p j : ℝ) ^ 3 := by positivity
        rw [mul_pow]
        dsimp [α]
        rw [Real.sq_sqrt hp0]
        push_cast
        ring
      have h_lo_sq : (((d - 1) ^ 2 : ℕ) : ℝ) < ((p j ^ 3 * x ^ 2 : ℕ) : ℝ) := by
        rw [← hsq_eq]
        push_cast only [Nat.cast_pow]
        exact pow_lt_pow_left₀ h_lo_r (by positivity) (by decide)
      have h_hi_sq : ((p j ^ 3 * x ^ 2 : ℕ) : ℝ) < (((d + 1) ^ 2 : ℕ) : ℝ) := by
        rw [← hsq_eq]
        push_cast only [Nat.cast_pow]
        exact pow_lt_pow_left₀ h_hi_r (by positivity) (by decide)
      exact ⟨x, hx_pos, Nat.cast_lt.mp h_lo_sq, Nat.cast_lt.mp h_hi_sq⟩
    choose x hx_pos hx_lo hx_hi using hx_exists
    let g : Fin M → ℕ := fun j => p j ^ 3 * x j ^ 2
    have hg_inj : Function.Injective g := by
      intro i j hij
      by_contra hne_ij
      exact cube_mul_sq_ne (hp_prime i) (hp_prime j) (hp_strict.injective.ne hne_ij)
        (by have := hx_pos i; omega) (by have := hx_pos j; omega) hij
    let S : Finset ℕ := Finset.univ.image g
    have hS_card : S.card = M := by
      rw [Finset.card_image_of_injective _ hg_inj, Finset.card_fin]
    let A := (Finset.Ico ((d - 1) ^ 2) (d ^ 2)).filter Powerful
    let B := (Finset.Ico (d ^ 2) ((d + 1) ^ 2)).filter Powerful
    have hS_sub : S ⊆ A ∪ B := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨j, _, rfl⟩
      have hpow : Powerful (g j) := powerful_cube_mul_sq (hp_prime j) (x j)
      by_cases hlt : g j < d ^ 2
      · exact Finset.mem_union_left B (Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨(hx_lo j).le, hlt⟩, hpow⟩)
      · exact Finset.mem_union_right A (Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, hx_hi j⟩, hpow⟩)
    have hsum_card : M ≤ erdos_942_h (d - 1) + erdos_942_h d := by
      calc
        M = S.card := hS_card.symm
        _ ≤ (A ∪ B).card := Finset.card_le_card hS_sub
        _ ≤ A.card + B.card := Finset.card_union_le A B
        _ = erdos_942_h (d - 1) + erdos_942_h d := by
          have hd1 : d - 1 + 1 = d := by omega
          simp only [erdos_942_h, A, B, hd1]
    by_cases hA : K ≤ erdos_942_h (d - 1)
    · exact ⟨d - 1, by omega, hA⟩
    · exact ⟨d, by omega, by omega⟩

/--
`limsup_{n → ∞} erdos_942_h(n) = ∞` in `ℕ∞`.
Discharges `Erdos942.erdos_942.variants.limsup`.
-/
theorem erdos_942_limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942_h)) = ⊤ := by
  set L : ℕ∞ := atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942_h))
  have hbound : Filter.IsBoundedUnder (· ≤ ·) atTop (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942_h)) :=
    ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
  have hle_all : ∀ K : ℕ, (K : ℕ∞) ≤ L := by
    intro K
    refine Filter.le_limsup_of_frequently_le ?_ hbound
    rw [Filter.frequently_atTop]
    intro N₀
    obtain ⟨m, hm_ge, hm_card⟩ := exists_large_h K N₀
    exact ⟨m, hm_ge, Nat.cast_le.mpr hm_card⟩
  cases hL : L with
  | top => rfl
  | coe K =>
    have hsucc : ((K + 1 : ℕ) : ℕ∞) ≤ (K : ℕ∞) := hL ▸ hle_all (K + 1)
    have hnat : K + 1 ≤ K := Nat.cast_le.mp hsucc
    omega

end Contribution.Erdos942
