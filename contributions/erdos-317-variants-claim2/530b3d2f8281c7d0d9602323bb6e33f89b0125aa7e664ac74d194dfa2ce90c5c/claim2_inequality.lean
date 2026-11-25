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

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 317: Exact LCM Lower Bound (`claim2_inequality`)

Complete self-contained Lean 4 proof of `Erdos317.claim2_inequality`:
for every `n ≥ 1` (hence eventually in `Filter.atTop`) and every `δ : Fin n → ℚ`
taking values in `{-1, 0, 1}`, if `lhs = |∑ k, δ k / (k + 1)| ≠ 0`, then
`lhs ≥ 1 / (Finset.Icc 1 n).lcm id`.

Multiplying the sum by `L = (Finset.Icc 1 n).lcm id` clears all denominators
`k + 1 ∣ L`, yielding a nonzero integer `M` with `|M| ≥ 1` and `(L : ℚ) * lhs = |M|`.
-/

namespace Contribution.Erdos317

open Finset Filter

/--
For all sufficiently large `n` (in fact all `n ≥ 1`), any nonzero signed harmonic sum
`∑ k : Fin n, δ k / (k + 1)` with `δ k ∈ {-1, 0, 1}` satisfies `lhs ≥ 1 / lcm(1..n)`.
Discharges `Erdos317.claim2_inequality`.
-/
theorem claim2_inequality : ∀ᶠ n in atTop,
    ∀ δ : (Fin n) → ℚ, δ '' Set.univ ⊆ {-1, 0, 1} →
    letI lhs := |∑ k, ((δ k : ℚ) / (k + 1))|
    lhs ≠ 0 → lhs ≥ 1 / (Icc 1 n).lcm id := by
  refine Filter.eventually_atTop.mpr ⟨1, fun n _hn δ hδ hlhs_ne => ?_⟩
  set L : ℕ := (Icc 1 n).lcm id
  have hL_ne : L ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro x hx
    rw [Finset.mem_Icc] at hx
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hx.1)
  have hL_pos : (0 : ℚ) < (L : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL_ne)
  let c : Fin n → ℤ := fun k => if δ k = 1 then 1 else if δ k = -1 then -1 else 0
  have hc_cast : ∀ k : Fin n, (c k : ℚ) = δ k := by
    intro k
    have hk : δ k ∈ ({-1, 0, 1} : Set ℚ) := hδ ⟨k, Set.mem_univ k, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with h1 | h0 | hpos
    · simp only [c, h1, Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_zero]
      norm_num
    · simp only [c, h0, Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_zero]
      norm_num
    · simp only [c, hpos, ↓reduceIte, Int.cast_one]
  let M : ℤ := ∑ k : Fin n, c k * ((L / (k.1 + 1) : ℕ) : ℤ)
  have hclear : (L : ℚ) * (∑ k : Fin n, (δ k : ℚ) / ((k : ℚ) + 1)) = (M : ℚ) := by
    rw [Finset.mul_sum]
    push_cast [M]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk_mem : k.1 + 1 ∈ Icc 1 n := Finset.mem_Icc.mpr ⟨Nat.succ_pos _, k.isLt⟩
    have hdvd : k.1 + 1 ∣ L := Finset.dvd_lcm hk_mem
    have hmul : (k.1 + 1) * (L / (k.1 + 1)) = L := Nat.mul_div_cancel' hdvd
    have hL_cast : (L : ℚ) = ((k.1 : ℚ) + 1) * ((L / (k.1 + 1) : ℕ) : ℚ) := by
      exact_mod_cast hmul.symm
    have hk_eq : (k.1 : ℚ) + 1 = (k : ℚ) + 1 := rfl
    have hden : ((k : ℚ) + 1) ≠ 0 := by positivity
    calc
      (L : ℚ) * (δ k / ((k : ℚ) + 1))
          = ((c k : ℚ) * (((k.1 : ℚ) + 1) * ((L / (k.1 + 1) : ℕ) : ℚ))) / ((k : ℚ) + 1) := by
            rw [← hL_cast, hc_cast]; ring
      _ = (c k : ℚ) * ((L / (k.1 + 1) : ℕ) : ℚ) := by
            rw [hk_eq]
            field_simp
  have hsum_ne : ∑ k : Fin n, ((δ k : ℚ) / (k + 1)) ≠ 0 := by
    intro h0
    apply hlhs_ne
    simp [h0]
  have hM_ne : M ≠ 0 := by
    intro hM0
    have hprod0 : (L : ℚ) * (∑ k : Fin n, (δ k : ℚ) / ((k : ℚ) + 1)) = 0 := by
      rw [hclear, hM0, Int.cast_zero]
    rcases mul_eq_zero.mp hprod0 with hL0 | hS0
    · exact hL_pos.ne' hL0
    · exact hsum_ne hS0
  have hM_abs : (1 : ℤ) ≤ |M| := Int.one_le_abs hM_ne
  have hM_q : (1 : ℚ) ≤ |(M : ℚ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hM_abs
  have hmul_lhs : (L : ℚ) * |∑ k, ((δ k : ℚ) / (k + 1))| = |(M : ℚ)| := by
    rw [← hclear, abs_mul, abs_of_nonneg hL_pos.le]
  change 1 / (L : ℚ) ≤ |∑ k, ((δ k : ℚ) / (k + 1))|
  rw [div_le_iff₀ hL_pos, mul_comm, hmul_lhs]
  exact hM_q

end Contribution.Erdos317
