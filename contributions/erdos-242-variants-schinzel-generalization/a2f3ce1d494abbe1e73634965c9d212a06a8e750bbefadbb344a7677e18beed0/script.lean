import Mathlib
import FormalConjectures.ErdosProblems.«242»

/-!
# Schinzel's generalization: small numerators and a multiples family

For the exact body of
`Erdos242.erdos_242.variants.schinzel_generalization`, this file proves:

* the complete conjectured conclusion for every positive numerator `a < 4`,
  with the stronger uniform threshold `n ≥ 2`;
* in particular, a parity construction covering every `n ≥ 2` for `a = 3`;
* for every positive `a`, the conclusion on every multiple `n` of `a` with
  `n ≥ 2a`, hence on an infinite arithmetic-progression tail.

The parent contribution disclosed in `sources.md` already handles the distinct
family `a ∣ n + 1`. Its supporting API is neither imported nor reproduced here.
-/

open scoped Topology

namespace Contribution.Erdos242SchinzelSmallNumerators

/-- The exact ordered three-unit-fraction conclusion in the Schinzel target
for fixed numerator `a` and denominator `n`. -/
def Decomp (a n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (a / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- Numerator one is covered for every `n ≥ 2`. The witnesses result from
two successive elementary unit-fraction splits, written here as one explicit
identity to avoid duplicating the parent's split API. -/
theorem numerator_one (n : ℕ) (hn : 2 ≤ n) : Decomp 1 n := by
  let q := n * (n + 1)
  have hq : 2 ≤ q := by
    dsimp [q]
    nlinarith
  refine ⟨n + 1, q + 1, q * (q + 1), by omega, ?_, ?_, ?_⟩
  · dsimp [q]
    nlinarith
  · calc
      q + 1 < 2 * (q + 1) := by omega
      _ ≤ q * (q + 1) := Nat.mul_le_mul hq (le_refl _)
  · dsimp [q]
    push_cast
    field_simp
    ring

/-- Numerator two is covered for every `n ≥ 2`, with witnesses
`n`, `n+1`, and `n(n+1)`. -/
theorem numerator_two (n : ℕ) (hn : 2 ≤ n) : Decomp 2 n := by
  refine ⟨n, n + 1, n * (n + 1), by omega, by omega, ?_, ?_⟩
  · nlinarith
  · push_cast
    field_simp
    ring

/-- Numerator three is covered for every `n ≥ 2`. For `n = 2m`, use
`m`, `n+1`, `n(n+1)`; for `n = 2m+1`, use `m+1`, `n`, `n(m+1)`. -/
theorem numerator_three (n : ℕ) (hn : 2 ≤ n) : Decomp 3 n := by
  let m := n / 2
  by_cases heven : n % 2 = 0
  · have hnrep : n = 2 * m := by omega
    have hm : 1 ≤ m := by omega
    refine ⟨m, n + 1, n * (n + 1), hm, by omega, ?_, ?_⟩
    · nlinarith
    · have hnrepq : (n : ℚ) = 2 * m := by exact_mod_cast hnrep
      norm_num [Nat.cast_add, Nat.cast_mul]
      rw [hnrepq]
      field_simp
      ring
  · have hnmod : n % 2 = 1 := by omega
    have hnrep : n = 2 * m + 1 := by omega
    have hm : 1 ≤ m := by omega
    refine ⟨m + 1, n, n * (m + 1), by omega, by omega, ?_, ?_⟩
    · nlinarith
    · have hnrepq : (n : ℚ) = 2 * m + 1 := by exact_mod_cast hnrep
      norm_num [Nat.cast_add, Nat.cast_mul]
      rw [hnrepq]
      field_simp
      ring

/-- Strong finite-parameter result: every positive numerator below four is
covered for every denominator `n ≥ 2`. -/
theorem small_positive_numerator
    (a n : ℕ) (ha : 0 < a) (ha4 : a < 4) (hn : 2 ≤ n) : Decomp a n := by
  have ha_cases : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  rcases ha_cases with rfl | rfl | rfl
  · exact numerator_one n hn
  · exact numerator_two n hn
  · exact numerator_three n hn

/-- Exact target-body use site: Schinzel's eventual statement holds for every
positive `a < 4`, with the explicit common threshold `2`. -/
theorem schinzel_target_body_for_small_positive_numerators
    (a : ℕ) (ha : 0 < a) (ha4 : a < 4) :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (a / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  exact small_positive_numerator a n ha ha4 hn

/-- The novel `a = 3` case, exposed directly in the literal syntax of the
target body. -/
theorem schinzel_target_body_for_three :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (3 / n : ℚ) = 1 / x + 1 / y + 1 / z :=
  schinzel_target_body_for_small_positive_numerators 3 (by norm_num) (by norm_num)

/-- For arbitrary positive `a`, every denominator `a*m` with `m ≥ 2` is
covered because `a/(a*m) = 1/m`, followed by `numerator_one`. -/
theorem multiple_family (a m : ℕ) (ha : 0 < a) (hm : 2 ≤ m) :
    Decomp a (a * m) := by
  have hq : (a / (a * m) : ℚ) = 1 / m := by
    field_simp
  obtain ⟨x, y, z, hx, hxy, hyz, hsum⟩ := numerator_one m hm
  refine ⟨x, y, z, hx, hxy, hyz, ?_⟩
  simpa only [Nat.cast_mul] using hq.trans hsum

/-- Equivalent divisor-facing interface: all multiples of `a` past `2a` are
covered. This is a full tail of an arithmetic progression of natural density
`1/a`, not merely an unspecified infinite subsequence. -/
theorem large_multiple_family
    (a n : ℕ) (ha : 0 < a) (han : a ∣ n) (hlarge : 2 * a ≤ n) : Decomp a n := by
  obtain ⟨m, rfl⟩ := han
  exact multiple_family a m ha (by nlinarith)

/-- Set-level handoff certifying containment of the entire multiples tail. -/
theorem multiples_tail_subset (a : ℕ) (ha : 0 < a) :
    {n : ℕ | 2 * a ≤ n ∧ a ∣ n} ⊆ {n : ℕ | Decomp a n} := by
  intro n hn
  exact large_multiple_family a n ha hn.2 hn.1

/-- For every positive numerator, the set of covered denominators is
infinite. The stronger arithmetic-progression containment is above. -/
theorem infinitely_many_denominators (a : ℕ) (ha : 0 < a) :
    Set.Infinite {n : ℕ | Decomp a n} := by
  have hinj : Function.Injective (fun m : ℕ => a * (2 + m)) := by
    intro m n hmn
    have h := Nat.mul_left_cancel ha hmn
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro n ⟨m, rfl⟩
  exact multiple_family a (2 + m) ha (by omega)

/-- Exact target-body use site for the arbitrary-numerator multiples family. -/
theorem target_body_on_multiples
    (a m : ℕ) (ha : 0 < a) (hm : 2 ≤ m) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / (a * m) : ℚ) = 1 / x + 1 / y + 1 / z :=
  by simpa only [Decomp, Nat.cast_mul] using multiple_family a m ha hm

end Contribution.Erdos242SchinzelSmallNumerators
