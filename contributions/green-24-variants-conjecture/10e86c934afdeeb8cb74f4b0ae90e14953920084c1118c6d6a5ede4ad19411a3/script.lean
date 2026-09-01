import Mathlib
import FormalConjectures.GreensOpenProblems.«24»

/-!
Independent proof of `Green24.variants.lower_HL`: the asymptotic constant
`γ = limsup (max013AffineTranslates n) / n²` satisfies `γ ≥ 1/12`.

Strategy: for the witness set `A = {0, 1, …, n-1} ⊆ ℤ`, every pair
`(x, x + j)` with `j ≥ 1` and `x + 3j ≤ n - 1` passes the filter in the
definition of `max013AffineTranslates` (the translate `{x, x+j, x+3j}` lies
in `A`).  Counting these pairs by a sigma-set injection gives at least
`∑_{s<n} ⌊s/3⌋ ≥ n²/12` solutions once `n ≥ 10`.  Hence the ratio is
eventually `≥ 1/12`, and since the ratio is bounded above (by the trivial
bound `n²`), the limsup is `≥ 1/12`.
-/

namespace Contribution.LowerHL

open Filter Finset

/-- The interval `{0, 1, ..., n-1}` as a finset of integers. -/
def base (n : ℕ) : Finset ℤ := (Finset.range n).image (Nat.cast : ℕ → ℤ)

lemma card_base (n : ℕ) : (base n).card = n := by
  rw [base, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

lemma mem_base {n m : ℕ} (h : m < n) : (m : ℤ) ∈ base n :=
  Finset.mem_image.2 ⟨m, Finset.mem_range.2 h, rfl⟩

/-- Index set for the solutions: pairs `⟨x, j⟩` with `x < n`, `1 ≤ j` and
`x + 3j ≤ n - 1`. -/
def idx (n : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Finset.range n).sigma fun x => Finset.Ico 1 ((n - 1 - x) / 3 + 1)

lemma card_idx (n : ℕ) : (idx n).card = ∑ s ∈ Finset.range n, s / 3 := by
  rw [idx, Finset.card_sigma]
  have h : ∀ x, (Finset.Ico 1 ((n - 1 - x) / 3 + 1)).card = (n - 1 - x) / 3 := by
    intro x
    rw [Nat.card_Ico]
    omega
  simp only [h]
  exact Finset.sum_range_reflect (fun s => s / 3) n

/-- The Gauss-type lower bound `n² ≤ 12 ∑_{s<n} ⌊s/3⌋` for `n ≥ 10`. -/
lemma sum_div3_lower {n : ℕ} (hn : 10 ≤ n) :
    n ^ 2 ≤ 12 * ∑ s ∈ Finset.range n, s / 3 := by
  have h1 : (∑ s ∈ Finset.range n, s) * 2 = n * (n - 1) := Finset.sum_range_id_mul_two n
  have h2 : ∑ s ∈ Finset.range n, s ≤ 3 * (∑ s ∈ Finset.range n, s / 3) + 2 * n := by
    calc ∑ s ∈ Finset.range n, s ≤ ∑ s ∈ Finset.range n, (3 * (s / 3) + 2) :=
          Finset.sum_le_sum fun s _ => by omega
      _ = 3 * (∑ s ∈ Finset.range n, s / 3) + 2 * n := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
            smul_eq_mul, mul_comm n 2]
  have h1n : (1 : ℕ) ≤ n := by omega
  zify [h1n] at h1 h2 hn ⊢
  nlinarith [h1, h2, hn,
    mul_nonneg (by linarith : (0 : ℤ) ≤ (n : ℤ) - 10) (by positivity : (0 : ℤ) ≤ (n : ℤ))]

/-- Injection of the index set into the filtered set of solution pairs. -/
lemma card_idx_le (n : ℕ) :
    (idx n).card ≤
      ((base n ×ˢ base n).filter
        (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ base n)).card := by
  apply Finset.card_le_card_of_injOn
    (fun p => (((p.1 : ℕ) : ℤ), ((p.1 + p.2 : ℕ) : ℤ)))
  · rintro ⟨x, j⟩ hp
    simp only [idx, Finset.mem_coe, Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico] at hp
    obtain ⟨hx, hj1, hj2⟩ := hp
    have hxj : x + j < n := by omega
    have hxj3 : x + 3 * j < n := by omega
    simp only [Finset.mem_coe]
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨mem_base hx, mem_base hxj⟩, ?_, ?_⟩
    · show ((x : ℕ) : ℤ) ≠ ((x + j : ℕ) : ℤ)
      intro h
      rw [Nat.cast_inj] at h
      omega
    · show ((x : ℕ) : ℤ) + 3 * (((x + j : ℕ) : ℤ) - ((x : ℕ) : ℤ)) ∈ base n
      have hkey : ((x : ℕ) : ℤ) + 3 * (((x + j : ℕ) : ℤ) - ((x : ℕ) : ℤ)) =
          ((x + 3 * j : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hkey]
      exact mem_base hxj3
  · rintro ⟨x, j⟩ - ⟨y, k⟩ - h
    simp only [Prod.mk.injEq, Nat.cast_inj] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    obtain rfl : j = k := by omega
    rfl

/-- The key finite bound: for `n ≥ 10`, `n² ≤ 12 · max013AffineTranslates n`. -/
lemma max_lower {n : ℕ} (hn : 10 ≤ n) :
    n ^ 2 ≤ 12 * Green24.max013AffineTranslates n := by
  have hstep : ∑ s ∈ Finset.range n, s / 3 ≤ Green24.max013AffineTranslates n := by
    unfold Green24.max013AffineTranslates
    have hbdd : BddAbove { k | ∃ A : Finset ℤ, A.card = n ∧
        k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card } := by
      refine ⟨n ^ 2, ?_⟩
      rintro k ⟨B, hB, rfl⟩
      apply le_trans (Finset.card_filter_le _ _)
      rw [Finset.card_product, hB, pow_two]
    have hmem : ((base n ×ˢ base n).filter
        (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ base n)).card ∈
        { k | ∃ A : Finset ℤ, A.card = n ∧
          k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card } :=
      ⟨base n, card_base n, rfl⟩
    calc ∑ s ∈ Finset.range n, s / 3 = (idx n).card := (card_idx n).symm
      _ ≤ ((base n ×ˢ base n).filter
            (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ base n)).card := card_idx_le n
      _ ≤ _ := le_csSup hbdd hmem
  have hsum := sum_div3_lower hn
  omega

theorem lower_HL : Green24.variants.gamma ≥ 1/12 := by
  rw [ge_iff_le]
  unfold Green24.variants.gamma
  apply Filter.le_limsup_of_frequently_le
  · refine (Filter.eventually_atTop.mpr ⟨10, fun n hn => ?_⟩).frequently
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 0 < n)
    have hpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h' : ((n : ℝ)) ^ 2 ≤ 12 * (Green24.max013AffineTranslates n : ℝ) := by
      exact_mod_cast max_lower hn
    rw [show (1 : ℝ) / 12 = 1 / 12 from rfl, div_le_div_iff₀ (by norm_num) hpos]
    linarith
  · refine Filter.isBoundedUnder_of ⟨1, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      norm_num
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hpos
      have hp2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
      rw [div_le_one hp2]
      exact_mod_cast Green24.variants.upper_trivial (n := n)


end Contribution.LowerHL
