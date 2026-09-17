import Mathlib
import FormalConjectures.GreensOpenProblems.«24»

/-!
# Green 24: interval witnesses for the affine-translate count

Foundation layer for a contribution to `Green24.variants.conjecture`
(`Green24.variants.gamma = 1/3`).

`Green24.max013AffineTranslates n` is the supremum, over all `A : Finset ℤ` with
`A.card = n`, of the number of ordered pairs `(x, y) ∈ A × A` with `x ≠ y` and
`x + 3 * (y - x) ∈ A`.  This file names that pair count for a single set
(`pairCount`), records that it is bounded by the supremum (`pairCount_le_max`),
and introduces the witness family `interval n = {0, 1, …, n - 1}` with its
cardinality and membership lemmas.  Later layers count the pairs of
`interval n` and pass to the limsup defining `Green24.variants.gamma`.
-/

namespace Contribution.Green24VariantsConjecture

open Finset

/-- The number of ordered pairs `(x, y) ∈ A × A` with `x ≠ y` and `x + 3 * (y - x) ∈ A`,
i.e. the quantity whose supremum over `n`-sets is `Green24.max013AffineTranslates n`.
The filter predicate is written exactly as in that definition. -/
def pairCount (A : Finset ℤ) : ℕ :=
  ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card

/-- The set of pair counts of `n`-element subsets of `ℤ` is bounded by `n ^ 2`. -/
lemma bddAbove_pairCounts (n : ℕ) :
    BddAbove { k | ∃ A : Finset ℤ, A.card = n ∧
      k = ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card } := by
  refine ⟨n ^ 2, ?_⟩
  rintro k ⟨A, hA, rfl⟩
  calc ((A ×ˢ A).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ A)).card
      ≤ (A ×ˢ A).card := Finset.card_filter_le _ _
    _ = n ^ 2 := by rw [Finset.card_product, hA, sq]

/-- Every `n`-set realises at most `Green24.max013AffineTranslates n` pairs. -/
lemma pairCount_le_max {A : Finset ℤ} {n : ℕ} (hA : A.card = n) :
    pairCount A ≤ Green24.max013AffineTranslates n := by
  unfold Green24.max013AffineTranslates pairCount
  exact le_csSup (bddAbove_pairCounts n) ⟨A, hA, rfl⟩

/-- The interval `{0, 1, …, n - 1}` as a finset of integers. -/
def interval (n : ℕ) : Finset ℤ := (Finset.range n).image (Nat.cast : ℕ → ℤ)

@[simp]
lemma card_interval (n : ℕ) : (interval n).card = n := by
  rw [interval, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- Membership in `interval n`: exactly the integers `z` with `0 ≤ z < n`. -/
lemma mem_interval {n : ℕ} {z : ℤ} : z ∈ interval n ↔ 0 ≤ z ∧ z < n := by
  unfold interval
  constructor
  · rintro hz
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨Int.natCast_nonneg m, by exact_mod_cast Finset.mem_range.1 hm⟩
  · rintro ⟨h0, hn⟩
    refine Finset.mem_image.2 ⟨z.toNat, Finset.mem_range.2 ?_, Int.toNat_of_nonneg h0⟩
    have : (z.toNat : ℤ) < n := by rw [Int.toNat_of_nonneg h0]; exact hn
    exact_mod_cast this

/-- A natural number below `n` lies in `interval n`. -/
lemma natCast_mem_interval {n m : ℕ} (h : m < n) : (m : ℤ) ∈ interval n :=
  Finset.mem_image.2 ⟨m, Finset.mem_range.2 h, rfl⟩

/- ### Counting the affine copies inside an interval

An affine copy of `{0, 1, 3}` inside `interval n` is `{x, x + d, x + 3d}` with `d ≥ 1` and
`x + 3d ≤ n - 1`.  Each such copy contributes two ordered pairs to `pairCount`: the
increasing pair `(x, x + d)` and the decreasing pair `(x + 3d, x + 2d)`.  Writing
`d = i + 1` and `m = (n - 1) / 3`, the copies are indexed by `⟨i, x⟩` with `i < m` and
`x + 3 (i + 1) < n`, so there are `∑_{i < m} (n - 3 (i + 1))` of them, and
`2 ∑_{i<m} (n - 3(i+1)) = 2 m n - 3 m (m + 1) ≥ (n ^ 2 - 5 n) / 3`. -/

/-- The pairs of `interval n` counted by `pairCount`. -/
def intervalPairs (n : ℕ) : Finset (ℤ × ℤ) :=
  (interval n ×ˢ interval n).filter (fun (x, y) ↦ x ≠ y ∧ x + 3 * (y - x) ∈ interval n)

lemma pairCount_interval_eq (n : ℕ) : pairCount (interval n) = (intervalPairs n).card := rfl

/-- Index of the copies `{x, x + d, x + 3d} ⊆ interval n`, encoded as `⟨i, x⟩` with
`d = i + 1`, `i < (n - 1) / 3` and `x + 3 (i + 1) < n`. -/
def copyIndex (n : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Finset.range ((n - 1) / 3)).sigma fun i => Finset.range (n - 3 * (i + 1))

lemma mem_copyIndex {n : ℕ} {p : (_ : ℕ) × ℕ} :
    p ∈ copyIndex n ↔ p.1 < (n - 1) / 3 ∧ p.2 + 3 * (p.1 + 1) < n := by
  rcases p with ⟨i, x⟩
  simp only [copyIndex, Finset.mem_sigma, Finset.mem_range]
  omega

lemma card_copyIndex (n : ℕ) :
    (copyIndex n).card = ∑ i ∈ Finset.range ((n - 1) / 3), (n - 3 * (i + 1)) := by
  simp [copyIndex, Finset.card_sigma, Finset.card_range]

/-- Closed form for twice the number of copies, valid while `3 m ≤ n`. -/
lemma two_mul_sum_copies (n : ℕ) : ∀ m : ℕ, 3 * m ≤ n →
    2 * (∑ i ∈ Finset.range m, (n - 3 * (i + 1))) + 3 * m * (m + 1) = 2 * m * n := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro h3
    have ih' := ih (by omega)
    rw [Finset.sum_range_succ]
    generalize hS : ∑ i ∈ Finset.range m, (n - 3 * (i + 1)) = S at ih' ⊢
    zify [h3] at ih' ⊢
    linear_combination ih'

/-- The increasing pair `(x, x + d)` of the copy indexed by `⟨i, x⟩`, `d = i + 1`. -/
def upPair (p : (_ : ℕ) × ℕ) : ℤ × ℤ := ((p.2 : ℤ), ((p.2 + (p.1 + 1) : ℕ) : ℤ))

/-- The decreasing pair `(x + 3d, x + 2d)` of the copy indexed by `⟨i, x⟩`, `d = i + 1`. -/
def downPair (p : (_ : ℕ) × ℕ) : ℤ × ℤ :=
  (((p.2 + 3 * (p.1 + 1) : ℕ) : ℤ), ((p.2 + 2 * (p.1 + 1) : ℕ) : ℤ))

lemma upPair_mem {n : ℕ} {p : (_ : ℕ) × ℕ} (hp : p ∈ copyIndex n) :
    upPair p ∈ intervalPairs n := by
  obtain ⟨hi, hx⟩ := mem_copyIndex.1 hp
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_interval.2 ⟨?_, ?_⟩,
    mem_interval.2 ⟨?_, ?_⟩⟩, ?_, mem_interval.2 ⟨?_, ?_⟩⟩ <;>
  (try simp only [upPair]) <;> (try push_cast) <;> omega

lemma downPair_mem {n : ℕ} {p : (_ : ℕ) × ℕ} (hp : p ∈ copyIndex n) :
    downPair p ∈ intervalPairs n := by
  obtain ⟨hi, hx⟩ := mem_copyIndex.1 hp
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨mem_interval.2 ⟨?_, ?_⟩,
    mem_interval.2 ⟨?_, ?_⟩⟩, ?_, mem_interval.2 ⟨?_, ?_⟩⟩ <;>
  (try simp only [downPair]) <;> (try push_cast) <;> omega

lemma upPair_injOn (n : ℕ) : Set.InjOn upPair (copyIndex n : Set ((_ : ℕ) × ℕ)) := by
  rintro ⟨i, x⟩ - ⟨j, y⟩ - h
  simp only [upPair, Prod.mk.injEq, Nat.cast_inj] at h
  obtain ⟨rfl, h2⟩ := h
  obtain rfl : i = j := by omega
  rfl

lemma downPair_injOn (n : ℕ) : Set.InjOn downPair (copyIndex n : Set ((_ : ℕ) × ℕ)) := by
  rintro ⟨i, x⟩ - ⟨j, y⟩ - h
  simp only [downPair, Prod.mk.injEq, Nat.cast_inj] at h
  obtain ⟨h1, h2⟩ := h
  obtain rfl : i = j := by omega
  obtain rfl : x = y := by omega
  rfl

/-- Increasing and decreasing pairs never coincide. -/
lemma disjoint_upPair_downPair (n : ℕ) :
    Disjoint ((copyIndex n).image upPair) ((copyIndex n).image downPair) := by
  rw [Finset.disjoint_left]
  rintro a ha hb
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hb
  simp only [upPair, downPair, Prod.mk.injEq] at hq
  push_cast at hq
  omega

/-- Both orientations of every copy are counted, so `pairCount (interval n)` is at least
twice the number of copies. -/
lemma two_mul_card_copyIndex_le (n : ℕ) : 2 * (copyIndex n).card ≤ pairCount (interval n) := by
  have hsub : (copyIndex n).image upPair ∪ (copyIndex n).image downPair ⊆ intervalPairs n := by
    intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
      exact upPair_mem hp
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
      exact downPair_mem hp
  calc 2 * (copyIndex n).card
      = ((copyIndex n).image upPair).card + ((copyIndex n).image downPair).card := by
        rw [Finset.card_image_of_injOn (upPair_injOn n),
          Finset.card_image_of_injOn (downPair_injOn n)]
        ring
    _ = ((copyIndex n).image upPair ∪ (copyIndex n).image downPair).card :=
        (Finset.card_union_of_disjoint (disjoint_upPair_downPair n)).symm
    _ ≤ (intervalPairs n).card := Finset.card_le_card hsub
    _ = pairCount (interval n) := (pairCount_interval_eq n).symm

/-- The interval `{0, …, n - 1}` contains at least `(n ^ 2 - 5 n) / 3` counted pairs. -/
lemma pairCount_interval_ge (n : ℕ) :
    n ^ 2 ≤ 3 * pairCount (interval n) + 5 * n := by
  have hcard := two_mul_card_copyIndex_le n
  rw [card_copyIndex] at hcard
  set m := (n - 1) / 3 with hm
  have hmn : 3 * m ≤ n := by omega
  have hsum := two_mul_sum_copies n m hmn
  generalize hS : ∑ i ∈ Finset.range m, (n - 3 * (i + 1)) = S at hcard hsum
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · positivity
  · have h1 : 3 * m + 1 ≤ n := by omega
    have h2 : n ≤ 3 * m + 3 := by omega
    zify at hcard hsum h1 h2 ⊢
    nlinarith [hcard, hsum,
      mul_nonneg (by linarith : (0 : ℤ) ≤ (n : ℤ) - 3 * m - 1)
        (by linarith : (0 : ℤ) ≤ 3 * m + 3 - (n : ℤ))]

/-- The interval witness transfers to the maximum:
`n ^ 2 ≤ 3 * max013AffineTranslates n + 5 n` for every `n`. -/
lemma max_ge (n : ℕ) :
    n ^ 2 ≤ 3 * Green24.max013AffineTranslates n + 5 * n := by
  have h1 := pairCount_interval_ge n
  have h2 := pairCount_le_max (card_interval n)
  omega

/- ### The limsup interface

`Green24.variants.gamma` is `limsup (max013AffineTranslates n / n ^ 2)`.  The lemmas below turn
eventual quadratic bounds on `max013AffineTranslates n` into bounds on `gamma`, so that later work
only has to produce finite-`n` inequalities. -/

open Filter Topology

/-- The ratio `max013AffineTranslates n / n ^ 2` never exceeds `1` (with `0 / 0 = 0` at `n = 0`). -/
lemma ratio_le_one (n : ℕ) : (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hp : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_one hp]
    exact_mod_cast Green24.variants.upper_trivial (n := n)

/-- The ratio sequence defining `gamma` is bounded above. -/
lemma ratio_isBoundedUnder :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2) :=
  isBoundedUnder_of ⟨1, fun n => ratio_le_one n⟩

/-- An eventual lower bound `c n ^ 2 - C n ≤ max013AffineTranslates n` gives `c ≤ gamma`. -/
theorem gamma_ge_of_eventually {c C : ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ 2 - C * n ≤ Green24.max013AffineTranslates n) :
    c ≤ Green24.variants.gamma := by
  unfold Green24.variants.gamma
  -- the comparison sequence `c - C / n` tends to `c`
  have hlim : Tendsto (fun n : ℕ => c - C / (n : ℝ)) atTop (𝓝 c) := by
    have h0 := (tendsto_const_nhds (x := c)).sub
      ((tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop)
    simpa using h0
  -- eventually it lies below the ratio
  have hle : (fun n : ℕ => c - C / (n : ℝ)) ≤ᶠ[atTop]
      fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2 := by
    filter_upwards [h, eventually_gt_atTop 0] with n hn hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [le_div_iff₀ (by positivity)]
    have hexp : (c - C / (n : ℝ)) * (n : ℝ) ^ 2 = c * (n : ℝ) ^ 2 - C * n := by
      field_simp
    linarith [hexp]
  -- the comparison sequence is bounded below (by `c - |C|` once `n ≥ 1`)
  have hcob : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => c - C / (n : ℝ)) := by
    refine isCoboundedUnder_le_of_eventually_le atTop (x := c - |C|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hCn : C / (n : ℝ) ≤ |C| := by
      calc C / (n : ℝ) ≤ |C| / (n : ℝ) := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hn1
    linarith
  calc c = limsup (fun n : ℕ => c - C / (n : ℝ)) atTop := hlim.limsup_eq.symm
    _ ≤ limsup (fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2) atTop :=
        limsup_le_limsup hle hcob ratio_isBoundedUnder

/-- The sharp lower bound: the intervals `{0, …, n - 1}` show `gamma ≥ 1 / 3`. -/
theorem gamma_ge_one_third :
    Green24.variants.gamma ≥ 1 / 3 := by
  rw [ge_iff_le]
  refine gamma_ge_of_eventually (C := (5 / 3 : ℝ)) (Filter.Eventually.of_forall fun n => ?_)
  have h : (n : ℝ) ^ 2 ≤ 3 * (Green24.max013AffineTranslates n : ℝ) + 5 * (n : ℝ) := by
    exact_mod_cast max_ge n
  linarith

/-- The ratio sequence defining `gamma` is nonnegative. -/
lemma ratio_nonneg (n : ℕ) : 0 ≤ (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2 := by
  positivity

/-- An eventual upper bound `max013AffineTranslates n ≤ c n ^ 2 + C n` gives `gamma ≤ c`. -/
theorem gamma_le_of_eventually {c C : ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (Green24.max013AffineTranslates n : ℝ) ≤ c * (n : ℝ) ^ 2 + C * n) :
    Green24.variants.gamma ≤ c := by
  unfold Green24.variants.gamma
  -- the comparison sequence `c + C / n` tends to `c`
  have hlim : Tendsto (fun n : ℕ => c + C / (n : ℝ)) atTop (𝓝 c) := by
    have h0 := (tendsto_const_nhds (x := c)).add
      ((tendsto_const_nhds (x := C)).div_atTop tendsto_natCast_atTop_atTop)
    simpa using h0
  -- eventually the ratio lies below it
  have hle : (fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2) ≤ᶠ[atTop]
      fun n : ℕ => c + C / (n : ℝ) := by
    filter_upwards [h, eventually_gt_atTop 0] with n hn hn0
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [div_le_iff₀ (by positivity)]
    have hexp : (c + C / (n : ℝ)) * (n : ℝ) ^ 2 = c * (n : ℝ) ^ 2 + C * n := by
      field_simp
    linarith [hexp]
  -- the ratio is bounded below by `0`
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2) :=
    isCoboundedUnder_le_of_le atTop fun n => ratio_nonneg n
  -- the comparison sequence is bounded above (by `c + |C|` once `n ≥ 1`)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => c + C / (n : ℝ)) := by
    refine ⟨c + |C|, ?_⟩
    rw [eventually_map]
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hCn : C / (n : ℝ) ≤ |C| := by
      calc C / (n : ℝ) ≤ |C| / (n : ℝ) := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hn1
    linarith
  calc limsup (fun n : ℕ => (Green24.max013AffineTranslates n : ℝ) / (n : ℝ) ^ 2) atTop
      ≤ limsup (fun n : ℕ => c + C / (n : ℝ)) atTop := limsup_le_limsup hle hcob hbdd
    _ = c := hlim.limsup_eq

/-- **Reduction of Green 24 to a finite-`n` upper bound.**  An eventual bound
`max013AffineTranslates n ≤ n ^ 2 / 3 + C n` is all that is missing for
`Green24.variants.conjecture`: together with `gamma_ge_one_third` it gives `gamma = 1 / 3`. -/
theorem conjecture_of_upper_bound {C : ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (Green24.max013AffineTranslates n : ℝ) ≤ (n : ℝ) ^ 2 / 3 + C * n) :
    Green24.variants.gamma = 1 / 3 := by
  refine le_antisymm (gamma_le_of_eventually (C := C) ?_) gamma_ge_one_third
  filter_upwards [h] with n hn
  linarith [hn]

end Contribution.Green24VariantsConjecture
