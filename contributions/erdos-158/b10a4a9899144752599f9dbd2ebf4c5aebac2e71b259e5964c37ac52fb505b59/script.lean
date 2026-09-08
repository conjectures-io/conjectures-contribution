import Mathlib
import FormalConjectures.ErdosProblems.«158»

/-!
# Erdős Problem 158: `B₂[g]` counting, and the target's `liminf` as a growth rate

Target: `Erdos158.erdos_158`.  Writing `A(N) = |A ∩ [0, N)|`, the right-hand side of its `↔`
asks whether every infinite `B₂[2]` set `A ⊆ ℕ` satisfies `liminf_N A(N) · N ^ (-1/2) = 0`.

## The obstacle

The pool file `FormalConjectures/ErdosProblems/158.lean` introduces `Erdos158.B2` and proves
exactly one fact about it, `Erdos158.b2_one : B2 1 A ↔ IsSidon A`.  The identifier `B2` occurs
in no other file of the `FormalConjectures` library, and `IsSidon` (defined in
`FormalConjecturesForMathlib/Combinatorics/Basic.lean`) comes with no bound on
`|A ∩ [0, N)|`; grepping the pinned Mathlib for `Sidon` returns nothing at all.  So nothing in
the environment bounds the counting function of a `B₂[g]` set, and nothing says that the real
sequence whose `liminf` the target takes is even bounded.

That gap is not cosmetic.  `Filter.liminf_le_iff`, `Filter.le_liminf_iff` and
`Filter.liminf_le_of_frequently_le` carry `IsCoboundedUnder` / `IsBoundedUnder` side conditions
supplied by a `by isBoundedDefault` autoparam, and for the target's sequence that autoparam
fails: elaborating `Filter.liminf_le_iff` at
`fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)` reports
"could not synthesize default value for parameter 'h₁'" and the same for `'h₂'`, leaving the
goals `IsCoboundedUnder (· ≥ ·) atTop _` and `IsBoundedUnder (· ≥ ·) atTop _` open.
Coboundedness is also what stops the target from being satisfied for the wrong reason: by
Mathlib's `Real.liminf_of_not_isCoboundedUnder`, *every* real sequence that is not
`IsCoboundedUnder (· ≥ ·)` has `liminf` equal to `0` on the nose.  `liminf_univ_eq_zero` below
exhibits this trap concretely, for `A = Set.univ`.

## What this file adds

* A pigeonhole counting bound for `B₂[g]` sets, `sq_ncard_inter_Iio_le`
  (`A(N) ^ 2 ≤ 2 * g * (2 * N - 1)`) and its real form `ncard_inter_Iio_le`
  (`A(N) ≤ 2 * √g * √N`), together with `isBoundedUnder_ge_normalized` and
  `isCoboundedUnder_ge_normalized`, which discharge the autoparams above, and
  `liminf_nonneg` / `liminf_le`, which place the target's `liminf` in `[0, 2 * √g]`.
* Two `liminf`-free, `Real.rpow`-free reformulations of the target's conclusion:
  `liminf_eq_zero_iff` (for every `ε > 0` there are infinitely many `N` with `A(N) < ε * √N`)
  and the square-root-free `liminf_eq_zero_iff_sq` (`A(N) ^ 2 < ε * N` infinitely often).
  Both are equivalences, and `liminf_eq_zero_of_finite` shows the target's `A.Infinite` binder
  is redundant, so `erdos_158_rhs_iff` restates the target's right-hand side verbatim.
* **The growth-rate form.**  `liminf_eq_zero_iff_nth` and `erdos_158_rhs_iff_nth` convert the
  target's analytic conclusion into a statement about the increasing enumeration
  `a₀ < a₁ < a₂ < ⋯` of `A` (Mathlib's `Nat.nth (· ∈ A)`): the `liminf` vanishes if and only if
  `aₖ / k²` is unbounded.  This is the shape in which the problem is usually stated, and it
  contains no filter, no `liminf` and no square root.  The dictionary between the two pictures
  is `ncard_inter_Iio_nth`, `ncard_inter_Iio_nth_succ` and `le_nth_ncard_inter_Iio`.
* The complementary lower bound `sq_succ_le_nth` (`(k+1)² ≤ 2g(2aₖ+1)`, i.e. `aₖ ≥ k²/(4g)`
  up to an additive constant) and `eventually_lt_nth`, which show the growth-rate condition is
  *not* vacuous and locate exactly what is open: a `B₂[g]` set always has
  `liminf aₖ / k² ≥ 1/(4g)`, and the target asks whether `limsup aₖ / k²` must be `∞`.
* `liminf_eq_zero_of_liminf_mul_sqrt_log_lt_top`: the Erdős–Sárközy–Sós route as a checked
  interface.  For a `B₂[g]` set, `liminf A(N) · N ^ (-1/2) · (log N) ^ (1/2) < ∞` implies the
  target's conclusion.  For `g = 1` that hypothesis is the theorem of [ESS94] recorded as the
  pool file's `Erdos158.erdos_158.variants.isSidon'`; for `g = 2` it is open, so this is a
  *sufficient* condition and not a reformulation — the converse is not proved here.
* `not_b2_two_squares`, `exists_infinite_liminf_ne_zero`: the `B₂[2]` hypothesis is necessary.
  The squares are an infinite subset of `ℕ` whose normalised counting function tends to `1`,
  and `325 = 1 + 324 = 36 + 289 = 100 + 225` shows they are not `B₂[2]`.
* `b2_two_doubleBlocks` and friends: `doubleBlocks B = 2 * B ∪ (2 * B + 1)` is an infinite
  `B₂[2]` set that is not Sidon and is denser than `B` by a factor `√2`, so the target is
  strictly more general than the solved Sidon case.

A later solver can use declaration `Contribution.Erdos158Counting.erdos_158_rhs_iff_nth` to
discharge or simplify obligation `∀ A : Set ℕ, A.Infinite → B2 2 A →
liminf (fun N : ℕ => ↑(A ∩ Set.Iio N).ncard * (N : ℝ) ^ (-1 / 2 : ℝ)) atTop = 0`, the right-hand
side of the `↔`, in target `Erdos158.erdos_158`.

*References:*
 - [erdosproblems.com/158](https://www.erdosproblems.com/158)
 - [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I. Journal of
   Number Theory (1994), 329-347.
-/

open Filter Set

namespace Contribution.Erdos158Counting

open Erdos158

variable {A : Set ℕ} {g : ℕ}

/- ## `B₂[g]` basics -/

/-- A `B₂[g]` set is a `B₂[g']` set for every `g' ≥ g`.  In particular every Sidon set is
`B₂[2]`, via the pool file's `Erdos158.b2_one`, so the class quantified over in
`Erdos158.erdos_158` contains every infinite Sidon set. -/
theorem b2_mono {g g' : ℕ} (hgg : g ≤ g') (hA : B2 g A) : B2 g' A := fun n =>
  (hA n).trans (by exact_mod_cast hgg)

/- ## The counting bound -/

/-- **Pigeonhole bound for `B₂[g]` sets.**  If `A` is `B₂[g]` then the number of its elements
below `N` satisfies `|A ∩ [0, N)| ^ 2 ≤ 2 * g * (2 * N - 1)`.

The pairs `(a, a')` from `A ∩ [0, N)` with `a ≤ a'` number at least `|A ∩ [0, N)| ^ 2 / 2`, their
sums lie in `[0, 2 * N - 1)`, and each sum is hit at most `g` times by the `B₂[g]` hypothesis. -/
theorem sq_ncard_inter_Iio_le (hA : B2 g A) (N : ℕ) :
    (A ∩ Set.Iio N).ncard ^ 2 ≤ 2 * g * (2 * N - 1) := by
  classical
  have hfin : (A ∩ Set.Iio N).Finite :=
    Set.Finite.subset (Set.finite_Iio N) Set.inter_subset_right
  set S : Finset ℕ := hfin.toFinset with hS
  have hSmem : ∀ a, a ∈ S ↔ a ∈ A ∧ a < N := by
    intro a; simp [hS]
  set T : Finset (ℕ × ℕ) := {p ∈ S ×ˢ S | p.1 ≤ p.2} with hTdef
  have h1 : S.card * S.card ≤ 2 * T.card := by
    have key := Finset.card_le_mul_card_image_of_maps_to
      (f := fun p : ℕ × ℕ => (min p.1 p.2, max p.1 p.2)) (s := S ×ˢ S) (t := T) ?_ 2 ?_
    · simpa [Finset.card_product] using key
    · intro p hp
      rw [Finset.mem_product] at hp
      rcases le_total p.1 p.2 with h | h
      · simp [hTdef, Finset.mem_product, hp.1, hp.2, h]
      · simp [hTdef, Finset.mem_product, hp.1, hp.2, h]
    · intro b _
      have hsub : {p ∈ S ×ˢ S | (min p.1 p.2, max p.1 p.2) = b} ⊆ {(b.1, b.2), (b.2, b.1)} := by
        intro p hp
        simp only [Finset.mem_filter] at hp
        obtain ⟨-, hp2⟩ := hp
        subst hp2
        rcases le_total p.1 p.2 with h | h
        · simp [min_eq_left h, max_eq_right h]
        · simp [min_eq_right h, max_eq_left h]
      exact (Finset.card_le_card hsub).trans (by simpa using Finset.card_insert_le _ _)
  have h2 : T.card ≤ g * (2 * N - 1) := by
    have key := Finset.card_le_mul_card_image_of_maps_to
      (f := fun p : ℕ × ℕ => p.1 + p.2) (s := T) (t := Finset.range (2 * N - 1)) ?_ g ?_
    · simpa using key
    · intro p hp
      simp only [hTdef, Finset.mem_filter, Finset.mem_product] at hp
      have ha := (hSmem p.1).1 hp.1.1
      have hb := (hSmem p.2).1 hp.1.2
      simp only [Finset.mem_range]
      omega
    · intro b _
      have hsub : (↑({p ∈ T | p.1 + p.2 = b}) : Set (ℕ × ℕ)) ⊆
          {x : ℕ × ℕ | x.1 + x.2 = b ∧ x.1 ≤ x.2 ∧ x.1 ∈ A ∧ x.2 ∈ A} := by
        intro p hp
        simp only [Finset.coe_filter, Set.mem_setOf_eq, hTdef, Finset.mem_filter,
          Finset.mem_product] at hp
        exact ⟨hp.2, hp.1.2, ((hSmem p.1).1 hp.1.1.1).1, ((hSmem p.2).1 hp.1.1.2).1⟩
      have hle := (Set.encard_le_encard hsub).trans (hA b)
      rw [Set.encard_coe_eq_coe_finsetCard] at hle
      exact_mod_cast hle
  have hcard : (A ∩ Set.Iio N).ncard = S.card := Set.ncard_eq_toFinset_card _ hfin
  rw [hcard, sq]
  calc S.card * S.card ≤ 2 * T.card := h1
    _ ≤ 2 * (g * (2 * N - 1)) := by omega
    _ = 2 * g * (2 * N - 1) := by ring

/-- The real form of `sq_ncard_inter_Iio_le`: a `B₂[g]` set has at most `2 * √g * √N` elements
below `N`. -/
theorem ncard_inter_Iio_le (hA : B2 g A) (N : ℕ) :
    ((A ∩ Set.Iio N).ncard : ℝ) ≤ 2 * Real.sqrt g * Real.sqrt N := by
  have hnat : (A ∩ Set.Iio N).ncard ^ 2 ≤ 4 * g * N := by
    refine (sq_ncard_inter_Iio_le hA N).trans ?_
    calc 2 * g * (2 * N - 1) ≤ 2 * g * (2 * N) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * g * N := by ring
  have hcast : ((A ∩ Set.Iio N).ncard : ℝ) ^ 2 ≤ 4 * (g : ℝ) * (N : ℝ) := by exact_mod_cast hnat
  have h2 := Real.sqrt_le_sqrt hcast
  rw [Real.sqrt_sq (by positivity)] at h2
  refine h2.trans_eq ?_
  rw [show (4 : ℝ) * g * N = 2 ^ 2 * ((g : ℝ) * N) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num), Real.sqrt_mul (by positivity), mul_assoc]

/-- Monotonicity of the counting function `N ↦ |A ∩ [0, N)|`. -/
theorem ncard_inter_Iio_mono (A : Set ℕ) {M N : ℕ} (hMN : M ≤ N) :
    (A ∩ Set.Iio M).ncard ≤ (A ∩ Set.Iio N).ncard :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ (Set.Iio_subset_Iio hMN))
    (Set.Finite.subset (Set.finite_Iio N) Set.inter_subset_right)

/- ## The normalised counting function -/

/-- The target's summand, rewritten without `Real.rpow`.  This is an equality of real numbers for
*every* `N`, including `N = 0`, where both sides are `0`. -/
theorem normalized_eq (A : Set ℕ) (N : ℕ) :
    ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)
      = ((A ∩ Set.Iio N).ncard : ℝ) / Real.sqrt N := by
  rw [show (- 1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg (by positivity),
    ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- For a `B₂[g]` set the target's summand is bounded by `2 * √g`, uniformly in `N`. -/
theorem normalized_le (hA : B2 g A) (N : ℕ) :
    ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ) ≤ 2 * Real.sqrt g := by
  rw [normalized_eq]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (N : ℝ)) with h0 | h0
  · rw [← h0]
    simp
  · rw [div_le_iff₀ h0]
    exact ncard_inter_Iio_le hA N

/-- Discharges the `IsBoundedUnder (· ≥ ·)` autoparam of `Filter.liminf_le_iff`,
`Filter.le_liminf_iff` and `Filter.liminf_le_of_frequently_le` for the target's sequence. -/
theorem isBoundedUnder_ge_normalized (A : Set ℕ) :
    IsBoundedUnder (· ≥ ·) atTop
      (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) :=
  isBoundedUnder_of ⟨0, fun _ => by positivity⟩

/-- Discharges the `IsCoboundedUnder (· ≥ ·)` autoparam of `Filter.liminf_le_iff`,
`Filter.le_liminf_iff` and `Filter.le_liminf_of_le` for the target's sequence.  This is the side
condition that `by isBoundedDefault` does not produce here, and it is what makes the target's
conclusion meaningful: by `Real.liminf_of_not_isCoboundedUnder` a real sequence that fails to be
`IsCoboundedUnder (· ≥ ·)` has `liminf` equal to `0` regardless of its values. -/
theorem isCoboundedUnder_ge_normalized (hA : B2 g A) :
    IsCoboundedUnder (· ≥ ·) atTop
      (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) :=
  IsCoboundedUnder.of_frequently_le (a := 2 * Real.sqrt g)
    (Frequently.of_forall (normalized_le hA))

/- ## Locating and reformulating the target's `liminf` -/

/-- The `liminf` in the target is nonnegative. -/
theorem liminf_nonneg (hA : B2 g A) :
    0 ≤ liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop :=
  le_liminf_of_le (isCoboundedUnder_ge_normalized hA)
    (Eventually.of_forall fun _ => by positivity)

/-- The `liminf` in the target is at most `2 * √g`; with `liminf_nonneg` this shows it is a
genuine real number in `[0, 2 * √g]`. -/
theorem liminf_le (hA : B2 g A) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop
      ≤ 2 * Real.sqrt g :=
  liminf_le_of_frequently_le (Frequently.of_forall (normalized_le hA))
    (isBoundedUnder_ge_normalized A)

/-- **Elementary form of the target's conclusion.**  For a `B₂[g]` set the `liminf` appearing in
`Erdos158.erdos_158` vanishes if and only if, for every `ε > 0`, there are infinitely many `N`
with fewer than `ε * √N` elements of `A` below `N`.  No `Real.rpow` and no `liminf` remain. -/
theorem liminf_eq_zero_iff (hA : B2 g A) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, ((A ∩ Set.Iio N).ncard : ℝ) < ε * Real.sqrt N := by
  have hbd := isBoundedUnder_ge_normalized A
  have hcob := isCoboundedUnder_ge_normalized hA
  have hconv : ∀ ε : ℝ, ((∃ᶠ N : ℕ in atTop,
      ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ) < ε) ↔
      ∃ᶠ N : ℕ in atTop, ((A ∩ Set.Iio N).ncard : ℝ) < ε * Real.sqrt N) := by
    intro ε
    refine frequently_congr ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    rw [normalized_eq, div_lt_iff₀ hpos]
  constructor
  · intro h ε hε
    exact (hconv ε).1 ((liminf_le_iff hcob hbd).1 h.le ε hε)
  · intro h
    exact le_antisymm ((liminf_le_iff hcob hbd).2 fun y hy => (hconv y).2 (h y hy))
      (liminf_nonneg hA)

/-- **Square-root-free form of the target's conclusion.**  Squaring `liminf_eq_zero_iff`: the
`liminf` vanishes if and only if for every `ε > 0` there are infinitely many `N` with
`A(N) ^ 2 < ε * N`.  Every transcendental function has now been eliminated from the statement. -/
theorem liminf_eq_zero_iff_sq (hA : B2 g A) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, ((A ∩ Set.Iio N).ncard : ℝ) ^ 2 < ε * (N : ℝ) := by
  rw [liminf_eq_zero_iff hA]
  constructor
  · intro h ε hε
    refine (h (Real.sqrt ε) (Real.sqrt_pos.2 hε)).mono fun N hN => ?_
    have hx : (0 : ℝ) ≤ ((A ∩ Set.Iio N).ncard : ℝ) := by positivity
    have hy : (Real.sqrt ε * Real.sqrt N) ^ 2 = ε * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt hε.le, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    have hpos : (0 : ℝ) < Real.sqrt ε * Real.sqrt N + ((A ∩ Set.Iio N).ncard : ℝ) := by linarith
    nlinarith [mul_pos (sub_pos.2 hN) hpos]
  · intro h ε hε
    refine (h (ε ^ 2) (by positivity)).mono fun N hN => ?_
    have hx : (0 : ℝ) ≤ ((A ∩ Set.Iio N).ncard : ℝ) := by positivity
    have hy : (ε * Real.sqrt N) ^ 2 = ε ^ 2 * (N : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonneg (sub_nonneg.2 hcon)
      (add_nonneg hx (mul_nonneg hε.le (Real.sqrt_nonneg (N : ℝ))))]

/-- The negation of `liminf_eq_zero_iff`, in the shape used inside the pool file.  The right-hand
side is exactly the intermediate claim
`∃ c > 0, ∀ᶠ N in atTop, c ≤ ↑(A ∩ Set.Iio N).ncard * (N : ℝ) ^ (-1 / 2 : ℝ)`
that the proof of `Erdos158.erdos_158.variants.isSidon` derives by hand from a `by_contra` and a
`csSup` computation. -/
theorem liminf_ne_zero_iff (hA : B2 g A) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop ≠ 0 ↔
      ∃ c > (0 : ℝ), ∀ᶠ N : ℕ in atTop,
        c ≤ ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ) := by
  have hbd := isBoundedUnder_ge_normalized A
  have hcob := isCoboundedUnder_ge_normalized hA
  constructor
  · intro h
    have hpos := (liminf_nonneg hA).lt_of_ne' h
    refine ⟨_, half_pos hpos, ?_⟩
    exact ((le_liminf_iff hcob hbd).1 le_rfl _ (by linarith)).mono fun N hN => hN.le
  · rintro ⟨c, hc, h⟩ heq
    have := le_liminf_of_le hcob h
    rw [heq] at this
    linarith

/-- The `A.Infinite` hypothesis of `Erdos158.erdos_158` is redundant: a finite set satisfies the
conclusion outright, because its counting function is bounded while `√N → ∞`. -/
theorem liminf_eq_zero_of_finite (hA : A.Finite) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine Tendsto.liminf_eq (squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_
    (hsqrt.const_div_atTop (A.ncard : ℝ)))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hle : ((A ∩ Set.Iio N).ncard : ℝ) ≤ (A.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left hA
  rw [normalized_eq]
  exact div_le_div_of_nonneg_right hle hpos.le

/-- **A trap in the target's statement.**  For `A = Set.univ` the sequence
`N ↦ A(N) * N ^ (-1/2)` is `√N`, which tends to `atTop` and is therefore *not*
`IsCoboundedUnder (· ≥ ·)`; Mathlib's `liminf` of it is `0`.  So `Set.univ` is an infinite set
satisfying the target's conclusion despite having the largest possible counting function, and
any solution must use the `B2 2` hypothesis through `isCoboundedUnder_ge_normalized` rather than
merely through a density bound. -/
theorem liminf_univ_eq_zero :
    liminf (fun N : ℕ => (((Set.univ : Set ℕ) ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ))
      atTop = 0 := by
  have hfun : (fun N : ℕ => (((Set.univ : Set ℕ) ∩ Set.Iio N).ncard : ℝ)
      * (N : ℝ) ^ (- 1 / 2 : ℝ)) = fun N : ℕ => Real.sqrt N := by
    funext N
    have hcard : ((Set.univ : Set ℕ) ∩ Set.Iio N).ncard = N := by
      rw [Set.univ_inter, show (Set.Iio N : Set ℕ) = ↑(Finset.range N) by ext x; simp,
        Set.ncard_coe_finset, Finset.card_range]
    rw [normalized_eq, hcard, Real.div_sqrt]
  rw [hfun]
  refine Real.liminf_of_not_isCoboundedUnder ?_
  rintro ⟨b, hb⟩
  have h1 : ∀ᶠ x : ℝ in map (fun N : ℕ => Real.sqrt N) atTop, x ≥ b + 1 := by
    rw [eventually_map]
    exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (b + 1)
  have := hb (b + 1) h1
  linarith

/-- **The target, reformulated.**  The right-hand side of `Erdos158.erdos_158` is equivalent to
the statement that every `B₂[2]` set has, for each `ε > 0`, infinitely many `N` with
`|A ∩ [0, N)| < ε * √N`.  This is an equivalence, so it is safe to use in either direction; note
that it also removes the `A.Infinite` binder, which `liminf_eq_zero_of_finite` shows is
redundant. -/
theorem erdos_158_rhs_iff :
    (∀ A : Set ℕ, A.Infinite → B2 2 A →
        liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0) ↔
      ∀ A : Set ℕ, B2 2 A → ∀ ε : ℝ, 0 < ε →
        ∃ᶠ N : ℕ in atTop, ((A ∩ Set.Iio N).ncard : ℝ) < ε * Real.sqrt N := by
  constructor
  · intro h A hA ε hε
    rcases A.finite_or_infinite with hfin | hinf
    · exact (liminf_eq_zero_iff hA).1 (liminf_eq_zero_of_finite hfin) ε hε
    · exact (liminf_eq_zero_iff hA).1 (h A hinf hA) ε hε
  · intro h A _ hA
    exact (liminf_eq_zero_iff hA).2 (h A hA)

/- ## The counting function versus the increasing enumeration of `A` -/

/-- Dictionary between `|A ∩ [0, N)|` and Mathlib's `Nat.count`, the entry point to the
`Nat.count` / `Nat.nth` API for the increasing enumeration of a set of naturals. -/
theorem ncard_inter_Iio_eq_count (A : Set ℕ) [DecidablePred (· ∈ A)] (N : ℕ) :
    (A ∩ Set.Iio N).ncard = Nat.count (· ∈ A) N := by
  rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [and_comm]

/-- `A` has exactly `k` elements below its `k`-th element `aₖ = Nat.nth (· ∈ A) k`. -/
theorem ncard_inter_Iio_nth (hAinf : A.Infinite) (k : ℕ) :
    (A ∩ Set.Iio (Nat.nth (· ∈ A) k)).ncard = k := by
  classical
  rw [ncard_inter_Iio_eq_count, Nat.count_nth_of_infinite (p := (· ∈ A)) hAinf]

/-- `A` has exactly `k + 1` elements below `aₖ + 1`, i.e. `A(aₖ + 1) = k + 1`. -/
theorem ncard_inter_Iio_nth_succ (hAinf : A.Infinite) (k : ℕ) :
    (A ∩ Set.Iio (Nat.nth (· ∈ A) k + 1)).ncard = k + 1 := by
  classical
  rw [ncard_inter_Iio_eq_count, Nat.count_nth_succ_of_infinite (p := (· ∈ A)) hAinf]

/-- The `A(N)`-th element of `A` is at least `N`: `N ≤ a_{A(N)}`. -/
theorem le_nth_ncard_inter_Iio (hAinf : A.Infinite) (N : ℕ) :
    N ≤ Nat.nth (· ∈ A) ((A ∩ Set.Iio N).ncard) := by
  classical
  rw [ncard_inter_Iio_eq_count]
  exact Nat.le_nth_count (p := (· ∈ A)) hAinf N

/-- **The enumeration of a `B₂[g]` set grows at least quadratically.**  If `a₀ < a₁ < ⋯` is the
increasing enumeration of an infinite `B₂[g]` set then `(k + 1) ^ 2 ≤ 2 * g * (2 * aₖ + 1)`; in
particular `aₖ ≥ k ^ 2 / (4 * g) - 1`.  This is `sq_ncard_inter_Iio_le` read at `N = aₖ + 1`. -/
theorem sq_succ_le_nth (hA : B2 g A) (hAinf : A.Infinite) (k : ℕ) :
    (k + 1) ^ 2 ≤ 2 * g * (2 * Nat.nth (· ∈ A) k + 1) := by
  have h := sq_ncard_inter_Iio_le hA (Nat.nth (· ∈ A) k + 1)
  rw [ncard_inter_Iio_nth_succ hAinf] at h
  have harith : 2 * (Nat.nth (· ∈ A) k + 1) - 1 = 2 * Nat.nth (· ∈ A) k + 1 := by omega
  rwa [harith] at h

/-- **Non-vacuity of the growth-rate condition.**  For an infinite `B₂[g]` set and any
`C < 1 / (4 * g)` (written multiplicatively as `4 * g * C < 1`), the inequality `C * k ^ 2 < aₖ`
holds for *all large* `k`, by `sq_succ_le_nth`.  So the condition appearing in
`liminf_eq_zero_iff_nth` is automatic for small `C`, and the whole content of
`Erdos158.erdos_158` is whether it also holds, infinitely often, for arbitrarily large `C`. -/
theorem eventually_lt_nth (hA : B2 g A) (hAinf : A.Infinite) {C : ℝ}
    (hC : 4 * (g : ℝ) * C < 1) :
    ∀ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 2 < (Nat.nth (· ∈ A) k : ℝ) := by
  have hg : 0 < g := by
    have h0 := sq_succ_le_nth hA hAinf 0
    rcases Nat.eq_zero_or_pos g with h | h
    · simp [h] at h0
    · exact h
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have he : (0 : ℝ) < 1 - 4 * (g : ℝ) * C := by linarith
  have htend : Tendsto (fun k : ℕ => (1 - 4 * (g : ℝ) * C) * (k : ℝ) ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop he
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
  filter_upwards [htend.eventually_gt_atTop (2 * (g : ℝ))] with k hk
  have hcast : ((k : ℝ) + 1) ^ 2 ≤ 2 * (g : ℝ) * (2 * (Nat.nth (· ∈ A) k : ℝ) + 1) := by
    exact_mod_cast sq_succ_le_nth hA hAinf k
  nlinarith [hgR, hk, hcast, Nat.cast_nonneg (α := ℝ) k]

/-- **The growth-rate form of the target's conclusion.**  Let `a₀ < a₁ < ⋯` be the increasing
enumeration `Nat.nth (· ∈ A)` of an infinite `B₂[g]` set `A`.  The `liminf` appearing in
`Erdos158.erdos_158` vanishes if and only if `aₖ / k ^ 2` is unbounded, i.e. for every real `C`
there are infinitely many `k` with `C * k ^ 2 < aₖ`.

Together with `eventually_lt_nth` (which gives `aₖ > C * k ^ 2` eventually whenever
`C < 1 / (4 * g)`) this says precisely that the open question is whether an infinite `B₂[2]` set
can have `aₖ = O(k ^ 2)`. -/
theorem liminf_eq_zero_iff_nth (hA : B2 g A) (hAinf : A.Infinite) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 ↔
      ∀ C : ℝ, ∃ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 2 < (Nat.nth (· ∈ A) k : ℝ) := by
  have hle : ∀ k : ℕ, k ≤ Nat.nth (· ∈ A) k := fun k => Nat.le_nth fun hf => absurd hf hAinf
  rw [liminf_eq_zero_iff_sq hA]
  constructor
  · intro h C
    rcases le_or_gt C 0 with hC | hC
    · refine ((eventually_ge_atTop 1).frequently).mono fun k hk => ?_
      have h1 : (1 : ℝ) ≤ (Nat.nth (· ∈ A) k : ℝ) := by
        exact_mod_cast le_trans hk (hle k)
      nlinarith [sq_nonneg ((k : ℝ))]
    · rw [frequently_atTop]
      intro k₀
      obtain ⟨N, hN, hlt⟩ :=
        frequently_atTop.1 (h C⁻¹ (by positivity)) (Nat.nth (· ∈ A) k₀ + 1)
      refine ⟨(A ∩ Set.Iio N).ncard, ?_, ?_⟩
      · calc k₀ ≤ k₀ + 1 := Nat.le_succ _
          _ = (A ∩ Set.Iio (Nat.nth (· ∈ A) k₀ + 1)).ncard :=
              (ncard_inter_Iio_nth_succ hAinf k₀).symm
          _ ≤ (A ∩ Set.Iio N).ncard := ncard_inter_Iio_mono A hN
      · have h2 : (N : ℝ) ≤ (Nat.nth (· ∈ A) ((A ∩ Set.Iio N).ncard) : ℝ) := by
          exact_mod_cast le_nth_ncard_inter_Iio hAinf N
        have h3 := mul_lt_mul_of_pos_left hlt hC
        rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at h3
        linarith
  · intro h ε hε
    rw [frequently_atTop]
    intro N₀
    obtain ⟨k, hk, hlt⟩ := frequently_atTop.1 (h ε⁻¹) N₀
    refine ⟨Nat.nth (· ∈ A) k, le_trans hk (hle k), ?_⟩
    rw [ncard_inter_Iio_nth hAinf]
    have h3 := mul_lt_mul_of_pos_left hlt hε
    rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] at h3
    exact h3

/-- **Use site 1.**  The target's right-hand side, verbatim, is equivalent to: for every infinite
`B₂[2]` set `A` with increasing enumeration `aₖ = Nat.nth (· ∈ A) k`, the ratio `aₖ / k ^ 2` is
unbounded.  A solver may replace the analytic obligation by this arithmetic one in either
direction. -/
theorem erdos_158_rhs_iff_nth :
    (∀ A : Set ℕ, A.Infinite → B2 2 A →
        liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0) ↔
      ∀ A : Set ℕ, A.Infinite → B2 2 A → ∀ C : ℝ,
        ∃ᶠ k : ℕ in atTop, C * (k : ℝ) ^ 2 < (Nat.nth (· ∈ A) k : ℝ) := by
  constructor
  · intro h A hinf hA
    exact (liminf_eq_zero_iff_nth hA hinf).1 (h A hinf hA)
  · intro h A hinf hA
    exact (liminf_eq_zero_iff_nth hA hinf).2 (h A hinf hA)

/- ## The Erdős–Sárközy–Sós route, as a checked interface -/

/-- **The `(log N) ^ (1/2)` bound implies the target's conclusion.**  If the normalised counting
function of a `B₂[g]` set stays bounded after multiplication by `(log N) ^ (1/2)`, then its
`liminf` is `0`.

For `g = 1` the hypothesis is the theorem of [ESS94] recorded, unproved, as
`Erdos158.erdos_158.variants.isSidon'`, and this lemma is the `B₂[g]` generalisation of the pool
file's derivation of `Erdos158.erdos_158.variants.isSidon` from it, with the Sidon hypothesis
replaced by `B2 g` and the pool file's hand-rolled `csSup` computation replaced by
`liminf_ne_zero_iff`.  For `g = 2` the hypothesis is *open*: it is a sufficient condition for the
target's conclusion, not a reformulation of it, and the converse is not proved here. -/
theorem liminf_eq_zero_of_liminf_mul_sqrt_log_lt_top (hA : B2 g A)
    (h : liminf (fun N : ℕ => ENNReal.ofReal (((A ∩ Set.Iio N).ncard : ℝ)
      * (N : ℝ) ^ (- 1 / 2 : ℝ) * Real.log N ^ (1 / 2 : ℝ))) atTop < ⊤) :
    liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 := by
  by_contra hne
  obtain ⟨c, hc, hev⟩ := (liminf_ne_zero_iff hA).1 hne
  have hlog : Tendsto (fun N : ℕ => Real.log N ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hbig : Tendsto (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)
      * Real.log N ^ (1 / 2 : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop (f₁ := fun N : ℕ => c * Real.log N ^ (1 / 2 : ℝ)) ?_
      (hlog.const_mul_atTop hc)
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    have hLnn : (0 : ℝ) ≤ Real.log N ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) _
    exact mul_le_mul_of_nonneg_right hN hLnn
  have hten : Tendsto (fun N : ℕ => ENNReal.ofReal (((A ∩ Set.Iio N).ncard : ℝ)
      * (N : ℝ) ^ (- 1 / 2 : ℝ) * Real.log N ^ (1 / 2 : ℝ))) atTop (nhds ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp hbig
  rw [hten.liminf_eq] at h
  exact lt_irrefl _ h

/-- **Use site 2.**  The interface of `liminf_eq_zero_of_liminf_mul_sqrt_log_lt_top` applied to
the target verbatim: proving the `B₂[2]` analogue of [ESS94] settles the right-hand side of
`Erdos158.erdos_158`, hence the target itself with the answer `True`. -/
theorem erdos_158_rhs_of_sqrt_log_bound
    (h : ∀ A : Set ℕ, A.Infinite → B2 2 A →
      liminf (fun N : ℕ => ENNReal.ofReal (((A ∩ Set.Iio N).ncard : ℝ)
        * (N : ℝ) ^ (- 1 / 2 : ℝ) * Real.log N ^ (1 / 2 : ℝ))) atTop < ⊤) :
    ∀ A : Set ℕ, A.Infinite → B2 2 A →
      liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop = 0 :=
  fun A hinf hA => liminf_eq_zero_of_liminf_mul_sqrt_log_lt_top hA (h A hinf hA)

/- ## The `B₂[2]` hypothesis cannot be dropped: the squares -/

/-- The set of perfect squares. -/
def squares : Set ℕ := Set.range fun k : ℕ => k ^ 2

/-- There are exactly `⌊√N⌋ + 1` squares below `N + 1`. -/
theorem ncard_squares_inter_Iio (N : ℕ) :
    (squares ∩ Set.Iio (N + 1)).ncard = Nat.sqrt N + 1 := by
  have h : squares ∩ Set.Iio (N + 1) = (fun k : ℕ => k ^ 2) '' Set.Iic (Nat.sqrt N) := by
    ext n
    simp only [squares, Set.mem_inter_iff, Set.mem_range, Set.mem_Iio, Set.mem_image, Set.mem_Iic]
    constructor
    · rintro ⟨⟨k, rfl⟩, hlt⟩
      exact ⟨k, Nat.le_sqrt'.2 (by omega), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, rfl⟩, ?_⟩
      have h1 := Nat.sqrt_le' N
      have h2 : k ^ 2 ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left hk 2
      omega
  rw [h, Set.ncard_image_of_injective _
      (fun a b hab => by simpa using Nat.pow_left_injective (by norm_num) hab),
    show Set.Iic (Nat.sqrt N) = ↑(Finset.Iic (Nat.sqrt N)) by simp,
    Set.ncard_coe_finset, Nat.card_Iic]

/-- Sandwich for the normalised counting function of the squares: it lies between `1` and
`1 + 1 / √N`. -/
theorem squares_normalized_bounds (M : ℕ) :
    1 ≤ ((squares ∩ Set.Iio (M + 1)).ncard : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (- 1 / 2 : ℝ) ∧
      ((squares ∩ Set.Iio (M + 1)).ncard : ℝ) * ((M + 1 : ℕ) : ℝ) ^ (- 1 / 2 : ℝ)
        ≤ 1 + 1 / Real.sqrt ((M : ℝ) + 1) := by
  have hpos : (0 : ℝ) < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hcast : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
  rw [normalized_eq, ncard_squares_inter_Iio, hcast]
  set s : ℕ := Nat.sqrt M with hs
  have hle : Real.sqrt ((M : ℝ) + 1) ≤ (s : ℝ) + 1 := by
    have h1 : (M : ℝ) + 1 ≤ ((s : ℝ) + 1) ^ 2 := by
      have hn : M + 1 ≤ (s + 1) ^ 2 := Nat.lt_succ_sqrt' M
      exact_mod_cast hn
    calc Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt (((s : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (s : ℝ) + 1 := Real.sqrt_sq (by positivity)
  have hge : (s : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) := by
    have h1 : ((s : ℝ)) ^ 2 ≤ (M : ℝ) + 1 := by
      have hn : (s : ℕ) ^ 2 ≤ M := Nat.sqrt_le' M
      have : ((s : ℝ)) ^ 2 ≤ (M : ℝ) := by exact_mod_cast hn
      linarith
    calc (s : ℝ) = Real.sqrt (((s : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((M : ℝ) + 1) := Real.sqrt_le_sqrt h1
  constructor
  · rw [le_div_iff₀ hpos]
    push_cast
    linarith
  · rw [div_le_iff₀ hpos]
    push_cast
    field_simp
    nlinarith [hpos, hge, hle]

/-- The normalised counting function of the squares converges to `1`. -/
theorem tendsto_squares_normalized :
    Tendsto (fun N : ℕ => ((squares ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ))
      atTop (nhds 1) := by
  have hsq : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun N : ℕ => 1 + 1 / Real.sqrt N) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (hsq.const_div_atTop (1 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    exact (squares_normalized_bounds M).1
  · filter_upwards [eventually_ge_atTop 1] with N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hb := (squares_normalized_bounds M).2
    have hc : (((M + 1 : ℕ) : ℝ)) = (M : ℝ) + 1 := by push_cast; ring
    rw [hc] at hb ⊢
    exact hb

/-- The squares are not a `B₂[2]` set: `325 = 1 + 324 = 36 + 289 = 100 + 225` gives three
representations. -/
theorem not_b2_two_squares : ¬ B2 2 squares := by
  intro h
  have hs : ∀ k : ℕ, (k ^ 2 : ℕ) ∈ squares := fun k => ⟨k, rfl⟩
  have hsub : ({(1, 324), (36, 289), (100, 225)} : Set (ℕ × ℕ)) ⊆
      {x : ℕ × ℕ | x.1 + x.2 = 325 ∧ x.1 ≤ x.2 ∧ x.1 ∈ squares ∧ x.2 ∈ squares} := by
    rintro x (rfl | rfl | rfl)
    · exact ⟨by norm_num, by norm_num, by simpa using hs 1, by simpa using hs 18⟩
    · exact ⟨by norm_num, by norm_num, by simpa using hs 6, by simpa using hs 17⟩
    · exact ⟨by norm_num, by norm_num, by simpa using hs 10, by simpa using hs 15⟩
  have hcard : ({(1, 324), (36, 289), (100, 225)} : Set (ℕ × ℕ)).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by simp), Set.encard_pair (by simp)]
    rfl
  have hcon := (Set.encard_le_encard hsub).trans (h 325)
  rw [hcard] at hcon
  norm_num at hcon

/-- **The `B₂[2]` hypothesis in `Erdos158.erdos_158` is necessary.**  Deleting it leaves a false
statement: the squares are infinite, are not `B₂[2]`, and their normalised counting function has
`liminf` equal to `1`.  Note that `Set.univ` would *not* witness this, by
`liminf_univ_eq_zero`. -/
theorem exists_infinite_liminf_ne_zero :
    ∃ A : Set ℕ, A.Infinite ∧ ¬ B2 2 A ∧
      liminf (fun N : ℕ => ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ)) atTop ≠ 0 := by
  refine ⟨squares, Set.infinite_range_of_injective fun a b hab => by
    simpa using Nat.pow_left_injective (by norm_num) hab, not_b2_two_squares, ?_⟩
  rw [tendsto_squares_normalized.liminf_eq]
  norm_num

/- ## `B₂[2]` is strictly weaker than Sidon: an infinite witness family -/

/-- `doubleBlocks B = 2 * B ∪ (2 * B + 1)`: replace each `b ∈ B` by the block `{2b, 2b+1}`. -/
def doubleBlocks (B : Set ℕ) : Set ℕ := (fun b => 2 * b) '' B ∪ (fun b => 2 * b + 1) '' B

/-- An element lies in `doubleBlocks B` exactly when the block it belongs to is indexed by `B`. -/
theorem mem_doubleBlocks {B : Set ℕ} {n : ℕ} : n ∈ doubleBlocks B ↔ n / 2 ∈ B := by
  constructor
  · rintro (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩) <;>
      simpa [show ∀ b : ℕ, 2 * b / 2 = b from fun b => by omega,
        show ∀ b : ℕ, (2 * b + 1) / 2 = b from fun b => by omega] using hb
  · intro h
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with he | ho
    · exact Or.inl ⟨n / 2, h, by show 2 * (n / 2) = n; omega⟩
    · exact Or.inr ⟨n / 2, h, by show 2 * (n / 2) + 1 = n; omega⟩

/-- **The block-doubling of a Sidon set is `B₂[2]`.**  Splitting the representations of `n` by
the parity of the smaller summand, the Sidon property of `B` makes each of the two classes a
singleton. -/
theorem b2_two_doubleBlocks {B : Set ℕ} (hB : IsSidon B) : B2 2 (doubleBlocks B) := by
  intro n
  have key : ∀ r : ℕ,
      {x : ℕ × ℕ | (x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ doubleBlocks B ∧ x.2 ∈ doubleBlocks B) ∧
        x.1 % 2 = r}.encard ≤ 1 := by
    intro r
    refine Set.encard_le_one_iff.2 ?_
    rintro x y ⟨⟨hx1, hx2, hx3, hx4⟩, hxr⟩ ⟨⟨hy1, hy2, hy3, hy4⟩, hyr⟩
    rw [mem_doubleBlocks] at hx3 hx4 hy3 hy4
    have hsum : x.1 / 2 + x.2 / 2 = y.1 / 2 + y.2 / 2 := by omega
    rcases hB _ hx3 _ hy3 _ hx4 _ hy4 hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact Prod.ext_iff.2 ⟨by omega, by omega⟩
  have hsub : {x : ℕ × ℕ | x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ doubleBlocks B ∧
        x.2 ∈ doubleBlocks B} ⊆
      {x : ℕ × ℕ | (x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ doubleBlocks B ∧
          x.2 ∈ doubleBlocks B) ∧ x.1 % 2 = 0} ∪
      {x : ℕ × ℕ | (x.1 + x.2 = n ∧ x.1 ≤ x.2 ∧ x.1 ∈ doubleBlocks B ∧
          x.2 ∈ doubleBlocks B) ∧ x.1 % 2 = 1} := by
    intro x hx
    rcases (show x.1 % 2 = 0 ∨ x.1 % 2 = 1 by omega) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  refine (Set.encard_le_encard hsub).trans ?_
  refine (Set.encard_union_le _ _).trans ?_
  calc _ ≤ (1 : ℕ∞) + 1 := add_le_add (key 0) (key 1)
    _ ≤ ((2 : ℕ) : ℕ∞) := by norm_num

/-- The block-doubling of a set with two distinct elements is never Sidon: it has the collision
`2b + (2b' + 1) = 2b' + (2b + 1)`. -/
theorem not_isSidon_doubleBlocks {B : Set ℕ} {b b' : ℕ} (hb : b ∈ B) (hb' : b' ∈ B)
    (hne : b ≠ b') : ¬ IsSidon (doubleBlocks B) := by
  intro h
  have h1 : 2 * b ∈ doubleBlocks B := Or.inl ⟨b, hb, rfl⟩
  have h2 : 2 * b' ∈ doubleBlocks B := Or.inl ⟨b', hb', rfl⟩
  have h3 : 2 * b' + 1 ∈ doubleBlocks B := Or.inr ⟨b', hb', rfl⟩
  have h4 : 2 * b + 1 ∈ doubleBlocks B := Or.inr ⟨b, hb, rfl⟩
  rcases h _ h1 _ h2 _ h3 _ h4 (by ring) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> omega

/-- Block-doubling preserves infiniteness. -/
theorem infinite_doubleBlocks {B : Set ℕ} (hB : B.Infinite) : (doubleBlocks B).Infinite :=
  Set.Infinite.mono Set.subset_union_left
    (hB.image (Set.injOn_of_injective (fun a b hab => by omega)))

/-- Block-doubling exactly doubles the counting function:
`|doubleBlocks B ∩ [0, 2N)| = 2 * |B ∩ [0, N)|`.  In the normalisation used by the target this
multiplies the counting function by `√2`, so these non-Sidon `B₂[2]` sets are genuinely denser
than the Sidon sets they come from. -/
theorem ncard_doubleBlocks_inter_Iio (B : Set ℕ) (N : ℕ) :
    (doubleBlocks B ∩ Set.Iio (2 * N)).ncard = 2 * (B ∩ Set.Iio N).ncard := by
  have hsplit : doubleBlocks B ∩ Set.Iio (2 * N) =
      (fun b => 2 * b) '' (B ∩ Set.Iio N) ∪ (fun b => 2 * b + 1) '' (B ∩ Set.Iio N) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_union, Set.mem_image, mem_doubleBlocks]
    constructor
    · rintro ⟨hn, hlt⟩
      rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h
      · exact Or.inl ⟨n / 2, ⟨hn, by omega⟩, by omega⟩
      · exact Or.inr ⟨n / 2, ⟨hn, by omega⟩, by omega⟩
    · rintro (⟨b, ⟨hb, hbN⟩, rfl⟩ | ⟨b, ⟨hb, hbN⟩, rfl⟩)
      · exact ⟨by rwa [show 2 * b / 2 = b from by omega], by omega⟩
      · exact ⟨by rwa [show (2 * b + 1) / 2 = b from by omega], by omega⟩
  rw [hsplit]
  have hfin : (B ∩ Set.Iio N).Finite :=
    Set.Finite.subset (Set.finite_Iio N) Set.inter_subset_right
  have hd : Disjoint ((fun b => 2 * b) '' (B ∩ Set.Iio N))
      ((fun b => 2 * b + 1) '' (B ∩ Set.Iio N)) := by
    rw [Set.disjoint_left]
    rintro a ⟨b, -, hb2⟩ ⟨c, -, hc2⟩
    have h1 : 2 * b = a := hb2
    have h2 : 2 * c + 1 = a := hc2
    omega
  have hinj1 : Function.Injective (fun b : ℕ => 2 * b) := by
    intro a b hab
    have h : 2 * a = 2 * b := hab
    omega
  have hinj2 : Function.Injective (fun b : ℕ => 2 * b + 1) := by
    intro a b hab
    have h : 2 * a + 1 = 2 * b + 1 := hab
    omega
  rw [Set.ncard_union_eq hd (hfin.image _) (hfin.image _),
    Set.ncard_image_of_injective _ hinj1, Set.ncard_image_of_injective _ hinj2]
  ring

/-- **Use site 3.**  The witness family really is a legal instance of the target's binders — an
infinite `B₂[2]` set that is not Sidon — so a solution to `Erdos158.erdos_158` cannot merely
invoke `Erdos158.erdos_158.variants.isSidon`.  Its `liminf` also lies in `[0, 2 * √2]`. -/
theorem doubleBlocks_mem_target_binders {B : Set ℕ} (hBinf : B.Infinite) (hB : IsSidon B) :
    (doubleBlocks B).Infinite ∧ B2 2 (doubleBlocks B) ∧ ¬ IsSidon (doubleBlocks B) ∧
      liminf (fun N : ℕ => ((doubleBlocks B ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (- 1 / 2 : ℝ))
        atTop ≤ 2 * Real.sqrt 2 := by
  obtain ⟨b, hb, b', hb', hne⟩ : ∃ b ∈ B, ∃ b' ∈ B, b ≠ b' := by
    obtain ⟨b, hb⟩ := hBinf.nonempty
    obtain ⟨b', hb', hne⟩ := (hBinf.diff (Set.finite_singleton b)).nonempty
    exact ⟨b, hb, b', hb', fun h => hne (by simp [h])⟩
  refine ⟨infinite_doubleBlocks hBinf, b2_two_doubleBlocks hB,
    not_isSidon_doubleBlocks hb hb' hne, ?_⟩
  simpa using liminf_le (b2_two_doubleBlocks hB)

end Contribution.Erdos158Counting
