import Mathlib
import FormalConjectures.ErdosProblems.«153»

/-!
# Erdős Problem 153: an infimum-free interface for `Erdos153.f`, attainment, exact values,
and an Erdős–Turán lower bound

Target: `Erdos153.erdos_153`, whose statement is `answer(_) ↔ Tendsto Erdos153.f atTop atTop`,
where `Erdos153.f n` is the infimum, over Sidon sets `A ⊆ ℕ` with `|A| = n`, of
`(1/t) * ∑_{1 ≤ i < t} (s_{i+1} - s_i)^2` for `A + A = {s_1 < ⋯ < s_t}`.

## The obstacle

The problem is open: `Erdos153.erdos_153` is tagged `research open`, and apart from the
definition `Erdos153.f` it is the only declaration in the target module, so there is no solved
companion to prove outright.  Before any analysis can start, `Erdos153.f` has to be made usable,
and it is not: its body is an `⨅` over the *subtype*
`{A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)}` of a term built from
`Finset.orderIsoOfFin`, summed over the coerced sort `↥(Set.Ico 1 (A + A).card)` with a
`Nat`-subtracted index `i - 1` carrying its own inequality proof.  Consequently:

* the number attached to a *single* Sidon set is buried in that dependent sum, out of reach of
  the ordinary `Finset.range` lemmas, until it is re-indexed;
* every lower bound on `f n` needs `le_ciInf`, hence an instance
  `Nonempty {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)}`, i.e. the existence of a Sidon
  set of each cardinality, which neither the target module nor `FormalConjecturesForMathlib`
  records; every upper bound needs `ciInf_le`, hence `BddBelow` of the range;
* an infimum over an infinite family is not a priori attained, so `c < f n` cannot be
  transferred to the individual competitors;
* the search space is infinite: without a cut-off, no exact value of `f n` is computable;
* `Mathlib` contains no `Sidon` material at all (a case-insensitive grep over `Mathlib` for
  `sidon` in the pinned toolchain returns nothing), so every counting fact used below had to be
  proved from scratch.

## What is proved

### Re-indexing and the bridge to the target's definition

* `nth`, with `nth_zero`, `nth_last`, `nth_eq_of_strictMono` and the `ℕ`-indexed interface
  `nth_eq_of_mono`: the monotone enumeration `Finset.orderEmbOfFin : Fin A.card ↪o ℕ` of a
  finite set repackaged as a total function `ℕ → ℕ`, with the API needed to identify it on
  explicit sets by `decide`.  `nth_eq_natNth` records honestly that this function *is* Mathlib's
  `Nat.nth (· ∈ A)`, so results proved here transfer to the `Nat.nth` API and back.
* `gapEnergy A`, the quantity minimised in `Erdos153.f`, as a plain `Finset.range` sum, and
  `f_eq : Erdos153.f n = ⨅ A : …, gapEnergy A.1`.  This is the bridge that makes everything
  below applicable to the target's own definition.
* `exists_isSidon_card` and the resulting `Nonempty` instance, `bddBelow_range_gapEnergy`, and
  the two one-sided rules `f_le_gapEnergy` and `le_f`.
* `tendsto_f_atTop_iff`: `Tendsto Erdos153.f atTop atTop` is *equivalent* to a statement with
  no infimum in it, quantified over individual Sidon sets.

### Normalisation, counting, and attainment

* `isSidon_add_singleton`, `nth_add_singleton`, `gapEnergy_add_singleton` and `exists_translate`:
  translation invariance, letting any competitor be normalised into `Finset.range (D + 1)`,
  `D` its diameter.
* `min'_add`, `max'_add`, `card_add_self_le_choose`, `card_add_self_of_isSidon` and
  `card_sq_le_two_mul_diam`: the sumset and Sidon counting facts.  The middle two pin the
  denominator of `gapEnergy` to `|A + A| = n(n+1)/2` for Sidon `A`; the last is the elementary
  diameter bound `n^2 ≤ n + 2 diam A`.
* `sum_gaps_eq`, `sq_diam_le_card_mul_sum_sq` and `four_mul_diam_sq_le`:
  `4 * diam A ^ 2 ≤ |A + A| * (|A + A| - 1) * gapEnergy A` for every nonempty `A`, Sidon or not.
  This is the engine both for the lower bound and for the finiteness of the search.
* `exists_gapEnergy_eq_f`: **the infimum defining `Erdos153.f n` is attained**, i.e. there is a
  Sidon set `A` with `|A| = n` and `Erdos153.f n = gapEnergy A`.  Consequently `lt_f_iff`:
  `c < Erdos153.f n ↔ ∀ Sidon A of size n, c < gapEnergy A`, whose `←` direction is false for a
  general infimum.

### The elementary lower bound, for comparison

* `real_gap_bound`, `gapEnergy_lower_bound` and `f_lower_bound`:
  `4n(n-1)/((n+1)(n+2)) ≤ Erdos153.f n` for every `n`, by Cauchy–Schwarz against the telescoped
  gap sum, fed with the elementary diameter bound.  `real_gap_bound` takes the diameter bound as
  a *parameter*, so a sharper Sidon diameter estimate upgrades the constant with no change to
  the rest.  This bound is exact at `n = 2` (it equals `f_two`).
* `lower_bound_lt_four`: the bound of `f_lower_bound` is `< 4` for every `n`, so this route
  cannot on its own decide the conjecture.  The rest of the file replaces that `4` by `16`.

### The Erdős–Turán inequality for Sidon sets

* `windowCount`, `sum_windowCount`, `sum_windowCount_sq`, `two_mul_sum_Ico`,
  `two_mul_sum_lower_le`, `sum_pairs_le` and `erdos_turan_ineq`:
  for a Sidon set `A ⊆ [0, N]` and any `l ≥ 1`,
  `|A|^2 * l ≤ (N + l) * (|A| + l - 1)`.
  This is the Erdős–Turán window estimate, double counting `∑_x |A ∩ (x - l, x]|` and its square
  against Cauchy–Schwarz; the Sidon hypothesis enters exactly once, as injectivity of
  `(a, b) ↦ a - b` on ordered pairs, in `two_mul_sum_lower_le`.
* `card_sq_mul_le_of_isSidon` and `diam_ge_of_isSidon`: taking `l = m * |A|` turns this into
  `m * n^2 ≤ (diam A + m * n) * (m + 1)`, i.e. `diam A ≥ m n^2/(m+1) - m n`.  Where
  `card_sq_le_two_mul_diam` gives only `diam A ≥ n(n-1)/2`, this gives, for each fixed `m` and
  all large `n`, `diam A ≥ (m/(m+1)) n^2 - m n`, so the leading constant can be pushed
  arbitrarily close to `1` instead of `1/2`; squaring that factor `2` in the Cauchy–Schwarz step
  is what turns `4` into `16`.

### The consequence for the target

* `real_sixteen_bound` (the arithmetic core, stated with the diameter estimate and the
  Cauchy–Schwarz estimate as parameters) and `f_lower_bound_param`: for `1 ≤ m` and `m + 1 ≤ n`,
  `16 * (m/(m+1))^2 * ((n - m - 1)/(n+1))^2 ≤ Erdos153.f n`.
* `real_ab_bound` and `eventually_le_f`: for every `c < 16`, `c ≤ Erdos153.f n` for all large
  `n` — against the `c < 4` that `f_lower_bound` and `lower_bound_lt_four` give.
  `param_lt_sixteen` records honestly that `16` is in turn the ceiling of this argument — every
  instance of `f_lower_bound_param` is `< 16` — so it too cannot on its own decide the
  conjecture.

### Exact values

* `f_eq_of_search`: a reusable **finite-search principle**.  If some Sidon set of size `n` has
  gap energy `v`, if every Sidon set of size `n` inside `Finset.range (D + 1)` has gap energy at
  least `v`, and if `|A+A|(|A+A|-1) v ≤ 4 (D+1)^2` (so that a competitor of energy `< v` must
  have diameter `≤ D`), then `Erdos153.f n = v`.
* `f_two : Erdos153.f 2 = 2/3`, `f_three : Erdos153.f 3 = 4/3` and `f_four : Erdos153.f 4 = 9/5`:
  exact values of the target's own function, each obtained from `f_eq_of_search` together with a
  `decide` classification of the Sidon sets in the relevant window
  (`{0,1}`; `{0,1,3}`, `{0,2,3}`; `{0,1,4,6}`, `{0,2,5,6}`) and the gap-energy computations
  `gapEnergy_zero_one`, `gapEnergy_zero_one_three`, `gapEnergy_zero_two_three`,
  `gapEnergy_zero_one_four_six`, `gapEnergy_zero_two_five_six`.

A later solver can use declaration `Contribution.Erdos153Gaps.tendsto_f_atTop_iff` to discharge
or simplify obligation `Tendsto Erdos153.f atTop atTop` in target `Erdos153.erdos_153`.

*References:*
- [erdosproblems.com/153](https://www.erdosproblems.com/153)
- [ESS94] Erdős, P. and Sárközy, A. and Sós, T., On Sum Sets of Sidon Sets, I.
  Journal of Number Theory (1994), 329-347.
-/

namespace Contribution.Erdos153Gaps

open scoped Pointwise
open Filter Finset

/- ### The `i`-th smallest element of a `Finset ℕ` -/

/-- `nth A i` is the `i`-th smallest element of `A` (0-indexed), and `0` when `A.card ≤ i`.
This is `Finset.orderEmbOfFin` made total, so that it can be summed over `Finset.range`. -/
noncomputable def nth (A : Finset ℕ) (i : ℕ) : ℕ :=
  if h : i < A.card then A.orderEmbOfFin rfl ⟨i, h⟩ else 0

theorem nth_eq (A : Finset ℕ) {i : ℕ} (h : i < A.card) :
    nth A i = A.orderEmbOfFin rfl ⟨i, h⟩ := dif_pos h

theorem nth_zero {A : Finset ℕ} (h : A.Nonempty) : nth A 0 = A.min' h := by
  rw [nth_eq A (Finset.card_pos.2 h)]
  exact Finset.orderEmbOfFin_zero rfl _

theorem nth_last {A : Finset ℕ} (h : A.Nonempty) : nth A (A.card - 1) = A.max' h := by
  rw [nth_eq A (by have := Finset.card_pos.2 h; omega)]
  exact Finset.orderEmbOfFin_last rfl (Finset.card_pos.2 h)

/-- The only strictly monotone enumeration of `A` by `Fin A.card` is `nth A`. -/
theorem nth_eq_of_strictMono {A : Finset ℕ} {k : ℕ} (hk : A.card = k) {g : Fin k → ℕ}
    (hmem : ∀ x, g x ∈ A) (hmono : StrictMono g) {i : ℕ} (hi : i < k) :
    nth A i = g ⟨i, hi⟩ := by
  subst hk
  rw [nth_eq A hi, ← Finset.orderEmbOfFin_unique rfl hmem hmono]

/-- `ℕ`-indexed form of `nth_eq_of_strictMono`: both hypotheses are bounded quantifiers over
`ℕ`, hence decidable, so `nth` can be read off an explicit finite set by `decide`. -/
theorem nth_eq_of_mono {A : Finset ℕ} {k : ℕ} (hk : A.card = k) {g : ℕ → ℕ}
    (hmem : ∀ i, i < k → g i ∈ A) (hmono : ∀ j, j < k → ∀ i, i < j → g i < g j)
    {i : ℕ} (hi : i < k) : nth A i = g i := by
  refine nth_eq_of_strictMono hk (g := fun x : Fin k => g x) (fun x => hmem x x.2) ?_ hi
  intro x y hxy
  exact hmono y y.2 x hxy

/-- Honest identification with the standard library: `nth A` is Mathlib's `Nat.nth (· ∈ A)`.
The definition above is kept because it is the form in which `decide` can evaluate it and
because it avoids carrying a `Set.Finite` argument through every statement; this lemma lets any
result here be transported to the `Nat.nth` API and back. -/
theorem nth_eq_natNth (A : Finset ℕ) (i : ℕ) : nth A i = Nat.nth (· ∈ A) i := by
  have hf : (setOf (· ∈ A)).Finite := A.finite_toSet
  have hFT : hf.toFinset = A := by
    ext x
    exact hf.mem_toFinset.trans Iff.rfl
  have hc : hf.toFinset.card = A.card := congrArg Finset.card hFT
  by_cases h : i < A.card
  · rw [nth, dif_pos h]
    have key := Finset.orderEmbOfFin_unique (s := A) (k := A.card) rfl
      (f := fun j : Fin A.card => Nat.nth (· ∈ A) (j : ℕ))
      (fun x => Nat.nth_mem_of_lt_card hf (lt_of_lt_of_eq x.2 hc.symm))
      (fun x y hxy => Nat.nth_strictMonoOn hf
        (by simp only [Set.mem_Iio]; exact lt_of_lt_of_eq x.2 hc.symm)
        (by simp only [Set.mem_Iio]; exact lt_of_lt_of_eq y.2 hc.symm) hxy)
    exact (congrFun key ⟨i, h⟩).symm
  · rw [nth, dif_neg h, Nat.nth_of_card_le hf (hc.trans_le (by omega))]

/- ### The quantity minimised in `Erdos153.f` -/

/-- `gapEnergy A = (1/t) ∑_{1 ≤ i < t} (s_{i+1} - s_i)^2` where `A + A = {s_1 < ⋯ < s_t}`:
the quantity whose infimum over Sidon sets of size `n` is `Erdos153.f n`, written as an
ordinary sum over `Finset.range`. -/
noncomputable def gapEnergy (A : Finset ℕ) : ℝ :=
  (∑ i ∈ Finset.range ((A + A).card - 1),
      ((nth (A + A) (i + 1) : ℝ) - (nth (A + A) i : ℝ)) ^ 2) / ((A + A).card : ℝ)

theorem gapEnergy_nonneg (A : Finset ℕ) : 0 ≤ gapEnergy A :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)

/-- **The bridge.**  The target's `Erdos153.f` is the infimum of `gapEnergy`. -/
theorem f_eq (n : ℕ) :
    Erdos153.f n = ⨅ A : {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)}, gapEnergy A.1 := by
  unfold Erdos153.f
  refine iInf_congr fun A => ?_
  dsimp only [gapEnergy]
  set B : Finset ℕ := (A : Finset ℕ) + (A : Finset ℕ) with hBdef
  congr 1
  calc _ = ∑ i : ↥(Set.Ico 1 B.card), ((nth B (i : ℕ) : ℝ) - (nth B ((i : ℕ) - 1) : ℝ)) ^ 2 :=
        Finset.sum_congr rfl fun i _ => by
          have h1 : (i : ℕ) < B.card := i.2.2
          have h2 : (i : ℕ) - 1 < B.card := by omega
          rw [nth_eq B h1, nth_eq B h2]
          simp only [Finset.coe_orderIsoOfFin_apply]
          rfl
    _ = ∑ j ∈ Finset.range (B.card - 1), ((nth B (j + 1) : ℝ) - (nth B j : ℝ)) ^ 2 := by
          rw [← Finset.sum_subtype (Finset.Ico 1 B.card) (by simp)
              (fun i => ((nth B i : ℝ) - (nth B (i - 1) : ℝ)) ^ 2), Finset.sum_Ico_eq_sum_range]
          refine Finset.sum_congr rfl fun j _ => ?_
          have h : 1 + j = j + 1 := by omega
          rw [h]
          simp

/- ### The index type of the infimum is nonempty and the family is bounded below -/

/-- There is a Sidon set of every cardinality. -/
theorem exists_isSidon_card (n : ℕ) : ∃ A : Finset ℕ, A.card = n ∧ IsSidon (A : Set ℕ) := by
  induction n with
  | zero => exact ⟨∅, by simp, by simp [IsSidon]⟩
  | succ k ih =>
    obtain ⟨A, hcard, hA⟩ := ih
    rcases Finset.eq_empty_or_nonempty A with rfl | hne
    · refine ⟨{0}, ?_, by simp [IsSidon]⟩
      simp at hcard
      simp [← hcard]
    · refine ⟨A ∪ {2 * A.max' hne + 1}, ?_,
        by simpa using Finset.IsSidon.insert_ge_max' hne hA le_rfl⟩
      have hs : 2 * A.max' hne + 1 ∉ A := fun h => by have := A.le_max' _ h; omega
      rw [Finset.union_comm, Finset.singleton_union, Finset.card_insert_of_notMem hs, hcard]

instance instNonemptySidonOfCard (n : ℕ) :
    Nonempty {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)} :=
  let ⟨A, h1, h2⟩ := exists_isSidon_card n
  ⟨⟨A, h1, h2⟩⟩

theorem bddBelow_range_gapEnergy (n : ℕ) :
    BddBelow (Set.range fun A : {A : Finset ℕ | A.card = n ∧ IsSidon (A : Set ℕ)} =>
      gapEnergy A.1) := by
  refine ⟨0, ?_⟩
  rintro x ⟨A, rfl⟩
  exact gapEnergy_nonneg _

/-- Upper bounds on `Erdos153.f n`: any single Sidon set of size `n` gives one. -/
theorem f_le_gapEnergy {n : ℕ} {A : Finset ℕ} (hcard : A.card = n) (hA : IsSidon (A : Set ℕ)) :
    Erdos153.f n ≤ gapEnergy A := by
  rw [f_eq]
  exact ciInf_le (bddBelow_range_gapEnergy n) ⟨A, hcard, hA⟩

/-- Lower bounds on `Erdos153.f n`: a uniform bound over all Sidon sets of size `n`. -/
theorem le_f {n : ℕ} {c : ℝ} (h : ∀ A : Finset ℕ, A.card = n → IsSidon (A : Set ℕ) →
    c ≤ gapEnergy A) : c ≤ Erdos153.f n := by
  rw [f_eq]
  exact le_ciInf fun A => h A.1 A.2.1 A.2.2

theorem f_nonneg (n : ℕ) : 0 ≤ Erdos153.f n := le_f fun A _ _ => gapEnergy_nonneg A

/-- **The infimum-free form of the target's right-hand side.** -/
theorem tendsto_f_atTop_iff :
    Tendsto Erdos153.f atTop atTop ↔
      ∀ c : ℝ, ∀ᶠ n in atTop, ∀ A : Finset ℕ, A.card = n → IsSidon (A : Set ℕ) →
        c ≤ gapEnergy A := by
  rw [Filter.tendsto_atTop]
  refine ⟨fun h c => ?_, fun h c => ?_⟩
  · filter_upwards [h c] with n hn A hcard hA
    exact hn.trans (f_le_gapEnergy hcard hA)
  · filter_upwards [h c] with n hn
    exact le_f hn

/- ### Translation invariance -/

theorem isSidon_add_singleton {A : Finset ℕ} {d : ℕ} :
    IsSidon ((A + ({d} : Finset ℕ) : Finset ℕ) : Set ℕ) ↔ IsSidon (A : Set ℕ) := by
  have hmem : ∀ x : ℕ, x ∈ ((A + ({d} : Finset ℕ) : Finset ℕ) : Set ℕ) ↔ ∃ a ∈ A, a + d = x := by
    intro x
    rw [Finset.mem_coe, Finset.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      rw [Finset.mem_singleton] at hb
      subst hb
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, d, Finset.mem_singleton_self _, rfl⟩
  constructor
  · intro h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    have hh := h (i₁ + d) ((hmem _).2 ⟨i₁, Finset.mem_coe.1 hi₁, rfl⟩)
      (j₁ + d) ((hmem _).2 ⟨j₁, Finset.mem_coe.1 hj₁, rfl⟩)
      (i₂ + d) ((hmem _).2 ⟨i₂, Finset.mem_coe.1 hi₂, rfl⟩)
      (j₂ + d) ((hmem _).2 ⟨j₂, Finset.mem_coe.1 hj₂, rfl⟩) (by omega)
    omega
  · intro h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    obtain ⟨a₁, ha₁, rfl⟩ := (hmem _).1 hi₁
    obtain ⟨b₁, hb₁, rfl⟩ := (hmem _).1 hj₁
    obtain ⟨a₂, ha₂, rfl⟩ := (hmem _).1 hi₂
    obtain ⟨b₂, hb₂, rfl⟩ := (hmem _).1 hj₂
    have hh := h a₁ (Finset.mem_coe.2 ha₁) b₁ (Finset.mem_coe.2 hb₁) a₂ (Finset.mem_coe.2 ha₂)
      b₂ (Finset.mem_coe.2 hb₂) (by omega)
    omega

theorem nth_add_singleton (B : Finset ℕ) (d : ℕ) {i : ℕ} (hi : i < B.card) :
    nth (B + ({d} : Finset ℕ)) i = nth B i + d := by
  have hcard : (B + ({d} : Finset ℕ)).card = B.card := Finset.card_add_singleton B d
  rw [nth_eq B hi]
  refine nth_eq_of_strictMono hcard (g := fun j : Fin B.card => B.orderEmbOfFin rfl j + d)
    (fun x => ?_) (fun x y hxy => ?_) hi
  · exact Finset.mem_add.2 ⟨_, B.orderEmbOfFin_mem rfl x, d, Finset.mem_singleton_self _, rfl⟩
  · simpa using (B.orderEmbOfFin rfl).strictMono hxy

theorem gapEnergy_add_singleton (A : Finset ℕ) (d : ℕ) :
    gapEnergy (A + ({d} : Finset ℕ)) = gapEnergy A := by
  have hAA : (A + ({d} : Finset ℕ)) + (A + ({d} : Finset ℕ))
      = (A + A) + ({d + d} : Finset ℕ) := by
    rw [add_add_add_comm, Finset.singleton_add_singleton]
  have hcard : ((A + A) + ({d + d} : Finset ℕ)).card = (A + A).card :=
    Finset.card_add_singleton _ _
  rw [gapEnergy, gapEnergy, hAA, hcard]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [nth_add_singleton _ _ (show i + 1 < (A + A).card by omega),
    nth_add_singleton _ _ (show i < (A + A).card by omega)]
  push_cast
  ring

/-- **Normalisation.**  Every nonempty Sidon set can be translated into
`Finset.range (diam + 1)` without changing its cardinality, its Sidon property or its gap
energy.  This is what makes the search for a minimiser finite. -/
theorem exists_translate {A : Finset ℕ} (hne : A.Nonempty) (hA : IsSidon (A : Set ℕ)) :
    ∃ B : Finset ℕ, B ⊆ Finset.range (A.max' hne - A.min' hne + 1) ∧ B.card = A.card ∧
      IsSidon (B : Set ℕ) ∧ gapEnergy B = gapEnergy A := by
  have hkey : A.image (· - A.min' hne) + ({A.min' hne} : Finset ℕ) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, b, hb, rfl⟩ := Finset.mem_add.1 hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      rw [Finset.mem_singleton] at hb
      subst hb
      have h1 := A.min'_le a ha
      have h2 : a - A.min' hne + A.min' hne = a := by omega
      rw [h2]
      exact ha
    · intro hx
      refine Finset.mem_add.2 ⟨x - A.min' hne, Finset.mem_image.2 ⟨x, hx, rfl⟩,
        A.min' hne, Finset.mem_singleton_self _, ?_⟩
      have := A.min'_le x hx
      omega
  refine ⟨A.image (· - A.min' hne), ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have h1 := A.le_max' a ha
    have h2 := A.min'_le a ha
    rw [Finset.mem_range]
    omega
  · have h := Finset.card_add_singleton (A.image (· - A.min' hne)) (A.min' hne)
    rw [hkey] at h
    exact h.symm
  · have h : IsSidon ((A.image (· - A.min' hne) + ({A.min' hne} : Finset ℕ) :
        Finset ℕ) : Set ℕ) := by
      rw [hkey]
      exact hA
    exact isSidon_add_singleton.1 h
  · have h := gapEnergy_add_singleton (A.image (· - A.min' hne)) (A.min' hne)
    rw [hkey] at h
    exact h.symm

/- ### Sumset counting -/

theorem min'_add {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty) (hAB : (A + B).Nonempty) :
    (A + B).min' hAB = A.min' hA + B.min' hB := by
  refine le_antisymm (Finset.min'_le _ _ ?_) (Finset.le_min' _ _ _ ?_)
  · exact Finset.mem_add.2 ⟨_, A.min'_mem hA, _, B.min'_mem hB, rfl⟩
  · rintro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
    exact Nat.add_le_add (A.min'_le _ ha) (B.min'_le _ hb)

theorem max'_add {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty) (hAB : (A + B).Nonempty) :
    (A + B).max' hAB = A.max' hA + B.max' hB := by
  refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ ?_)
  · rintro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hx
    exact Nat.add_le_add (A.le_max' _ ha) (B.le_max' _ hb)
  · exact Finset.mem_add.2 ⟨_, A.max'_mem hA, _, B.max'_mem hB, rfl⟩

/-- A sumset `A + A` has at most `(|A| + 1) choose 2` elements: the sums are indexed by
unordered pairs.  (`Finset.card_add_le` only gives the weaker bound `|A|^2`.) -/
theorem card_add_self_le_choose (A : Finset ℕ) : (A + A).card ≤ (A.card + 1).choose 2 := by
  rw [← Finset.card_sym2]
  refine Finset.card_le_card_of_surjOn
    (Sym2.lift ⟨fun x y => x + y, fun x y => Nat.add_comm x y⟩) ?_
  rintro x hx
  simp only [Finset.coe_add, Set.mem_add, Finset.mem_coe] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨s(a, b), by simp [ha, hb], by simp⟩

/-- For a *Sidon* set the bound of `card_add_self_le_choose` is an equality: the sums `a + b`
are pairwise distinct apart from the coincidence `a + b = b + a`. -/
theorem card_add_self_of_isSidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) :
    (A + A).card = (A.card + 1).choose 2 := by
  refine le_antisymm (card_add_self_le_choose A) ?_
  rw [← Finset.card_sym2]
  refine Finset.card_le_card_of_injOn
    (Sym2.lift ⟨fun x y => x + y, fun x y => Nat.add_comm x y⟩) ?_ ?_
  · rintro z hz
    induction z using Sym2.ind with
    | _ a b =>
      simp only [Finset.mem_coe, Finset.mk_mem_sym2_iff] at hz
      exact Finset.mem_coe.2 (Finset.mem_add.2 ⟨a, hz.1, b, hz.2, rfl⟩)
  · refine Sym2.ind fun a b => ?_
    intro hz
    refine Sym2.ind (fun c d => ?_)
    intro hw hEq
    simp only [Finset.mem_coe, Finset.mk_mem_sym2_iff] at hz hw
    simp only [Sym2.lift_mk] at hEq
    rcases hA a hz.1 c hw.1 b hz.2 d hw.2 hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]

/-- **The elementary diameter bound.**  A Sidon set of size `n` has diameter at least
`n(n-1)/2`: its `n(n-1)` ordered differences are pairwise distinct nonzero integers of absolute
value at most the diameter.  `diam_ge_of_isSidon` below improves the leading constant. -/
theorem card_sq_le_two_mul_diam {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (h : A.Nonempty) :
    A.card * A.card ≤ A.card + 2 * (A.max' h - A.min' h) := by
  set D := A.max' h - A.min' h with hD
  have key : A.offDiag.card ≤ ((Finset.Icc (-(D : ℤ)) (D : ℤ)).erase 0).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p.1 : ℤ) - (p.2 : ℤ)) ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_coe, Finset.mem_offDiag] at hp
      obtain ⟨ha, hb, hab⟩ := hp
      have h1 := A.min'_le a ha
      have h2 := A.le_max' a ha
      have h3 := A.min'_le b hb
      have h4 := A.le_max' b hb
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc]
      exact ⟨sub_ne_zero.2 (by exact_mod_cast hab), by omega, by omega⟩
    · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hEq
      simp only [Finset.mem_coe, Finset.mem_offDiag] at hp hq
      obtain ⟨ha, hb, hab⟩ := hp
      obtain ⟨hc, hd, _⟩ := hq
      simp only at hEq
      have hsum : a + d = c + b := by omega
      rcases hA a ha c hc d hd b hb hsum with ⟨h1, h2⟩ | ⟨h1, _⟩
      · simp [h1, h2]
      · exact absurd h1 hab
  rw [Finset.offDiag_card, Finset.card_erase_of_mem (by simp), Int.card_Icc] at key
  have hD2 : ((D : ℤ) + 1 - -(D : ℤ)).toNat = 2 * D + 1 := by omega
  rw [hD2] at key
  have hcard : A.card ≤ A.card * A.card := Nat.le_mul_of_pos_left _ (Finset.card_pos.2 h)
  omega

/- ### Cauchy–Schwarz on the gaps of `A + A` -/

/-- The consecutive gaps of `A + A` telescope to twice the diameter of `A`. -/
theorem sum_gaps_eq {A : Finset ℕ} (hne : A.Nonempty) :
    ∑ i ∈ Finset.range ((A + A).card - 1), ((nth (A + A) (i + 1) : ℝ) - (nth (A + A) i : ℝ))
      = 2 * ((A.max' hne : ℝ) - (A.min' hne : ℝ)) := by
  have hBne : (A + A).Nonempty := hne.add hne
  rw [Finset.sum_range_sub (fun i => (nth (A + A) i : ℝ)) ((A + A).card - 1),
    nth_last hBne, nth_zero hBne, max'_add hne hne hBne, min'_add hne hne hBne]
  push_cast
  ring

/-- Cauchy–Schwarz against the telescoped gap sum. -/
theorem sq_diam_le_card_mul_sum_sq {A : Finset ℕ} (hne : A.Nonempty) :
    (2 * ((A.max' hne : ℝ) - (A.min' hne : ℝ))) ^ 2
      ≤ (((A + A).card : ℝ) - 1) * ∑ i ∈ Finset.range ((A + A).card - 1),
          ((nth (A + A) (i + 1) : ℝ) - (nth (A + A) i : ℝ)) ^ 2 := by
  have hBpos : 0 < (A + A).card := Finset.card_pos.2 (hne.add hne)
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range ((A + A).card - 1))
    (f := fun i => ((nth (A + A) (i + 1) : ℝ) - (nth (A + A) i : ℝ)))
  rw [Finset.card_range, sum_gaps_eq hne, Nat.cast_sub hBpos, Nat.cast_one] at h
  exact h

/-- **The diameter/energy inequality.**  No Sidon hypothesis is needed: for every nonempty `A`,
`4 * diam A ^ 2 ≤ |A + A| * (|A + A| - 1) * gapEnergy A`.  A large diameter forces a large gap
energy, which is what makes the minimisation problem finite. -/
theorem four_mul_diam_sq_le {A : Finset ℕ} (hne : A.Nonempty) :
    4 * ((A.max' hne : ℝ) - (A.min' hne : ℝ)) ^ 2
      ≤ ((A + A).card : ℝ) * (((A + A).card : ℝ) - 1) * gapEnergy A := by
  have hBpos : 0 < (A + A).card := Finset.card_pos.2 (hne.add hne)
  have hc : ((A + A).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hBpos.ne'
  have h := sq_diam_le_card_mul_sum_sq hne
  have key : ((A + A).card : ℝ) * (((A + A).card : ℝ) - 1) * gapEnergy A
      = (((A + A).card : ℝ) - 1) * ∑ i ∈ Finset.range ((A + A).card - 1),
          ((nth (A + A) (i + 1) : ℝ) - (nth (A + A) i : ℝ)) ^ 2 := by
    rw [gapEnergy]
    field_simp
  rw [key]
  nlinarith [h]

/- ### The infimum is attained -/

/-- **The infimum defining `Erdos153.f n` is a minimum.**  There is a Sidon set of size `n`
whose gap energy is exactly `Erdos153.f n`. -/
theorem exists_gapEnergy_eq_f (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ IsSidon (A : Set ℕ) ∧ Erdos153.f n = gapEnergy A := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · refine ⟨∅, rfl, by simp [IsSidon], ?_⟩
      have h0 : gapEnergy (∅ : Finset ℕ) = 0 := by simp [gapEnergy]
      refine le_antisymm ?_ (h0 ▸ f_nonneg 0)
      simpa [h0] using f_le_gapEnergy (n := 0) (A := ∅) rfl (by simp [IsSidon])
    · refine ⟨{0}, rfl, by simp [IsSidon], ?_⟩
      have h0 : gapEnergy ({0} : Finset ℕ) = 0 := by
        rw [gapEnergy, Finset.singleton_add_singleton]
        norm_num
      refine le_antisymm ?_ (h0 ▸ f_nonneg 1)
      simpa [h0] using f_le_gapEnergy (n := 1) (A := {0}) rfl (by simp [IsSidon])
  · obtain ⟨A₁, hA₁card, hA₁sidon⟩ := exists_isSidon_card n
    have hA₁ne : A₁.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨B₁, hB₁sub, hB₁card, hB₁sidon, hB₁energy⟩ := exists_translate hA₁ne hA₁sidon
    set t : ℕ := (n + 1).choose 2 with ht
    have ht3 : 3 ≤ t := by
      rw [ht]
      calc (3 : ℕ) = Nat.choose 3 2 := by norm_num
        _ ≤ (n + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
    have htcard : ∀ A : Finset ℕ, A.card = n → IsSidon (A : Set ℕ) → (A + A).card = t := by
      intro A hc hs
      rw [card_add_self_of_isSidon hs, hc, ht]
    have hK : (0 : ℝ) < (t : ℝ) * ((t : ℝ) - 1) := by
      have h3 : (3 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht3
      nlinarith
    obtain ⟨M, hM⟩ := exists_nat_gt (max ((t : ℝ) * ((t : ℝ) - 1) * gapEnergy B₁ / 4)
      ((A₁.max' hA₁ne - A₁.min' hA₁ne : ℕ) : ℝ))
    have hMpos : 0 < M := by
      have h0 : (0 : ℝ) ≤ max ((t : ℝ) * ((t : ℝ) - 1) * gapEnergy B₁ / 4)
          ((A₁.max' hA₁ne - A₁.min' hA₁ne : ℕ) : ℝ) := le_max_of_le_right (Nat.cast_nonneg _)
      exact_mod_cast h0.trans_lt hM
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMpos
    have hMD : A₁.max' hA₁ne - A₁.min' hA₁ne ≤ M := by
      have h := (le_max_right _ _).trans_lt hM
      exact_mod_cast h.le
    have hME : (t : ℝ) * ((t : ℝ) - 1) * gapEnergy B₁ < 4 * (M : ℝ) ^ 2 := by
      have h1 := (le_max_left _ _).trans_lt hM
      nlinarith [hM1]
    set T : Finset (Finset ℕ) :=
      (Finset.range (M + 1)).powerset.filter (fun A => A.card = n ∧ IsSidon (A : Set ℕ)) with hT
    have hrange₁ : Finset.range (A₁.max' hA₁ne - A₁.min' hA₁ne + 1) ⊆ Finset.range (M + 1) :=
      Finset.range_subset_range.2 (by omega)
    have hB₁T : B₁ ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hB₁sub.trans hrange₁, hB₁card.trans hA₁card, hB₁sidon⟩
    obtain ⟨A₀, hA₀T, hA₀min⟩ := T.exists_min_image gapEnergy ⟨B₁, hB₁T⟩
    have hA₀ : A₀.card = n ∧ IsSidon (A₀ : Set ℕ) := by
      rw [hT, Finset.mem_filter] at hA₀T
      exact hA₀T.2
    refine ⟨A₀, hA₀.1, hA₀.2, le_antisymm (f_le_gapEnergy hA₀.1 hA₀.2) ?_⟩
    refine le_f fun A hAcard hAsidon => ?_
    have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
    by_cases hD : A.max' hAne - A.min' hAne ≤ M
    · obtain ⟨B, hBsub, hBcard, hBsidon, hBenergy⟩ := exists_translate hAne hAsidon
      have hrange : Finset.range (A.max' hAne - A.min' hAne + 1) ⊆ Finset.range (M + 1) :=
        Finset.range_subset_range.2 (by omega)
      have hBT : B ∈ T := by
        rw [hT, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hBsub.trans hrange, hBcard.trans hAcard, hBsidon⟩
      rw [← hBenergy]
      exact hA₀min B hBT
    · push_neg at hD
      have hmm : A.min' hAne ≤ A.max' hAne := A.min'_le _ (A.max'_mem hAne)
      have hDR : (M : ℝ) + 1 ≤ (A.max' hAne : ℝ) - (A.min' hAne : ℝ) := by
        have h : (M : ℝ) + 1 ≤ ((A.max' hAne - A.min' hAne : ℕ) : ℝ) := by exact_mod_cast hD
        rwa [Nat.cast_sub hmm] at h
      have hCS := four_mul_diam_sq_le hAne
      rw [htcard A hAcard hAsidon] at hCS
      have hDsq : ((M : ℝ) + 1) ^ 2 ≤ ((A.max' hAne : ℝ) - (A.min' hAne : ℝ)) ^ 2 := by
        nlinarith [hDR, hM1]
      have hlt : (t : ℝ) * ((t : ℝ) - 1) * gapEnergy B₁
          < (t : ℝ) * ((t : ℝ) - 1) * gapEnergy A := by
        nlinarith [hCS, hDsq, hME, hM1]
      exact (hA₀min B₁ hB₁T).trans (lt_of_mul_lt_mul_left hlt hK.le).le

/-- Because the infimum is attained, a *strict* lower bound may be checked on the individual
competitors — the `←` direction fails for a general infimum. -/
theorem lt_f_iff {n : ℕ} {c : ℝ} :
    c < Erdos153.f n ↔ ∀ A : Finset ℕ, A.card = n → IsSidon (A : Set ℕ) → c < gapEnergy A := by
  refine ⟨fun h A hcard hA => h.trans_le (f_le_gapEnergy hcard hA), fun h => ?_⟩
  obtain ⟨A, hcard, hA, hEq⟩ := exists_gapEnergy_eq_f n
  rw [hEq]
  exact h A hcard hA

/- ### The elementary lower bound, for comparison -/

/-- The arithmetic core of the elementary bound: Cauchy–Schwarz (`hCS`) against a diameter bound
(`hdiam`) and a sumset-size bound (`hcard`).  The diameter bound is a *parameter*, so a sharper
Sidon diameter estimate upgrades the constant without touching any other proof; that is exactly
what `diam_ge_of_isSidon` does below. -/
theorem real_gap_bound {N t S D : ℝ} (hN2 : 2 ≤ N) (ht0 : 0 < t) (hS0 : 0 ≤ S)
    (hCS : (2 * D) ^ 2 ≤ (t - 1) * S) (hdiam : N * (N - 1) ≤ 2 * D)
    (hcard : 2 * t ≤ N * (N + 1)) :
    4 * N * (N - 1) / ((N + 1) * (N + 2)) ≤ S / t := by
  have h0 : 0 ≤ N * (N - 1) := by nlinarith
  have hsq : N * (N - 1) * (N * (N - 1)) ≤ 2 * D * (2 * D) := mul_self_le_mul_self h0 hdiam
  have h1 : N ^ 2 * (N - 1) ^ 2 ≤ (t - 1) * S := by nlinarith [hCS, hsq]
  have h2 : 2 * (t - 1) ≤ (N - 1) * (N + 2) := by nlinarith [hcard]
  have h3 : 2 * (N ^ 2 * (N - 1) ^ 2) ≤ S * ((N - 1) * (N + 2)) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 hS0, h1]
  have hN1 : (0 : ℝ) < N - 1 := by linarith
  have h4 : 2 * N ^ 2 * (N - 1) ≤ S * (N + 2) :=
    le_of_mul_le_mul_left (by nlinarith [h3]) hN1
  rw [div_le_div_iff₀ (by nlinarith) ht0]
  nlinarith [mul_le_mul_of_nonneg_right h4 (show (0 : ℝ) ≤ N + 1 by linarith),
    mul_le_mul_of_nonneg_left hcard (show (0 : ℝ) ≤ 2 * N * (N - 1) by nlinarith)]

/-- Every Sidon set of size `n ≥ 2` has gap energy at least `4n(n-1)/((n+1)(n+2))`. -/
theorem gapEnergy_lower_bound {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (hn : 2 ≤ A.card) :
    4 * (A.card : ℝ) * ((A.card : ℝ) - 1) / (((A.card : ℝ) + 1) * ((A.card : ℝ) + 2))
      ≤ gapEnergy A := by
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hBpos : 0 < (A + A).card := Finset.card_pos.2 (hne.add hne)
  have hmm : A.min' hne ≤ A.max' hne := A.min'_le _ (A.max'_mem hne)
  have hdiam : (A.card : ℝ) * ((A.card : ℝ) - 1)
      ≤ 2 * ((A.max' hne : ℝ) - (A.min' hne : ℝ)) := by
    have h1 : (A.card : ℝ) * (A.card : ℝ)
        ≤ (A.card : ℝ) + 2 * ((A.max' hne : ℝ) - (A.min' hne : ℝ)) := by
      have h2 : ((A.card * A.card : ℕ) : ℝ)
          ≤ ((A.card + 2 * (A.max' hne - A.min' hne) : ℕ) : ℝ) := by
        exact_mod_cast card_sq_le_two_mul_diam hA hne
      push_cast [Nat.cast_sub hmm] at h2
      linarith
    nlinarith [h1]
  have hcard : 2 * ((A + A).card : ℝ) ≤ (A.card : ℝ) * ((A.card : ℝ) + 1) := by
    have h2 : (((A + A).card : ℕ) : ℝ) ≤ (((A.card + 1).choose 2 : ℕ) : ℝ) := by
      exact_mod_cast card_add_self_le_choose A
    rw [Nat.cast_choose_two ℝ] at h2
    push_cast at h2
    linarith
  rw [gapEnergy]
  refine real_gap_bound (by exact_mod_cast hn) (by exact_mod_cast hBpos)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_diam_le_card_mul_sum_sq hne) hdiam hcard

/-- `4n(n-1)/((n+1)(n+2)) ≤ Erdos153.f n` for every `n`.  This is what the Cauchy–Schwarz route
yields when fed the elementary diameter bound `card_sq_le_two_mul_diam`. -/
theorem f_lower_bound (n : ℕ) :
    4 * (n : ℝ) * ((n : ℝ) - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) ≤ Erdos153.f n := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> · norm_num; exact f_nonneg _
  · exact le_f fun A hcard hA => by
      subst hcard
      exact gapEnergy_lower_bound hA hn

/-- Honest ceiling of the elementary route: its bound is `< 4` for every `n`.  The whole point of
the Erdős–Turán input below is to replace this `4` by `16`. -/
theorem lower_bound_lt_four (n : ℕ) :
    4 * (n : ℝ) * ((n : ℝ) - 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) < 4 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [div_lt_iff₀ (by nlinarith)]
  nlinarith

/- ### The Erdős–Turán window inequality for Sidon sets -/

/-- `windowCount A l x` is the number of elements of `A` in the window `(x - l, x]`. -/
def windowCount (A : Finset ℕ) (l x : ℕ) : ℕ := #{a ∈ A | a ≤ x ∧ x < a + l}

/-- Gauss' sum in the form needed below. -/
theorem two_mul_sum_Ico (l : ℕ) : 2 * ∑ d ∈ Finset.Ico 1 l, (l - d) = l * (l - 1) := by
  induction l with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hstep : ∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 + 1 - d)
        = (∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 - d)) + j := by
      calc ∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 + 1 - d)
          = ∑ d ∈ Finset.Ico 1 (j + 1), ((j + 1 - d) + 1) :=
            Finset.sum_congr rfl fun d hd => by
              simp only [Finset.mem_Ico] at hd; omega
        _ = (∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 - d)) + #(Finset.Ico 1 (j + 1)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
        _ = (∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 - d)) + j := by rw [Nat.card_Ico]; omega
    rw [hstep]
    have hlast : j + 1 + 1 - (j + 1) = 1 := by omega
    rw [hlast]
    have hexp : 2 * ((∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 - d)) + j + 1)
        = 2 * (∑ d ∈ Finset.Ico 1 (j + 1), (j + 1 - d)) + 2 * j + 2 := by ring
    rw [hexp, ih]
    simp only [Nat.add_sub_cancel]
    ring

/-- **Where the Sidon hypothesis enters.**  The map `(a, b) ↦ a - b` is injective on the ordered
pairs of a Sidon set, so the overlaps `(l - (a - b))⁺` over pairs with `b < a` are dominated by
the triangular sum `∑_{d < l} (l - d)`. -/
theorem two_mul_sum_lower_le {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (l : ℕ) :
    2 * ∑ p ∈ {p ∈ A.offDiag | p.2 < p.1}, ((min p.1 p.2 + l) - max p.1 p.2) ≤ l * (l - 1) := by
  set T : Finset (ℕ × ℕ) := {p ∈ A.offDiag | p.2 < p.1} with hT
  set T' : Finset (ℕ × ℕ) := {p ∈ T | p.1 < p.2 + l} with hT'
  have hTT' : T' ⊆ T := Finset.filter_subset _ _
  have hzero : ∀ p ∈ T, p ∉ T' → ((min p.1 p.2 + l) - max p.1 p.2) = 0 := by
    intro p hp hp'
    rw [hT', Finset.mem_filter] at hp'
    push_neg at hp'
    have hge := hp' hp
    rw [hT, Finset.mem_filter] at hp
    have h2 := hp.2
    have e1 : min p.1 p.2 = p.2 := by omega
    have e2 : max p.1 p.2 = p.1 := by omega
    rw [e1, e2]
    omega
  rw [← Finset.sum_subset hTT' hzero]
  have hrw : ∑ p ∈ T', ((min p.1 p.2 + l) - max p.1 p.2) = ∑ p ∈ T', (l - (p.1 - p.2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hT', Finset.mem_filter, hT, Finset.mem_filter] at hp
    have h2 := hp.1.2
    have e1 : min p.1 p.2 = p.2 := by omega
    have e2 : max p.1 p.2 = p.1 := by omega
    rw [e1, e2]
    omega
  rw [hrw]
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 - p.2) (T' : Set (ℕ × ℕ)) := by
    intro p hp q hq hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hT', hT, Finset.mem_filter,
      Finset.mem_offDiag] at hp hq
    obtain ⟨⟨⟨hp1, hp2, _⟩, hplt⟩, _⟩ := hp
    obtain ⟨⟨⟨hq1, hq2, _⟩, hqlt⟩, _⟩ := hq
    simp only at hEq
    have hsum : p.1 + q.2 = q.1 + p.2 := by omega
    rcases hA p.1 hp1 q.1 hq1 q.2 hq2 p.2 hp2 hsum with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext h1 h2.symm
    · omega
  rw [← Finset.sum_image hinj]
  have hsub : T'.image (fun p : ℕ × ℕ => p.1 - p.2) ⊆ Finset.Ico 1 l := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hd
    rw [hT', Finset.mem_filter, hT, Finset.mem_filter] at hp
    simp only [Finset.mem_Ico]
    have h1 := hp.1.2
    have h2 := hp.2
    omega
  calc 2 * ∑ d ∈ T'.image (fun p : ℕ × ℕ => p.1 - p.2), (l - d)
      ≤ 2 * ∑ d ∈ Finset.Ico 1 l, (l - d) :=
        Nat.mul_le_mul_left 2 (Finset.sum_le_sum_of_subset hsub)
    _ = l * (l - 1) := two_mul_sum_Ico l

/-- Each element of `A` lies in exactly `l` of the windows. -/
theorem sum_windowCount {A : Finset ℕ} {N : ℕ} (hsub : ∀ a ∈ A, a ≤ N) (l : ℕ) :
    ∑ x ∈ Finset.range (N + l), windowCount A l x = A.card * l := by
  have h : ∀ a ∈ A, (∑ x ∈ Finset.range (N + l), if a ≤ x ∧ x < a + l then 1 else 0) = l := by
    intro a ha
    rw [← Finset.card_filter]
    have hEq : {x ∈ Finset.range (N + l) | a ≤ x ∧ x < a + l} = Finset.Ico a (a + l) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      have := hsub a ha
      omega
    rw [hEq, Nat.card_Ico]
    omega
  simp only [windowCount, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul]

/-- A pair `(a, b)` lies in exactly `(l - |a - b|)⁺` common windows. -/
theorem sum_windowCount_sq {A : Finset ℕ} {N : ℕ} (hsub : ∀ a ∈ A, a ≤ N) (l : ℕ) :
    ∑ x ∈ Finset.range (N + l), (windowCount A l x) ^ 2
      = ∑ p ∈ A ×ˢ A, ((min p.1 p.2 + l) - max p.1 p.2) := by
  have hsq : ∀ x, (windowCount A l x) ^ 2
      = ∑ p ∈ A ×ˢ A, if (p.1 ≤ x ∧ x < p.1 + l) ∧ (p.2 ≤ x ∧ x < p.2 + l) then 1 else 0 := by
    intro x
    rw [← Finset.card_filter, windowCount, sq, ← Finset.card_product]
    congr 1
    ext p
    simp only [Finset.mem_product, Finset.mem_filter]
    tauto
  simp only [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨ha, hb⟩ := Finset.mem_product.1 hp
  rw [← Finset.card_filter]
  have hEq : {x ∈ Finset.range (N + l) | (p.1 ≤ x ∧ x < p.1 + l) ∧ (p.2 ≤ x ∧ x < p.2 + l)}
      = Finset.Ico (max p.1 p.2) (min p.1 p.2 + l) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    have h1 := hsub _ ha
    have h2 := hsub _ hb
    omega
  rw [hEq, Nat.card_Ico]

/-- The second moment of the window counts of a Sidon set. -/
theorem sum_pairs_le {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (l : ℕ) :
    ∑ p ∈ A ×ˢ A, ((min p.1 p.2 + l) - max p.1 p.2) ≤ A.card * l + l * (l - 1) := by
  rw [← Finset.diag_union_offDiag A, Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  have hdiag : ∑ p ∈ A.diag, ((min p.1 p.2 + l) - max p.1 p.2) = A.card * l := by
    have hcst : ∀ p ∈ A.diag, ((min p.1 p.2 + l) - max p.1 p.2) = l := by
      intro p hp
      rw [Finset.mem_diag] at hp
      obtain ⟨_, h2⟩ := hp
      rw [← h2]
      simp
    rw [Finset.sum_congr rfl hcst, Finset.sum_const, smul_eq_mul, Finset.diag_card]
  have hoff : ∑ p ∈ A.offDiag, ((min p.1 p.2 + l) - max p.1 p.2) ≤ l * (l - 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not A.offDiag (fun p => p.2 < p.1)]
    have hsymm : ∑ p ∈ {p ∈ A.offDiag | ¬ (p.2 < p.1)}, ((min p.1 p.2 + l) - max p.1 p.2)
        = ∑ p ∈ {p ∈ A.offDiag | p.2 < p.1}, ((min p.1 p.2 + l) - max p.1 p.2) := by
      refine Finset.sum_equiv (Equiv.prodComm ℕ ℕ) (fun p => ?_) (fun p _ => ?_)
      · simp only [Finset.mem_filter, Finset.mem_offDiag, Equiv.prodComm_apply, Prod.fst_swap,
          Prod.snd_swap]
        constructor
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          exact ⟨⟨h2, h1, fun h => h3 h.symm⟩, by omega⟩
        · rintro ⟨⟨h1, h2, h3⟩, h4⟩
          exact ⟨⟨h2, h1, fun h => h3 h.symm⟩, by omega⟩
      · simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
        rw [min_comm, max_comm]
    rw [hsymm]
    have h2 := two_mul_sum_lower_le hA l
    omega
  omega

/-- **The Erdős–Turán window inequality.**  If `A ⊆ [0, N]` is Sidon and `l ≥ 1` then
`|A|^2 * l ≤ (N + l) * (|A| + l - 1)`.  Taking `l` large forces `N ≳ |A|^2`, twice the bound
`N ≥ |A|(|A|-1)/2` given by counting distinct differences. -/
theorem erdos_turan_ineq {A : Finset ℕ} {N l : ℕ} (hA : IsSidon (A : Set ℕ))
    (hsub : ∀ a ∈ A, a ≤ N) (hl : 1 ≤ l) :
    A.card ^ 2 * l ≤ (N + l) * (A.card + l - 1) := by
  have hcs : (∑ x ∈ Finset.range (N + l), windowCount A l x) ^ 2
      ≤ (N + l) * ∑ x ∈ Finset.range (N + l), (windowCount A l x) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (N + l))
      (f := fun x => (windowCount A l x : ℝ))
    rw [Finset.card_range] at h
    exact_mod_cast h
  rw [sum_windowCount hsub l, sum_windowCount_sq hsub l] at hcs
  have hfac : A.card * l + l * (l - 1) = l * (A.card + l - 1) := by
    have h1 : A.card + l - 1 = A.card + (l - 1) := by omega
    rw [h1, Nat.mul_add, Nat.mul_comm l A.card]
  have h2 : (A.card * l) ^ 2 ≤ (N + l) * (l * (A.card + l - 1)) := by
    refine hcs.trans (Nat.mul_le_mul_left _ ?_)
    rw [← hfac]
    exact sum_pairs_le hA l
  have h3 : (A.card ^ 2 * l) * l ≤ ((N + l) * (A.card + l - 1)) * l := by
    calc (A.card ^ 2 * l) * l = (A.card * l) ^ 2 := by ring
      _ ≤ (N + l) * (l * (A.card + l - 1)) := h2
      _ = ((N + l) * (A.card + l - 1)) * l := by ring
  exact Nat.le_of_mul_le_mul_right h3 (by omega)

/-- `erdos_turan_ineq` transported to an arbitrary Sidon set via `exists_translate`, with `N`
replaced by the diameter. -/
theorem card_sq_mul_le_of_isSidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (hne : A.Nonempty)
    {l : ℕ} (hl : 1 ≤ l) :
    A.card ^ 2 * l ≤ ((A.max' hne - A.min' hne) + l) * (A.card + l - 1) := by
  obtain ⟨B, hBsub, hBcard, hBsidon, _⟩ := exists_translate hne hA
  have hb : ∀ b ∈ B, b ≤ A.max' hne - A.min' hne := by
    intro b hb
    have hmem := hBsub hb
    rw [Finset.mem_range] at hmem
    omega
  have h := erdos_turan_ineq hBsidon hb hl
  rwa [hBcard] at h

/-- **The diameter of a Sidon set.**  Specialising `l = m * |A|` in the Erdős–Turán inequality:
`m * n^2 ≤ (diam A + m * n) * (m + 1)`, i.e. `diam A ≥ m n^2/(m+1) - m n`.  As `m` grows the
leading constant tends to `1`, against the `1/2` of the elementary distinct-differences count. -/
theorem diam_ge_of_isSidon {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) (hne : A.Nonempty) {m : ℕ}
    (hm : 1 ≤ m) :
    m * A.card ^ 2 ≤ ((A.max' hne - A.min' hne) + m * A.card) * (m + 1) := by
  have hn1 : 1 ≤ A.card := Finset.card_pos.2 hne
  have hl : 1 ≤ m * A.card := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h := card_sq_mul_le_of_isSidon hA hne hl
  have hle : A.card + m * A.card - 1 ≤ (m + 1) * A.card := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h2 : (m * A.card ^ 2) * A.card
      ≤ (((A.max' hne - A.min' hne) + m * A.card) * (m + 1)) * A.card := by
    calc (m * A.card ^ 2) * A.card = A.card ^ 2 * (m * A.card) := by ring
      _ ≤ ((A.max' hne - A.min' hne) + m * A.card) * (A.card + m * A.card - 1) := h
      _ ≤ ((A.max' hne - A.min' hne) + m * A.card) * ((m + 1) * A.card) :=
          Nat.mul_le_mul_left _ hle
      _ = (((A.max' hne - A.min' hne) + m * A.card) * (m + 1)) * A.card := by ring
  exact Nat.le_of_mul_le_mul_right h2 hn1

/- ### The lower bound `16` for the gap energy -/

/-- The arithmetic core.  It takes the diameter estimate (`hd`) and the Cauchy–Schwarz estimate
(`hCS`) as parameters, so any sharpening of `diam_ge_of_isSidon` upgrades the constant with no
change to the rest. -/
theorem real_sixteen_bound {x y d T E : ℝ} (hx : 1 ≤ x) (hy : x + 1 ≤ y)
    (hd0 : 0 ≤ d) (hd : x * y ^ 2 ≤ (d + x * y) * (x + 1)) (hT : T = y * (y + 1) / 2)
    (hE : 0 ≤ E) (hCS : 4 * d ^ 2 ≤ T * (T - 1) * E) :
    16 * (x / (x + 1)) ^ 2 * ((y - x - 1) / (y + 1)) ^ 2 ≤ E := by
  have hx0 : (0 : ℝ) < x + 1 := by linarith
  have hy0 : (0 : ℝ) < y + 1 := by linarith
  have hy2 : (2 : ℝ) ≤ y := by linarith
  have hz : (0 : ℝ) ≤ y - x - 1 := by linarith
  have hw0 : 0 ≤ x * y * (y - x - 1) / (x + 1) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hz) hx0.le
  have hw : x * y * (y - x - 1) / (x + 1) ≤ d := by
    rw [div_le_iff₀ hx0]
    nlinarith [hd]
  have hd2 : (x * y * (y - x - 1) / (x + 1)) ^ 2 ≤ d ^ 2 := by nlinarith [hw, hw0]
  have hTpos : (0 : ℝ) < T := by rw [hT]; nlinarith
  have hCS2 : 4 * d ^ 2 ≤ T ^ 2 * E := by nlinarith [mul_nonneg hTpos.le hE]
  have hrewrite : 16 * (x / (x + 1)) ^ 2 * ((y - x - 1) / (y + 1)) ^ 2
      = 4 * (x * y * (y - x - 1) / (x + 1)) ^ 2 / T ^ 2 := by
    rw [hT]
    field_simp
    ring
  rw [hrewrite, div_le_iff₀ (by positivity)]
  nlinarith [hd2, hCS2]

/-- **The lower bound on the target's own function.**  For every `m ≥ 1` and every `n ≥ m + 1`,
`16 (m/(m+1))^2 ((n-m-1)/(n+1))^2 ≤ Erdos153.f n`.  Letting `n → ∞` and then `m → ∞` gives the
constant `16`; the same route without the Erdős–Turán input gives only `4`. -/
theorem f_lower_bound_param {m n : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    16 * ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 * (((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1)) ^ 2
      ≤ Erdos153.f n := by
  refine le_f fun A hcard hA => ?_
  have hne : A.Nonempty := Finset.card_pos.1 (by omega)
  have hmm : A.min' hne ≤ A.max' hne := A.min'_le _ (A.max'_mem hne)
  have hd0 : (0 : ℝ) ≤ (A.max' hne : ℝ) - (A.min' hne : ℝ) := by
    have h : (A.min' hne : ℝ) ≤ (A.max' hne : ℝ) := by exact_mod_cast hmm
    linarith
  have hdN := diam_ge_of_isSidon hA hne hm
  rw [hcard] at hdN
  have hdR : (m : ℝ) * (n : ℝ) ^ 2
      ≤ (((A.max' hne : ℝ) - (A.min' hne : ℝ)) + (m : ℝ) * (n : ℝ)) * ((m : ℝ) + 1) := by
    have h := (Nat.cast_le (α := ℝ)).2 hdN
    push_cast [Nat.cast_sub hmm] at h
    linarith
  have hCS := four_mul_diam_sq_le hne
  rw [card_add_self_of_isSidon hA, hcard] at hCS
  have hTeq : (((n + 1).choose 2 : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    rw [Nat.cast_choose_two ℝ]
    push_cast
    ring
  rw [hTeq] at hCS
  exact real_sixteen_bound (by exact_mod_cast hm) (by exact_mod_cast hmn) hd0 hdR rfl
    (gapEnergy_nonneg A) hCS

/-- Honest ceiling: every instance of `f_lower_bound_param` is strictly below `16`, so this
family of bounds cannot on its own decide the conjecture. -/
theorem param_lt_sixteen {m n : ℕ} (hmn : m + 1 ≤ n) :
    16 * ((m : ℝ) / ((m : ℝ) + 1)) ^ 2 * (((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1)) ^ 2 < 16 := by
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hbn : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
  have ha : (m : ℝ) / ((m : ℝ) + 1) < 1 := by rw [div_lt_one hm0]; linarith
  have ha0 : (0 : ℝ) ≤ (m : ℝ) / ((m : ℝ) + 1) := by positivity
  have hb : ((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one hn0]; linarith
  have hb0 : (0 : ℝ) ≤ ((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1) :=
    div_nonneg (by linarith) hn0.le
  have hab : ((m : ℝ) / ((m : ℝ) + 1)) * (((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1)) < 1 := by
    nlinarith
  nlinarith [hab, mul_nonneg ha0 hb0]

/-- An elementary inequality: for `a, b ≤ 1`, `16 a^2 b^2` is within `32(1-a) + 32(1-b)` of
`16`. -/
theorem real_ab_bound {a b : ℝ} (ha1 : a ≤ 1) (hb1 : b ≤ 1) :
    16 - 32 * (1 - a) - 32 * (1 - b) ≤ 16 * a ^ 2 * b ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1), sq_nonneg (a * b - 1)]

/-- **What the Erdős–Turán input buys.**  For every `c < 16`, `c ≤ Erdos153.f n` for all large
`n`.  The conjecture `Tendsto Erdos153.f atTop atTop` asks for every constant `c`, so this is a
strictly weaker statement; `param_lt_sixteen` shows `16` really is the ceiling of the method. -/
theorem eventually_le_f {c : ℝ} (hc : c < 16) : ∀ᶠ n : ℕ in atTop, c ≤ Erdos153.f n := by
  rcases le_or_gt c 0 with hc0 | hc0
  · exact Filter.Eventually.of_forall fun n => hc0.trans (f_nonneg n)
  have h16 : (0 : ℝ) < 16 - c := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (64 / (16 - c))
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (64 * ((m₀ : ℝ) + 1 + 2) / (16 - c))
  filter_upwards [eventually_ge_atTop (max N₀ (m₀ + 1 + 1))] with n hn
  set m : ℕ := m₀ + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmR : 64 / (16 - c) ≤ (m : ℝ) + 1 := by
    have h : (m₀ : ℝ) ≤ (m : ℝ) + 1 := by
      have : (m : ℝ) = (m₀ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
      linarith
    linarith
  have hnm : m + 1 ≤ n := (le_max_right N₀ (m₀ + 1 + 1)).trans hn
  have hnN : (N₀ : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (le_max_left N₀ (m₀ + 1 + 1)).trans hn
  have hnR : 64 * ((m : ℝ) + 2) / (16 - c) ≤ (n : ℝ) + 1 := by
    have hmm : (m : ℝ) + 2 = (m₀ : ℝ) + 1 + 2 := by rw [hmdef]; push_cast; ring
    rw [hmm]
    linarith
  refine le_trans ?_ (f_lower_bound_param hm1 hnm)
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbn : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnm
  have ha1 : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one hm0]; linarith
  have hb1 : ((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hn0]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hA1 : 1 - (m : ℝ) / ((m : ℝ) + 1) = 1 / ((m : ℝ) + 1) := by field_simp; ring
  have hB1 : 1 - ((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1) = ((m : ℝ) + 2) / ((n : ℝ) + 1) := by
    field_simp
    ring
  have hmR' : 64 ≤ ((m : ℝ) + 1) * (16 - c) := by
    rw [div_le_iff₀ h16] at hmR
    linarith
  have hnR' : 64 * ((m : ℝ) + 2) ≤ ((n : ℝ) + 1) * (16 - c) := by
    rw [div_le_iff₀ h16] at hnR
    linarith
  have hAle : 32 * (1 - (m : ℝ) / ((m : ℝ) + 1)) ≤ (16 - c) / 2 := by
    rw [hA1, mul_one_div, div_le_iff₀ hm0]
    linarith
  have hBle : 32 * (1 - ((n : ℝ) - (m : ℝ) - 1) / ((n : ℝ) + 1)) ≤ (16 - c) / 2 := by
    rw [hB1, ← mul_div_assoc, div_le_iff₀ hn0]
    linarith
  have hfin := real_ab_bound ha1 hb1
  linarith

/- ### Exact values of `Erdos153.f` -/

/-- **A finite-search principle for `Erdos153.f`.**  `hcut` says that a competitor of energy
below `v` must have diameter at most `D` (via `four_mul_diam_sq_le`), `hlow` checks the finitely
many normalised competitors of diameter at most `D`, and `A` realises the value. -/
theorem f_eq_of_search {n D : ℕ} {v : ℝ} (hn : 2 ≤ n)
    (hcut : (((n + 1).choose 2 : ℕ) : ℝ) * ((((n + 1).choose 2 : ℕ) : ℝ) - 1) * v
        ≤ 4 * ((D : ℝ) + 1) ^ 2)
    (hlow : ∀ B : Finset ℕ, B ⊆ Finset.range (D + 1) → B.card = n → IsSidon (B : Set ℕ) →
        v ≤ gapEnergy B)
    (A : Finset ℕ) (hAcard : A.card = n) (hA : IsSidon (A : Set ℕ)) (hAv : gapEnergy A = v) :
    Erdos153.f n = v := by
  refine le_antisymm (hAv ▸ f_le_gapEnergy hAcard hA) (le_f fun C hCcard hC => ?_)
  have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
  have hmm : C.min' hCne ≤ C.max' hCne := C.min'_le _ (C.max'_mem hCne)
  by_cases hd : C.max' hCne - C.min' hCne ≤ D
  · obtain ⟨B, hBsub, hBcard, hBsidon, hBenergy⟩ := exists_translate hCne hC
    rw [← hBenergy]
    exact hlow B (hBsub.trans (Finset.range_subset_range.2 (by omega)))
      (hBcard.trans hCcard) hBsidon
  · push_neg at hd
    have hCS := four_mul_diam_sq_le hCne
    rw [card_add_self_of_isSidon hC, hCcard] at hCS
    have hDR : ((D : ℝ) + 1) ≤ (C.max' hCne : ℝ) - (C.min' hCne : ℝ) := by
      have h1 : D + 1 ≤ C.max' hCne - C.min' hCne := by omega
      have h2 : ((D + 1 : ℕ) : ℝ) ≤ ((C.max' hCne - C.min' hCne : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub hmm] at h2
      push_cast at h2
      linarith
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have hDsq : ((D : ℝ) + 1) ^ 2 ≤ ((C.max' hCne : ℝ) - (C.min' hCne : ℝ)) ^ 2 := by
      nlinarith [hDR, hD0]
    have hT3 : (3 : ℝ) ≤ (((n + 1).choose 2 : ℕ) : ℝ) := by
      have h : (3 : ℕ) ≤ (n + 1).choose 2 := by
        calc (3 : ℕ) = Nat.choose 3 2 := by norm_num
          _ ≤ (n + 1).choose 2 := Nat.choose_le_choose 2 (by omega)
      exact_mod_cast h
    have hTT : (0 : ℝ) < (((n + 1).choose 2 : ℕ) : ℝ) * ((((n + 1).choose 2 : ℕ) : ℝ) - 1) := by
      nlinarith
    refine le_of_mul_le_mul_left ?_ hTT
    nlinarith [hcut, hCS, hDsq]

theorem gapEnergy_zero_one : gapEnergy {0, 1} = 2 / 3 := by
  have hcard : (({0, 1} : Finset ℕ) + {0, 1}).card = 3 := by decide
  have hnth : ∀ i, i < 3 → nth (({0, 1} : Finset ℕ) + {0, 1}) i = i := by
    intro i hi
    refine nth_eq_of_mono hcard (g := fun j => j) ?_ ?_ hi
    · decide
    · decide
  rw [gapEnergy, hcard]
  norm_num [Finset.sum_range_succ, hnth 0, hnth 1, hnth 2]

/-- **A checked value of the target's own function.** -/
theorem f_two : Erdos153.f 2 = 2 / 3 := by
  refine f_eq_of_search (D := 1) (by norm_num) (by norm_num) ?_ {0, 1} (by decide) (by decide)
    gapEnergy_zero_one
  intro B hsub hcard hB
  have key : ∀ C ∈ (Finset.range 2).powersetCard 2, IsSidon (C : Set ℕ) → C = {0, 1} := by
    decide +kernel
  rw [key B (Finset.mem_powersetCard.2 ⟨hsub, hcard⟩) hB, gapEnergy_zero_one]

theorem gapEnergy_zero_one_three : gapEnergy {0, 1, 3} = 4 / 3 := by
  have hcard : (({0, 1, 3} : Finset ℕ) + {0, 1, 3}).card = 6 := by decide
  have hnth : ∀ i, i < 6 → nth (({0, 1, 3} : Finset ℕ) + {0, 1, 3}) i =
      (if i ≤ 4 then i else 6) := by
    intro i hi
    refine nth_eq_of_mono hcard (g := fun j => if j ≤ 4 then j else 6) ?_ ?_ hi
    · decide
    · decide
  rw [gapEnergy, hcard]
  norm_num [Finset.sum_range_succ, hnth 0, hnth 1, hnth 2, hnth 3, hnth 4, hnth 5]

theorem gapEnergy_zero_two_three : gapEnergy {0, 2, 3} = 4 / 3 := by
  have hcard : (({0, 2, 3} : Finset ℕ) + {0, 2, 3}).card = 6 := by decide
  have hnth : ∀ i, i < 6 → nth (({0, 2, 3} : Finset ℕ) + {0, 2, 3}) i =
      (if i = 0 then 0 else i + 1) := by
    intro i hi
    refine nth_eq_of_mono hcard (g := fun j => if j = 0 then 0 else j + 1) ?_ ?_ hi
    · decide
    · decide
  rw [gapEnergy, hcard]
  norm_num [Finset.sum_range_succ, hnth 0, hnth 1, hnth 2, hnth 3, hnth 4, hnth 5]

/-- **A second checked value.** -/
theorem f_three : Erdos153.f 3 = 4 / 3 := by
  refine f_eq_of_search (D := 3) (by norm_num)
    (by norm_num [show Nat.choose 4 2 = 6 from rfl]) ?_ {0, 1, 3} (by decide) (by decide)
    gapEnergy_zero_one_three
  intro B hsub hcard hB
  have key : ∀ C ∈ (Finset.range 4).powersetCard 3, IsSidon (C : Set ℕ) →
      C = {0, 1, 3} ∨ C = {0, 2, 3} := by decide +kernel
  rcases key B (Finset.mem_powersetCard.2 ⟨hsub, hcard⟩) hB with rfl | rfl
  · rw [gapEnergy_zero_one_three]
  · rw [gapEnergy_zero_two_three]

theorem gapEnergy_zero_one_four_six : gapEnergy {0, 1, 4, 6} = 9 / 5 := by
  have hcard : (({0, 1, 4, 6} : Finset ℕ) + {0, 1, 4, 6}).card = 10 := by decide
  have hnth : ∀ i, i < 10 → nth (({0, 1, 4, 6} : Finset ℕ) + {0, 1, 4, 6}) i =
      (if i ≤ 2 then i else if i ≤ 7 then i + 1 else if i = 8 then 10 else 12) := by
    intro i hi
    refine nth_eq_of_mono hcard
      (g := fun j => if j ≤ 2 then j else if j ≤ 7 then j + 1 else if j = 8 then 10 else 12)
      ?_ ?_ hi
    · decide +kernel
    · decide +kernel
  rw [gapEnergy, hcard]
  norm_num [Finset.sum_range_succ, hnth 0, hnth 1, hnth 2, hnth 3, hnth 4, hnth 5, hnth 6,
    hnth 7, hnth 8, hnth 9]

theorem gapEnergy_zero_two_five_six : gapEnergy {0, 2, 5, 6} = 9 / 5 := by
  have hcard : (({0, 2, 5, 6} : Finset ℕ) + {0, 2, 5, 6}).card = 10 := by decide
  have hnth : ∀ i, i < 10 → nth (({0, 2, 5, 6} : Finset ℕ) + {0, 2, 5, 6}) i =
      (if i = 0 then 0 else if i = 1 then 2 else if i ≤ 6 then i + 2
        else if i = 7 then 10 else i + 3) := by
    intro i hi
    refine nth_eq_of_mono hcard
      (g := fun j => if j = 0 then 0 else if j = 1 then 2 else if j ≤ 6 then j + 2
        else if j = 7 then 10 else j + 3) ?_ ?_ hi
    · decide +kernel
    · decide +kernel
  rw [gapEnergy, hcard]
  norm_num [Finset.sum_range_succ, hnth 0, hnth 1, hnth 2, hnth 3, hnth 4, hnth 5, hnth 6,
    hnth 7, hnth 8, hnth 9]

/-- **A third checked value.**  The only Sidon `4`-sets of diameter `6` are `{0,1,4,6}` and
`{0,2,5,6}`, and a competitor of energy below `9/5` cannot have diameter `7` or more. -/
theorem f_four : Erdos153.f 4 = 9 / 5 := by
  refine f_eq_of_search (D := 6) (by norm_num)
    (by norm_num [show Nat.choose 5 2 = 10 from rfl]) ?_ {0, 1, 4, 6} (by decide)
    (by decide) gapEnergy_zero_one_four_six
  intro B hsub hcard hB
  have key : ∀ C ∈ (Finset.range 7).powersetCard 4, IsSidon (C : Set ℕ) →
      C = {0, 1, 4, 6} ∨ C = {0, 2, 5, 6} := by decide +kernel
  rcases key B (Finset.mem_powersetCard.2 ⟨hsub, hcard⟩) hB with rfl | rfl
  · rw [gapEnergy_zero_one_four_six]
  · rw [gapEnergy_zero_two_five_six]

/- ### A worked use site -/

/-- **Worked use site.**  Whatever proposition `P` a solver puts in the `answer(…)` slot of
`Erdos153.erdos_153`, the target statement `P ↔ Tendsto Erdos153.f atTop atTop` may be replaced
by an equivalent statement mentioning neither `Erdos153.f` nor any infimum; and by
`eventually_le_f` the right-hand side already holds for every threshold `c < 16`, so only
thresholds `c ≥ 16` remain. -/
theorem erdos_153_reduction (P : Prop) :
    (P ↔ Tendsto Erdos153.f atTop atTop) ↔
      (P ↔ ∀ c : ℝ, 16 ≤ c → ∀ᶠ n in atTop, ∀ A : Finset ℕ, A.card = n →
        IsSidon (A : Set ℕ) → c ≤ gapEnergy A) := by
  refine iff_congr Iff.rfl (Iff.trans tendsto_f_atTop_iff ?_)
  refine ⟨fun h c _ => h c, fun h c => ?_⟩
  rcases le_or_gt 16 c with hc | hc
  · exact h c hc
  · filter_upwards [eventually_le_f hc] with n hn A hcard hA
    exact hn.trans (f_le_gapEnergy hcard hA)

end Contribution.Erdos153Gaps
