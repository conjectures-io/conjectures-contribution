import Mathlib
import FormalConjectures.ErdosProblems.«155»

/-!
# Erdős 155: the Sidon threshold function, and the case `k = 2` proved outright

The target is `Erdos155.erdos_155`, whose reward obligation is
`∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1`, where
`F N = Finset.maxSidonSubsetCard (Finset.Icc 1 N)` is the largest size of a Sidon subset of
`{1, …, N}`.

## The obstacle

Two layers, one bureaucratic and one mathematical.

*Bureaucratic.* `Finset.maxSidonSubsetCard A` is defined as
`(A.powerset.filter fun B ↦ IsSidon (B : Set α)).sup Finset.card`. In the pinned environment the
only declarations that mention it are that definition, the counting functions `Erdos30.h`,
`Erdos43.f` and `Erdos155.F` (three names for one and the same expression) together with
`Green31.F` (that expression cast to `ℝ`), and the statement
`Erdos44.maxSidonSubsetCard_icc_bound`, which the pool leaves unproved; and `Mathlib` itself
contains no occurrence of the string `Sidon`. So nothing turns a Sidon subset into a lower bound
for `F`, nothing turns the value of `F` back into an extremal Sidon set, and `F` has no
monotonicity: `exact?` closes none of `Monotone F`, `F (N + 1) ≤ F N + 1`,
`∃ B ⊆ Icc 1 N, IsSidon B ∧ B.card = F N`, `B.card ≤ F N` (for Sidon `B ⊆ Icc 1 N`), or
`∃ N, m ≤ F N`. Everything below has to be re-derived from the `Finset.sup`-over-`powerset`
definition.

*Mathematical.* The target is a statement about the gaps between the *jumps* of `F` (the `N` with
`F N < F (N + 1)`), whereas the bounds known for `F` — such as the `2√N` of Erdős 44 — bound the
*number* of jumps below a point, hence only their average gap, never an individual one. A priori
`F` could still jump at two nearby integers arbitrarily far out, and that is exactly what the
target denies.

## What is proved here

**1. The case `k = 2` of the target, outright and with no exceptional set** (`F_add_two_le`): for
every `N ≥ 1`, `F (N + 2) ≤ F N + 1`, i.e. `F` never jumps at two consecutive integers `≥ 1`. With
`F_succ_le` (the case `k = 1`, valid for every `N`) this discharges two of the target's obligations
completely rather than eventually. The argument is extremality plus symmetry:

* if `F` jumped at `N` and at `N + 1`, a maximum Sidon set `B ⊆ {1, …, N + 2}` must contain `N + 2`
  (else it fits in `{1, …, N + 1}`), and after deleting `N + 2` it is still extremal for
  `{1, …, N + 1}`, so it must contain `N + 1` too (`top_mem_of_lt`, `two_top_mem_of_lt_of_lt`);
* the reflection `x ↦ N + 3 - x` preserves the interval, the Sidon property and cardinality
  (`isSidon_reflect`, `card_reflect`), so the reflected set is extremal as well and the previous
  point puts `1` and `2` into `B`;
* but `2` then lies in `B` and, as the mirror image of `N + 1 ∈ B`, also in the reflection of `B`,
  while `sidon_inter_reflect` says that intersection is exactly `{1, N + 2}`; hence `N = 0`.

**2. The target restated on the Sidon threshold function** (`L`, `erdos_155_iff_gap_eventually`,
`erdos_155_iff_gap_tendsto`). `L m = sInf {N | m ≤ F N}` is the least `N` whose interval
`{1, …, N}` contains an `m`-element Sidon set — informally, one more than the length of an optimal
Golomb ruler with `m` marks, an identification not formalised here. `L` is total because `F` is
unbounded, which needs a construction: `exists_sidon_card` exhibits, for every `n`, a Sidon set of
size `n + 1` inside `{1, …, 2 ^ (n + 1) - 1}` (crude next to the true `√N` order, but enough). The
API is the Galois connection `L_le_iff : L m ≤ N ↔ m ≤ F N` with its strict form `lt_L_iff`, the
exactness `F_L : F (L m) = m`, `L_mono`, and `jump_iff_eq_L`, which says the jumps of `F` are
exactly the numbers `L m - 1`. On top of it, the reward obligation of the target is proved
*equivalent* to `∀ k, ∀ᶠ m in atTop, L m + k ≤ L (m + 1)`, i.e. to
`Tendsto (fun m => L (m + 1) - L m) atTop atTop`: Erdős 155 holds if and only if the gaps between
consecutive Sidon thresholds diverge. Both directions are proved. In that language the case `k = 2`
reads `L_add_two_le : 2 ≤ m → L m + 2 ≤ L (m + 1)`.

**3. Reusable Sidon API.** `reflect` with `reflect_subset`, `mem_reflect_iff`, `card_reflect`,
`isSidon_reflect` and `sidon_inter_reflect` is the reflection symmetry of Sidon sets in an
interval, stated for `IsSidon` and an arbitrary `Finset ℕ`, so it serves any Sidon problem in the
pool. `sidon_inter_reflect` is the structural core: a Sidon set using both endpoints of `{1, …, M}`
meets its own reflection in exactly `{1, M}`, i.e. it takes at most one point from each mirror pair
`{j, M + 1 - j}`. `card_le_F`, `exists_max_sidon`, `F_mono` and `F_succ_le` are the missing
extraction and monotonicity layer for `Finset.maxSidonSubsetCard (Finset.Icc 1 ·)`. Because
`Erdos30.h` and `Erdos43.f` unfold to the very same expression as `Erdos155.F`, each of these
lemmas restates verbatim for those two targets and is proved there by the term already given here
(checked: `Monotone Erdos30.h := F_mono`); for the `ℝ`-valued `Green31.F` the same statements need
one `Nat.cast_le` step.

**4. A halved bound for every `k`** (`F_add_le_add_half`): for `N ≥ 1`,
`F (N + k) ≤ F N + (k + 1) / 2`. Unit steps alone give only `F (N + k) ≤ F N + k`, and the target
asks for `F N + 1` eventually; this is the trivial bound with `k` replaced by `⌈k / 2⌉`, uniformly
in `N ≥ 1`, obtained by iterating the case `k = 2` (`F_add_two_mul_le`).

**5. Checked small values and delimiters.** `jump_lt_seven` computes `F` on `{1, …, N}` for `N ≤ 7`
by kernel evaluation and pins the jumps below `7` to exactly `0, 1, 3, 6`; `L_values` turns this
into `L 1 = 1`, `L 2 = 2`, `L 3 = 4`, `L 4 = 7` (the optimal Golomb rulers with `1, 2, 3, 4` marks
have lengths `0, 1, 3, 6`). Consequences: `F_add_two_le` is sharp at `N = 1`, so it cannot be
improved to `F (N + 2) ≤ F N`; `L 2 = L 1 + 1` shows the hypothesis `2 ≤ m` of `L_add_two_le` is
sharp; `not_forall_F_add_two_le` shows the hypothesis `1 ≤ N` of `F_add_two_le` cannot be dropped;
and `not_forall_F_add_three_le` shows that from `k = 3` on the target's "sufficiently large `N`" is
genuinely needed, since `F (N + 3) ≤ F N + 1` already fails at `N = 1`.

## Direct relevance

A later solver can use declaration `Contribution.Erdos155Golomb.erdos_155_iff_gap_tendsto` to
discharge or simplify obligation `∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1` in target
`Erdos155.erdos_155`: it is a proved equivalence (both directions) between that obligation and the
divergence of the gaps of the threshold function `L`, so the solver may work with optimal Golomb
ruler lengths and never touch `Finset.maxSidonSubsetCard` again. `erdos_155_iff_three_le` and
`erdos_155_iff_gap_three_le` are the same handoff after the cases `k = 1` and `k = 2` have been
discharged here, and `eventually_F_add_two_le` is the case `k = 2` in the exact shape the target
uses.

## What is not proved

Nothing here decides the conjecture; the case `k = 3` is open in this file and is the smallest one
missing. `sidon_gap_two_configs` says precisely why the method above stops: for `k = 3` the two
jumps must sit at `N` and `N + 2`, the reflection argument still forces `1` and `N + 3` into a
maximum Sidon set of `{1, …, N + 3}`, but the branches it leaves are the configurations
`{1, 2, N + 1, N + 3}` and `{1, 3, N + 2, N + 3}`, and both of those are checked here to be Sidon
for every `N ≥ 4`. So no repeated sum can be extracted from them, and `k = 3` needs a different
idea rather than a longer case analysis.
-/

open Filter Finset

namespace Contribution.Erdos155Golomb

open Erdos155

/-  ### Minimal API for `F` -/

/-- Any Sidon subset of `{1, …, N}` bounds `F N` from below. -/
theorem card_le_F {N : ℕ} {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 N)
    (hB : IsSidon (B : Set ℕ)) : B.card ≤ F N :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hsub, hB⟩)

/-- The supremum defining `F N` is attained by an actual Sidon subset of `{1, …, N}`. -/
theorem exists_max_sidon (N : ℕ) :
    ∃ B ⊆ Finset.Icc 1 N, IsSidon (B : Set ℕ) ∧ B.card = F N := by
  have hne : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [IsSidon]⟩⟩
  obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  exact ⟨B, hB.1, hB.2, hBeq.symm⟩

/-- `F` is nondecreasing. -/
theorem F_mono : Monotone F := by
  intro a b hab
  obtain ⟨B, hsub, hB, hcard⟩ := exists_max_sidon a
  exact hcard ▸ card_le_F (hsub.trans (Finset.Icc_subset_Icc le_rfl hab)) hB

/-- `F` moves in unit steps: this is the case `k = 1` of the target obligation, and it holds for
every `N`, not merely eventually. -/
theorem F_succ_le (N : ℕ) : F (N + 1) ≤ F N + 1 := by
  obtain ⟨B, hsub, hB, hcard⟩ := exists_max_sidon (N + 1)
  have h1 : B.erase (N + 1) ⊆ Finset.Icc 1 N := by
    intro x hx
    obtain ⟨hne, hxB⟩ := Finset.mem_erase.1 hx
    have hx' := Finset.mem_Icc.1 (hsub hxB)
    exact Finset.mem_Icc.2 ⟨hx'.1, by omega⟩
  have h2 : IsSidon ((B.erase (N + 1) : Finset ℕ) : Set ℕ) :=
    Set.IsSidon.subset hB (by exact_mod_cast Finset.erase_subset _ _)
  have h3 := card_le_F h1 h2
  have h4 : B.card - 1 ≤ (B.erase (N + 1)).card := Finset.pred_card_le_card_erase
  omega

/-  ### Reflecting a Sidon set inside an interval -/

/-- The reflection `x ↦ M + 1 - x` of a finite set of naturals in the interval `{1, …, M}`. -/
def reflect (M : ℕ) (B : Finset ℕ) : Finset ℕ := B.image fun x => M + 1 - x

/-- Reflection maps `{1, …, M}` to itself. -/
theorem reflect_subset {M : ℕ} {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 M) :
    reflect M B ⊆ Finset.Icc 1 M := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
  have hx' := Finset.mem_Icc.1 (hsub hx)
  exact Finset.mem_Icc.2 ⟨by omega, by omega⟩

/-- Membership in the reflection, for a set contained in `{1, …, M}`. -/
theorem mem_reflect_iff {M : ℕ} {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 M) {y : ℕ}
    (hy1 : 1 ≤ y) (hy2 : y ≤ M) : y ∈ reflect M B ↔ M + 1 - y ∈ B := by
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h
    have hx' := Finset.mem_Icc.1 (hsub hx)
    have hxe : M + 1 - y = x := by omega
    rwa [hxe]
  · intro h
    exact Finset.mem_image.2 ⟨M + 1 - y, h, by omega⟩

/-- Reflection preserves cardinality. -/
theorem card_reflect {M : ℕ} {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 M) :
    (reflect M B).card = B.card := by
  refine Finset.card_image_of_injOn ?_
  intro a ha b hb hab
  have ha' := Finset.mem_Icc.1 (hsub (Finset.mem_coe.1 ha))
  have hb' := Finset.mem_Icc.1 (hsub (Finset.mem_coe.1 hb))
  simp only at hab
  omega

/-- Reflection preserves the Sidon property. This is the symmetry that makes the extremal
argument below work: the reflection of a maximum Sidon subset of `{1, …, M}` is again one. -/
theorem isSidon_reflect {M : ℕ} {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 M)
    (hB : IsSidon (B : Set ℕ)) : IsSidon ((reflect M B : Finset ℕ) : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi₁)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hj₁)
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi₂)
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hj₂)
  have ha' := Finset.mem_Icc.1 (hsub ha)
  have hb' := Finset.mem_Icc.1 (hsub hb)
  have hc' := Finset.mem_Icc.1 (hsub hc)
  have hd' := Finset.mem_Icc.1 (hsub hd)
  have hsum' : a + c = b + d := by omega
  rcases hB a (Finset.mem_coe.2 ha) b (Finset.mem_coe.2 hb) c (Finset.mem_coe.2 hc) d
      (Finset.mem_coe.2 hd) hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

/-- **A Sidon set that uses both endpoints of `{1, …, M}` meets its own reflection only in those
two endpoints.** Indeed `y + (M + 1 - y) = 1 + M`, so if both `y` and its mirror image lie in `B`
then the Sidon property forces `{y, M + 1 - y} = {1, M}`. Equivalently: `B` contains at most one
point out of each mirror pair `{j, M + 1 - j}` with `2 ≤ j ≤ M - 1`. -/
theorem sidon_inter_reflect {M : ℕ} {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 M)
    (hB : IsSidon (B : Set ℕ)) (h1 : 1 ∈ B) (hM : M ∈ B) :
    B ∩ reflect M B = {1, M} := by
  have hM1 : 1 ≤ M := (Finset.mem_Icc.1 (hsub h1)).2
  ext y
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hyB, hyR⟩
    have hy := Finset.mem_Icc.1 (hsub hyB)
    have hy' : M + 1 - y ∈ B := (mem_reflect_iff hsub hy.1 hy.2).1 hyR
    have hsum : y + (M + 1 - y) = 1 + M := by omega
    rcases hB y (Finset.mem_coe.2 hyB) 1 (Finset.mem_coe.2 h1) (M + 1 - y)
        (Finset.mem_coe.2 hy') M (Finset.mem_coe.2 hM) hsum with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (rfl | rfl)
    · exact ⟨h1, (mem_reflect_iff hsub le_rfl hM1).2 (by simpa using hM)⟩
    · exact ⟨hM, (mem_reflect_iff hsub hM1 le_rfl).2 (by simpa using h1)⟩

/-  ### Extremal Sidon sets at a jump of `F` -/

/-- **Endpoint lemma.** If `F` jumps from `N` to `N + 1`, then *every* maximum Sidon subset of
`{1, …, N + 1}` contains the right endpoint `N + 1`. -/
theorem top_mem_of_lt {N : ℕ} (hjump : F N < F (N + 1)) {B : Finset ℕ}
    (hsub : B ⊆ Finset.Icc 1 (N + 1)) (hB : IsSidon (B : Set ℕ)) (hcard : B.card = F (N + 1)) :
    N + 1 ∈ B := by
  by_contra hmem
  have hsub' : B ⊆ Finset.Icc 1 N := by
    intro x hx
    have hx' := Finset.mem_Icc.1 (hsub hx)
    have hxne : x ≠ N + 1 := by rintro rfl; exact hmem hx
    exact Finset.mem_Icc.2 ⟨hx'.1, by omega⟩
  have := card_le_F hsub' hB
  omega

/-- **Two-endpoint lemma.** If `F` jumps at `N` and again at `N + 1`, then every maximum Sidon
subset of `{1, …, N + 2}` contains both `N + 1` and `N + 2`: it must use the top point because of
the second jump, and after deleting that point it is still extremal for `{1, …, N + 1}`, so the
first jump forces it to use `N + 1` as well. -/
theorem two_top_mem_of_lt_of_lt {N : ℕ} (h1 : F N < F (N + 1)) (h2 : F (N + 1) < F (N + 1 + 1))
    {B : Finset ℕ} (hsub : B ⊆ Finset.Icc 1 (N + 1 + 1)) (hB : IsSidon (B : Set ℕ))
    (hcard : B.card = F (N + 1 + 1)) : N + 1 ∈ B ∧ N + 1 + 1 ∈ B := by
  have htop : N + 1 + 1 ∈ B := top_mem_of_lt h2 hsub hB hcard
  refine ⟨?_, htop⟩
  have hstep := F_succ_le (N + 1)
  have hCsub : B.erase (N + 1 + 1) ⊆ Finset.Icc 1 (N + 1) := by
    intro x hx
    obtain ⟨hne, hxB⟩ := Finset.mem_erase.1 hx
    have hx' := Finset.mem_Icc.1 (hsub hxB)
    exact Finset.mem_Icc.2 ⟨hx'.1, by omega⟩
  have hCsidon : IsSidon ((B.erase (N + 1 + 1) : Finset ℕ) : Set ℕ) :=
    Set.IsSidon.subset hB (by exact_mod_cast Finset.erase_subset _ _)
  have hCcard : (B.erase (N + 1 + 1)).card = F (N + 1) := by
    rw [Finset.card_erase_of_mem htop, hcard]
    omega
  exact Finset.mem_of_mem_erase (top_mem_of_lt h1 hCsub hCsidon hCcard)

/-  ### The case `k = 2` of Erdős 155 -/

/-- **The case `k = 2` of the target, with no exceptional set at all.**
For every `N ≥ 1` we have `F (N + 2) ≤ F N + 1`, i.e. `F` cannot jump twice in two steps.

Proof: if it did, then `F` jumps at `N` and at `N + 1`, so a maximum Sidon set `B ⊆ {1, …, N+2}`
contains `N + 1` and `N + 2` by `two_top_mem_of_lt_of_lt`. Its reflection `reflect (N+2) B` is
another maximum Sidon subset of `{1, …, N+2}`, so it too contains `N + 1` and `N + 2`, which means
`B` contains `2` and `1`. Now `2` lies in `B` and, being the mirror image of `N + 1 ∈ B`, also in
`reflect (N+2) B`; by `sidon_inter_reflect` that intersection is `{1, N + 2}`, forcing `N = 0`. -/
theorem F_add_two_le {N : ℕ} (hN : 1 ≤ N) : F (N + 2) ≤ F N + 1 := by
  by_contra hcon
  push_neg at hcon
  have hs1 : F (N + 1) ≤ F N + 1 := F_succ_le N
  have hs2 : F (N + 1 + 1) ≤ F (N + 1) + 1 := F_succ_le (N + 1)
  have hs3 : F N ≤ F (N + 1) := F_mono (by omega)
  have heq : N + 2 = N + 1 + 1 := by omega
  rw [heq] at hcon
  have h1 : F N < F (N + 1) := by omega
  have h2 : F (N + 1) < F (N + 1 + 1) := by omega
  obtain ⟨B, hsub, hB, hcard⟩ := exists_max_sidon (N + 1 + 1)
  obtain ⟨hmemN1, hmemN2⟩ := two_top_mem_of_lt_of_lt h1 h2 hsub hB hcard
  have hRsub : reflect (N + 1 + 1) B ⊆ Finset.Icc 1 (N + 1 + 1) := reflect_subset hsub
  have hRsidon : IsSidon ((reflect (N + 1 + 1) B : Finset ℕ) : Set ℕ) := isSidon_reflect hsub hB
  have hRcard : (reflect (N + 1 + 1) B).card = F (N + 1 + 1) := by
    rw [card_reflect hsub, hcard]
  obtain ⟨hR1, hR2⟩ := two_top_mem_of_lt_of_lt h1 h2 hRsub hRsidon hRcard
  have hmem1 : 1 ∈ B := by
    have := (mem_reflect_iff hsub (by omega) (by omega)).1 hR2
    have he : N + 1 + 1 + 1 - (N + 1 + 1) = 1 := by omega
    rwa [he] at this
  have hkey := sidon_inter_reflect hsub hB hmem1 hmemN2
  have hmem2 : 2 ∈ B ∩ reflect (N + 1 + 1) B := by
    refine Finset.mem_inter.2 ⟨?_, ?_⟩
    · have := (mem_reflect_iff hsub (by omega) (by omega)).1 hR1
      have he : N + 1 + 1 + 1 - (N + 1) = 2 := by omega
      rwa [he] at this
    · refine (mem_reflect_iff hsub (by omega) (by omega)).2 ?_
      have he : N + 1 + 1 + 1 - 2 = N + 1 := by omega
      rwa [he]
  rw [hkey] at hmem2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem2
  omega

/-- Iterating the main theorem: from any starting point `N ≥ 1`, `F` gains at most one unit per
*two* steps. -/
theorem F_add_two_mul_le {N : ℕ} (hN : 1 ≤ N) (j : ℕ) : F (N + 2 * j) ≤ F N + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : F (N + 2 * j + 2) ≤ F (N + 2 * j) + 1 := F_add_two_le (by omega)
    have he : N + 2 * (j + 1) = N + 2 * j + 2 := by ring
    rw [he]
    omega

/-- **A halved bound.** For every `N ≥ 1` and every `k`, `F (N + k) ≤ F N + ⌈k / 2⌉`. The bound
available from unit steps alone is `F (N + k) ≤ F N + k`; the target asks for `F N + 1` for
large `N`. This replaces `k` by `⌈k / 2⌉` uniformly in `N ≥ 1`. -/
theorem F_add_le_add_half {N : ℕ} (hN : 1 ≤ N) (k : ℕ) : F (N + k) ≤ F N + (k + 1) / 2 := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j, hj⟩ := he
    have hk : k = 2 * j := by omega
    subst hk
    have h := F_add_two_mul_le hN j
    omega
  · obtain ⟨j, hj⟩ := ho
    subst hj
    have h := F_add_two_mul_le hN j
    have h2 := F_succ_le (N + 2 * j)
    have he : N + (2 * j + 1) = N + 2 * j + 1 := by omega
    rw [he]
    omega

/-  ### `F` is unbounded -/

/-- A crude but explicit supply of Sidon sets: for every `n` there is a Sidon set of size `n + 1`
inside `{1, …, 2 ^ (n + 1) - 1}`. Built by repeatedly appending `2 * max + 1`, which keeps the
Sidon property by `Finset.IsSidon.insert_ge_max'`. The bound is exponentially far from the truth
(the extremal size is of order `√N`), but it is all that is needed to make the threshold function
`L` below total. -/
theorem exists_sidon_card (n : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.Icc 1 (2 ^ (n + 1) - 1) ∧ IsSidon (B : Set ℕ) ∧ n + 1 ≤ B.card := by
  induction n with
  | zero => exact ⟨{1}, by decide, by simp [IsSidon], by simp⟩
  | succ n ih =>
    obtain ⟨B, hsub, hB, hcard⟩ := ih
    have hne : B.Nonempty := Finset.card_pos.1 (by omega)
    have hpow : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    have hp1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have hmax : B.max' hne ≤ 2 ^ (n + 1) - 1 :=
      (Finset.mem_Icc.1 (hsub (B.max'_mem hne))).2
    have hs : 2 * B.max' hne + 1 ≤ 2 ^ (n + 1 + 1) - 1 := by omega
    have hSid := Finset.IsSidon.insert_ge_max' hne hB hs
    have hnotmem : (2 ^ (n + 1 + 1) - 1) ∉ B := by
      intro hmem
      have := Finset.le_max' B _ hmem
      omega
    refine ⟨B ∪ {2 ^ (n + 1 + 1) - 1}, ?_, by simpa using hSid, ?_⟩
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · have hx' := Finset.mem_Icc.1 (hsub hx)
        exact Finset.mem_Icc.2 ⟨hx'.1, by omega⟩
      · rw [Finset.mem_singleton] at hx
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · have hins : B ∪ {2 ^ (n + 1 + 1) - 1} = insert (2 ^ (n + 1 + 1) - 1) B := by
        rw [Finset.union_comm, Finset.insert_eq]
      rw [hins, Finset.card_insert_of_notMem hnotmem]
      omega

/-- An explicit lower bound for `F`, enough to show it is unbounded. -/
theorem succ_le_F_two_pow (n : ℕ) : n + 1 ≤ F (2 ^ (n + 1) - 1) := by
  obtain ⟨B, hsub, hB, hcard⟩ := exists_sidon_card n
  exact hcard.trans (card_le_F hsub hB)

/-- `F` takes arbitrarily large values. -/
theorem exists_le_F (m : ℕ) : ∃ N, m ≤ F N :=
  ⟨2 ^ (m + 1) - 1, le_trans (Nat.le_succ m) (succ_le_F_two_pow m)⟩

/-  ### The Sidon threshold function `L` -/

/-- `L m` is the least `N` for which `{1, …, N}` contains a Sidon set with `m` elements.
So `L m - 1` is the length of an optimal Golomb ruler with `m` marks, and the jumps of `F` are
exactly the numbers `L m - 1`. -/
noncomputable def L (m : ℕ) : ℕ := sInf {N | m ≤ F N}

/-- The defining Galois connection between `L` and `F`. -/
theorem L_le_iff {m N : ℕ} : L m ≤ N ↔ m ≤ F N := by
  have hne : {N | m ≤ F N}.Nonempty := exists_le_F m
  have hmem : m ≤ F (L m) := Nat.sInf_mem hne
  exact ⟨fun h => hmem.trans (F_mono h), fun h => Nat.sInf_le h⟩

/-- The strict form of the Galois connection. -/
theorem lt_L_iff {m N : ℕ} : F N < m ↔ N < L m := by
  rw [← not_le, ← not_le (a := L m), L_le_iff]

/-- `L` is a genuine inverse to `F`: the threshold is attained exactly. -/
theorem F_L (m : ℕ) : F (L m) = m := by
  have h1 : m ≤ F (L m) := L_le_iff.1 le_rfl
  have hF0 : F 0 = 0 := by decide
  rcases Nat.eq_zero_or_pos (L m) with hz | hz
  · rw [hz] at h1 ⊢
    rw [hF0] at h1 ⊢
    omega
  · obtain ⟨j, hj⟩ : ∃ j, L m = j + 1 := ⟨L m - 1, by omega⟩
    have hFj : F j < m := lt_L_iff.2 (by omega)
    have hstep := F_succ_le j
    rw [hj] at h1 ⊢
    omega

/-- `L` is nondecreasing. -/
theorem L_mono : Monotone L := by
  intro a b hab
  rw [L_le_iff, F_L]
  exact hab

/-- **The jumps of `F` are exactly the numbers `L m - 1`.** This is what makes `L` the right
bookkeeping device for the target: the target controls the spacing of the jumps of `F`, and here
that spacing becomes the spacing of the values of `L`. -/
theorem jump_iff_eq_L {N : ℕ} : F N < F (N + 1) ↔ ∃ m, L m = N + 1 := by
  constructor
  · intro h
    exact ⟨F (N + 1), le_antisymm (L_le_iff.2 le_rfl) (lt_L_iff.1 h)⟩
  · rintro ⟨m, hm⟩
    have h1 : F N < m := lt_L_iff.2 (by omega)
    have h2 : m ≤ F (N + 1) := by rw [← hm]; exact le_of_eq (F_L m).symm
    omega

/-- **The case `k = 2`, read on the threshold function.** Consecutive Sidon thresholds differ by
at least `2` from `m = 2` on; equivalently, the length of an optimal Golomb ruler grows by at least
`2` when a mark is added. (At `m = 1` this fails: `L 1 = 1` and `L 2 = 2`.) -/
theorem L_add_two_le {m : ℕ} (hm : 2 ≤ m) : L m + 2 ≤ L (m + 1) := by
  have hF1 : F 1 = 1 := by decide
  have h2 : 1 < L m := lt_L_iff.1 (by omega)
  obtain ⟨j, hj⟩ : ∃ j, L m = j + 1 := ⟨L m - 1, by omega⟩
  have hFj : F j < m := lt_L_iff.2 (by omega)
  have hstep : F (j + 2) ≤ F j + 1 := F_add_two_le (by omega)
  have hlt : j + 2 < L (m + 1) := lt_L_iff.1 (by omega)
  omega

/-- **Reformulation of the target.** The reward obligation of `Erdos155.erdos_155` says exactly
that the gaps between consecutive Sidon thresholds are eventually larger than any fixed `k`. -/
theorem erdos_155_iff_gap_eventually :
    (∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1) ↔
      ∀ k : ℕ, ∀ᶠ m in atTop, L m + k ≤ L (m + 1) := by
  constructor
  · intro h k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · filter_upwards with m
      have := L_mono (show m ≤ m + 1 by omega)
      omega
    · obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (h k hk)
      refine eventually_atTop.2 ⟨F N₀ + 1, fun m hm => ?_⟩
      have hlt : N₀ < L m := lt_L_iff.1 (by omega)
      obtain ⟨j, hj⟩ : ∃ j, L m = j + 1 := ⟨L m - 1, by omega⟩
      have hFj : F j < m := lt_L_iff.2 (by omega)
      have hstep := hN₀ j (by omega)
      have hlt2 : j + k < L (m + 1) := lt_L_iff.1 (by omega)
      omega
  · intro h k hk
    obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (h k)
    refine eventually_atTop.2 ⟨L M₀, fun N hN => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hM : M₀ ≤ F N := by
      calc M₀ = F (L M₀) := (F_L M₀).symm
        _ ≤ F N := F_mono hN
    have hgap := hM₀ (F N + 1) (by omega)
    have h1 : N < L (F N + 1) := lt_L_iff.1 (by omega)
    have h2 : L (F N + 1 + 1) ≤ N + k := L_le_iff.2 (by omega)
    omega

/-- **Reformulation of the target, in limit form.** `Erdos155.erdos_155`'s reward obligation holds
if and only if the gaps `L (m + 1) - L m` between consecutive optimal Golomb ruler lengths tend to
infinity. -/
theorem erdos_155_iff_gap_tendsto :
    (∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1) ↔
      Tendsto (fun m => L (m + 1) - L m) atTop atTop := by
  rw [erdos_155_iff_gap_eventually, tendsto_atTop]
  constructor
  · intro h k
    filter_upwards [h k] with m hm
    omega
  · intro h k
    filter_upwards [h k] with m hm
    have := L_mono (show m ≤ m + 1 by omega)
    omega

/-  ### Small values, checked by kernel evaluation -/

/-- The jumps of `F` below `7` are exactly at `0`, `1`, `3` and `6`, checked by kernel evaluation
of `Finset.maxSidonSubsetCard` on `{1, …, N}` for `N ≤ 7`. Two consequences: the gaps `1 → 3` and
`3 → 6` show that the bound `F (N + 2) ≤ F N + 1` of `F_add_two_le` is attained at `N = 1` (so it
cannot be improved to `F (N + 2) ≤ F N`), and the adjacent jumps at `0` and `1` are exactly why
`F (0 + 2) ≤ F 0 + 1` fails, which is what the hypothesis `1 ≤ N` there excludes. -/
theorem jump_lt_seven (N : ℕ) (hN : N < 7) :
    F N < F (N + 1) ↔ (N = 0 ∨ N = 1 ∨ N = 3 ∨ N = 6) := by
  interval_cases N <;> decide +kernel

/-- The first four Sidon thresholds, i.e. the optimal Golomb rulers with `1, 2, 3, 4` marks have
lengths `0, 1, 3, 6`. Note `L 2 = L 1 + 1`, so the hypothesis `2 ≤ m` in `L_add_two_le` is sharp. -/
theorem L_values : L 1 = 1 ∧ L 2 = 2 ∧ L 3 = 4 ∧ L 4 = 7 := by
  refine ⟨le_antisymm (L_le_iff.2 (by decide +kernel)) ?_,
    le_antisymm (L_le_iff.2 (by decide +kernel)) ?_,
    le_antisymm (L_le_iff.2 (by decide +kernel)) ?_,
    le_antisymm (L_le_iff.2 (by decide +kernel)) ?_⟩
  · exact lt_L_iff.1 (by decide +kernel)
  · exact lt_L_iff.1 (by decide +kernel)
  · exact lt_L_iff.1 (by decide +kernel)
  · exact lt_L_iff.1 (by decide +kernel)

/-- The hypothesis `1 ≤ N` in `F_add_two_le` cannot be dropped: `F 2 = 2` while `F 0 = 0`. -/
theorem not_forall_F_add_two_le : ¬ ∀ N, F (N + 2) ≤ F N + 1 := by
  intro h
  exact absurd (h 0) (by decide)

/-- The next case, `k = 3`, genuinely needs the "for all sufficiently large `N`" of the target:
unlike `F_add_two_le`, the inequality `F (N + 3) ≤ F N + 1` is not available for all `N ≥ 1`, since
it fails at `N = 1` where `F 4 = 3` and `F 1 = 1`. -/
theorem not_forall_F_add_three_le : ¬ ∀ N, 1 ≤ N → F (N + 3) ≤ F N + 1 := by
  intro h
  exact absurd (h 1 le_rfl) (by decide)

/-- **Why the reflection argument stops at `k = 2`.** Run the proof of `F_add_two_le` for `k = 3`:
the two jumps must then sit at `N` and `N + 2` (they cannot be adjacent, by `F_add_two_le` itself),
`sidon_inter_reflect` still forces `1` and `N + 3` into a maximum Sidon set `B ⊆ {1, …, N + 3}`,
and the case analysis on whether `2 ∈ B` and whether `N + 2 ∈ B` closes two of its four branches
but leaves the configurations `{1, 2, N + 1, N + 3}` and `{1, 3, N + 2, N + 3}` standing. This
lemma checks that those two really are Sidon for every `N ≥ 4`, so no repeated sum can be extracted
from them and the argument genuinely has to be replaced, not merely pushed, to reach `k = 3`. -/
theorem sidon_gap_two_configs {N : ℕ} (hN : 4 ≤ N) :
    IsSidon ({1, 2, N + 1, N + 3} : Set ℕ) ∧ IsSidon ({1, 3, N + 2, N + 3} : Set ℕ) := by
  constructor <;>
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
    rcases hi₁ with rfl | rfl | rfl | rfl <;> rcases hj₁ with rfl | rfl | rfl | rfl <;>
      rcases hi₂ with rfl | rfl | rfl | rfl <;> rcases hj₂ with rfl | rfl | rfl | rfl <;> omega

/-  ### Use sites against the target -/

/-- The `k = 2` instance of the reward obligation of `Erdos155.erdos_155`, in the exact shape the
target uses. -/
theorem eventually_F_add_two_le : ∀ᶠ N in atTop, Erdos155.F (N + 2) ≤ Erdos155.F N + 1 :=
  eventually_atTop.2 ⟨1, fun _ hN => F_add_two_le hN⟩

/-- **Worked use site.** The reward obligation of `Erdos155.erdos_155` is *equivalent* to its
restriction to `k ≥ 3`: the cases `k = 1` and `k = 2` are discharged here outright, by `F_succ_le`
and `F_add_two_le`. Both directions are proved, so no strength is lost or silently assumed. -/
theorem erdos_155_iff_three_le :
    (∀ k ≥ 1, ∀ᶠ N in atTop, Erdos155.F (N + k) ≤ Erdos155.F N + 1) ↔
      (∀ k ≥ 3, ∀ᶠ N in atTop, Erdos155.F (N + k) ≤ Erdos155.F N + 1) := by
  refine ⟨fun h k hk => h k (by omega), fun h k hk => ?_⟩
  match k, hk with
  | 1, _ => exact Eventually.of_forall F_succ_le
  | 2, _ => exact eventually_F_add_two_le
  | (j + 3), _ => exact h (j + 3) (by omega)

/-- **Worked use site, combined.** Putting the two reformulations together: the reward obligation
of `Erdos155.erdos_155` holds iff the Golomb gaps diverge, and by `L_add_two_le` that divergence
is already known past the value `2`. -/
theorem erdos_155_iff_gap_three_le :
    (∀ k ≥ 1, ∀ᶠ N in atTop, Erdos155.F (N + k) ≤ Erdos155.F N + 1) ↔
      (∀ k ≥ 3, ∀ᶠ m in atTop, L m + k ≤ L (m + 1)) := by
  rw [erdos_155_iff_gap_eventually]
  refine ⟨fun h k _ => h k, fun h k => ?_⟩
  rcases Nat.lt_or_ge k 3 with hk | hk
  · filter_upwards [h 3 le_rfl] with m hm
    omega
  · exact h k hk

end Contribution.Erdos155Golomb
