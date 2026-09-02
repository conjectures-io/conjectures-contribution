import Mathlib
import FormalConjectures.ErdosProblems.«196»

/-!
# A usable interface for monotone 4-term APs (Erdős Problem 196)

Target: `Erdos196.erdos_196`, whose right-hand side is `∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4`.

`HasMonotoneAP f k` is defined as the existence of a list `l` of indices, pairwise increasing,
such that `l.map f` is a `List.IsAPOfLength k`, and `List.IsAPOfLength` is itself defined by
`∃ a d, s = (List.range k).map (a + · • d) ∨ s = (List.range k).reverse.map (a + · • d)`.
So every attempt to build or to refute a monotone 4-term AP starts by fighting a list equality
against `List.range 4` under a `reverse` / `no reverse` disjunction, by re-deriving the length
of the index list, and by turning `List.Pairwise (· < ·)` into usable inequalities.

This file removes that friction for `k = 3, 4` over `ℕ` and adds the structural lemmas that
either direction of an attack on the problem needs.

A later solver can use declaration `Contribution.Erdos196MonotoneAP.hasMonotoneAP_four_iff` to
discharge or simplify obligation `∀ (f : ℕ ≃ ℕ), HasMonotoneAP f 4` (the right-hand side of
`Erdos196.erdos_196`) in target erdos-196: it replaces the list / `range` / `reverse` definition
by the elementary statement `∃ b₀ < b₁ < b₂ < b₃, f b₀ + f b₂ = 2 * f b₁ ∧ f b₁ + f b₃ = 2 * f b₂`,
in which the increasing and the decreasing case have been merged into two linear equations.

Main declarations:
* `listIsAPOfLength_three_iff`, `listIsAPOfLength_four_iff`: `List.IsAPOfLength` on an explicit
  3- or 4-element list, as an `rcases`-friendly disjunction over an arbitrary additive
  commutative monoid (so also usable for `Erdos195`, the analogous problem over `ℤ`).
* `listIsAPOfLength_three_iff_nat`, `listIsAPOfLength_four_iff_nat`: over `ℕ` the two cases
  merge into linear equations, so the disjunction disappears entirely.
* `hasMonotoneAP_three_iff`, `hasMonotoneAP_four_iff`: the resulting index characterisations.
* `not_hasMonotoneAP_four_iff`: the shape in which one verifies an avoiding permutation.
* `hasMonotoneAP_four_iff_of_injective`: for injective `f` (e.g. a permutation) the progression
  really is strictly monotone, i.e. the common difference is positive. This is what the
  docstring of `HasMonotoneAP` claims informally ("increasing or decreasing"); the definition
  alone does not give it, since a constant list is an AP of every length.
* `listIsAPOfLength_two_nat`, `hasMonotoneAP_two`: the degenerate cases; over `ℕ` every two
  element list is an AP, so `HasMonotoneAP f k` is automatic for `k ≤ 2`.
* `hasMonotoneAP_mono`: monotonicity in the length `k`.
* `hasMonotoneAP_of_comp_strictMono`: passing to a subsequence, the standard reduction step.
* `not_hasMonotoneAP_three_of_growth`, `not_hasMonotoneAP_four_of_growth`: an obstruction at the
  level of sequences; a sequence of naturals with `2 * f n < f (n + 1)` has no monotone 3-term AP,
  hence none of length 4. That growth hypothesis is the only one needed, since it already forces
  `f` to be strictly monotone. Caveat: no `f : ℕ ≃ ℕ` satisfies it, so these two lemmas are a
  non-vacuity check about sequences and are *not* progress on the target.
* `no_equiv_satisfies_growth`: the proof of that caveat - no permutation of `ℕ` satisfies
  `∀ n, 2 * f n < f (n + 1)`, so growth-based obstructions cannot be instantiated at the target's
  binder `∀ (f : ℕ ≃ ℕ)`.
* `hasMonotoneAP_three_of_equiv`: every permutation of `ℕ` does contain a monotone 3-term AP
  (Davis-Entringer-Graham-Simmons), proved here by an infinite descent through
  `hasMonotoneAP_three_iff`. This settles, inside the pool's own vocabulary, the case below the
  open one, and it is the worked example of the interface being used to *prove* a statement of
  the shape of the target.
* `erdos_196_iff_indices`, `hasMonotoneAP_of_le_three`, `hasMonotoneAP_four_refl`: further worked
  use sites against the target statement itself.
* `not_hasMonotoneAP_four_pow`: a non-vacuity witness at the level of sequences - the powers of `3`
  have no monotone 4-term AP. They are not a permutation of `ℕ`, so this bounds no permutation;
  it only shows that `HasMonotoneAP · 4` is not automatic.

*References:*
- [erdosproblems.com/196](https://www.erdosproblems.com/196)
- [DEGS77] Davis, J. A., Entringer, R. C., Graham, R. L. and Simmons, G. J., On permutations
  containing no long arithmetic progressions. Acta Arith. 34 (1977/78), 81-90. They proved that
  every permutation of the positive integers contains a monotone 3-term AP, and that some
  permutation contains no monotone 5-term AP; the 4-term case is the open problem 196.
- [LV11] LeSaulnier, T. D. and Vijay, S., On permutations avoiding arithmetic progressions.
  Discrete Math. 311 (2011), 205-207.
- [Ad23] Adenwalla, S., A Generalisation of a Result on Monotone Arithmetic Progressions in
  Permutations of the Positive Integers. arXiv:2302.09662 (2023).
-/

namespace Contribution.Erdos196MonotoneAP

section Monoid

variable {α : Type*} [AddCommMonoid α]

/-- Unfolding of `List.IsAPOfLength` for an explicit three element list: the first term of the
progression is `x₀` (increasing case) or `x₂` (decreasing case). -/
theorem listIsAPOfLength_three_iff {x₀ x₁ x₂ : α} :
    ([x₀, x₁, x₂] : List α).IsAPOfLength 3 ↔
      (∃ d, x₁ = x₀ + d ∧ x₂ = x₀ + 2 • d) ∨ (∃ d, x₁ = x₂ + d ∧ x₀ = x₂ + 2 • d) := by
  unfold List.IsAPOfLength List.IsAPOfLengthWith
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.cons.injEq, zero_smul, add_zero,
    one_smul, and_true]
  constructor
  · rintro ⟨a, d, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
    · exact Or.inl ⟨d, rfl, rfl⟩
    · exact Or.inr ⟨d, rfl, rfl⟩
  · rintro (⟨d, rfl, rfl⟩ | ⟨d, rfl, rfl⟩)
    · exact ⟨x₀, d, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨x₂, d, Or.inr ⟨rfl, rfl, rfl⟩⟩

/-- Unfolding of `List.IsAPOfLength` for an explicit four element list: the first term of the
progression is `x₀` (increasing case) or `x₃` (decreasing case). -/
theorem listIsAPOfLength_four_iff {x₀ x₁ x₂ x₃ : α} :
    ([x₀, x₁, x₂, x₃] : List α).IsAPOfLength 4 ↔
      (∃ d, x₁ = x₀ + d ∧ x₂ = x₀ + 2 • d ∧ x₃ = x₀ + 3 • d) ∨
      (∃ d, x₂ = x₃ + d ∧ x₁ = x₃ + 2 • d ∧ x₀ = x₃ + 3 • d) := by
  unfold List.IsAPOfLength List.IsAPOfLengthWith
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.cons.injEq, zero_smul, add_zero,
    one_smul, and_true]
  constructor
  · rintro ⟨a, d, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact Or.inl ⟨d, rfl, rfl, rfl⟩
    · exact Or.inr ⟨d, rfl, rfl, rfl⟩
  · rintro (⟨d, rfl, rfl, rfl⟩ | ⟨d, rfl, rfl, rfl⟩)
    · exact ⟨x₀, d, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · exact ⟨x₃, d, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩

variable {β : Type*} [Preorder β] {f : β → α} {k k' : ℕ}

/-- `HasMonotoneAP` is monotone in the length: a monotone `k`-term AP contains a monotone
`k'`-term AP for every `k' ≤ k`. Both the increasing and the decreasing case are covered, by
taking a prefix resp. a suffix of the index list. -/
theorem hasMonotoneAP_mono (h : HasMonotoneAP f k) (hk : k' ≤ k) : HasMonotoneAP f k' := by
  obtain ⟨l, ⟨a, d, hap⟩, hp⟩ := h
  have htake : (List.range k).take k' = List.range k' := by
    simp [Nat.min_eq_left hk]
  rcases hap with hap | hap
  · refine ⟨l.take k', ⟨a, d, Or.inl ?_⟩, List.Pairwise.sublist (List.take_sublist _ _) hp⟩
    rw [List.map_take, hap, ← List.map_take, htake]
  · refine ⟨l.drop (k - k'), ⟨a, d, Or.inr ?_⟩, List.Pairwise.sublist (List.drop_sublist _ _) hp⟩
    have hrev : (List.range k).reverse.drop (k - k') = (List.range k').reverse := by
      rw [List.drop_reverse, List.length_range, Nat.sub_sub_self hk, htake]
    rw [List.map_drop, hap, ← List.map_drop, hrev]

/-- Passing to a subsequence: if the subsequence `f ∘ g` of `f` (indices selected by a strictly
monotone `g`) has a monotone `k`-term AP, then so does `f`. This is the standard reduction step
when producing monotone progressions: it is enough to find one on any increasing set of
indices. -/
theorem hasMonotoneAP_of_comp_strictMono {γ : Type*} [Preorder γ] {g : γ → β} (hg : StrictMono g)
    (h : HasMonotoneAP (f ∘ g) k) : HasMonotoneAP f k := by
  obtain ⟨l, hap, hp⟩ := h
  refine ⟨l.map g, ?_, List.pairwise_map.mpr (hp.imp fun hlt => hg hlt)⟩
  rwa [List.map_map]

end Monoid

section Nat

/-- Over `ℕ` every two element list is an arithmetic progression of length `2`. -/
theorem listIsAPOfLength_two_nat {x y : ℕ} : ([x, y] : List ℕ).IsAPOfLength 2 := by
  unfold List.IsAPOfLength List.IsAPOfLengthWith
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.cons_append, List.cons.injEq, zero_smul, add_zero,
    one_smul, and_true]
  rcases le_total x y with h | h
  · exact ⟨x, y - x, Or.inl ⟨rfl, by omega⟩⟩
  · exact ⟨y, x - y, Or.inr ⟨by omega, rfl⟩⟩

/-- Over `ℕ`, a three element list is an arithmetic progression of length `3` iff the middle
entry is the average of the outer two. The increasing and the decreasing case of
`List.IsAPOfLength` collapse into this single linear equation. -/
theorem listIsAPOfLength_three_iff_nat {x₀ x₁ x₂ : ℕ} :
    ([x₀, x₁, x₂] : List ℕ).IsAPOfLength 3 ↔ x₀ + x₂ = 2 * x₁ := by
  rw [listIsAPOfLength_three_iff]
  simp only [smul_eq_mul]
  constructor
  · rintro (⟨d, h₁, h₂⟩ | ⟨d, h₁, h₂⟩) <;> omega
  · intro h
    rcases le_total x₀ x₁ with hle | hle
    · exact Or.inl ⟨x₁ - x₀, by omega, by omega⟩
    · exact Or.inr ⟨x₁ - x₂, by omega, by omega⟩

/-- Over `ℕ`, a four element list is an arithmetic progression of length `4` iff both of its
consecutive triples satisfy the averaging equation. The increasing and the decreasing case of
`List.IsAPOfLength` collapse into these two linear equations. -/
theorem listIsAPOfLength_four_iff_nat {x₀ x₁ x₂ x₃ : ℕ} :
    ([x₀, x₁, x₂, x₃] : List ℕ).IsAPOfLength 4 ↔ x₀ + x₂ = 2 * x₁ ∧ x₁ + x₃ = 2 * x₂ := by
  rw [listIsAPOfLength_four_iff]
  simp only [smul_eq_mul]
  constructor
  · rintro (⟨d, h₁, h₂, h₃⟩ | ⟨d, h₁, h₂, h₃⟩) <;> omega
  · rintro ⟨h₁, h₂⟩
    rcases le_total x₀ x₁ with hle | hle
    · exact Or.inl ⟨x₁ - x₀, by omega, by omega, by omega⟩
    · exact Or.inr ⟨x₂ - x₃, by omega, by omega, by omega⟩

/-- Index characterisation of a monotone 3-term AP of a sequence of naturals. -/
theorem hasMonotoneAP_three_iff (f : ℕ → ℕ) :
    HasMonotoneAP f 3 ↔ ∃ b₀ b₁ b₂, b₀ < b₁ ∧ b₁ < b₂ ∧ f b₀ + f b₂ = 2 * f b₁ := by
  constructor
  · rintro ⟨l, hap, hp⟩
    have hlen : l.length = 3 := by simpa using hap.length
    obtain ⟨b₀, b₁, b₂, rfl⟩ := List.length_eq_three.mp hlen
    simp only [List.map_cons, List.map_nil] at hap
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq,
      implies_true, true_and, or_false, IsEmpty.forall_iff] at hp
    exact ⟨b₀, b₁, b₂, by omega, by omega, listIsAPOfLength_three_iff_nat.mp hap⟩
  · rintro ⟨b₀, b₁, b₂, h₀, h₁, hap⟩
    refine ⟨[b₀, b₁, b₂], ?_, ?_⟩
    · simpa using listIsAPOfLength_three_iff_nat.mpr hap
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _)) <;>
        intro x hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;> omega

/-- Index characterisation of a monotone 4-term AP of a sequence of naturals: this is the
right-hand side of `Erdos196.erdos_196`, unfolded into elementary arithmetic. -/
theorem hasMonotoneAP_four_iff (f : ℕ → ℕ) :
    HasMonotoneAP f 4 ↔ ∃ b₀ b₁ b₂ b₃, b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧
      f b₀ + f b₂ = 2 * f b₁ ∧ f b₁ + f b₃ = 2 * f b₂ := by
  constructor
  · rintro ⟨l, hap, hp⟩
    have hlen : l.length = 4 := by simpa using hap.length
    obtain ⟨b₀, b₁, b₂, b₃, rfl⟩ := List.length_eq_four.mp hlen
    simp only [List.map_cons, List.map_nil] at hap
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp, forall_eq,
      implies_true, true_and, or_false, IsEmpty.forall_iff] at hp
    obtain ⟨e₁, e₂⟩ := listIsAPOfLength_four_iff_nat.mp hap
    exact ⟨b₀, b₁, b₂, b₃, by omega, by omega, by omega, e₁, e₂⟩
  · rintro ⟨b₀, b₁, b₂, b₃, h₀, h₁, h₂, e₁, e₂⟩
    refine ⟨[b₀, b₁, b₂, b₃], ?_, ?_⟩
    · simpa using listIsAPOfLength_four_iff_nat.mpr ⟨e₁, e₂⟩
    · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
        (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))) <;>
        intro x hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;> omega

/-- The form in which one verifies that a candidate permutation avoids monotone 4-term APs. -/
theorem not_hasMonotoneAP_four_iff (f : ℕ → ℕ) :
    ¬ HasMonotoneAP f 4 ↔ ∀ b₀ b₁ b₂ b₃, b₀ < b₁ → b₁ < b₂ → b₂ < b₃ →
      f b₀ + f b₂ = 2 * f b₁ → f b₁ + f b₃ ≠ 2 * f b₂ := by
  rw [hasMonotoneAP_four_iff]
  push_neg
  rfl

/-- Every sequence of naturals has a monotone 2-term AP, so the content of `HasMonotoneAP`
starts at `k = 3`. -/
theorem hasMonotoneAP_two (f : ℕ → ℕ) : HasMonotoneAP f 2 := by
  refine ⟨[0, 1], by simpa using listIsAPOfLength_two_nat, ?_⟩
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-- For an injective `f` (for instance a permutation of `ℕ`) a monotone 4-term AP really is
strictly increasing or strictly decreasing: the common difference `d` is positive. The
definition of `HasMonotoneAP` by itself does not give this, since a constant list is an
arithmetic progression of every length. -/
theorem hasMonotoneAP_four_iff_of_injective {f : ℕ → ℕ} (hf : Function.Injective f) :
    HasMonotoneAP f 4 ↔ ∃ b₀ b₁ b₂ b₃ d, 0 < d ∧ b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧
      ((f b₁ = f b₀ + d ∧ f b₂ = f b₀ + 2 * d ∧ f b₃ = f b₀ + 3 * d) ∨
       (f b₂ = f b₃ + d ∧ f b₁ = f b₃ + 2 * d ∧ f b₀ = f b₃ + 3 * d)) := by
  rw [hasMonotoneAP_four_iff]
  constructor
  · rintro ⟨b₀, b₁, b₂, b₃, h₀, h₁, h₂, e₁, e₂⟩
    have hne : f b₀ ≠ f b₁ := fun h => absurd (hf h) (by omega)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨b₀, b₁, b₂, b₃, f b₁ - f b₀, by omega, h₀, h₁, h₂,
        Or.inl ⟨by omega, by omega, by omega⟩⟩
    · exact ⟨b₀, b₁, b₂, b₃, f b₂ - f b₃, by omega, h₀, h₁, h₂,
        Or.inr ⟨by omega, by omega, by omega⟩⟩
  · rintro ⟨b₀, b₁, b₂, b₃, d, hd, h₀, h₁, h₂, ⟨e₁, e₂, e₃⟩ | ⟨e₁, e₂, e₃⟩⟩ <;>
      exact ⟨b₀, b₁, b₂, b₃, h₀, h₁, h₂, by omega, by omega⟩

/-- An obstruction at the level of sequences: a sequence of naturals whose terms more than double
has no monotone 3-term AP, because the last term of a putative progression already exceeds twice
the middle one. The doubling hypothesis is the only one required - it already forces `f` to be
strictly monotone.

Caveat: no `f : ℕ ≃ ℕ` satisfies `∀ n, 2 * f n < f (n + 1)` (that is `no_equiv_satisfies_growth`
below), so this lemma can never be instantiated at the target's binder. It witnesses that
`HasMonotoneAP · 3` is not automatic for sequences; it is not progress on Erdős 196. -/
theorem not_hasMonotoneAP_three_of_growth {f : ℕ → ℕ} (hgrow : ∀ n, 2 * f n < f (n + 1)) :
    ¬ HasMonotoneAP f 3 := by
  have hmono : Monotone f :=
    (strictMono_nat_of_lt_succ fun n => by have := hgrow n; omega).monotone
  rw [hasMonotoneAP_three_iff]
  rintro ⟨b₀, b₁, b₂, h₀, h₁, hap⟩
  have h₂ : f (b₁ + 1) ≤ f b₂ := hmono (by omega)
  have h₃ := hgrow b₁
  omega

/-- The same obstruction at length `4`, via `hasMonotoneAP_mono`, and with the same caveat: no
permutation of `ℕ` satisfies the growth hypothesis. -/
theorem not_hasMonotoneAP_four_of_growth {f : ℕ → ℕ} (hgrow : ∀ n, 2 * f n < f (n + 1)) :
    ¬ HasMonotoneAP f 4 := fun h =>
  not_hasMonotoneAP_three_of_growth hgrow (hasMonotoneAP_mono h (by norm_num))

end Nat

section Permutations

variable {k : ℕ}

/-- **The case below the target.** Every permutation of `ℕ` contains a monotone
3-term arithmetic progression, i.e. the analogue of the right-hand side of `Erdos196.erdos_196`
with `4` replaced by `3` is true. This is the result of Davis, Entringer, Graham and Simmons;
the proof here is an infinite descent, and it is written entirely through
`hasMonotoneAP_three_iff`, which is what makes it short.

Let `p` be the position of the value `0` and let `d` exceed every value occurring at a position
`< p`. For `v ≥ d` the value `v` sits at a position `> p`, so the progression `0, v, 2 * v`
forces the position of `2 * v` to be to the *left* of the position of `v` (otherwise the three
positions increase and we have a monotone AP). Iterating along `d, 2 * d, 4 * d, …` produces an
infinite strictly decreasing sequence of positions, which is absurd. -/
theorem hasMonotoneAP_three_of_equiv (f : ℕ ≃ ℕ) : HasMonotoneAP (⇑f) 3 := by
  rw [hasMonotoneAP_three_iff]
  by_contra hcon
  push_neg at hcon
  set p : ℕ := f.symm 0 with hp
  set d : ℕ := (Finset.range p).sup (fun i => f i) + 1 with hd
  have hpos : ∀ v, d ≤ v → p < f.symm v := by
    intro v hv
    rcases lt_trichotomy (f.symm v) p with h | h | h
    · exfalso
      have hmem : f.symm v ∈ Finset.range p := Finset.mem_range.mpr h
      have hsup := Finset.le_sup (f := fun i => f i) hmem
      simp only [Equiv.apply_symm_apply] at hsup
      omega
    · exfalso
      have hv0 : v = 0 := by simpa [hp] using congrArg f h
      omega
    · exact h
  have key : ∀ v, d ≤ v → f.symm (2 * v) < f.symm v := by
    intro v hv
    have h1 : p < f.symm v := hpos v hv
    have h2 : p < f.symm (2 * v) := hpos (2 * v) (by omega)
    rcases lt_trichotomy (f.symm (2 * v)) (f.symm v) with h | h | h
    · exact h
    · exact absurd (by simpa using congrArg f h : 2 * v = v) (by omega)
    · exact absurd (by simp [hp]) (hcon p (f.symm v) (f.symm (2 * v)) h1 h)
  have hdesc : ∀ i, f.symm (2 ^ i * d) + i ≤ f.symm d := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      have hle : d ≤ 2 ^ n * d := Nat.le_mul_of_pos_left d (Nat.two_pow_pos n)
      have hkey := key (2 ^ n * d) hle
      have heq : 2 ^ (n + 1) * d = 2 * (2 ^ n * d) := by ring
      rw [heq]
      omega
  have hfin := hdesc (f.symm d + 1)
  omega

/-- **Use site.** For a permutation of `ℕ`, monotone APs of length up to `3` are automatic;
`k = 4` is exactly the open case asked about by `Erdos196.erdos_196`. -/
theorem hasMonotoneAP_of_le_three (f : ℕ ≃ ℕ) (hk : k ≤ 3) : HasMonotoneAP (⇑f) k :=
  hasMonotoneAP_mono (hasMonotoneAP_three_of_equiv f) hk

/-- **The growth obstruction is empty at the target's binder.** No permutation of `ℕ` satisfies
`∀ n, 2 * f n < f (n + 1)`: such an `f` is strictly monotone, hence `n ≤ f n`, which forces
`f 0 = 0` and `f 1 = 1`, hence `3 ≤ f 2`, leaving no position for the value `2`.

Consequently `not_hasMonotoneAP_three_of_growth` and `not_hasMonotoneAP_four_of_growth` cannot be
applied to any `f : ℕ ≃ ℕ`; they say something about sequences, not about `Erdos196.erdos_196`. -/
theorem no_equiv_satisfies_growth (f : ℕ ≃ ℕ) : ¬ ∀ n, 2 * f n < f (n + 1) := by
  intro hgrow
  have hmono : StrictMono (⇑f) := strictMono_nat_of_lt_succ fun n => by have := hgrow n; omega
  have hle : ∀ n, n ≤ f n := fun n => by simpa using hmono.id_le n
  have h0 : f 0 = 0 := by
    have h₁ := hle (f.symm 0)
    rw [f.apply_symm_apply] at h₁
    have h₂ := f.apply_symm_apply 0
    rw [Nat.le_zero.mp h₁] at h₂
    exact h₂
  have h1 : f 1 = 1 := by
    have h₁ := hle (f.symm 1)
    rw [f.apply_symm_apply] at h₁
    have h₂ := f.apply_symm_apply 1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h₁ with h | h <;> rw [h] at h₂ <;> omega
  have hg : 2 * f 1 < f 2 := by simpa using hgrow 1
  have h₁ := hle (f.symm 2)
  rw [f.apply_symm_apply] at h₁
  have h₂ := f.apply_symm_apply 2
  have hcases : f.symm 2 = 0 ∨ f.symm 2 = 1 ∨ f.symm 2 = 2 := by omega
  rcases hcases with h | h | h <;> rw [h] at h₂ <;> omega

end Permutations

section UseSite

/- ### Further use sites against the target statement -/

/-- **Use site.** The right-hand side of `Erdos196.erdos_196` is equivalent to an elementary
arithmetic statement about indices, with no lists and no case split on the direction of the
progression. A solver can `rw [erdos_196_iff_indices]` and work with the right-hand side. -/
theorem erdos_196_iff_indices :
    (∀ f : ℕ ≃ ℕ, HasMonotoneAP (⇑f) 4) ↔
      ∀ f : ℕ ≃ ℕ, ∃ b₀ b₁ b₂ b₃, b₀ < b₁ ∧ b₁ < b₂ ∧ b₂ < b₃ ∧
        f b₀ + f b₂ = 2 * f b₁ ∧ f b₁ + f b₃ = 2 * f b₂ :=
  forall_congr' fun f => hasMonotoneAP_four_iff (⇑f)

/-- **Use site, sanity check.** The identity permutation has a monotone 4-term AP; the witness is
produced from two `norm_num`-checkable equations, with no list manipulation. -/
theorem hasMonotoneAP_four_refl : HasMonotoneAP (⇑(Equiv.refl ℕ)) 4 :=
  (hasMonotoneAP_four_iff _).mpr ⟨0, 1, 2, 3, by norm_num⟩

/-- **Use site, non-vacuity.** `HasMonotoneAP · 4` is not automatic: the powers of `3` have no
monotone 4-term AP. (They are of course not a permutation of `ℕ`, which is what makes
`erdos_196` hard.) -/
theorem not_hasMonotoneAP_four_pow : ¬ HasMonotoneAP (fun n => 3 ^ n) 4 := by
  refine not_hasMonotoneAP_four_of_growth fun n => ?_
  have h : (0 : ℕ) < 3 ^ n := pow_pos (by norm_num) n
  rw [pow_succ]
  omega

end UseSite

end Contribution.Erdos196MonotoneAP

