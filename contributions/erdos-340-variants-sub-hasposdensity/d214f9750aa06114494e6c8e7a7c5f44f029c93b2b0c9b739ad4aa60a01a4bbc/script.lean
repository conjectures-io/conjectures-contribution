import FormalConjectures.ErdosProblems.«340»
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Structural and density-interface contributions toward Erdős problem 340

This standalone contribution contains 71 public theorems and 7 supporting
definitions, with all new declarations in the Contribution namespace: 59
structural and finite-window theorems, 10 exhaustion and density-interface
theorems, and 2 fixed-prefix limit theorems.
It establishes finite Sidon difference identities, exhaustion of fixed windows,
conditional analytic density interfaces, and the zero-density limit for each
fixed finite prefix. It does not prove or refute the infinite density conjecture.
-/
/-
Structural contributions toward Erdős problem 340, positive density of A - A.
This section proves 20 structural results; it does not claim the open density target.
Proof dependencies are audited during submission preparation.
-/

open scoped Pointwise

namespace Contribution.Erdos340


/-- The first `n + 1` elements produced by the pinned greedy Sidon construction. -/
def greedyPrefix (n : ℕ) : Finset ℕ := (Finset.greedySidon.aux n).1.1

private theorem greedyPrefix_zero : greedyPrefix 0 = {1} := rfl

private theorem greedy_zero : Finset.greedySidon 0 = 1 := rfl

private theorem greedyPrefix_succ (n : ℕ) :
    greedyPrefix (n + 1) = greedyPrefix n ∪ {Finset.greedySidon (n + 1)} := by
  simp only [greedyPrefix, Finset.greedySidon, Finset.greedySidon.aux]

private theorem greedy_mem_greedyPrefix (n : ℕ) : Finset.greedySidon n ∈ greedyPrefix n := by
  cases n with
  | zero => simp [greedyPrefix_zero, greedy_zero]
  | succ n => rw [greedyPrefix_succ]; simp

private theorem greedyPrefix_nonempty (n : ℕ) : (greedyPrefix n).Nonempty :=
  ⟨_, greedy_mem_greedyPrefix n⟩

theorem greedyPrefix_isSidon (n : ℕ) : IsSidon (greedyPrefix n : Set ℕ) :=
  (Finset.greedySidon.aux n).1.2

private theorem greedyPrefix_subset_succ (n : ℕ) : greedyPrefix n ⊆ greedyPrefix (n + 1) := by
  rw [greedyPrefix_succ]
  exact Finset.subset_union_left

theorem greedyPrefix_monotone : Monotone greedyPrefix :=
  monotone_nat_of_le_succ greedyPrefix_subset_succ

private theorem greedy_succ_gt_greedyPrefix (n : ℕ) {a : ℕ} (ha : a ∈ greedyPrefix n) :
    a < Finset.greedySidon (n + 1) := by
  have h := (Finset.greedySidon.go (greedyPrefix n) (greedyPrefix_isSidon n)
    ((greedyPrefix n).max' (greedyPrefix_nonempty n) + 1)).2.1
  have hle : a ≤ (greedyPrefix n).max' (greedyPrefix_nonempty n) := Finset.le_max' _ a ha
  have heq : Finset.greedySidon (n + 1) =
      (Finset.greedySidon.go (greedyPrefix n) (greedyPrefix_isSidon n)
        ((greedyPrefix n).max' (greedyPrefix_nonempty n) + 1)).1 := by
    dsimp only [Finset.greedySidon, Finset.greedySidon.aux]
    apply congrArg (fun s => (Finset.greedySidon.go (greedyPrefix n) (greedyPrefix_isSidon n) s).val)
    exact dif_pos (greedyPrefix_nonempty n)
  rw [heq]
  omega

theorem greedy_strictMono : StrictMono Finset.greedySidon := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact greedy_succ_gt_greedyPrefix n (greedy_mem_greedyPrefix n)

theorem greedy_index_lower_bound (n : ℕ) : n + 1 ≤ Finset.greedySidon n := by
  induction n with
  | zero => simp [greedy_zero]
  | succ n ih =>
    have h : Finset.greedySidon n < Finset.greedySidon (n + 1) := greedy_strictMono (Nat.lt_succ_self n)
    change n + 1 + 1 ≤ Finset.greedySidon (n + 1)
    omega

private theorem greedy_not_mem_greedyPrefix (n : ℕ) : Finset.greedySidon (n + 1) ∉ greedyPrefix n := by
  intro h
  exact (Nat.lt_irrefl _ (greedy_succ_gt_greedyPrefix n h))

theorem greedyPrefix_card (n : ℕ) : (greedyPrefix n).card = n + 1 := by
  induction n with
  | zero => simp [greedyPrefix_zero]
  | succ n ih =>
    rw [greedyPrefix_succ, Finset.union_singleton, Finset.card_insert_of_notMem
      (greedy_not_mem_greedyPrefix n), ih]

theorem greedyPrefix_eq_image (n : ℕ) :
    greedyPrefix n = (Finset.range (n + 1)).image Finset.greedySidon := by
  induction n with
  | zero => simp [greedyPrefix_zero, greedy_zero]
  | succ n ih =>
    simp only [greedyPrefix_succ, ih, Finset.range_add_one, Finset.image_insert,
      Finset.union_singleton]

theorem range_isSidon : IsSidon (Set.range Finset.greedySidon) := by
  intro a ha b hb c hc d hd habcd
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨l, rfl⟩ := hd
  let m := max (max i j) (max k l)
  have hi : i ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hj : j ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hk : k ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hl : l ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  exact greedyPrefix_isSidon m _ (greedyPrefix_monotone hi (greedy_mem_greedyPrefix i))
    _ (greedyPrefix_monotone hj (greedy_mem_greedyPrefix j))
    _ (greedyPrefix_monotone hk (greedy_mem_greedyPrefix k))
    _ (greedyPrefix_monotone hl (greedy_mem_greedyPrefix l)) habcd


theorem greedyPrefix_max (n : ℕ) :
    (greedyPrefix n).max' (greedyPrefix_nonempty n) = Finset.greedySidon n := by
  apply le_antisymm
  · apply Finset.max'_le
    intro a ha
    rw [greedyPrefix_eq_image] at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact greedy_strictMono.monotone (by simpa using Finset.mem_range.mp hi)
  · exact Finset.le_max' _ _ (greedy_mem_greedyPrefix n)

private theorem greedy_go_minimal {A : Finset ℕ} (hA : IsSidon (A : Set ℕ))
    {m x : ℕ} (hm : m ≤ x) (hx : x ∉ A) (hs : IsSidon (↑(A ∪ {x}) : Set ℕ)) :
    (Finset.greedySidon.go A hA m).1 ≤ x := by
  unfold Finset.greedySidon.go
  split_ifs with h
  · exact Nat.find_min' _ ⟨hm, hx, hs⟩
  · exact hm

theorem greedy_succ_le_of_admissible (n : ℕ) {x : ℕ}
    (hx : Finset.greedySidon n < x)
    (hs : IsSidon (↑(greedyPrefix n ∪ {x}) : Set ℕ)) :
    Finset.greedySidon (n + 1) ≤ x := by
  have hxA : x ∉ greedyPrefix n := by
    intro h
    have := Finset.le_max' (greedyPrefix n) x h
    rw [greedyPrefix_max] at this
    omega
  have heq : Finset.greedySidon (n + 1) =
      (Finset.greedySidon.go (greedyPrefix n) (greedyPrefix_isSidon n)
        ((greedyPrefix n).max' (greedyPrefix_nonempty n) + 1)).1 := by
    dsimp only [Finset.greedySidon, Finset.greedySidon.aux]
    apply congrArg (fun s => (Finset.greedySidon.go (greedyPrefix n) (greedyPrefix_isSidon n) s).val)
    exact dif_pos (greedyPrefix_nonempty n)
  rw [heq]
  apply greedy_go_minimal _ _ hxA hs
  rw [greedyPrefix_max]
  omega

theorem greedy_skipped_collision (n : ℕ) {x : ℕ}
    (hx : Finset.greedySidon n < x) (hxnext : x < Finset.greedySidon (n + 1)) :
    ∃ a ∈ greedyPrefix n, ∃ b ∈ greedyPrefix n, ∃ c ∈ greedyPrefix n,
      x + a = b + c := by
  have hbound : ∀ a ∈ greedyPrefix n, a < x := by
    intro a ha
    have := Finset.le_max' (greedyPrefix n) a ha
    rw [greedyPrefix_max] at this
    omega
  by_contra! hcollision
  have hs : IsSidon (↑(greedyPrefix n ∪ {x}) : Set ℕ) := by
    rw [Finset.coe_union, Finset.coe_singleton]
    apply (Set.IsSidon.insert (greedyPrefix_isSidon n)).2
    right
    intro a ha b hb
    constructor
    · have := hbound a ha
      have := hbound b hb
      omega
    · intro c hc
      exact hcollision a ha b hb c hc
  have := greedy_succ_le_of_admissible n hx hs
  omega

/-- A positive difference in a Sidon set has a unique ordered representation. -/
theorem positiveDifference_unique {A : Set ℕ} (hA : IsSidon A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : b < a) (hcd : d < c) (heq : a - b = c - d) : a = c ∧ b = d := by
  have hs : a + d = c + b := by omega
  rcases hA a ha c hc d hd b hb hs with h | h
  · exact ⟨h.1, h.2.symm⟩
  · omega

/-- Uniqueness of positive differences is equivalent to the Sidon condition. -/
theorem sidon_iff_positiveDifference_unique {A : Set ℕ} : IsSidon A ↔
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      b < a → d < c → a - b = c - d → a = c ∧ b = d := by
  constructor
  · intro h a ha b hb c hc d hd hab hcd heq
    exact positiveDifference_unique h ha hb hc hd hab hcd heq
  · intro h a ha b hb c hc d hd heq
    by_cases hab : a = b
    · exact Or.inl ⟨hab, by omega⟩
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hh := h b hb a ha c hc d hd hlt (by omega) (by omega)
        exact Or.inr ⟨hh.2, hh.1.symm⟩
      · have hh := h a ha b hb d hd c hc hgt (by omega) (by omega)
        exact Or.inr ⟨hh.1, hh.2.symm⟩

/-- A Sidon set contains no nonconstant three-term arithmetic progression. -/
theorem sidon_no_three_term {A : Set ℕ} (hA : IsSidon A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (heq : a + c = b + b) : a = b ∧ b = c := by
  rcases hA a ha b hb c hc b hb heq with h | h <;> omega

/-- Above all current entries, insertion fails exactly when a new positive
difference repeats an old positive difference. -/
theorem insert_above_iff {A : Set ℕ} (hA : IsSidon A) {x : ℕ}
    (hx : ∀ a ∈ A, a < x) :
    IsSidon (A ∪ {x}) ↔
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, b < c → x - a ≠ c - b := by
  have hnot : x ∉ A := fun h ↦ Nat.lt_irrefl x (hx x h)
  rw [Set.IsSidon.insert hA]
  simp only [hnot, false_or]
  constructor
  · intro h a ha b hb c hc hbc heq
    exact (h b hb c hc).2 a ha (by have := hx a ha; omega)
  · intro h a ha b hb
    refine ⟨?_, ?_⟩
    · have := hx a ha
      have := hx b hb
      omega
    · intro c hc heq
      have hxc := hx c hc
      have hab : a < b := by omega
      exact h c hc a ha b hb hab (by omega)

/-- Rejected candidates have a concrete three-entry arithmetic obstruction. -/
theorem rejection_iff {A : Set ℕ} (hA : IsSidon A) {x : ℕ}
    (hx : ∀ a ∈ A, a < x) :
    ¬ IsSidon (A ∪ {x}) ↔
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, b < c ∧ x = a + (c - b) := by
  rw [insert_above_iff hA hx]
  push Not
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hbc, heq⟩
    exact ⟨a, ha, b, hb, c, hc, hbc, by have := hx a ha; omega⟩
  · rintro ⟨a, ha, b, hb, c, hc, hbc, heq⟩
    exact ⟨a, ha, b, hb, c, hc, hbc, by omega⟩

/-- Positive differences of a finite set, without multiplicities. -/
def positiveDifferences (s : Finset ℕ) : Finset ℕ :=
  ((s ×ˢ s).filter (fun p ↦ p.1 < p.2)).image (fun p ↦ p.2 - p.1)

/-- All natural-number differences, including truncated subtraction. -/
def finiteDifferences (s : Finset ℕ) : Finset ℕ :=
  (s ×ˢ s).image (fun p ↦ p.2 - p.1)

/-- Sidon uniqueness gives the exact number of positive prefix differences. -/
theorem positiveDifferences_card {s : Finset ℕ} (hs : IsSidon (s : Set ℕ)) :
    (positiveDifferences s).card = s.card.choose 2 := by
  unfold positiveDifferences
  calc
    _ = ((s ×ˢ s).filter (fun p ↦ p.1 < p.2)).card := by
      apply Finset.card_image_iff.mpr
      intro p hp q hq heq
      change p ∈ (s ×ˢ s).filter (fun p ↦ p.1 < p.2) at hp
      change q ∈ (s ×ˢ s).filter (fun p ↦ p.1 < p.2) at hq
      simp only [Finset.mem_filter, Finset.mem_product] at hp hq
      have h := positiveDifference_unique hs hp.1.2 hp.1.1 hq.1.2 hq.1.1
        hp.2 hq.2 heq
      exact Prod.ext h.2 h.1
    _ = s.card.choose 2 := Finset.card_product_filter_lt

/-- Natural subtraction adds just zero to the positive difference set. -/
theorem finiteDifferences_eq_insert_zero {s : Finset ℕ} (hs : s.Nonempty) :
    finiteDifferences s = insert 0 (positiveDifferences s) := by
  ext d
  simp only [finiteDifferences, positiveDifferences, Finset.mem_image,
    Finset.mem_product, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, heq⟩
    by_cases hab : a < b
    · exact Or.inr ⟨(a, b), ⟨⟨ha, hb⟩, hab⟩, heq⟩
    · left
      dsimp at heq
      omega
  · rintro (rfl | ⟨p, hp, heq⟩)
    · obtain ⟨a, ha⟩ := hs
      exact ⟨(a, a), ⟨ha, ha⟩, Nat.sub_self a⟩
    · exact ⟨p, hp.1, heq⟩

/-- A nonempty finite Sidon set has exactly `choose(card,2)+1` natural differences. -/
theorem finiteDifferences_card {s : Finset ℕ} (hs : IsSidon (s : Set ℕ))
    (hne : s.Nonempty) : (finiteDifferences s).card = s.card.choose 2 + 1 := by
  rw [finiteDifferences_eq_insert_zero hne, Finset.card_insert_of_notMem,
    positiveDifferences_card hs]
  intro h
  simp only [positiveDifferences, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product] at h
  obtain ⟨⟨a, b⟩, ⟨_, hab⟩, heq⟩ := h
  dsimp at hab heq
  omega

/-- Exact finite-prefix difference count for the pinned greedy sequence. -/
theorem greedyPrefix_difference_card (n : ℕ) :
    (finiteDifferences (greedyPrefix n)).card = (n + 1).choose 2 + 1 := by
  rw [finiteDifferences_card (greedyPrefix_isSidon n), greedyPrefix_card]
  apply Finset.card_pos.mp
  rw [greedyPrefix_card]
  omega

/-- Prefix differences give a rigorous lower bound for the full difference set
at the last prefix value. This is a finite bound, not a limiting-density claim. -/
theorem greedyPrefix_difference_lower_bound (n : ℕ) :
    (n + 1).choose 2 + 1 ≤
      (((Set.range Finset.greedySidon - Set.range Finset.greedySidon) ∩
        Set.Iio (Finset.greedySidon n)).ncard) := by
  rw [← greedyPrefix_difference_card n]
  have hsub : (↑(finiteDifferences (greedyPrefix n)) : Set ℕ) ⊆
      (Set.range Finset.greedySidon - Set.range Finset.greedySidon) ∩
        Set.Iio (Finset.greedySidon n) := by
    intro d hd
    obtain ⟨⟨a, b⟩, hp, heq⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    rw [greedyPrefix_eq_image] at ha hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    change Finset.greedySidon j - Finset.greedySidon i = d at heq
    constructor
    · rw [← heq]
      exact Set.sub_mem_sub (Set.mem_range_self j) (Set.mem_range_self i)
    · have hib := greedy_index_lower_bound i
      have hjb : Finset.greedySidon j ≤ Finset.greedySidon n :=
        greedy_strictMono.monotone (by have := Finset.mem_range.mp hj; omega)
      change d < Finset.greedySidon n
      have hn := greedy_index_lower_bound n
      omega
  simpa using Set.ncard_le_ncard hsub

end Contribution.Erdos340

/-
Finite insertion and adjacent-prefix difference identities for Erdős 340.
These results extend StructuralLemmas without any limiting-density claim.
-/

namespace Contribution.Erdos340

theorem mem_positiveDifferences_iff {s : Finset ℕ} {d : ℕ} :
    d ∈ positiveDifferences s ↔ ∃ a ∈ s, ∃ b ∈ s, a < b ∧ b - a = d := by
  simp only [positiveDifferences, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product, Prod.exists]
  aesop

theorem mem_finiteDifferences_iff {s : Finset ℕ} {d : ℕ} :
    d ∈ finiteDifferences s ↔ ∃ a ∈ s, ∃ b ∈ s, b - a = d := by
  simp only [finiteDifferences, Finset.mem_image, Finset.mem_product, Prod.exists]
  aesop

theorem positiveDifferences_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    positiveDifferences s ⊆ positiveDifferences t := by
  intro d hd
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_positiveDifferences_iff.mp hd
  exact mem_positiveDifferences_iff.mpr ⟨a, hst ha, b, hst hb, hab, rfl⟩

theorem finiteDifferences_mono {s t : Finset ℕ} (hst : s ⊆ t) :
    finiteDifferences s ⊆ finiteDifferences t := by
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_finiteDifferences_iff.mp hd
  exact mem_finiteDifferences_iff.mpr ⟨a, hst ha, b, hst hb, rfl⟩

/-- Differences supplied by appending a value above a finite set. -/
def appendedDifferences (s : Finset ℕ) (x : ℕ) : Finset ℕ :=
  s.image (fun a => x - a)

theorem appendedDifferences_card {s : Finset ℕ} {x : ℕ}
    (hx : ∀ a ∈ s, a < x) : (appendedDifferences s x).card = s.card := by
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  change x - a = x - b at hab
  have := hx a ha
  have := hx b hb
  omega

theorem zero_not_mem_appendedDifferences {s : Finset ℕ} {x : ℕ}
    (hx : ∀ a ∈ s, a < x) : 0 ∉ appendedDifferences s x := by
  rintro hd
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hd
  have := hx a ha
  omega

theorem positiveDifferences_insert_above {s : Finset ℕ} {x : ℕ}
    (hx : ∀ a ∈ s, a < x) :
    positiveDifferences (insert x s) = positiveDifferences s ∪ appendedDifferences s x := by
  ext d
  constructor
  · intro hd
    obtain ⟨a, ha, b, hb, hab, heq⟩ := mem_positiveDifferences_iff.mp hd
    rcases Finset.mem_insert.mp ha with rfl | has
    · rcases Finset.mem_insert.mp hb with rfl | hbs
      · omega
      · have := hx b hbs
        omega
    · rcases Finset.mem_insert.mp hb with rfl | hbs
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, has, heq⟩)
      · exact Finset.mem_union_left _
          (mem_positiveDifferences_iff.mpr ⟨a, has, b, hbs, hab, heq⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact positiveDifferences_mono (Finset.subset_insert _ _) hd
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      exact mem_positiveDifferences_iff.mpr
        ⟨a, Finset.mem_insert_of_mem ha, x, Finset.mem_insert_self _ _, hx a ha, rfl⟩

theorem finiteDifferences_insert_above {s : Finset ℕ} {x : ℕ}
    (hne : s.Nonempty) (hx : ∀ a ∈ s, a < x) :
    finiteDifferences (insert x s) = finiteDifferences s ∪ appendedDifferences s x := by
  rw [finiteDifferences_eq_insert_zero (Finset.insert_nonempty x s),
    positiveDifferences_insert_above hx, finiteDifferences_eq_insert_zero hne]
  exact (Finset.insert_union 0 _ _).symm

/-- Sidon uniqueness makes every appended difference new. -/
theorem finiteDifferences_disjoint_appended {s : Finset ℕ} {x : ℕ}
    (hs : IsSidon (↑(insert x s) : Set ℕ)) (hx : ∀ a ∈ s, a < x) :
    Disjoint (finiteDifferences s) (appendedDifferences s x) := by
  apply Finset.disjoint_left.mpr
  intro d hd hnew
  obtain ⟨a, ha, b, hb, hab⟩ := mem_finiteDifferences_iff.mp hd
  obtain ⟨c, hc, hxc⟩ := Finset.mem_image.mp hnew
  have hcx := hx c hc
  have hba : a < b := by omega
  have heq : b - a = x - c := by omega
  have h := positiveDifference_unique hs
    (Finset.mem_insert_of_mem hb) (Finset.mem_insert_of_mem ha)
    (Finset.mem_insert_self x s) (Finset.mem_insert_of_mem hc) hba hcx heq
  have := hx b hb
  omega

theorem greedyPrefix_member_bounds {n a : ℕ} (ha : a ∈ greedyPrefix n) :
    1 ≤ a ∧ a ≤ Finset.greedySidon n := by
  rw [greedyPrefix_eq_image] at ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  exact ⟨(by have := greedy_index_lower_bound i; omega), greedy_strictMono.monotone hi'⟩

theorem greedyPrefix_all_lt_next (n : ℕ) :
    ∀ a ∈ greedyPrefix n, a < Finset.greedySidon (n + 1) := by
  intro a ha
  exact lt_of_le_of_lt (greedyPrefix_member_bounds ha).2
    (greedy_strictMono (Nat.lt_succ_self n))

theorem greedyPrefix_succ_eq_insert (n : ℕ) :
    greedyPrefix (n + 1) = insert (Finset.greedySidon (n + 1)) (greedyPrefix n) := by
  simp only [greedyPrefix_eq_image, Finset.range_add_one, Finset.image_insert]

private theorem prefix_nonempty (n : ℕ) : (greedyPrefix n).Nonempty := by
  apply Finset.card_pos.mp
  rw [greedyPrefix_card]
  omega

theorem greedyPrefix_difference_monotone :
    Monotone (fun n => finiteDifferences (greedyPrefix n)) := by
  intro m n hmn
  exact finiteDifferences_mono (greedyPrefix_monotone hmn)

theorem greedyPrefix_difference_succ (n : ℕ) :
    finiteDifferences (greedyPrefix (n + 1)) =
      finiteDifferences (greedyPrefix n) ∪
        appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1)) := by
  rw [greedyPrefix_succ_eq_insert]
  exact finiteDifferences_insert_above (prefix_nonempty n) (greedyPrefix_all_lt_next n)

theorem greedyPrefix_difference_disjoint_next (n : ℕ) :
    Disjoint (finiteDifferences (greedyPrefix n))
      (appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1))) := by
  apply finiteDifferences_disjoint_appended
  · rw [← greedyPrefix_succ_eq_insert]
    exact greedyPrefix_isSidon (n + 1)
  · exact greedyPrefix_all_lt_next n

theorem greedyPrefix_appended_card (n : ℕ) :
    (appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1))).card = n + 1 := by
  rw [appendedDifferences_card (greedyPrefix_all_lt_next n), greedyPrefix_card]

/-- Appending the next greedy term adds exactly `n + 1` distinct differences. -/
theorem greedyPrefix_difference_card_succ (n : ℕ) :
    (finiteDifferences (greedyPrefix (n + 1))).card =
      (finiteDifferences (greedyPrefix n)).card + (n + 1) := by
  rw [greedyPrefix_difference_succ,
    Finset.card_union_of_disjoint (greedyPrefix_difference_disjoint_next n),
    greedyPrefix_appended_card]

theorem greedyPrefix_difference_sdiff (n : ℕ) :
    finiteDifferences (greedyPrefix (n + 1)) \ finiteDifferences (greedyPrefix n) =
      appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1)) := by
  rw [greedyPrefix_difference_succ]
  have hd := Finset.disjoint_left.mp (greedyPrefix_difference_disjoint_next n)
  ext d
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

theorem greedyPrefix_difference_sdiff_card (n : ℕ) :
    (finiteDifferences (greedyPrefix (n + 1)) \ finiteDifferences (greedyPrefix n)).card =
      n + 1 := by
  rw [greedyPrefix_difference_sdiff, greedyPrefix_appended_card]

theorem greedyPrefix_difference_lt_last {n d : ℕ}
    (hd : d ∈ finiteDifferences (greedyPrefix n)) : d < Finset.greedySidon n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_finiteDifferences_iff.mp hd
  have := greedyPrefix_member_bounds ha
  have := greedyPrefix_member_bounds hb
  omega

/-- Packing all distinct prefix differences below the final value. -/
theorem greedyPrefix_packing_bound (n : ℕ) :
    (n + 1).choose 2 + 1 ≤ Finset.greedySidon n := by
  rw [← greedyPrefix_difference_card n, ← Finset.card_range (Finset.greedySidon n)]
  apply Finset.card_le_card
  intro d hd
  exact Finset.mem_range.mpr (greedyPrefix_difference_lt_last hd)

end Contribution.Erdos340

/-
Counts and ratios in finite windows [0, N). The cutoff is a value cutoff,
whereas greedyPrefix n contains n + 1 sequence terms. No asymptotic
hypothesis or conclusion is used in this section.
-/

namespace Contribution.Erdos340

def differenceWindow (s : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (finiteDifferences s).filter (fun d => d < N)

noncomputable def differenceWindowDensity (s : Finset ℕ) (N : ℕ) : ℝ :=
  (differenceWindow s N).card / (N : ℝ)

theorem differenceWindow_mono_set {s t : Finset ℕ} (hst : s ⊆ t) (N : ℕ) :
    differenceWindow s N ⊆ differenceWindow t N := by
  intro d hd
  obtain ⟨hd, hN⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨finiteDifferences_mono hst hd, hN⟩

theorem differenceWindow_mono_cutoff (s : Finset ℕ) {M N : ℕ} (hMN : M ≤ N) :
    differenceWindow s M ⊆ differenceWindow s N := by
  intro d hd
  obtain ⟨hd, hM⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd, lt_of_lt_of_le hM hMN⟩

theorem differenceWindow_card_le_cutoff (s : Finset ℕ) (N : ℕ) :
    (differenceWindow s N).card ≤ N := by
  rw [← Finset.card_range N]
  apply Finset.card_le_card
  intro d hd
  exact Finset.mem_range.mpr (by simpa using (Finset.mem_filter.mp hd).2)

theorem differenceWindow_card_le_total (s : Finset ℕ) (N : ℕ) :
    (differenceWindow s N).card ≤ (finiteDifferences s).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem differenceWindowDensity_nonneg (s : Finset ℕ) (N : ℕ) :
    0 ≤ differenceWindowDensity s N := by
  unfold differenceWindowDensity
  positivity

theorem differenceWindowDensity_le_one (s : Finset ℕ) (N : ℕ) :
    differenceWindowDensity s N ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg N)
  exact_mod_cast differenceWindow_card_le_cutoff s N

/-- The ratio agrees with the canonical partial-density definition for the finite set. -/
theorem differenceWindowDensity_eq_partialDensity (s : Finset ℕ) (N : ℕ) :
    differenceWindowDensity s N =
      (↑(finiteDifferences s) : Set ℕ).partialDensity Set.univ N := by
  have heq : (↑(differenceWindow s N) : Set ℕ) =
      (↑(finiteDifferences s) : Set ℕ) ∩ Set.Iio N := by
    ext d
    simp [differenceWindow]
  simp only [differenceWindowDensity, Set.partialDensity, Set.inter_univ,
    Set.univ_inter, ← heq, Set.ncard_coe_finset]
  simp

theorem le_differenceWindowDensity_iff {s : Finset ℕ} {N : ℕ}
    (hN : 0 < N) (c : ℝ) :
    c ≤ differenceWindowDensity s N ↔ c * N ≤ ((differenceWindow s N).card : ℝ) := by
  exact le_div_iff₀ (by exact_mod_cast hN)

theorem differenceWindowDensity_le_iff {s : Finset ℕ} {N : ℕ}
    (hN : 0 < N) (c : ℝ) :
    differenceWindowDensity s N ≤ c ↔ ((differenceWindow s N).card : ℝ) ≤ c * N := by
  exact div_le_iff₀ (by exact_mod_cast hN)

theorem greedyPrefix_window_eq_total (n N : ℕ) (hN : Finset.greedySidon n ≤ N) :
    differenceWindow (greedyPrefix n) N = finiteDifferences (greedyPrefix n) := by
  apply Finset.filter_eq_self.mpr
  intro d hd
  exact lt_of_lt_of_le (greedyPrefix_difference_lt_last hd) hN

theorem greedyPrefix_window_card (n N : ℕ) (hN : Finset.greedySidon n ≤ N) :
    (differenceWindow (greedyPrefix n) N).card = (n + 1).choose 2 + 1 := by
  rw [greedyPrefix_window_eq_total n N hN, greedyPrefix_difference_card]

theorem greedyPrefix_window_density (n N : ℕ) (hN : Finset.greedySidon n ≤ N) :
    differenceWindowDensity (greedyPrefix n) N =
      (((n + 1).choose 2 + 1 : ℕ) : ℝ) / N := by
  rw [differenceWindowDensity, greedyPrefix_window_card n N hN]

/-- At an arbitrary cutoff, the new count is exactly the number of new differences below it. -/
theorem greedyPrefix_window_card_succ (n N : ℕ) :
    (differenceWindow (greedyPrefix (n + 1)) N).card =
      (differenceWindow (greedyPrefix n) N).card +
      ((appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1))).filter
        (fun d => d < N)).card := by
  unfold differenceWindow
  rw [greedyPrefix_difference_succ, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  exact (greedyPrefix_difference_disjoint_next n).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- An equivalent update counts old sequence entries in a short interval below the new term. -/
theorem greedyPrefix_window_increment_tail (n N : ℕ) :
    ((appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1))).filter
      (fun d => d < N)).card =
      ((greedyPrefix n).filter (fun a => Finset.greedySidon (n + 1) < a + N)).card := by
  have heq : (appendedDifferences (greedyPrefix n) (Finset.greedySidon (n + 1))).filter
      (fun d => d < N) =
      ((greedyPrefix n).filter (fun a => Finset.greedySidon (n + 1) < a + N)).image
        (fun a => Finset.greedySidon (n + 1) - a) := by
    ext d
    simp only [appendedDifferences, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hlt⟩
      have := greedyPrefix_all_lt_next n a ha
      exact ⟨a, ⟨ha, by omega⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hlt⟩, rfl⟩
      have := greedyPrefix_all_lt_next n a ha
      exact ⟨⟨a, ha, rfl⟩, by omega⟩
  rw [heq]
  apply Finset.card_image_iff.mpr
  intro a ha b hb hab
  change Finset.greedySidon (n + 1) - a = Finset.greedySidon (n + 1) - b at hab
  have := greedyPrefix_all_lt_next n a (Finset.mem_filter.mp ha).1
  have := greedyPrefix_all_lt_next n b (Finset.mem_filter.mp hb).1
  omega

theorem greedyPrefix_window_card_succ_le (n N : ℕ) :
    (differenceWindow (greedyPrefix (n + 1)) N).card ≤
      (differenceWindow (greedyPrefix n) N).card + (n + 1) := by
  rw [greedyPrefix_window_card_succ]
  apply Nat.add_le_add_left
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    (greedyPrefix_appended_card n)

theorem greedyPrefix_window_density_monotone (N : ℕ) :
    Monotone (fun n => differenceWindowDensity (greedyPrefix n) N) := by
  intro m n hmn
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast Finset.card_le_card
    (differenceWindow_mono_set (greedyPrefix_monotone hmn) N)

theorem greedyPrefix_window_density_succ_le (n N : ℕ) :
    differenceWindowDensity (greedyPrefix (n + 1)) N ≤
      differenceWindowDensity (greedyPrefix n) N + ((n + 1 : ℕ) : ℝ) / N := by
  unfold differenceWindowDensity
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact_mod_cast greedyPrefix_window_card_succ_le n N

/-- A window no larger than the next sequence gap acquires no new differences. -/
theorem greedyPrefix_window_unchanged_below_gap (n N : ℕ)
    (hN : N ≤ Finset.greedySidon (n + 1) - Finset.greedySidon n) :
    differenceWindow (greedyPrefix (n + 1)) N = differenceWindow (greedyPrefix n) N := by
  apply Finset.Subset.antisymm
  · intro d hd
    obtain ⟨hd, hdN⟩ := Finset.mem_filter.mp hd
    rw [greedyPrefix_difference_succ] at hd
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Finset.mem_filter.mpr ⟨hd, hdN⟩
    · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hd
      have := (greedyPrefix_member_bounds ha).2
      omega
  · exact differenceWindow_mono_set (greedyPrefix_monotone (Nat.le_succ n)) N

end Contribution.Erdos340

/- Finite-window exhaustion for the actual greedy difference set.
These results do not assert an asymptotic density or a uniform rate. -/

open Filter
open scoped Pointwise Topology
open Contribution.Erdos340

namespace Contribution.Erdos340Asymptotics

def greedyDifferenceSet : Set ℕ :=
  Set.range Finset.greedySidon - Set.range Finset.greedySidon

private theorem prefixDifference_monotone :
    Monotone (fun n ↦ finiteDifferences (greedyPrefix n)) := by
  intro m n hmn d hd
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hd
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
  exact Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr
    ⟨greedyPrefix_monotone hmn ha, greedyPrefix_monotone hmn hb⟩, heq⟩

/-- Every full-set difference occurs in some prefix, with no uniform index bound asserted. -/
theorem mem_difference_iff_exists_prefix (d : ℕ) :
    d ∈ greedyDifferenceSet ↔ ∃ n, d ∈ finiteDifferences (greedyPrefix n) := by
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    refine ⟨max i j, Finset.mem_image.mpr ⟨(Finset.greedySidon j, Finset.greedySidon i), ?_, heq⟩⟩
    apply Finset.mem_product.mpr
    constructor
    · rw [greedyPrefix_eq_image]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    · rw [greedyPrefix_eq_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  · rintro ⟨n, hd⟩
    obtain ⟨⟨a, b⟩, hp, heq⟩ := Finset.mem_image.mp hd
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
    rw [greedyPrefix_eq_image] at ha hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    rw [← heq]
    exact Set.sub_mem_sub (Set.mem_range_self j) (Set.mem_range_self i)

/-- Each fixed finite window eventually stabilizes to the full difference set.
The threshold may depend arbitrarily on the window. -/
theorem eventually_prefix_window_eq (N : ℕ) :
    ∀ᶠ m in atTop,
      (↑(finiteDifferences (greedyPrefix m)) : Set ℕ) ∩ Set.Iio N =
        greedyDifferenceSet ∩ Set.Iio N := by
  have hfin : (greedyDifferenceSet ∩ Set.Iio N).Finite :=
    (Set.finite_Iio N).subset Set.inter_subset_right
  have hall : ∀ᶠ m in atTop, ∀ d ∈ greedyDifferenceSet ∩ Set.Iio N,
      d ∈ finiteDifferences (greedyPrefix m) := by
    apply (Filter.eventually_all_finite hfin).mpr
    intro d hd
    obtain ⟨n, hn⟩ := (mem_difference_iff_exists_prefix d).mp hd.1
    exact (eventually_ge_atTop n).mono fun m hm ↦ prefixDifference_monotone hm hn
  apply hall.mono
  intro m hm
  ext d
  constructor
  · rintro ⟨hd, hdN⟩
    exact ⟨(mem_difference_iff_exists_prefix d).mpr ⟨m, hd⟩, hdN⟩
  · intro hd
    exact ⟨hm d hd, hd.2⟩

/-- A finite prefix gives a density lower bound at every window containing it. -/
theorem prefix_density_lower_bound (n N : ℕ) (hn : Finset.greedySidon n ≤ N) :
    (((n + 1).choose 2 + 1 : ℕ) : ℝ) / N ≤
      greedyDifferenceSet.partialDensity Set.univ N := by
  have hcount : (n + 1).choose 2 + 1 ≤
      (greedyDifferenceSet ∩ Set.Iio N).ncard := by
    apply (greedyPrefix_difference_lower_bound n).trans
    refine Set.ncard_le_ncard ?_ ((Set.finite_Iio N).subset Set.inter_subset_right)
    intro d hd
    exact ⟨hd.1, lt_of_lt_of_le hd.2 hn⟩
  have hreal : (((n + 1).choose 2 + 1 : ℕ) : ℝ) ≤
      ((greedyDifferenceSet ∩ Set.Iio N).ncard : ℝ) := by exact_mod_cast hcount
  simpa [Set.partialDensity] using div_le_div_of_nonneg_right hreal (Nat.cast_nonneg N)

end Contribution.Erdos340Asymptotics

/-
Analytic interfaces for natural density. Every result applies to arbitrary sets
of natural numbers. The hypotheses needed for a positive limiting density remain
explicit; this file does not establish them for the greedy Sidon difference set.
-/

open Filter
open scoped Topology

namespace Contribution.DensityInterface

/-- Positive lower density is exactly an eventually uniform positive lower bound. -/
theorem lowerDensity_pos_iff_eventually_lower_bound (S : Set ℕ) :
    0 < S.lowerDensity ↔
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ N in atTop, c ≤ S.partialDensity Set.univ N := by
  have hnonneg (N : ℕ) : 0 ≤ S.partialDensity Set.univ N := by
    unfold Set.partialDensity
    positivity
  have hnonempty : {c : ℝ | ∀ᶠ N in atTop, c ≤ S.partialDensity Set.univ N}.Nonempty :=
    ⟨0, .of_forall hnonneg⟩
  have hbounded : BddAbove {c : ℝ | ∀ᶠ N in atTop, c ≤ S.partialDensity Set.univ N} := by
    refine ⟨1, ?_⟩
    intro c hc
    obtain ⟨N, hN⟩ := hc.exists
    exact hN.trans (Set.partialDensity_le_one S Set.univ N)
  change 0 < sSup {c : ℝ | ∀ᶠ N in atTop, c ≤ S.partialDensity Set.univ N} ↔ _
  constructor
  · intro h
    obtain ⟨c, hc, hpos⟩ := exists_lt_of_lt_csSup hnonempty h
    exact ⟨c, hpos, hc⟩
  · rintro ⟨c, hpos, hc⟩
    exact hpos.trans_le (le_csSup hbounded hc)

/-- The eventual bound can be stated with an explicit threshold on the natural variable. -/
theorem lowerDensity_pos_iff_uniform_tail_bound (S : Set ℕ) :
    0 < S.lowerDensity ↔
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, c ≤ S.partialDensity Set.univ N := by
  rw [lowerDensity_pos_iff_eventually_lower_bound]
  simp only [eventually_atTop]

/-- If a set has density, its lower density is that same limit. -/
theorem lowerDensity_eq_of_hasDensity {S : Set ℕ} {d : ℝ} (hd : S.HasDensity d) :
    S.lowerDensity = d := by
  exact (show Tendsto (fun N : ℕ => S.partialDensity Set.univ N) atTop (𝓝 d) from hd).liminf_eq

/-- Positive lower density suffices precisely when the density limit also exists. -/
theorem hasPosDensity_iff_limit_exists_and_lowerDensity_pos (S : Set ℕ) :
    S.HasPosDensity ↔ (∃ d : ℝ, S.HasDensity d) ∧ 0 < S.lowerDensity := by
  constructor
  · rintro ⟨d, hpos, hd⟩
    exact ⟨⟨d, hd⟩, by rwa [lowerDensity_eq_of_hasDensity hd]⟩
  · rintro ⟨⟨d, hd⟩, hpos⟩
    exact ⟨d, by rwa [← lowerDensity_eq_of_hasDensity hd], hd⟩

/-- An explicit sufficient condition separates convergence from uniform positivity. -/
theorem hasPosDensity_of_limit_and_uniform_tail_bound {S : Set ℕ}
    (hlimit : ∃ d : ℝ, S.HasDensity d) {c : ℝ} (hc : 0 < c)
    (hbound : ∃ N₀ : ℕ, ∀ N ≥ N₀, c ≤ S.partialDensity Set.univ N) :
    S.HasPosDensity := by
  apply (hasPosDensity_iff_limit_exists_and_lowerDensity_pos S).2
  exact ⟨hlimit, (lowerDensity_pos_iff_uniform_tail_bound S).2 ⟨c, hc, hbound⟩⟩

/-- A uniform linear counting bound gives positive lower density. -/
theorem lowerDensity_pos_of_uniform_count_bound {S : Set ℕ} {c : ℝ} (hc : 0 < c)
    (hbound : ∃ N₀ : ℕ, ∀ N ≥ N₀, c * N ≤ ((S ∩ Set.Iio N).ncard : ℝ)) :
    0 < S.lowerDensity := by
  apply (lowerDensity_pos_iff_eventually_lower_bound S).2
  refine ⟨c, hc, ?_⟩
  obtain ⟨N₀, hN₀⟩ := hbound
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1] with N hN hNpos
  have hpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  simpa [Set.partialDensity] using (le_div_iff₀ hpos).2 (hN₀ N hN)

/-- A positive counting bound closes the target only when convergence is also proved. -/
theorem hasPosDensity_of_limit_and_uniform_count_bound {S : Set ℕ}
    (hlimit : ∃ d : ℝ, S.HasDensity d) {c : ℝ} (hc : 0 < c)
    (hbound : ∃ N₀ : ℕ, ∀ N ≥ N₀, c * N ≤ ((S ∩ Set.Iio N).ncard : ℝ)) :
    S.HasPosDensity := by
  exact (hasPosDensity_iff_limit_exists_and_lowerDensity_pos S).2
    ⟨hlimit, lowerDensity_pos_of_uniform_count_bound hc hbound⟩

end Contribution.DensityInterface

/-
For each fixed greedy prefix, its difference-window density tends to zero as
the window cutoff tends to infinity. This corrects a proposed positive-liminf
intermediate assertion. It does not determine the density of the infinite
greedy Sidon difference set.
-/

open Filter
open scoped Topology
open Contribution.Erdos340

namespace Contribution.FixedPrefixLimit

/-- With the source prefix fixed, the window density has limit zero. -/
theorem fixedPrefix_density_tendsto_zero (n : ℕ) :
    Tendsto (fun N : ℕ => differenceWindowDensity (greedyPrefix n) N)
      atTop (𝓝 (0 : ℝ)) := by
  have hlimit := tendsto_const_div_atTop_nhds_zero_nat
    ((((n + 1).choose 2 + 1 : ℕ) : ℝ))
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (Finset.greedySidon n)] with N hN
  exact (greedyPrefix_window_density n N hN).symm

/-- In particular, the fixed-prefix lower limiting density is exactly zero. -/
theorem fixedPrefix_density_liminf_eq_zero (n : ℕ) :
    Filter.liminf (fun N : ℕ => differenceWindowDensity (greedyPrefix n) N) atTop = 0 :=
  (fixedPrefix_density_tendsto_zero n).liminf_eq

end Contribution.FixedPrefixLimit

namespace Contribution.Examples

/-- Apply the finite-prefix count directly to the infinite difference set. -/
example (n N : ℕ) (hn : Finset.greedySidon n ≤ N) :
    (((n + 1).choose 2 + 1 : ℕ) : ℝ) / N ≤
      Erdos340Asymptotics.greedyDifferenceSet.partialDensity Set.univ N :=
  Erdos340Asymptotics.prefix_density_lower_bound n N hn

/-- The target follows only after both global hypotheses are established. -/
example (hlimit : ∃ d : ℝ, Erdos340Asymptotics.greedyDifferenceSet.HasDensity d)
    {c : ℝ} (hc : 0 < c)
    (hcount : ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ ((Erdos340Asymptotics.greedyDifferenceSet ∩ Set.Iio N).ncard : ℝ)) :
    Erdos340Asymptotics.greedyDifferenceSet.HasPosDensity :=
  DensityInterface.hasPosDensity_of_limit_and_uniform_count_bound hlimit hc hcount

end Contribution.Examples
