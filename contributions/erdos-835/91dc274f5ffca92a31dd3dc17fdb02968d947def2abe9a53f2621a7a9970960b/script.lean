import FormalConjectures.ErdosProblems.«835»

-- ==== from Wave_property_iff_chromaticNumber.lean ====
/-!
Proof of `Erdos835.property_iff_chromaticNumber`: for `0 < k`, the chromatic number of the
Johnson graph `J(2k, k)` equals `k + 1` iff the `k`-subsets of a `2k`-set have a
`(k+1)`-coloring such that every `(k+1)`-subset contains all `k + 1` colors.
-/

open Finset SimpleGraph

namespace Contribution.PropertyIffChromaticNumber

variable {k : ℕ}

/-- Two distinct `k`-element vertices contained in a common `(k+1)`-set are adjacent
in `J(2k, k)`. -/
private lemma adj_of_subsets {A : Finset (Fin (2 * k))} (hA : #A = k + 1)
    {s t : {s : Finset (Fin (2 * k)) // #s = k}} (hs : s.val ⊆ A) (ht : t.val ⊆ A)
    (hst : s ≠ t) : J(2 * k, k).Adj s t := by
  rw [johnson_adj_iff_ge]
  refine ⟨hst, ?_⟩
  have h1 : #(s.val ∪ t.val) ≤ k + 1 := by
    rw [← hA]
    exact card_le_card (union_subset hs ht)
  have h2 := card_union_add_card_inter s.val t.val
  rw [s.prop, t.prop] at h2
  omega

/-- The vertices of `J(2k, k)` that are proper subsets of a fixed `(k+1)`-set `A` number
exactly `k + 1`. -/
private lemma card_ssubsets {A : Finset (Fin (2 * k))} (hA : #A = k + 1) :
    #(univ.filter (fun s : {s : Finset (Fin (2 * k)) // #s = k} => s.val ⊂ A)) = k + 1 := by
  have h : #(A.powersetCard k) = k + 1 := by
    rw [card_powersetCard, hA, Nat.choose_succ_self_right]
  rw [← h]
  apply card_nbij (fun s => s.val)
  · intro s hs
    simp only [mem_coe, mem_filter_univ] at hs
    simp only [mem_coe, mem_powersetCard]
    exact ⟨(Finset.ssubset_iff_subset_ne.mp hs).1, s.prop⟩
  · exact Subtype.val_injective.injOn
  · intro x hx
    simp only [mem_coe, mem_powersetCard] at hx
    have hxA : x ⊂ A := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hx.1, fun h' => ?_⟩
      have hx2 := hx.2
      rw [h', hA] at hx2
      omega
    exact ⟨⟨x, hx.2⟩, by simp only [mem_coe, mem_filter_univ]; exact hxA, rfl⟩

private lemma property_unfold (k : ℕ) : Erdos835.Property k ↔
    ∃ c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1),
      ∀ A : Finset (Fin (2 * k)), #A = k + 1 →
        image c (univ.filter (fun s : {s : Finset (Fin (2 * k)) // #s = k} => s.val ⊂ A)) =
          (univ : Finset (Fin (k + 1))) :=
  Iff.rfl

theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔
    Erdos835.Property k := by
  rw [property_unfold]
  constructor
  · intro hχ
    have he : J(2 * k, k).chromaticNumber = ((k + 1 : ℕ) : ℕ∞) := by exact_mod_cast hχ
    obtain ⟨C⟩ := chromaticNumber_le_iff_colorable.mp he.le
    refine ⟨⇑C, fun A hA => ?_⟩
    have hinj : Set.InjOn (⇑C)
        (univ.filter (fun s : {s : Finset (Fin (2 * k)) // #s = k} => s.val ⊂ A)) := by
      intro s hs t ht hct
      by_contra hne
      simp only [mem_coe, mem_filter_univ] at hs ht
      exact C.valid
        (adj_of_subsets hA (Finset.ssubset_iff_subset_ne.mp hs).1 (Finset.ssubset_iff_subset_ne.mp ht).1 hne)
        hct
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, card_ssubsets hA, Fintype.card_fin]
  · rintro ⟨c, hc⟩
    have hcol : J(2 * k, k).Colorable (k + 1) := by
      refine ⟨Coloring.mk c ?_⟩
      intro s t hadj
      have hst : s ≠ t := hadj.ne
      have h3 : #(s.val ∩ t.val) + 1 = k := by rwa [johnson_adj] at hadj
      have h2 := card_union_add_card_inter s.val t.val
      rw [s.prop, t.prop] at h2
      have hA : #(s.val ∪ t.val) = k + 1 := by omega
      have hinj : Set.InjOn c (univ.filter
          (fun u : {s : Finset (Fin (2 * k)) // #s = k} => u.val ⊂ s.val ∪ t.val)) := by
        apply injOn_of_card_image_eq
        rw [hc _ hA, card_ssubsets hA, card_univ, Fintype.card_fin]
      have hmem : ∀ u : {s : Finset (Fin (2 * k)) // #s = k}, u.val ⊆ s.val ∪ t.val →
          u ∈ univ.filter
            (fun u : {s : Finset (Fin (2 * k)) // #s = k} => u.val ⊂ s.val ∪ t.val) := by
        intro u hu
        rw [mem_filter_univ]
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hu, fun h' => ?_⟩
        have hu2 := u.prop
        rw [h', hA] at hu2
        omega
      intro hcs
      exact hst (hinj (mem_coe.mpr (hmem s subset_union_left))
        (mem_coe.mpr (hmem t subset_union_right)) hcs)
    have hlow : ((k + 1 : ℕ) : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
      obtain ⟨A, -, hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k + 1)
        (by rw [card_univ, Fintype.card_fin]; omega)
      apply le_chromaticNumber_of_pairwise_adj (ι := ↥(A.powersetCard k))
        (f := fun x => ⟨x.val, (mem_powersetCard.mp x.prop).2⟩)
      case hn => rw [Nat.card_eq_finsetCard, card_powersetCard, hA, Nat.choose_succ_self_right]
      case hf =>
        intro i j hij
        refine adj_of_subsets hA (mem_powersetCard.mp i.prop).1 (mem_powersetCard.mp j.prop).1 ?_
        intro h
        exact hij (Subtype.ext (Subtype.mk_eq_mk.mp h))
    exact_mod_cast le_antisymm (chromaticNumber_le_iff_colorable.mpr hcol) hlow


end Contribution.PropertyIffChromaticNumber

-- ==== from Wave_johnsonGraph_18_9.lean ====
/-
Proof of `Erdos835.johnsonGraph_18_9_chromaticNumber`: the chromatic number of the Johnson
graph `J(18, 9)` is greater than `10`. Parity double count: in a proper `10`-coloring every
`10`-subset of `Fin 18` contains exactly one `9`-subset of color `0`; counting color-`0`
`9`-subsets inside a fixed `11`-set `E` against the `10`-subsets of `E` gives `11 = 2 * m`.
-/

open Finset SimpleGraph

namespace Contribution.JohnsonGraph189ChromaticNumber

private lemma adj_of_subsets {A : Finset (Fin 18)} (hA : #A = 10)
    {s t : {s : Finset (Fin 18) // #s = 9}} (hs : s.val ⊆ A) (ht : t.val ⊆ A)
    (hst : s ≠ t) : J(18, 9).Adj s t := by
  rw [johnson_adj_iff_ge]
  refine ⟨hst, ?_⟩
  have h1 : #(s.val ∪ t.val) ≤ 10 := by
    rw [← hA]
    exact card_le_card (union_subset hs ht)
  have h2 := card_union_add_card_inter s.val t.val
  rw [s.prop, t.prop] at h2
  omega

private lemma card_subsets {A : Finset (Fin 18)} (hA : #A = 10) :
    #(univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => S.val ⊆ A)) = 10 := by
  have hch : Nat.choose 10 9 = 10 := by decide
  have h : #(A.powersetCard 9) = 10 := by rw [card_powersetCard, hA, hch]
  rw [← h]
  apply card_nbij (fun S => S.val)
  · intro S hS
    simp only [mem_coe, mem_filter_univ] at hS
    simp only [mem_coe, mem_powersetCard]
    exact ⟨hS, S.prop⟩
  · exact Subtype.val_injective.injOn
  · intro x hx
    simp only [mem_coe, mem_powersetCard] at hx
    exact ⟨⟨x, hx.2⟩, by simp only [mem_coe, mem_filter_univ]; exact hx.1, rfl⟩

/-- In a proper `10`-coloring of `J(18, 9)`, every `10`-set contains exactly one `9`-subset
of color `0`. -/
private lemma card_color_subsets (C : (J(18, 9)).Coloring (Fin 10)) {A : Finset (Fin 18)}
    (hA : #A = 10) :
    #((univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => C S = 0)).filter
      (fun S => S.val ⊆ A)) = 1 := by
  rw [filter_filter]
  have hinj : Set.InjOn (⇑C)
      (univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => S.val ⊆ A)) := by
    intro s hs t ht hct
    by_contra hne
    simp only [mem_coe, mem_filter_univ] at hs ht
    exact C.valid (adj_of_subsets hA hs ht hne) hct
  have himg : (univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => S.val ⊆ A)).image ⇑C =
      univ := by
    apply eq_univ_of_card
    rw [card_image_of_injOn hinj, card_subsets hA, Fintype.card_fin]
  have h0 : (0 : Fin 10) ∈
      (univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => S.val ⊆ A)).image ⇑C := by
    rw [himg]
    exact mem_univ _
  rw [mem_image] at h0
  obtain ⟨S₀, hS₀mem, hS₀⟩ := h0
  rw [card_eq_one]
  refine ⟨S₀, ?_⟩
  ext S
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨hc0, hsub⟩
    refine hinj (mem_coe.mpr (mem_filter.mpr ⟨mem_univ S, hsub⟩)) (mem_coe.mpr hS₀mem) ?_
    rw [hc0, hS₀]
  · rintro rfl
    exact ⟨hS₀, (mem_filter.mp hS₀mem).2⟩

/-- A `9`-subset of the `11`-set `E` lies in exactly two `10`-subsets of `E`. -/
private lemma card_supersets {E : Finset (Fin 18)} (hE : #E = 11)
    {S : {s : Finset (Fin 18) // #s = 9}} (hSE : S.val ⊆ E) :
    #((E.powersetCard 10).filter (fun A => S.val ⊆ A)) = 2 := by
  have hsd : #(E \ S.val) = 2 := by
    have h := card_sdiff (s := S.val) (t := E)
    rw [inter_eq_left.mpr hSE, hE, S.prop] at h
    omega
  rw [← hsd]
  refine (card_bij (fun x _ => insert x S.val) ?_ ?_ ?_).symm
  · intro x hx
    rw [mem_sdiff] at hx
    show insert x S.val ∈ (E.powersetCard 10).filter (fun A => S.val ⊆ A)
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨insert_subset_iff.mpr ⟨hx.1, hSE⟩, ?_⟩, subset_insert _ _⟩
    rw [card_insert_of_notMem hx.2, S.prop]
  · intro x hx y hy hxy
    rw [mem_sdiff] at hx hy
    have hxy' : insert x S.val = insert y S.val := hxy
    have hmem : x ∈ insert y S.val := hxy' ▸ mem_insert_self x S.val
    rcases mem_insert.mp hmem with h | h
    · exact h
    · exact absurd h hx.2
  · intro A hA
    rw [mem_filter, mem_powersetCard] at hA
    obtain ⟨⟨hAE, hA10⟩, hSA⟩ := hA
    have h1 : #(A \ S.val) = 1 := by
      have h := card_sdiff (s := S.val) (t := A)
      rw [inter_eq_left.mpr hSA, hA10, S.prop] at h
      omega
    obtain ⟨x, hx⟩ := card_eq_one.mp h1
    have hxA : x ∈ A \ S.val := by
      rw [hx]
      exact mem_singleton_self x
    rw [mem_sdiff] at hxA
    refine ⟨x, ?_, ?_⟩
    · rw [mem_sdiff]
      exact ⟨hAE hxA.1, hxA.2⟩
    · show insert x S.val = A
      rw [insert_eq, ← hx]
      exact sdiff_union_of_subset hSA

private lemma card_supersets_zero {E : Finset (Fin 18)}
    {S : {s : Finset (Fin 18) // #s = 9}} (hSE : ¬ S.val ⊆ E) :
    #((E.powersetCard 10).filter (fun A => S.val ⊆ A)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro A hA hSA
  exact hSE (hSA.trans (mem_powersetCard.mp hA).1)

theorem johnsonGraph_18_9_chromaticNumber : J(18, 9).chromaticNumber > 9 + 1 := by
  have key : ¬ (J(18, 9)).Colorable 10 := by
    rintro ⟨C⟩
    obtain ⟨E, -, hE⟩ := exists_subset_card_eq (s := (univ : Finset (Fin 18))) (n := 11)
      (by rw [card_univ, Fintype.card_fin]; omega)
    have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (r := fun (A : Finset (Fin 18)) (S : {s : Finset (Fin 18) // #s = 9}) => S.val ⊆ A)
      (s := E.powersetCard 10)
      (t := univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => C S = 0))
    have h1 : ∀ A ∈ E.powersetCard 10,
        #((univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => C S = 0)).bipartiteAbove
          (fun (A : Finset (Fin 18)) (S : {s : Finset (Fin 18) // #s = 9}) => S.val ⊆ A) A)
          = 1 := by
      intro A hA
      unfold Finset.bipartiteAbove
      exact card_color_subsets C (mem_powersetCard.mp hA).2
    have hchoose : Nat.choose 11 10 = 11 := by decide
    have hL : ∑ A ∈ E.powersetCard 10,
        #((univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => C S = 0)).bipartiteAbove
          (fun (A : Finset (Fin 18)) (S : {s : Finset (Fin 18) // #s = 9}) => S.val ⊆ A) A)
          = 11 := by
      rw [Finset.sum_congr rfl h1, sum_const, smul_eq_mul, mul_one, card_powersetCard, hE,
        hchoose]
    have hR : 2 ∣ ∑ S ∈ univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => C S = 0),
        #((E.powersetCard 10).bipartiteBelow
          (fun (A : Finset (Fin 18)) (S : {s : Finset (Fin 18) // #s = 9}) => S.val ⊆ A) S) := by
      apply Finset.dvd_sum
      intro S hS
      unfold Finset.bipartiteBelow
      by_cases hSE : S.val ⊆ E
      · exact ⟨1, by rw [mul_one]; exact card_supersets hE hSE⟩
      · exact ⟨0, by rw [mul_zero]; exact card_supersets_zero hSE⟩
    have h11 : (11 : ℕ) = ∑ S ∈ univ.filter (fun S : {s : Finset (Fin 18) // #s = 9} => C S = 0),
        #((E.powersetCard 10).bipartiteBelow
          (fun (A : Finset (Fin 18)) (S : {s : Finset (Fin 18) // #s = 9}) => S.val ⊆ A) S) :=
      hL.symm.trans hdc
    rw [← h11] at hR
    omega
  have h10 : ((10 : ℕ) : ℕ∞) < J(18, 9).chromaticNumber :=
    lt_chromaticNumber_iff_not_colorable.mpr key
  refine lt_of_le_of_lt ?_ h10
  norm_num


end Contribution.JohnsonGraph189ChromaticNumber
