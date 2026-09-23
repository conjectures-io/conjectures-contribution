import FormalConjectures.ErdosProblems.«949»

/-!
# Erdős 949: a general Zorn criterion and three solved cases

Target: every sum-free `S ⊆ ℝ` has some `A ⊆ Sᶜ` with `#A = 𝔠` and `A + A ⊆ Sᶜ`.

* `exists_of_small_traces` — the Zorn argument from the file's own Sidon proof, isolated and
  generalized: it suffices to find `X` with `#X = 𝔠`, `#(S ∩ X) < 𝔠`, `#(S ∩ (X + X)) < 𝔠`.
  No hypothesis on `S` at all.
* `exists_of_mk_lt` — the case `#S < 𝔠` (take `X = univ`).
* `exists_of_bddAbove`, `exists_of_bddBelow` — `S` bounded on one side (a half-line works).
* `exists_of_span_ne_top` — `S` does not span `ℝ` over `ℚ` (a coset of the span works).
* `erdos_949_of_cases` — the target holds for every `S` in any of these classes, so a counterexample
  must have `#S = 𝔠`, be unbounded above and below, and span `ℝ` over `ℚ`.
-/

open Cardinal
open scoped Pointwise

namespace Contribution.Erdos949Partial

/-- **General Zorn criterion for Erdős 949.** If some set `X` of size continuum meets `S` in
fewer than continuum points, and `X + X` also meets `S` in fewer than continuum points, then
there is `A ⊆ Sᶜ` of size continuum with `A + A ⊆ Sᶜ`. No hypothesis on `S` is needed. -/
theorem exists_of_small_traces (S X : Set ℝ) (hX : #X = 𝔠)
    (h1 : #(S ∩ X : Set ℝ) < 𝔠) (h2 : #(S ∩ (X + X) : Set ℝ) < 𝔠) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  classical
  set T : Set ℝ := S ∩ (X + X) with hT
  set Y : Set ℝ := {x | x ∈ X ∧ x ∉ S ∧ x + x ∉ S} with hY
  -- `X \ Y` is small.
  have hXY : X ⊆ Y ∪ (S ∩ X) ∪ ((fun t => t / 2) '' T) := by
    intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inl (Or.inr ⟨hxS, hx⟩)
    by_cases hxx : x + x ∈ S
    · refine Or.inr ⟨x + x, ⟨hxx, Set.add_mem_add hx hx⟩, by ring⟩
    · exact Or.inl (Or.inl ⟨hx, hxS, hxx⟩)
  have hYc : #Y = 𝔠 := by
    refine le_antisymm (by simpa using mk_set_le Y) ?_
    by_contra hlt
    push Not at hlt
    have : #X < 𝔠 := by
      calc #X ≤ #(↑(Y ∪ (S ∩ X) ∪ ((fun t => t / 2) '' T))) := mk_subtype_mono hXY
        _ ≤ #Y + #(S ∩ X : Set ℝ) + #((fun t => t / 2) '' T) := by
            grw [mk_union_le, mk_union_le]
        _ < 𝔠 := by
            refine add_lt_of_lt aleph0_le_continuum
              (add_lt_of_lt aleph0_le_continuum hlt h1) ?_
            exact lt_of_le_of_lt mk_image_le h2
    exact absurd hX (ne_of_lt this)
  -- Zorn: maximal `A ⊆ Y` with pairwise sums outside `S`.
  obtain ⟨A, ⟨hAY, hAS⟩, hAmax⟩ := by
    refine zorn_subset {A | A ⊆ Y ∧ ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S} ?_
    intro C hCS hC
    refine ⟨⋃₀ C, ⟨Set.sUnion_subset fun A hA => (hCS hA).1, ?_⟩, fun A hA => Set.subset_sUnion_of_mem hA⟩
    rintro x ⟨A, hA, hx⟩ y ⟨B, hB, hy⟩
    rcases hC.total hA hB with hAB | hBA
    · exact (hCS hB).2 x (hAB hx) y hy
    · exact (hCS hA).2 x hx y (hBA hy)
  -- Maximality: every point of `Y` outside `A` differs from a point of `T` by an element of `A`.
  have hcover : Y ⊆ A ∪ ⋃ a ∈ A, (fun t => t - a) '' T := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    right
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and] at hno
    have hins : insert y A ∈ {A | A ⊆ Y ∧ ∀ x ∈ A, ∀ y ∈ A, x + y ∉ S} := by
      refine ⟨Set.insert_subset hy hAY, ?_⟩
      have hya : ∀ a ∈ A, y + a ∉ S := by
        intro a ha hS
        exact hno a ha (y + a) ⟨hS, Set.add_mem_add hy.1 (hAY ha).1⟩ (by ring)
      rintro u (rfl | hu) v (rfl | hv)
      · exact hy.2.2
      · exact hya v hv
      · rw [add_comm]; exact hya u hu
      · exact hAS u hu v hv
    exact hyA (hAmax hins (Set.subset_insert _ _) (Set.mem_insert _ _))
  refine ⟨A, fun a ha => (hAY ha).2.1, ?_, ?_⟩
  · refine le_antisymm (by simpa using mk_set_le A) ?_
    by_contra hlt
    push Not at hlt
    have hTs : #T < 𝔠 := h2
    have : #Y < 𝔠 := by
      calc #Y ≤ #(↑(A ∪ ⋃ a ∈ A, (fun t => t - a) '' T)) := mk_subtype_mono hcover
        _ ≤ #A + #A * #T := by
            obtain rfl | hA := A.eq_empty_or_nonempty
            · simp
            have : Nonempty A := hA.coe_sort
            grw [mk_union_le, mk_biUnion_le, ciSup_le fun _ => mk_image_le]
        _ < 𝔠 := add_lt_of_lt aleph0_le_continuum hlt (mul_lt_of_lt aleph0_le_continuum hlt hTs)
    exact absurd hYc (ne_of_lt this)
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    exact hAS x hx y hy


/-- Case `#S < 𝔠`. -/
theorem exists_of_mk_lt (S : Set ℝ) (hS : #S < 𝔠) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  refine exists_of_small_traces S Set.univ (by simp) ?_ ?_
  · exact lt_of_le_of_lt (mk_subtype_mono Set.inter_subset_left) hS
  · exact lt_of_le_of_lt (mk_subtype_mono Set.inter_subset_left) hS

/-- Case `S` bounded above: the half-line `(max M 0, ∞)` works. -/
theorem exists_of_bddAbove (S : Set ℝ) (hS : BddAbove S) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  obtain ⟨M, hM⟩ := hS
  refine ⟨Set.Ioi (max M 0), ?_, Cardinal.mk_Ioi_real _, ?_⟩
  · intro x hx hxS
    have := hM hxS
    have : M < x := lt_of_le_of_lt (le_max_left _ _) hx
    linarith
  · rintro _ ⟨x, hx, y, hy, rfl⟩ hxyS
    have h := hM hxyS
    simp only [Set.mem_Ioi] at hx hy
    have h0 := le_max_right M 0
    have h1 := le_max_left M 0
    linarith

/-- Case `S` bounded below: the half-line `(-∞, min M 0)` works. -/
theorem exists_of_bddBelow (S : Set ℝ) (hS : BddBelow S) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  obtain ⟨M, hM⟩ := hS
  refine ⟨Set.Iio (min M 0), ?_, Cardinal.mk_Iio_real _, ?_⟩
  · intro x hx hxS
    have := hM hxS
    have : x < M := lt_of_lt_of_le hx (min_le_left _ _)
    linarith
  · rintro _ ⟨x, hx, y, hy, rfl⟩ hxyS
    have h := hM hxyS
    simp only [Set.mem_Iio] at hx hy
    have h0 := min_le_right M 0
    have h1 := min_le_left M 0
    linarith

/-- Case `S` does not span `ℝ` over `ℚ`: a coset `c + span S` with `c ∉ span S` works. -/
theorem exists_of_span_ne_top (S : Set ℝ) (hS : Submodule.span ℚ S ≠ ⊤) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  classical
  rcases lt_or_eq_of_le (show #S ≤ 𝔠 by simpa using mk_set_le S) with hlt | heq
  · exact exists_of_mk_lt S hlt
  set V := Submodule.span ℚ S with hV
  obtain ⟨c, hc⟩ : ∃ c, c ∉ V := by
    by_contra h
    push Not at h
    exact hS (eq_top_iff.mpr fun x _ => h x)
  refine ⟨(fun v => c + v) '' (V : Set ℝ), ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ hmem
    have hs : c + v ∈ V := Submodule.subset_span hmem
    exact hc (by simpa using V.sub_mem hs hv)
  · rw [Cardinal.mk_image_eq (add_right_injective c)]
    refine le_antisymm (by simpa using mk_set_le (V : Set ℝ)) ?_
    calc 𝔠 = #S := heq.symm
      _ ≤ #(V : Set ℝ) := mk_subtype_mono Submodule.subset_span
  · rintro _ ⟨_, ⟨v, hv, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩ hmem
    have hs : c + v + (c + w) ∈ V := Submodule.subset_span hmem
    have h2c : (2 : ℚ) • c ∈ V := by
      have : (2 : ℚ) • c = c + v + (c + w) - (v + w) := by
        rw [two_smul]; ring
      rw [this]; exact V.sub_mem hs (V.add_mem hv hw)
    have : c ∈ V := by
      have := V.smul_mem ((2 : ℚ)⁻¹) h2c
      simpa [smul_smul] using this
    exact hc this

/-- The target statement holds for every `S` in any of the classes above. Consequently a
counterexample to `Erdos949.erdos_949` must satisfy `#S = 𝔠`, be unbounded above and below, and
span `ℝ` over `ℚ`. -/
theorem erdos_949_of_cases (S : Set ℝ)
    (h : #S < 𝔠 ∨ BddAbove S ∨ BddBelow S ∨ Submodule.span ℚ S ≠ ⊤) :
    ∃ A ⊆ Sᶜ, #A = 𝔠 ∧ A + A ⊆ Sᶜ := by
  rcases h with h | h | h | h
  · exact exists_of_mk_lt S h
  · exact exists_of_bddAbove S h
  · exact exists_of_bddBelow S h
  · exact exists_of_span_ne_top S h

end Contribution.Erdos949Partial
