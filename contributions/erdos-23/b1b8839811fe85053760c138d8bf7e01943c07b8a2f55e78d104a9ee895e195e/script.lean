import Mathlib
import FormalConjectures.ErdosProblems.«23»

/-!
# Erdős Problem 23: the `n1_tight` variant

`C₅` is triangle-free, and any bipartite subgraph must drop at least one edge: a
bipartite graph is 2-colorable, but a subgraph dropping no edge equals `C₅`, whose
chromatic number is 3.
-/

open SimpleGraph

namespace Contribution.ErdosTwentyThreeN1Tight

theorem n1_tight :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
        H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  refine ⟨cycleGraph 5, ?_, ?_⟩
  · have h : (cycleGraph 5).cliqueFinset 3 = ∅ := by decide
    exact cliqueFinset_eq_empty_iff.mp h
  · intro H hle hbip
    have hne : H ≠ cycleGraph 5 := by
      rintro rfl
      have h3 : (cycleGraph 5).chromaticNumber = 3 :=
        chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)
      have hle2 : (cycleGraph 5).chromaticNumber ≤ 2 :=
        chromaticNumber_le_iff_colorable.mpr hbip
      rw [h3] at hle2
      norm_num at hle2
    have hlt : H < cycleGraph 5 := lt_of_le_of_ne hle hne
    have hss : H.edgeSet ⊂ (cycleGraph 5).edgeSet := edgeSet_ssubset_edgeSet.mpr hlt
    obtain ⟨e, heG, heH⟩ := Set.exists_of_ssubset hss
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro h0
    refine Finset.eq_empty_iff_forall_notMem.mp h0 e ?_
    simp only [Finset.mem_sdiff, mem_edgeFinset]
    exact ⟨heG, fun hh => heH hh⟩

end Contribution.ErdosTwentyThreeN1Tight

