import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem 944: Dirac's Conjecture for k = 5, r = 1 via C_17(1, 3, 4, 5)

Proves unconditionally that Dirac's conjecture holds for `k = 5` and `r = 1`
(discharging `Erdos944.erdos_944.variants.dirac_conjecture.k_eq_5`), via the explicit
17-vertex circulant graph `C_17(1, 3, 4, 5)`:
1. `C17` is 5-colorable and `C17 \ {v}` is 4-colorable for every vertex `v`, using cyclic symmetry.
2. Any independent set of size 5 in `C17` or in `C17 \ {e}` is impossible, verified cleanly via
   symmetry reduction to ordered non-neighbor tuples (`70` 4-tuples and `22` 3-tuples) checked
   in the Lean kernel by `decide`.
3. Lifting to `ULift.{u} (Fin 17)` gives a universe-polymorphic graph satisfying
   `Erdos944.SimpleGraph.IsErdos944 G 5 1`.
-/

namespace Contribution.Erdos944DiracK5R1

private def sub17 (x y : Fin 17) : Fin 17 :=
  ⟨(x.val + 17 - y.val) % 17, Nat.mod_lt _ (by decide)⟩

private theorem sub17_self (x : Fin 17) : sub17 x x = 0 := by
  apply Fin.ext
  simp [sub17]

private theorem sub17_eq_zero_iff (x y : Fin 17) : sub17 x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Fin.ext
    have := congrArg Fin.val h
    have hx := x.isLt
    have hy := y.isLt
    simp only [sub17, Fin.val_zero] at this
    omega
  · rintro rfl
    exact sub17_self x

private theorem sub17_injective (p : Fin 17) : Function.Injective (fun x => sub17 x p) := by
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  have hx := x.isLt
  have hy := y.isLt
  have hp := p.isLt
  simp only [sub17] at this
  omega

private theorem sub17_sub17 (x y p : Fin 17) : sub17 (sub17 x p) (sub17 y p) = sub17 x y := by
  apply Fin.ext
  have hx := x.isLt
  have hy := y.isLt
  have hp := p.isLt
  simp only [sub17]
  omega

private def isStep17 (d : ℕ) : Bool :=
  d == 1 || d == 3 || d == 4 || d == 5 || d == 12 || d == 13 || d == 14 || d == 16

private def adj17 (x y : Fin 17) : Bool :=
  isStep17 (sub17 x y).val

private theorem adj17_symm : ∀ x y : Fin 17, adj17 x y = adj17 y x := by decide

private theorem adj17_irrefl : ∀ x : Fin 17, adj17 x x = false := by decide

/-- The 17-vertex circulant graph `C_17(1, 3, 4, 5)`. -/
def C17 : SimpleGraph (Fin 17) where
  Adj x y := adj17 x y = true
  symm := ⟨fun _ _ h => by rw [adj17_symm]; exact h⟩
  loopless := ⟨fun x h => by rw [adj17_irrefl x] at h; cases h⟩

private theorem C17_adj_sub17 (x y p : Fin 17) : C17.Adj (sub17 x p) (sub17 y p) ↔ C17.Adj x y := by
  change adj17 (sub17 x p) (sub17 y p) = true ↔ adj17 x y = true
  simp only [adj17, sub17_sub17]

private def col4MinusZero (v : Fin 17) : Fin 4 :=
  if v.val == 1 || v.val == 3 || v.val == 9 || v.val == 11 then 0
  else if v.val == 2 || v.val == 4 || v.val == 10 || v.val == 12 then 1
  else if v.val == 5 || v.val == 7 || v.val == 13 || v.val == 15 then 2
  else 3

private theorem col4MinusZero_valid :
    ∀ u v : Fin 17, u ≠ 0 → v ≠ 0 → adj17 u v = true → col4MinusZero u ≠ col4MinusZero v := by
  decide

/-- Explicit proper 5-coloring of `C17`. -/
theorem C17_colorable_five : C17.Colorable 5 := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if v = 0 then 4 else (col4MinusZero v).castSucc) ?_⟩
  intro u v huv h_eq
  by_cases hu : u = 0 <;> by_cases hv : v = 0
  · subst hu; subst hv; exact huv.ne rfl
  · subst hu
    simp only [hv, ↓reduceIte] at h_eq
    have h4 : (4 : Fin 5).val = (col4MinusZero v).castSucc.val := congrArg Fin.val h_eq
    have hlt := (col4MinusZero v).isLt
    simp at h4
    omega
  · subst hv
    simp only [hu, ↓reduceIte] at h_eq
    have h4 : (col4MinusZero u).castSucc.val = (4 : Fin 5).val := congrArg Fin.val h_eq
    have hlt := (col4MinusZero u).isLt
    simp at h4
    omega
  · simp only [hu, hv, ↓reduceIte] at h_eq
    have hval : col4MinusZero u = col4MinusZero v := by
      apply Fin.ext
      simpa using congrArg Fin.val h_eq
    exact col4MinusZero_valid u v hu hv huv hval

/-- Deleting any single vertex `v` from `C17` yields a 4-colorable graph. -/
theorem C17_deleteVert_colorable_four (v : Fin 17) :
    ((⊤ : C17.Subgraph).deleteVerts {v}).coe.Colorable 4 := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => col4MinusZero (sub17 x.val v)) ?_⟩
  intro x y hxy
  rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj] at hxy
  rcases hxy with ⟨_, hx_ne, _, hy_ne, hadj⟩
  have h1 : sub17 x.val v ≠ 0 := fun h => hx_ne ((sub17_eq_zero_iff x.val v).mp h)
  have h2 : sub17 y.val v ≠ 0 := fun h => hy_ne ((sub17_eq_zero_iff y.val v).mp h)
  have hadj' : adj17 (sub17 x.val v) (sub17 y.val v) = true := (C17_adj_sub17 x.val y.val v).mpr hadj
  exact col4MinusZero_valid (sub17 x.val v) (sub17 y.val v) h1 h2 hadj'

private def adjNat17 (x y : ℕ) : Bool :=
  isStep17 ((x + 17 - y) % 17)

private theorem adjNat17_of_C17_adj {x y : Fin 17} (h : C17.Adj x y) :
    adjNat17 x.val y.val = true :=
  h

private def hasAdj3 (a b c : ℕ) : Bool :=
  adjNat17 a b || adjNat17 a c || adjNat17 b c

private def hasAdj4 (a b c e : ℕ) : Bool :=
  adjNat17 a b || adjNat17 a c || adjNat17 a e || adjNat17 b c || adjNat17 b e || adjNat17 c e

private theorem not_hasAdj3 {x y z : Fin 17} (hxy : ¬ C17.Adj x y) (hxz : ¬ C17.Adj x z)
    (hyz : ¬ C17.Adj y z) : hasAdj3 x.val y.val z.val = false := by
  have f1 : adjNat17 x.val y.val = false := Bool.eq_false_iff.mpr fun h => hxy (by exact h)
  have f2 : adjNat17 x.val z.val = false := Bool.eq_false_iff.mpr fun h => hxz (by exact h)
  have f3 : adjNat17 y.val z.val = false := Bool.eq_false_iff.mpr fun h => hyz (by exact h)
  simp [hasAdj3, f1, f2, f3]

private theorem not_hasAdj4 {x y z w : Fin 17}
    (h1 : ¬ C17.Adj x y) (h2 : ¬ C17.Adj x z) (h3 : ¬ C17.Adj x w)
    (h4 : ¬ C17.Adj y z) (h5 : ¬ C17.Adj y w) (h6 : ¬ C17.Adj z w) :
    hasAdj4 x.val y.val z.val w.val = false := by
  have f1 : adjNat17 x.val y.val = false := Bool.eq_false_iff.mpr fun h => h1 (by exact h)
  have f2 : adjNat17 x.val z.val = false := Bool.eq_false_iff.mpr fun h => h2 (by exact h)
  have f3 : adjNat17 x.val w.val = false := Bool.eq_false_iff.mpr fun h => h3 (by exact h)
  have f4 : adjNat17 y.val z.val = false := Bool.eq_false_iff.mpr fun h => h4 (by exact h)
  have f5 : adjNat17 y.val w.val = false := Bool.eq_false_iff.mpr fun h => h5 (by exact h)
  have f6 : adjNat17 z.val w.val = false := Bool.eq_false_iff.mpr fun h => h6 (by exact h)
  simp [hasAdj4, f1, f2, f3, f4, f5, f6]

private def checkTriples1 (a b : ℕ) (L : List ℕ) : Bool :=
  L.all fun c => hasAdj3 a b c

private theorem checkTriples1_sound {a b c : ℕ} {L : List ℕ} (hc : checkTriples1 a b L = true)
    (hmem : c ∈ L) : hasAdj3 a b c = true :=
  List.all_eq_true.mp hc c hmem

private def checkTriples2 (a : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => checkTriples1 a b bs && checkTriples2 a bs

private theorem checkTriples2_sound {a : ℕ} : ∀ {L : List ℕ},
    L.Pairwise (· < ·) → checkTriples2 a L = true →
    ∀ {b c : ℕ}, b ∈ L → c ∈ L → b < c → hasAdj3 a b c = true
  | [], _, _ => fun hb => by simp at hb
  | x :: xs, hs, hc => fun hb hc' hbc => by
    simp only [checkTriples2, Bool.and_eq_true] at hc
    rw [List.pairwise_cons] at hs
    simp only [List.mem_cons] at hb hc'
    rcases hb with rfl | hb_xs
    · rcases hc' with hcx | hc_xs
      · omega
      · exact checkTriples1_sound hc.1 hc_xs
    · rcases hc' with rfl | hc_xs
      · have hxb : _ < _ := hs.1 _ hb_xs
        omega
      · exact checkTriples2_sound hs.2 hc.2 hb_xs hc_xs hbc

private def checkTriples3 : List ℕ → Bool
  | [] => true
  | a :: xs => checkTriples2 a xs && checkTriples3 xs

private theorem checkTriples3_sound : ∀ {L : List ℕ},
    L.Pairwise (· < ·) → checkTriples3 L = true →
    ∀ {a b c : ℕ}, a ∈ L → b ∈ L → c ∈ L → a < b → b < c → hasAdj3 a b c = true
  | [], _, _ => fun ha => by simp at ha
  | x :: xs, hs, hc => fun ha hb hc' hab hbc => by
    simp only [checkTriples3, Bool.and_eq_true] at hc
    rw [List.pairwise_cons] at hs
    simp only [List.mem_cons] at ha hb hc'
    rcases ha with rfl | ha_xs
    · rcases hb with hbx | hb_xs
      · omega
      · rcases hc' with hcx | hc_xs
        · omega
        · exact checkTriples2_sound hs.2 hc.1 hb_xs hc_xs hbc
    · have hxa : _ < _ := hs.1 _ ha_xs
      rcases hb with rfl | hb_xs
      · omega
      · rcases hc' with rfl | hc_xs
        · omega
        · exact checkTriples3_sound hs.2 hc.2 ha_xs hb_xs hc_xs hab hbc

private def checkQuads1 (a b c : ℕ) (L : List ℕ) : Bool :=
  L.all fun e => hasAdj4 a b c e

private theorem checkQuads1_sound {a b c e : ℕ} {L : List ℕ} (hc : checkQuads1 a b c L = true)
    (hmem : e ∈ L) : hasAdj4 a b c e = true :=
  List.all_eq_true.mp hc e hmem

private def checkQuads2 (a b : ℕ) : List ℕ → Bool
  | [] => true
  | c :: cs => checkQuads1 a b c cs && checkQuads2 a b cs

private theorem checkQuads2_sound {a b : ℕ} : ∀ {L : List ℕ},
    L.Pairwise (· < ·) → checkQuads2 a b L = true →
    ∀ {c e : ℕ}, c ∈ L → e ∈ L → c < e → hasAdj4 a b c e = true
  | [], _, _ => fun hc => by simp at hc
  | x :: xs, hs, hc => fun hc' he hce => by
    simp only [checkQuads2, Bool.and_eq_true] at hc
    rw [List.pairwise_cons] at hs
    simp only [List.mem_cons] at hc' he
    rcases hc' with rfl | hc_xs
    · rcases he with hex | he_xs
      · omega
      · exact checkQuads1_sound hc.1 he_xs
    · rcases he with rfl | he_xs
      · have hxc : _ < _ := hs.1 _ hc_xs
        omega
      · exact checkQuads2_sound hs.2 hc.2 hc_xs he_xs hce

private def checkQuads3 (a : ℕ) : List ℕ → Bool
  | [] => true
  | b :: bs => checkQuads2 a b bs && checkQuads3 a bs

private theorem checkQuads3_sound {a : ℕ} : ∀ {L : List ℕ},
    L.Pairwise (· < ·) → checkQuads3 a L = true →
    ∀ {b c e : ℕ}, b ∈ L → c ∈ L → e ∈ L → b < c → c < e → hasAdj4 a b c e = true
  | [], _, _ => fun hb => by simp at hb
  | x :: xs, hs, hc => fun hb hc' he hbc hce => by
    simp only [checkQuads3, Bool.and_eq_true] at hc
    rw [List.pairwise_cons] at hs
    simp only [List.mem_cons] at hb hc' he
    rcases hb with rfl | hb_xs
    · rcases hc' with hcx | hc_xs
      · omega
      · rcases he with hex | he_xs
        · omega
        · exact checkQuads2_sound hs.2 hc.1 hc_xs he_xs hce
    · have hxb : _ < _ := hs.1 _ hb_xs
      rcases hc' with rfl | hc_xs
      · omega
      · rcases he with rfl | he_xs
        · omega
        · exact checkQuads3_sound hs.2 hc.2 hb_xs hc_xs he_xs hbc hce

private def checkQuads4 : List ℕ → Bool
  | [] => true
  | a :: xs => checkQuads3 a xs && checkQuads4 xs

private theorem checkQuads4_sound : ∀ {L : List ℕ},
    L.Pairwise (· < ·) → checkQuads4 L = true →
    ∀ {a b c e : ℕ}, a ∈ L → b ∈ L → c ∈ L → e ∈ L →
      a < b → b < c → c < e → hasAdj4 a b c e = true
  | [], _, _ => fun ha => by simp at ha
  | x :: xs, hs, hc => fun ha hb hc' he hab hbc hce => by
    simp only [checkQuads4, Bool.and_eq_true] at hc
    rw [List.pairwise_cons] at hs
    simp only [List.mem_cons] at ha hb hc' he
    rcases ha with rfl | ha_xs
    · rcases hb with hbx | hb_xs
      · omega
      · rcases hc' with hcx | hc_xs
        · omega
        · rcases he with hex | he_xs
          · omega
          · exact checkQuads3_sound hs.2 hc.1 hb_xs hc_xs he_xs hbc hce
    · have hxa : _ < _ := hs.1 _ ha_xs
      rcases hb with rfl | hb_xs
      · omega
      · rcases hc' with rfl | hc_xs
        · omega
        · rcases he with rfl | he_xs
          · omega
          · exact checkQuads4_sound hs.2 hc.2 ha_xs hb_xs hc_xs he_xs hab hbc hce

private def nonNb0 : List ℕ := [2, 6, 7, 8, 9, 10, 11, 15]

private theorem nonNb0_sorted : nonNb0.Pairwise (· < ·) := by decide

private theorem checkNonNb0_true : checkQuads4 nonNb0 = true := by decide

private theorem mem_nonNb0_of_not_adj :
    ∀ x : Fin 17, x ≠ 0 → adj17 0 x = false → x.val ∈ nonNb0 := by
  decide

private theorem extract_four_of_card_ge_four {U : Finset ℕ} (hcard : 4 ≤ U.card) :
    ∃ a b c e : ℕ, a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ e ∈ U ∧ a < b ∧ b < c ∧ c < e := by
  have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
  set a := U.min' hU_ne
  have ha_mem : a ∈ U := Finset.min'_mem U hU_ne
  set U1 := U.erase a
  have h1_card : 3 ≤ U1.card := by rw [Finset.card_erase_of_mem ha_mem]; omega
  have hU1_ne : U1.Nonempty := Finset.card_pos.mp (by omega)
  set b := U1.min' hU1_ne
  have hb_mem1 : b ∈ U1 := Finset.min'_mem U1 hU1_ne
  have hb_mem : b ∈ U := (Finset.mem_erase.mp hb_mem1).2
  have hab : a < b := by
    have hle : a ≤ b := Finset.min'_le U b hb_mem
    have hne : b ≠ a := (Finset.mem_erase.mp hb_mem1).1
    omega
  set U2 := U1.erase b
  have h2_card : 2 ≤ U2.card := by rw [Finset.card_erase_of_mem hb_mem1]; omega
  have hU2_ne : U2.Nonempty := Finset.card_pos.mp (by omega)
  set c := U2.min' hU2_ne
  have hc_mem2 : c ∈ U2 := Finset.min'_mem U2 hU2_ne
  have hc_mem1 : c ∈ U1 := (Finset.mem_erase.mp hc_mem2).2
  have hc_mem : c ∈ U := (Finset.mem_erase.mp hc_mem1).2
  have hbc : b < c := by
    have hle : b ≤ c := Finset.min'_le U1 c hc_mem1
    have hne : c ≠ b := (Finset.mem_erase.mp hc_mem2).1
    omega
  set U3 := U2.erase c
  have h3_card : 1 ≤ U3.card := by rw [Finset.card_erase_of_mem hc_mem2]; omega
  have hU3_ne : U3.Nonempty := Finset.card_pos.mp (by omega)
  set e := U3.min' hU3_ne
  have he_mem3 : e ∈ U3 := Finset.min'_mem U3 hU3_ne
  have he_mem2 : e ∈ U2 := (Finset.mem_erase.mp he_mem3).2
  have he_mem1 : e ∈ U1 := (Finset.mem_erase.mp he_mem2).2
  have he_mem : e ∈ U := (Finset.mem_erase.mp he_mem1).2
  have hce : c < e := by
    have hle : c ≤ e := Finset.min'_le U2 e he_mem2
    have hne : e ≠ c := (Finset.mem_erase.mp he_mem3).1
    omega
  exact ⟨a, b, c, e, ha_mem, hb_mem, hc_mem, he_mem, hab, hbc, hce⟩

private theorem extract_three_of_card_ge_three {U : Finset ℕ} (hcard : 3 ≤ U.card) :
    ∃ a b c : ℕ, a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ a < b ∧ b < c := by
  have hU_ne : U.Nonempty := Finset.card_pos.mp (by omega)
  set a := U.min' hU_ne
  have ha_mem : a ∈ U := Finset.min'_mem U hU_ne
  set U1 := U.erase a
  have h1_card : 2 ≤ U1.card := by rw [Finset.card_erase_of_mem ha_mem]; omega
  have hU1_ne : U1.Nonempty := Finset.card_pos.mp (by omega)
  set b := U1.min' hU1_ne
  have hb_mem1 : b ∈ U1 := Finset.min'_mem U1 hU1_ne
  have hb_mem : b ∈ U := (Finset.mem_erase.mp hb_mem1).2
  have hab : a < b := by
    have hle : a ≤ b := Finset.min'_le U b hb_mem
    have hne : b ≠ a := (Finset.mem_erase.mp hb_mem1).1
    omega
  set U2 := U1.erase b
  have h2_card : 1 ≤ U2.card := by rw [Finset.card_erase_of_mem hb_mem1]; omega
  have hU2_ne : U2.Nonempty := Finset.card_pos.mp (by omega)
  set c := U2.min' hU2_ne
  have hc_mem2 : c ∈ U2 := Finset.min'_mem U2 hU2_ne
  have hc_mem1 : c ∈ U1 := (Finset.mem_erase.mp hc_mem2).2
  have hc_mem : c ∈ U := (Finset.mem_erase.mp hc_mem1).2
  have hbc : b < c := by
    have hle : b ≤ c := Finset.min'_le U1 c hc_mem1
    have hne : c ≠ b := (Finset.mem_erase.mp hc_mem2).1
    omega
  exact ⟨a, b, c, ha_mem, hb_mem, hc_mem, hab, hbc⟩

/-- `C17` has independence number `≤ 4`. -/
theorem no_indep_five_C17 {S : Finset (Fin 17)} (hcard : 5 ≤ S.card)
    (hind : ∀ u ∈ S, ∀ v ∈ S, ¬ C17.Adj u v) : False := by
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hS_ne
  set T : Finset (Fin 17) := (S.erase p).image (fun y => sub17 y p)
  have hT_card : 4 ≤ T.card := by
    rw [Finset.card_image_of_injective _ (sub17_injective p), Finset.card_erase_of_mem hp]
    omega
  have hT_sub : ∀ x ∈ T, x ≠ 0 ∧ x.val ∈ nonNb0 := by
    intro x hx
    obtain ⟨y, hy_er, rfl⟩ := Finset.mem_image.mp hx
    have hy_ne : y ≠ p := (Finset.mem_erase.mp hy_er).1
    have hy_S : y ∈ S := (Finset.mem_erase.mp hy_er).2
    have hx0 : sub17 y p ≠ 0 := fun h => hy_ne ((sub17_eq_zero_iff y p).mp h)
    have hnot : adj17 0 (sub17 y p) = false := by
      have hna : ¬ C17.Adj (sub17 p p) (sub17 y p) := by
        rw [C17_adj_sub17]
        exact hind p hp y hy_S
      rw [sub17_self] at hna
      exact Bool.eq_false_iff.mpr fun h => hna h
    exact ⟨hx0, mem_nonNb0_of_not_adj (sub17 y p) hx0 hnot⟩
  have hT_ind : ∀ x ∈ T, ∀ y ∈ T, ¬ C17.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨u, hu_er, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv_er, rfl⟩ := Finset.mem_image.mp hy
    have hu_S := (Finset.mem_erase.mp hu_er).2
    have hv_S := (Finset.mem_erase.mp hv_er).2
    rw [C17_adj_sub17] at hxy
    exact hind u hu_S v hv_S hxy
  set U : Finset ℕ := T.image Fin.val
  have hU_card : 4 ≤ U.card := by
    rw [Finset.card_image_of_injective _ Fin.val_injective]
    exact hT_card
  obtain ⟨a, b, c, e, ha, hb, hc, he, hab, hbc, hce⟩ := extract_four_of_card_ge_four hU_card
  obtain ⟨fa, hfa, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨fb, hfb, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨fc, hfc, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨fe, hfe, rfl⟩ := Finset.mem_image.mp he
  have hadj := checkQuads4_sound nonNb0_sorted checkNonNb0_true
    (hT_sub fa hfa).2 (hT_sub fb hfb).2 (hT_sub fc hfc).2 (hT_sub fe hfe).2 hab hbc hce
  have hfalse := not_hasAdj4 (hT_ind fa hfa fb hfb) (hT_ind fa hfa fc hfc)
    (hT_ind fa hfa fe hfe) (hT_ind fb hfb fc hfc) (hT_ind fb hfb fe hfe) (hT_ind fc hfc fe hfe)
  rw [hadj] at hfalse
  cases hfalse

private def common1 : List ℕ := [7, 8, 9, 10, 11]
private def common3 : List ℕ := [9, 10, 11]
private def common4 : List ℕ := [2, 6, 10, 11, 15]
private def common5 : List ℕ := [7, 11, 15]

private theorem common1_sorted : common1.Pairwise (· < ·) := by decide
private theorem common3_sorted : common3.Pairwise (· < ·) := by decide
private theorem common4_sorted : common4.Pairwise (· < ·) := by decide
private theorem common5_sorted : common5.Pairwise (· < ·) := by decide

private theorem check_common1_true : checkTriples3 common1 = true := by decide
private theorem check_common3_true : checkTriples3 common3 = true := by decide
private theorem check_common4_true : checkTriples3 common4 = true := by decide
private theorem check_common5_true : checkTriples3 common5 = true := by decide

private theorem mem_common1 :
    ∀ x : Fin 17, x ≠ 0 → x ≠ 1 → adj17 0 x = false → adj17 1 x = false → x.val ∈ common1 := by decide

private theorem mem_common3 :
    ∀ x : Fin 17, x ≠ 0 → x ≠ 3 → adj17 0 x = false → adj17 3 x = false → x.val ∈ common3 := by decide

private theorem mem_common4 :
    ∀ x : Fin 17, x ≠ 0 → x ≠ 4 → adj17 0 x = false → adj17 4 x = false → x.val ∈ common4 := by decide

private theorem mem_common5 :
    ∀ x : Fin 17, x ≠ 0 → x ≠ 5 → adj17 0 x = false → adj17 5 x = false → x.val ∈ common5 := by decide

private theorem orbit_pair_of_adj {a b : Fin 17} (hab : C17.Adj a b) :
    (∃ p q : Fin 17, (p = a ∧ q = b ∨ p = b ∧ q = a) ∧
      (sub17 q p).val ∈ ([1, 3, 4, 5] : List ℕ)) := by
  have hd : ∀ x y : Fin 17, adj17 x y = true →
      (sub17 y x).val ∈ ([1, 3, 4, 5] : List ℕ) ∨
      (sub17 x y).val ∈ ([1, 3, 4, 5] : List ℕ) := by decide
  rcases hd a b hab with h1 | h2
  · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, h1⟩
  · exact ⟨b, a, Or.inr ⟨rfl, rfl⟩, h2⟩

/-- Deleting any single edge from `C17` leaves a graph with independence number `≤ 4`. -/
theorem no_indep_five_C17_deleteEdge {a b : Fin 17} {S : Finset (Fin 17)} (hcard : 5 ≤ S.card)
    (hind : ∀ u ∈ S, ∀ v ∈ S, ¬ (C17.deleteEdges {s(a, b)}).Adj u v) : False := by
  by_cases h_both : C17.Adj a b ∧ a ∈ S ∧ b ∈ S
  · rcases h_both with ⟨hab_adj, haS, hbS⟩
    obtain ⟨p, q, hpq_cases, hd_mem⟩ := orbit_pair_of_adj hab_adj
    have hpS : p ∈ S := by rcases hpq_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hqS : q ∈ S := by rcases hpq_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hpq_ne : p ≠ q := by
      intro h; subst h; exact hab_adj.ne (by rcases hpq_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
    have hspq : s(p, q) = s(a, b) := by
      rcases hpq_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
    set S' := (S.erase p).erase q
    have hS'_card : 3 ≤ S'.card := by
      have hq_in : q ∈ S.erase p := Finset.mem_erase.mpr ⟨hpq_ne.symm, hqS⟩
      rw [Finset.card_erase_of_mem hq_in, Finset.card_erase_of_mem hpS]
      omega
    set T : Finset (Fin 17) := S'.image (fun y => sub17 y p)
    have hT_card : 3 ≤ T.card := by
      rw [Finset.card_image_of_injective _ (sub17_injective p)]
      exact hS'_card
    set d : Fin 17 := sub17 q p
    have hd0 : d ≠ 0 := fun h => hpq_ne ((sub17_eq_zero_iff q p).mp h).symm
    have hind_T : ∀ x ∈ T, ∀ y ∈ T, ¬ C17.Adj x y := by
      intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have hu_neq : u ≠ q := (Finset.mem_erase.mp hu).1
      have hu_er : u ∈ S.erase p := (Finset.mem_erase.mp hu).2
      have hu_S : u ∈ S := (Finset.mem_erase.mp hu_er).2
      have hv_S : v ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).2
      have hu_nep : u ≠ p := (Finset.mem_erase.mp hu_er).1
      rw [C17_adj_sub17] at hxy
      apply hind u hu_S v hv_S
      rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, ← hspq]
      refine ⟨hxy, fun hpair => ?_⟩
      rcases Sym2.eq_iff.mp hpair with ⟨hup, _⟩ | ⟨huq, _⟩
      · exact hu_nep hup
      · exact hu_neq huq
    have hT_non : ∀ x ∈ T, x ≠ 0 ∧ x ≠ d ∧ adj17 0 x = false ∧ adj17 d x = false := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hy_neq : y ≠ q := (Finset.mem_erase.mp hy).1
      have hy_er : y ∈ S.erase p := (Finset.mem_erase.mp hy).2
      have hy_nep : y ≠ p := (Finset.mem_erase.mp hy_er).1
      have hy_S : y ∈ S := (Finset.mem_erase.mp hy_er).2
      have hx0 : sub17 y p ≠ 0 := fun h => hy_nep ((sub17_eq_zero_iff y p).mp h)
      have hxd : sub17 y p ≠ d := fun h => hy_neq (sub17_injective p h)
      have hn0 : adj17 0 (sub17 y p) = false := by
        apply Bool.eq_false_iff.mpr
        intro hadj
        have hpy : C17.Adj p y := by
          rw [← C17_adj_sub17 p y p, sub17_self]
          exact hadj
        apply hind p hpS y hy_S
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, ← hspq]
        refine ⟨hpy, fun hpair => ?_⟩
        rcases Sym2.eq_iff.mp hpair with ⟨_, h_eq⟩ | ⟨h_eq, _⟩
        · exact hy_neq h_eq
        · exact hpq_ne h_eq
      have hnd : adj17 d (sub17 y p) = false := by
        apply Bool.eq_false_iff.mpr
        intro hadj
        have hqy : C17.Adj q y := by
          rw [← C17_adj_sub17 q y p]
          exact hadj
        apply hind q hqS y hy_S
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, ← hspq]
        refine ⟨hqy, fun hpair => ?_⟩
        rcases Sym2.eq_iff.mp hpair with ⟨h_eq, _⟩ | ⟨_, h_eq⟩
        · exact hpq_ne h_eq.symm
        · exact hy_nep h_eq
      exact ⟨hx0, hxd, hn0, hnd⟩
    set U : Finset ℕ := T.image Fin.val
    have hU_card : 3 ≤ U.card := by
      rw [Finset.card_image_of_injective _ Fin.val_injective]
      exact hT_card
    obtain ⟨u, v, w, hu, hv, hw, huv, hvw⟩ := extract_three_of_card_ge_three hU_card
    obtain ⟨fu, hfu, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨fv, hfv, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨fw, hfw, rfl⟩ := Finset.mem_image.mp hw
    have hfalse := not_hasAdj3 (hind_T fu hfu fv hfv) (hind_T fu hfu fw hfw) (hind_T fv hfv fw hfw)
    have htru : hasAdj3 fu.val fv.val fw.val = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd_mem
      rcases hd_mem with h1 | h3 | h4 | h5
      · have hd1 : d = 1 := Fin.ext h1
        rw [hd1] at hT_non
        have m1 := mem_common1 fu (hT_non fu hfu).1 (hT_non fu hfu).2.1 (hT_non fu hfu).2.2.1 (hT_non fu hfu).2.2.2
        have m2 := mem_common1 fv (hT_non fv hfv).1 (hT_non fv hfv).2.1 (hT_non fv hfv).2.2.1 (hT_non fv hfv).2.2.2
        have m3 := mem_common1 fw (hT_non fw hfw).1 (hT_non fw hfw).2.1 (hT_non fw hfw).2.2.1 (hT_non fw hfw).2.2.2
        exact checkTriples3_sound common1_sorted check_common1_true m1 m2 m3 huv hvw
      · have hd3 : d = 3 := Fin.ext h3
        rw [hd3] at hT_non
        have m1 := mem_common3 fu (hT_non fu hfu).1 (hT_non fu hfu).2.1 (hT_non fu hfu).2.2.1 (hT_non fu hfu).2.2.2
        have m2 := mem_common3 fv (hT_non fv hfv).1 (hT_non fv hfv).2.1 (hT_non fv hfv).2.2.1 (hT_non fv hfv).2.2.2
        have m3 := mem_common3 fw (hT_non fw hfw).1 (hT_non fw hfw).2.1 (hT_non fw hfw).2.2.1 (hT_non fw hfw).2.2.2
        exact checkTriples3_sound common3_sorted check_common3_true m1 m2 m3 huv hvw
      · have hd4 : d = 4 := Fin.ext h4
        rw [hd4] at hT_non
        have m1 := mem_common4 fu (hT_non fu hfu).1 (hT_non fu hfu).2.1 (hT_non fu hfu).2.2.1 (hT_non fu hfu).2.2.2
        have m2 := mem_common4 fv (hT_non fv hfv).1 (hT_non fv hfv).2.1 (hT_non fv hfv).2.2.1 (hT_non fv hfv).2.2.2
        have m3 := mem_common4 fw (hT_non fw hfw).1 (hT_non fw hfw).2.1 (hT_non fw hfw).2.2.1 (hT_non fw hfw).2.2.2
        exact checkTriples3_sound common4_sorted check_common4_true m1 m2 m3 huv hvw
      · have hd5 : d = 5 := Fin.ext h5
        rw [hd5] at hT_non
        have m1 := mem_common5 fu (hT_non fu hfu).1 (hT_non fu hfu).2.1 (hT_non fu hfu).2.2.1 (hT_non fu hfu).2.2.2
        have m2 := mem_common5 fv (hT_non fv hfv).1 (hT_non fv hfv).2.1 (hT_non fv hfv).2.2.1 (hT_non fv hfv).2.2.2
        have m3 := mem_common5 fw (hT_non fw hfw).1 (hT_non fw hfw).2.1 (hT_non fw hfw).2.2.1 (hT_non fw hfw).2.2.2
        exact checkTriples3_sound common5_sorted check_common5_true m1 m2 m3 huv hvw
    rw [htru] at hfalse
    cases hfalse
  · refine no_indep_five_C17 hcard fun u hu v hv hadj => ?_
    apply hind u hu v hv
    rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨hadj, fun hpair => ?_⟩
    apply h_both
    rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, hu, hv⟩
    · exact ⟨hadj.symm, hv, hu⟩

private theorem exists_color_class_ge_five {H : SimpleGraph (Fin 17)} (hc : H.Colorable 4) :
    ∃ S : Finset (Fin 17), 5 ≤ S.card ∧ ∀ u ∈ S, ∀ v ∈ S, ¬ H.Adj u v := by
  obtain ⟨col⟩ := hc
  have hsum : (Finset.univ : Finset (Fin 17)).card =
      ∑ k ∈ (Finset.univ : Finset (Fin 4)),
        ((Finset.univ : Finset (Fin 17)).filter (fun v => col v = k)).card := by
    refine Finset.card_eq_sum_card_fiberwise (f := col) (fun v _ => Finset.mem_univ (col v))
  have h17 : ∑ k ∈ (Finset.univ : Finset (Fin 4)),
      ((Finset.univ : Finset (Fin 17)).filter (fun v => col v = k)).card = 17 := by
    rw [← hsum]
    decide
  by_contra hnone
  push Not at hnone
  have hle4 : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      ((Finset.univ : Finset (Fin 17)).filter (fun v => col v = k)).card ≤ 4 := by
    intro k _
    by_contra hk
    rw [not_le] at hk
    obtain ⟨u, hu, v, hv, huv⟩ :=
      hnone ((Finset.univ : Finset (Fin 17)).filter (fun v => col v = k)) (by omega)
    have hcu : col u = k := (Finset.mem_filter.mp hu).2
    have hcv : col v = k := (Finset.mem_filter.mp hv).2
    exact col.valid huv (hcu.trans hcv.symm)
  have hsum_le : ∑ k ∈ (Finset.univ : Finset (Fin 4)),
      ((Finset.univ : Finset (Fin 17)).filter (fun v => col v = k)).card ≤
      ∑ _k ∈ (Finset.univ : Finset (Fin 4)), 4 :=
    Finset.sum_le_sum hle4
  have h4x4 : ∑ _k ∈ (Finset.univ : Finset (Fin 4)), 4 = 16 := by decide
  omega

/-- `C17` is not 4-colorable. -/
theorem C17_not_colorable_four : ¬ C17.Colorable 4 := by
  intro hc
  obtain ⟨S, hcard, hind⟩ := exists_color_class_ge_five hc
  exact no_indep_five_C17 hcard hind

/-- Deleting any single edge of `C17` leaves a graph that is still not 4-colorable. -/
theorem C17_deleteEdge_not_colorable_four (e : Sym2 (Fin 17)) :
    ¬ (C17.deleteEdges {e}).Colorable 4 := by
  induction e using Sym2.ind with
  | _ a b =>
    intro hc
    obtain ⟨S, hcard, hind⟩ := exists_color_class_ge_five hc
    exact no_indep_five_C17_deleteEdge hcard hind

/-- Chromatic number and 5-vertex-criticality without critical edges on `ULift.{u} (Fin 17)`. -/
theorem dirac_k5_r1_bridge :
    ∃ (V : Type u) (G : SimpleGraph V),
      (G.chromaticNumber = 5 ∧ ∀ v : V,
        ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber <
          (⊤ : G.Subgraph).coe.chromaticNumber) ∧
      ∀ (edges : Set (Sym2 V)),
        (G.deleteEdges edges).chromaticNumber < G.chromaticNumber → 1 < edges.ncard := by
  let V := ULift.{u} (Fin 17)
  let G : SimpleGraph V := C17.comap ULift.down
  have hG5 : G.Colorable 5 :=
    C17_colorable_five.of_hom (SimpleGraph.Hom.comap ULift.down C17)
  have hG4 : ¬ G.Colorable 4 := by
    intro h
    exact C17_not_colorable_four
      (h.of_hom ⟨ULift.up, fun {x y} hxy => hxy⟩)
  have hchi : G.chromaticNumber = (5 : ℕ∞) := by
    apply le_antisymm
    · exact SimpleGraph.chromaticNumber_le_iff_colorable.mpr hG5
    · refine SimpleGraph.le_chromaticNumber_iff_colorable.mpr fun m hm => ?_
      by_contra hlt
      have hm4 : m ≤ 4 := Nat.le_of_lt_succ (Nat.cast_lt.mp (lt_of_not_ge hlt))
      exact hG4 (hm.mono hm4)
  have htop : (⊤ : G.Subgraph).coe.chromaticNumber = G.chromaticNumber := by
    apply le_antisymm
    · let f1 : (⊤ : G.Subgraph).coe →g G :=
        { toFun := Subtype.val
          map_rel' := fun h => h }
      exact SimpleGraph.chromaticNumber_mono_of_hom f1
    · let f2 : G →g (⊤ : G.Subgraph).coe :=
        { toFun := fun x => ⟨x, trivial⟩
          map_rel' := fun hxy => by simpa using hxy }
      exact SimpleGraph.chromaticNumber_mono_of_hom f2
  refine ⟨V, G, ⟨hchi, ?_⟩, ?_⟩
  · intro v
    rw [htop, hchi]
    have h4 : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable 4 := by
      let f3 : ((⊤ : G.Subgraph).deleteVerts {v}).coe →g ((⊤ : C17.Subgraph).deleteVerts {v.down}).coe :=
        { toFun := fun x => ⟨x.val.down, by
            have hx := x.prop
            simp only [SimpleGraph.Subgraph.deleteVerts_verts, Set.mem_sdiff,
              Set.mem_singleton_iff] at hx ⊢
            exact ⟨trivial, fun hmem => hx.2 (ULift.ext _ _ hmem)⟩⟩
          map_rel' := fun {x y} hxy => by
            rw [SimpleGraph.Subgraph.coe_adj, SimpleGraph.Subgraph.deleteVerts_adj] at hxy ⊢
            rcases hxy with ⟨_, hx_ne, _, hy_ne, hadj⟩
            refine ⟨trivial, ?_, trivial, ?_, hadj⟩
            · intro hmem; exact hx_ne (ULift.ext _ _ hmem)
            · intro hmem; exact hy_ne (ULift.ext _ _ hmem) }
      exact (C17_deleteVert_colorable_four v.down).of_hom f3
    have hle : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber ≤ (4 : ℕ∞) :=
      SimpleGraph.chromaticNumber_le_iff_colorable.mpr h4
    exact lt_of_le_of_lt hle (by decide : (4 : ℕ∞) < 5)
  · intro edges hlt
    rw [hchi] at hlt
    have h4_le : (G.deleteEdges edges).chromaticNumber ≤ (4 : ℕ∞) := by
      cases hχ : (G.deleteEdges edges).chromaticNumber with
      | top => simp [hχ] at hlt
      | coe m =>
        rw [hχ] at hlt
        exact Nat.cast_le.mpr (by exact_mod_cast Nat.lt_succ_iff.mp (Nat.cast_lt.mp hlt))
    have hcol4 : (G.deleteEdges edges).Colorable 4 :=
      SimpleGraph.chromaticNumber_le_iff_colorable.mp h4_le
    by_contra hnot
    rw [not_lt] at hnot
    rcases (by omega : edges.ncard = 0 ∨ edges.ncard = 1) with h0 | h1
    · have hempty : edges = ∅ := (Set.ncard_eq_zero edges.toFinite).mp h0
      rw [hempty, SimpleGraph.deleteEdges_empty] at hcol4
      exact hG4 hcol4
    · obtain ⟨e, rfl⟩ := Set.ncard_eq_one.mp h1
      have hsub : (C17.deleteEdges {Sym2.map ULift.down e}).Colorable 4 := by
        refine hcol4.of_hom ⟨ULift.up, fun {x y} hxy => ?_⟩
        rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hxy ⊢
        refine ⟨hxy.1, fun hpair => hxy.2 ?_⟩
        rw [← hpair]
        induction e using Sym2.ind with
        | _ u v => simp
      exact C17_deleteEdge_not_colorable_four _ hsub

end Contribution.Erdos944DiracK5R1
