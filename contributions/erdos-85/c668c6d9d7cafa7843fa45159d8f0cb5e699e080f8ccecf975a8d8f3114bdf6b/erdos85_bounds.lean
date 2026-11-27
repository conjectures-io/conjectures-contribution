import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic

/-!
# Erdős Problem 85: Reiman Upper Bound, Small-`n` Drop, and Exact Extremal Values

Self-contained Lean 4 contribution establishing structural bounds and exact values for `Erdos85.f n`,
the minimal degree threshold forcing a 4-cycle `C₄` on `n` vertices:
- General equivalence between `¬ (cycleGraph 4) ⊑ G` and the common-neighbor bound `≤ 1`,
- Reiman's cherry-counting bound `∑ w, d(w) (d(w) - 1) ≤ n (n - 1)` and `f n ≤ k` when `n ≤ k (k - 1)`,
- Exact values `f 1 = 1`, `f 2 = 2`, `f 3 = 3`, `f 4 = 2`, `f 5 = 3`, `f 6 = 3`,
- Non-monotonicity drop `f 4 < f 3`,
- Exact extremal witnesses `f 10 = 4` (Petersen), `f 15 = 5` (polarity graph), and `f 16 = 5`.
-/

namespace Contribution.Erdos85

open SimpleGraph Finset

/--
Minimal integer `k` for which every simple graph on `Fin n` with `G.minDegree ≥ k` contains a
copy of `cycleGraph 4`. Matches `Erdos85.f` definitionally.
-/
noncomputable def f (n : ℕ) : ℕ :=
  open scoped Classical in
  sInf {k : ℕ | ∀ (G : SimpleGraph (Fin n)), G.minDegree ≥ k → (cycleGraph 4) ⊑ G}

private lemma minDegree_congr_dec {V : Type*} [Fintype V] (G : SimpleGraph V)
    (d₁ d₂ : DecidableRel G.Adj) :
    @SimpleGraph.minDegree V G _ d₁ = @SimpleGraph.minDegree V G _ d₂ := by
  cases Subsingleton.elim d₁ d₂
  rfl

/-- Upper bound `f n ≤ k` from showing every graph on `Fin n` with `minDegree ≥ k` has a `C₄`. -/
theorem f_le_of_forall {n k : ℕ}
    (h : ∀ (G : SimpleGraph (Fin n)), open scoped Classical in G.minDegree ≥ k → (cycleGraph 4) ⊑ G) :
    f n ≤ k := by
  unfold f
  exact Nat.sInf_le h

/-- Trivial upper bound `f n ≤ n` for `n > 0`. -/
theorem f_le_self {n : ℕ} (hn : 0 < n) : f n ≤ n := by
  apply f_le_of_forall
  intro G hmin
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hlt : (open scoped Classical in G.minDegree) < Fintype.card (Fin n) :=
    open scoped Classical in G.minDegree_lt_card
  simp only [Fintype.card_fin] at hlt
  omega

/-- Lower bound `d + 1 ≤ f n` from an explicit `C₄`-free graph on `Fin n` with all degrees `≥ d`. -/
theorem lt_f_of_c4_free {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin n, d ≤ G.degree v) (hc4 : ¬ (cycleGraph 4) ⊑ G) : d + 1 ≤ f n := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  unfold f
  set S : Set ℕ :=
    {k : ℕ | ∀ (H : SimpleGraph (Fin n)), open scoped Classical in H.minDegree ≥ k → (cycleGraph 4) ⊑ H}
  have hmem_n : n ∈ S := by
    intro H hmin
    have hlt : (open scoped Classical in H.minDegree) < Fintype.card (Fin n) :=
      open scoped Classical in H.minDegree_lt_card
    simp only [Fintype.card_fin] at hlt
    omega
  refine le_csInf ⟨n, hmem_n⟩ ?_
  intro k hk
  by_contra hkd
  have hle : k ≤ d := by omega
  have hd_min : d ≤ G.minDegree := G.le_minDegree_of_forall_le_degree d hdeg
  have hk_min : (@SimpleGraph.minDegree (Fin n) G (Fin.fintype n)
      (fun a b => Classical.propDecidable (G.Adj a b))) ≥ k := by
    change k ≤ _
    rw [minDegree_congr_dec G _ inferInstance]
    exact hle.trans hd_min
  exact hc4 (hk G hk_min)

private lemma copy_cycleGraph4_of_four {V : Type*} {G : SimpleGraph V} (a b c d : V)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (had_ne : a ≠ d)
    (hbc_ne : b ≠ c) (hbd_ne : b ≠ d) (hcd_ne : c ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a) :
    (cycleGraph 4) ⊑ G := by
  refine ⟨⟨⟨![a, b, c, d], ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd hij (by decide)
      | exact hab
      | exact hab.symm
      | exact hbc
      | exact hbc.symm
      | exact hcd
      | exact hcd.symm
      | exact hda
      | exact hda.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij hab_ne
      | exact absurd hij hac_ne
      | exact absurd hij had_ne
      | exact absurd hij hab_ne.symm
      | exact absurd hij hbc_ne
      | exact absurd hij hbd_ne
      | exact absurd hij hac_ne.symm
      | exact absurd hij hbc_ne.symm
      | exact absurd hij hcd_ne
      | exact absurd hij had_ne.symm
      | exact absurd hij hbd_ne.symm
      | exact absurd hij hcd_ne.symm

/--
A finite graph is `C₄`-free if and only if every pair of distinct vertices has at most one
common neighbor.
-/
theorem c4_free_iff_common_neighbors_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ (cycleGraph 4) ⊑ G ↔ ∀ u v : V, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  constructor
  · intro hc4 u v huv
    by_contra hlt
    have hgt : 1 < (G.neighborFinset u ∩ G.neighborFinset v).card := Nat.lt_of_not_ge hlt
    rcases Finset.one_lt_card.mp hgt with ⟨x, hx, y, hy, hxy⟩
    simp only [Finset.mem_inter, mem_neighborFinset] at hx hy
    have hc : (cycleGraph 4) ⊑ G :=
      copy_cycleGraph4_of_four u x v y
        (G.ne_of_adj hx.1) huv (G.ne_of_adj hy.1)
        (G.ne_of_adj hx.2).symm hxy (G.ne_of_adj hy.2)
        hx.1 hx.2.symm hy.2 hy.1.symm
    exact hc4 hc
  · intro hcn hc4
    rcases hc4 with ⟨φ⟩
    have hu_ne_v : φ 0 ≠ φ 2 := φ.injective.ne (by decide)
    have h1_ne_3 : φ 1 ≠ φ 3 := φ.injective.ne (by decide)
    have hadj01 : G.Adj (φ 0) (φ 1) := φ.toHom.map_rel (by decide)
    have hadj21 : G.Adj (φ 2) (φ 1) := φ.toHom.map_rel (by decide)
    have hadj03 : G.Adj (φ 0) (φ 3) := φ.toHom.map_rel (by decide)
    have hadj23 : G.Adj (φ 2) (φ 3) := φ.toHom.map_rel (by decide)
    have hsub : ({φ 1, φ 3} : Finset V) ⊆ G.neighborFinset (φ 0) ∩ G.neighborFinset (φ 2) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_inter, mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hadj01, hadj21⟩
      · exact ⟨hadj03, hadj23⟩
    have hcard : 2 ≤ (G.neighborFinset (φ 0) ∩ G.neighborFinset (φ 2)).card := by
      calc
        2 = ({φ 1, φ 3} : Finset V).card := (Finset.card_pair h1_ne_3).symm
        _ ≤ (G.neighborFinset (φ 0) ∩ G.neighborFinset (φ 2)).card := Finset.card_le_card hsub
    have hle := hcn (φ 0) (φ 2) hu_ne_v
    omega

/--
Reiman's cherry-counting inequality: in any finite `C₄`-free graph on `V`,
`∑ w, deg(w) * (deg(w) - 1) ≤ |V| * (|V| - 1)`.
-/
theorem reiman_cherry_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc4 : ¬ (cycleGraph 4) ⊑ G) :
    ∑ w : V, G.degree w * (G.degree w - 1) ≤ Fintype.card V * (Fintype.card V - 1) := by
  have hcn := (c4_free_iff_common_neighbors_le_one G).mp hc4
  have hlhs : ∑ w : V, G.degree w * (G.degree w - 1) =
      ∑ w : V, ((G.neighborFinset w).offDiag).card := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.offDiag_card, G.card_neighborFinset_eq_degree]
    have hmul : G.degree w * G.degree w - G.degree w = G.degree w * (G.degree w - 1) := by
      simpa using (Nat.mul_sub_left_distrib (G.degree w) (G.degree w) 1).symm
    exact hmul.symm
  have hrhs : Fintype.card V * (Fintype.card V - 1) =
      ((Finset.univ : Finset V).offDiag).card := by
    rw [Finset.offDiag_card, Finset.card_univ]
    have hmul : Fintype.card V * Fintype.card V - Fintype.card V =
        Fintype.card V * (Fintype.card V - 1) := by
      simpa using (Nat.mul_sub_left_distrib (Fintype.card V) (Fintype.card V) 1).symm
    exact hmul.symm
  rw [hlhs, hrhs]
  have hfilt : ∀ w : V,
      ((G.neighborFinset w).offDiag).card =
        ∑ p ∈ (Finset.univ : Finset V).offDiag,
          if w ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2 then 1 else 0 := by
    intro w
    have hsub : (G.neighborFinset w).offDiag =
        (Finset.univ : Finset V).offDiag.filter
          (fun p => w ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2) := by
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_inter, mem_neighborFinset, G.adj_comm w]
      tauto
    rw [hsub, Finset.card_filter]
  simp_rw [hfilt]
  rw [Finset.sum_comm]
  have hinner : ∀ p ∈ (Finset.univ : Finset V).offDiag,
      (∑ w : V, if w ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2 then 1 else 0) =
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card := by
    intro p _
    rw [← Finset.card_filter]
    congr 1
    ext w
    simp
  calc
    ∑ p ∈ (Finset.univ : Finset V).offDiag,
        ∑ w : V, (if w ∈ G.neighborFinset p.1 ∩ G.neighborFinset p.2 then 1 else 0)
      = ∑ p ∈ (Finset.univ : Finset V).offDiag,
          (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card := Finset.sum_congr rfl hinner
    _ ≤ ∑ _p ∈ (Finset.univ : Finset V).offDiag, 1 := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_offDiag] at hp
        exact hcn p.1 p.2 hp.2.2
    _ = ((Finset.univ : Finset V).offDiag).card := by simp

/-- Minimum-degree form of Reiman's bound on `Fin n` (`n > 0`). -/
theorem reiman_minDegree_bound {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hc4 : ¬ (cycleGraph 4) ⊑ G) :
    G.minDegree * (G.minDegree - 1) ≤ n - 1 := by
  have hsum := reiman_cherry_bound G hc4
  simp only [Fintype.card_fin] at hsum
  have hterm : ∀ w : Fin n, G.minDegree * (G.minDegree - 1) ≤ G.degree w * (G.degree w - 1) := by
    intro w
    have hle := G.minDegree_le_degree w
    exact Nat.mul_le_mul hle (Nat.sub_le_sub_right hle 1)
  have hnsum : n * (G.minDegree * (G.minDegree - 1)) ≤ n * (n - 1) := by
    calc
      n * (G.minDegree * (G.minDegree - 1))
        = ∑ _w : Fin n, G.minDegree * (G.minDegree - 1) := by simp
      _ ≤ ∑ w : Fin n, G.degree w * (G.degree w - 1) := Finset.sum_le_sum fun w _ => hterm w
      _ ≤ n * (n - 1) := hsum
  exact Nat.le_of_mul_le_mul_left hnsum hn

/-- General Reiman upper bound: if `n ≤ k * (k - 1)` and `0 < n`, then `f n ≤ k`. -/
theorem f_le_of_reiman {n k : ℕ} (hn : 0 < n) (hk : n ≤ k * (k - 1)) : f n ≤ k := by
  apply f_le_of_forall
  intro G hmin
  by_contra hc4
  classical
  have hdeg := reiman_minDegree_bound hn G hc4
  have hmin' : k ≤ G.minDegree := by
    simpa only [minDegree_congr_dec G (Classical.decRel G.Adj) _] using hmin
  have hmul : k * (k - 1) ≤ G.minDegree * (G.minDegree - 1) :=
    Nat.mul_le_mul hmin' (Nat.sub_le_sub_right hmin' 1)
  omega

private lemma eq_of_testBit_of_atMostOneBit {m i j : ℕ}
    (hm : m = 0 ∨ m = 2 ^ m.log2) (hi : m.testBit i = true) (hj : m.testBit j = true) :
    i = j := by
  rcases hm with rfl | h
  · simp at hi
  · rw [h, Nat.testBit_two_pow] at hi hj
    simp only [decide_eq_true_eq] at hi hj
    exact hi.symm.trans hj

private def bitGraph {n : ℕ} (mask : Fin n → ℕ)
    (hirr : ∀ u : Fin n, (mask u).testBit u.val = false)
    (hsym : ∀ u v : Fin n, (mask u).testBit v.val = (mask v).testBit u.val) :
    SimpleGraph (Fin n) where
  Adj u v := (mask u).testBit v.val = true
  symm := ⟨fun u v h => by rw [← hsym u v]; exact h⟩
  loopless := ⟨fun u h => by rw [hirr u] at h; exact Bool.false_ne_true h⟩

private instance instDecidableBitGraph {n : ℕ} (mask : Fin n → ℕ)
    (hirr : ∀ u : Fin n, (mask u).testBit u.val = false)
    (hsym : ∀ u v : Fin n, (mask u).testBit v.val = (mask v).testBit u.val) :
    DecidableRel (bitGraph mask hirr hsym).Adj :=
  fun u v => inferInstanceAs (Decidable ((mask u).testBit v.val = true))

private lemma lt_f_of_bitMask {n d : ℕ} (hn : 0 < n) (mask : Fin n → ℕ)
    (hirr : ∀ u : Fin n, (mask u).testBit u.val = false)
    (hsym : ∀ u v : Fin n, (mask u).testBit v.val = (mask v).testBit u.val)
    (hdeg : ∀ u : Fin n,
      (Finset.univ.filter (fun v : Fin n => (mask u).testBit v.val = true)).card = d)
    (hc4 : ∀ u v : Fin n, u ≠ v →
      let m := mask u &&& mask v
      m = 0 ∨ m = 2 ^ m.log2) :
    d + 1 ≤ f n := by
  let G := bitGraph mask hirr hsym
  refine lt_f_of_c4_free hn G (fun v => ?_) ?_
  · rw [← G.card_neighborFinset_eq_degree]
    have hset : G.neighborFinset v =
        Finset.univ.filter (fun w : Fin n => (mask v).testBit w.val = true) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborFinset]
      rfl
    rw [hset, hdeg v]
  · rw [c4_free_iff_common_neighbors_le_one G]
    intro u v huv
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_inter, mem_neighborFinset] at hx hy
    change (mask u).testBit x.val = true ∧ (mask v).testBit x.val = true at hx
    change (mask u).testBit y.val = true ∧ (mask v).testBit y.val = true at hy
    have hxand : (mask u &&& mask v).testBit x.val = true := by
      rw [Nat.testBit_and, hx.1, hx.2]
      rfl
    have hyand : (mask u &&& mask v).testBit y.val = true := by
      rw [Nat.testBit_and, hy.1, hy.2]
      rfl
    exact Fin.ext (eq_of_testBit_of_atMostOneBit (hc4 u v huv) hxand hyand)

/-- Exact value `f 1 = 1`. -/
theorem f_one_eq : f 1 = 1 := by
  apply le_antisymm (f_le_self (by decide))
  refine lt_f_of_c4_free (by decide) (⊥ : SimpleGraph (Fin 1)) (fun v => by simp) ?_
  intro ⟨φ⟩
  have h : φ 0 ≠ φ 1 := φ.injective.ne (by decide)
  exact h (Subsingleton.elim _ _)

/-- Exact value `f 2 = 2`. -/
theorem f_two_eq : f 2 = 2 := by
  apply le_antisymm (f_le_self (by decide))
  refine lt_f_of_c4_free (by decide) (⊤ : SimpleGraph (Fin 2)) (fun v => by
    fin_cases v <;> decide) ?_
  intro ⟨φ⟩
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card (Fin 2) := Fintype.card_le_of_injective φ φ.injective
  simp at hcard

/-- Exact value `f 3 = 3` (realized by `K₃`). -/
theorem f_three_eq : f 3 = 3 := by
  apply le_antisymm (f_le_self (by decide))
  refine lt_f_of_c4_free (by decide) (⊤ : SimpleGraph (Fin 3)) (fun v => by
    fin_cases v <;> decide) ?_
  intro ⟨φ⟩
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card (Fin 3) := Fintype.card_le_of_injective φ φ.injective
  simp at hcard

private lemma four_adj_of_not_adj {G : SimpleGraph (Fin 4)} [DecidableRel G.Adj]
    (v x y z : Fin 4) (hv2 : 2 ≤ G.degree v)
    (hx : x ≠ v) (hy : y ≠ v) (hz : z ≠ v) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnx : ¬ G.Adj v x) : G.Adj v y ∧ G.Adj v z := by
  have huniv : ∀ w : Fin 4, w = v ∨ w = x ∨ w = y ∨ w = z := by
    fin_cases v <;> fin_cases x <;> fin_cases y <;> fin_cases z <;>
      first
      | exact absurd rfl hx
      | exact absurd rfl hy
      | exact absurd rfl hz
      | exact absurd rfl hxy
      | exact absurd rfl hxz
      | exact absurd rfl hyz
      | exact (fun w => by fin_cases w <;> simp)
  have hsub_single : ∀ p : Fin 4, (∀ w ∈ G.neighborFinset v, w = p) → False := by
    intro p hp
    have hsub : G.neighborFinset v ⊆ {p} := by
      intro w hw
      simp only [Finset.mem_singleton]
      exact hp w hw
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton, G.card_neighborFinset_eq_degree] at hle
    omega
  constructor
  · by_contra hny
    apply hsub_single z
    intro w hw
    rw [mem_neighborFinset] at hw
    rcases huniv w with rfl | rfl | rfl | rfl
    · exact absurd hw (G.ne_of_adj hw rfl |>.elim)
    · exact absurd hw hnx
    · exact absurd hw hny
    · rfl
  · by_contra hnz
    apply hsub_single y
    intro w hw
    rw [mem_neighborFinset] at hw
    rcases huniv w with rfl | rfl | rfl | rfl
    · exact absurd hw (G.ne_of_adj hw rfl |>.elim)
    · exact absurd hw hnx
    · rfl
    · exact absurd hw hnz

private lemma four_adj_or_adj {G : SimpleGraph (Fin 4)} [DecidableRel G.Adj]
    (v a b c : Fin 4) (hv2 : 2 ≤ G.degree v)
    (hva : v ≠ a) (hvb : v ≠ b) (hvc : v ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.Adj v b ∨ G.Adj v c := by
  by_contra hnone
  simp only [not_or] at hnone
  have huniv : ∀ w : Fin 4, w = v ∨ w = a ∨ w = b ∨ w = c := by
    fin_cases v <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
      first
      | exact absurd rfl hva.symm
      | exact absurd rfl hvb.symm
      | exact absurd rfl hvc.symm
      | exact absurd rfl hab
      | exact absurd rfl hac
      | exact absurd rfl hbc
      | exact (fun w => by fin_cases w <;> simp)
  have hsub : G.neighborFinset v ⊆ {a} := by
    intro w hw
    rw [mem_neighborFinset] at hw
    simp only [Finset.mem_singleton]
    rcases huniv w with rfl | rfl | rfl | rfl
    · exact absurd hw (G.ne_of_adj hw rfl |>.elim)
    · rfl
    · exact absurd hw hnone.1
    · exact absurd hw hnone.2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_singleton, G.card_neighborFinset_eq_degree] at hle
  omega

private lemma four_verts_c4 (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj]
    (hmin : G.minDegree ≥ 2) : (cycleGraph 4) ⊑ G := by
  have hdeg : ∀ v : Fin 4, 2 ≤ G.degree v := fun v => hmin.trans (G.minDegree_le_degree v)
  by_cases h01 : G.Adj 0 1
  · by_cases h02 : G.Adj 0 2
    · by_cases h03 : G.Adj 0 3
      · rcases four_adj_or_adj 1 0 2 3 (hdeg 1)
            (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) with h12 | h13
        · rcases four_adj_or_adj 3 0 1 2 (hdeg 3)
              (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) with h31 | h32
          · exact copy_cycleGraph4_of_four 0 3 1 2 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) h03 h31 h12 h02.symm
          · exact copy_cycleGraph4_of_four 0 1 2 3 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) h01 h12 h32.symm h03.symm
        · rcases four_adj_or_adj 2 0 1 3 (hdeg 2)
              (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) with h21 | h23
          · exact copy_cycleGraph4_of_four 0 2 1 3 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) h02 h21 h13 h03.symm
          · exact copy_cycleGraph4_of_four 0 1 3 2 (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) h01 h13 h23.symm h02.symm
      · have h0 := four_adj_of_not_adj 0 3 1 2 (hdeg 0)
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) h03
        have h3 := four_adj_of_not_adj 3 0 1 2 (hdeg 3)
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (fun h => h03 h.symm)
        exact copy_cycleGraph4_of_four 0 1 3 2 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) h0.1 h3.1.symm h3.2 h0.2.symm
    · have h0 := four_adj_of_not_adj 0 2 1 3 (hdeg 0)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h02
      have h2 := four_adj_of_not_adj 2 0 1 3 (hdeg 2)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (fun h => h02 h.symm)
      exact copy_cycleGraph4_of_four 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h0.1 h2.1.symm h2.2 h0.2.symm
  · have h0 := four_adj_of_not_adj 0 1 2 3 (hdeg 0)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h01
    have h1 := four_adj_of_not_adj 1 0 2 3 (hdeg 1)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (fun h => h01 h.symm)
    exact copy_cycleGraph4_of_four 0 2 1 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h0.1 h1.1.symm h1.2 h0.2.symm

/-- Exact value `f 4 = 2`. -/
theorem f_four_eq : f 4 = 2 := by
  apply le_antisymm
  · apply f_le_of_forall
    intro G hmin
    exact @four_verts_c4 G (Classical.decRel G.Adj) hmin
  · exact lt_f_of_bitMask (by decide) ![2, 1, 8, 4]
      (by decide) (by decide) (by decide) (by decide)

/-- Non-monotonicity witness at small `n`: `f 4 < f 3` (`2 < 3`). -/
theorem f_drop_at_three : f 4 < f 3 := by
  rw [f_four_eq, f_three_eq]
  norm_num

/-- Exact value `f 5 = 3` (realized by `C₅`). -/
theorem f_five_eq : f 5 = 3 := by
  apply le_antisymm (f_le_of_reiman (by decide) (by norm_num))
  exact lt_f_of_bitMask (by decide) ![18, 5, 10, 20, 9]
    (by decide) (by decide) (by decide) (by decide)

/-- Exact value `f 6 = 3` (realized by `C₆`). -/
theorem f_six_eq : f 6 = 3 := by
  apply le_antisymm (f_le_of_reiman (by decide) (by norm_num))
  exact lt_f_of_bitMask (by decide) ![34, 5, 10, 20, 40, 17]
    (by decide) (by decide) (by decide) (by decide)

/-- Exact value `f 10 = 4` (realized by the 3-regular Petersen graph). -/
theorem f_ten_eq : f 10 = 4 := by
  apply le_antisymm (f_le_of_reiman (by decide) (by norm_num))
  exact lt_f_of_bitMask (by decide) ![50, 69, 138, 276, 521, 385, 770, 548, 104, 208]
    (by decide) (by decide) (by decide) (by decide)

/-- Exact value `f 15 = 5` (realized by the 4-regular polarity graph `ER₄ \ (L₀ ∪ {ν})`). -/
theorem f_fifteen_eq : f 15 = 5 := by
  apply le_antisymm (f_le_of_reiman (by decide) (by norm_num))
  exact lt_f_of_bitMask (by decide)
    ![4626, 113, 1304, 8340, 15, 16706, 2210, 10312, 17444, 28673, 6404, 5312, 3585, 17032, 8992]
    (by decide) (by decide) (by decide) (by decide)

/-- Exact value `f 16 = 5` (realized by an explicit 4-regular `C₄`-free graph on 16 vertices). -/
theorem f_sixteen_eq : f 16 = 5 := by
  apply le_antisymm (f_le_of_reiman (by decide) (by norm_num))
  exact lt_f_of_bitMask (by decide)
    ![3586, 8833, 4448, 22544, 37384, 41220, 5252, 24642,
      16932, 275, 34881, 17417, 92, 32930, 2440, 9264]
    (by decide) (by decide) (by decide) (by decide)

/-- Equality `f 15 = f 16` showing no drop occurs at `n = 15 → 16`. -/
theorem f_fifteen_eq_sixteen : f 15 = f 16 := by
  rw [f_fifteen_eq, f_sixteen_eq]

end Contribution.Erdos85
