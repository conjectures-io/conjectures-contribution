import FormalConjectures.ErdosProblems.«885»

-- ==== from Harvest1_885k2.lean ====
/-!
Erdős 885, k = 2 (Erdős–Rosenfeld): witnesses N = {48, 240} whose factor
difference sets share {8, 22}: 48 = 12·4 = 24·2 and 240 = 20·12 = 30·8.
-/

namespace Contribution.Erdos885KEq2

/-- If `n = (b + d) * b` then `d` is a factor difference of `n`. -/
lemma mem_fds {n b d : ℕ} (hab : n = (b + d) * b) :
    d ∈ Erdos885.factorDifferenceSet n := by
  refine ⟨b + d, b, hab, ?_⟩
  push_cast
  rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]

/-- For `n ≥ 1` the factor difference set of `n` is finite. -/
lemma fds_finite {n : ℕ} (hn : 1 ≤ n) : (Erdos885.factorDifferenceSet n).Finite := by
  apply (Set.finite_Iic n).subset
  rintro d ⟨a, b, hab, hd⟩
  rw [← Int.natCast_natAbs] at hd
  have ha : a ≤ n := Nat.le_of_dvd hn ⟨b, hab⟩
  have hb : b ≤ n := Nat.le_of_dvd hn ⟨a, by rw [hab, mul_comm]⟩
  have hd' : d = ((a : ℤ) - b).natAbs := Nat.cast_inj.mp hd
  simp only [Set.mem_Iic]
  omega

theorem k_eq_2 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 2 ∧
      (⋂ n ∈ Ns, Erdos885.factorDifferenceSet n).ncard ≥ 2 := by
  refine ⟨{48, 240}, by decide, by decide, ?_⟩
  have hsub : (↑({8, 22} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({48, 240} : Finset ℕ), Erdos885.factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter]
    intro n hn
    fin_cases hn <;> rcases hd with rfl | rfl
    · exact mem_fds (b := 4) (by norm_num)
    · exact mem_fds (b := 2) (by norm_num)
    · exact mem_fds (b := 12) (by norm_num)
    · exact mem_fds (b := 8) (by norm_num)
  have hfin : (⋂ n ∈ ({48, 240} : Finset ℕ), Erdos885.factorDifferenceSet n).Finite := by
    apply (fds_finite (n := 48) (by norm_num)).subset
    intro d hd
    simp only [Set.mem_iInter] at hd
    exact hd 48 (by decide)
  calc (2 : ℕ) = ({8, 22} : Finset ℕ).card := by decide
    _ = (↑({8, 22} : Finset ℕ) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end Contribution.Erdos885KEq2

-- ==== from Harvest1_885k3.lean ====
/-
Erdős 885, k = 3 (Jiménez-Urroz): witnesses N = {112, 952, 3240} whose factor
difference sets share {6, 54, 111}:
112 = 14·8 = 56·2 = 112·1, 952 = 34·28 = 68·14 = 119·8, 3240 = 60·54 = 90·36 = 135·24.
-/

namespace Contribution.Erdos885KEq3

/-- If `n = (b + d) * b` then `d` is a factor difference of `n`. -/
lemma mem_fds {n b d : ℕ} (hab : n = (b + d) * b) :
    d ∈ Erdos885.factorDifferenceSet n := by
  refine ⟨b + d, b, hab, ?_⟩
  push_cast
  rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]

/-- For `n ≥ 1` the factor difference set of `n` is finite. -/
lemma fds_finite {n : ℕ} (hn : 1 ≤ n) : (Erdos885.factorDifferenceSet n).Finite := by
  apply (Set.finite_Iic n).subset
  rintro d ⟨a, b, hab, hd⟩
  rw [← Int.natCast_natAbs] at hd
  have ha : a ≤ n := Nat.le_of_dvd hn ⟨b, hab⟩
  have hb : b ≤ n := Nat.le_of_dvd hn ⟨a, by rw [hab, mul_comm]⟩
  have hd' : d = ((a : ℤ) - b).natAbs := Nat.cast_inj.mp hd
  simp only [Set.mem_Iic]
  omega

theorem k_eq_3 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 3 ∧
      (⋂ n ∈ Ns, Erdos885.factorDifferenceSet n).ncard ≥ 3 := by
  refine ⟨{112, 952, 3240}, by decide, by decide, ?_⟩
  have hsub : (↑({6, 54, 111} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({112, 952, 3240} : Finset ℕ), Erdos885.factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter]
    intro n hn
    fin_cases hn <;> rcases hd with rfl | rfl | rfl
    · exact mem_fds (b := 8) (by norm_num)
    · exact mem_fds (b := 2) (by norm_num)
    · exact mem_fds (b := 1) (by norm_num)
    · exact mem_fds (b := 28) (by norm_num)
    · exact mem_fds (b := 14) (by norm_num)
    · exact mem_fds (b := 8) (by norm_num)
    · exact mem_fds (b := 54) (by norm_num)
    · exact mem_fds (b := 36) (by norm_num)
    · exact mem_fds (b := 24) (by norm_num)
  have hfin : (⋂ n ∈ ({112, 952, 3240} : Finset ℕ),
      Erdos885.factorDifferenceSet n).Finite := by
    apply (fds_finite (n := 112) (by norm_num)).subset
    intro d hd
    simp only [Set.mem_iInter] at hd
    exact hd 112 (by decide)
  calc (3 : ℕ) = ({6, 54, 111} : Finset ℕ).card := by decide
    _ = (↑({6, 54, 111} : Finset ℕ) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end Contribution.Erdos885KEq3

-- ==== from Harvest1_885k4.lean ====
/-
Erdős 885, k = 4: witnesses N = {1860300, 5063500, 13351500, 65663136} whose factor difference sets
all contain {420, 2595, 3684, 4380}:
  1860300 = 1590·1170 = 3180·585 = 4134·450 = 4770·390
  5063500 = 2470·2050 = 3895·1300 = 4750·1066 = 5330·950
  13351500 = 3870·3450 = 5175·2580 = 5934·2250 = 6450·2070
  65663136 = 8316·7896 = 9504·6909 = 10152·6468 = 10584·6204
-/

namespace Contribution.Erdos885KEq4

/-- If `n = (b + d) * b` then `d` is a factor difference of `n`. -/
lemma mem_fds {n b d : ℕ} (hab : n = (b + d) * b) :
    d ∈ Erdos885.factorDifferenceSet n := by
  refine ⟨b + d, b, hab, ?_⟩
  push_cast
  rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]

/-- For `n ≥ 1` the factor difference set of `n` is finite. -/
lemma fds_finite {n : ℕ} (hn : 1 ≤ n) : (Erdos885.factorDifferenceSet n).Finite := by
  apply (Set.finite_Iic n).subset
  rintro d ⟨a, b, hab, hd⟩
  rw [← Int.natCast_natAbs] at hd
  have ha : a ≤ n := Nat.le_of_dvd hn ⟨b, hab⟩
  have hb : b ≤ n := Nat.le_of_dvd hn ⟨a, by rw [hab, mul_comm]⟩
  have hd' : d = ((a : ℤ) - b).natAbs := Nat.cast_inj.mp hd
  simp only [Set.mem_Iic]
  omega

theorem k_eq_4 :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = 4 ∧
      (⋂ n ∈ Ns, Erdos885.factorDifferenceSet n).ncard ≥ 4 := by
  refine ⟨{1860300, 5063500, 13351500, 65663136}, by decide, by decide, ?_⟩
  have hsub : (↑({420, 2595, 3684, 4380} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({1860300, 5063500, 13351500, 65663136} : Finset ℕ), Erdos885.factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter]
    intro n hn
    fin_cases hn <;> rcases hd with rfl | rfl | rfl | rfl
    · exact mem_fds (b := 1170) (by norm_num)
    · exact mem_fds (b := 585) (by norm_num)
    · exact mem_fds (b := 450) (by norm_num)
    · exact mem_fds (b := 390) (by norm_num)
    · exact mem_fds (b := 2050) (by norm_num)
    · exact mem_fds (b := 1300) (by norm_num)
    · exact mem_fds (b := 1066) (by norm_num)
    · exact mem_fds (b := 950) (by norm_num)
    · exact mem_fds (b := 3450) (by norm_num)
    · exact mem_fds (b := 2580) (by norm_num)
    · exact mem_fds (b := 2250) (by norm_num)
    · exact mem_fds (b := 2070) (by norm_num)
    · exact mem_fds (b := 7896) (by norm_num)
    · exact mem_fds (b := 6909) (by norm_num)
    · exact mem_fds (b := 6468) (by norm_num)
    · exact mem_fds (b := 6204) (by norm_num)
  have hfin : (⋂ n ∈ ({1860300, 5063500, 13351500, 65663136} : Finset ℕ),
      Erdos885.factorDifferenceSet n).Finite := by
    apply (fds_finite (n := 1860300) (by norm_num)).subset
    intro d hd
    simp only [Set.mem_iInter] at hd
    exact hd 1860300 (by decide)
  calc (4 : ℕ) = ({420, 2595, 3684, 4380} : Finset ℕ).card := by decide
    _ = (↑({420, 2595, 3684, 4380} : Finset ℕ) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end Contribution.Erdos885KEq4
