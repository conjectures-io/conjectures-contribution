import FormalConjectures.ErdosProblems.«126»
import TaskSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace Contribution.Subb

open Erdos126
open scoped BigOperators

/-- The product of the ordered distinct pairwise sums of a finite set. -/
def addFactorsProduct (A : Finset ℕ) : ℕ :=
  ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)

/-- Diagonal pairs are excluded, so no factor in the product can be zero. -/
theorem addFactorsProduct_ne_zero (A : Finset ℕ) : addFactorsProduct A ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  rintro ⟨a, b⟩ hab hsum
  obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp hsum
  exact (Finset.mem_offDiag.mp hab).2.2 (ha.trans hb.symm)

/-- Inclusion of finite sets induces divisibility of their pairwise-sum products. -/
theorem addFactorsProduct_dvd_of_subset {A B : Finset ℕ} (hAB : A ⊆ B) :
    addFactorsProduct A ∣ addFactorsProduct B := by
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.offDiag_mono hAB)

/-- The number of distinct prime factors of the pairwise-sum product is monotone. -/
theorem primeFactorsCard_le_of_subset {A B : Finset ℕ} (hAB : A ⊆ B) :
    (addFactorsProduct A).primeFactors.card ≤ (addFactorsProduct B).primeFactors.card := by
  apply Finset.card_le_card
  exact Nat.primeFactors_mono (addFactorsProduct_dvd_of_subset hAB) (addFactorsProduct_ne_zero B)

/-- The extremal function in Erdős 126 is nondecreasing. -/
theorem maximalAddFactorsCard_monotone (f : ℕ → ℕ)
    (hf : IsMaximalAddFactorsCard f) : Monotone f := by
  apply monotone_nat_of_le_succ
  intro n
  apply (hf (n + 1)).2
  intro A hA
  change f n ≤ (addFactorsProduct A).primeFactors.card
  have hpos : 0 < A.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have herase : (A.erase a).card = n := by
    rw [Finset.card_erase_of_mem ha, hA]
    omega
  have hlower := (hf n).1 (A.erase a) herase
  change f n ≤ (addFactorsProduct (A.erase a)).primeFactors.card at hlower
  exact hlower.trans (primeFactorsCard_le_of_subset (Finset.erase_subset a A))

end Contribution.Subb
