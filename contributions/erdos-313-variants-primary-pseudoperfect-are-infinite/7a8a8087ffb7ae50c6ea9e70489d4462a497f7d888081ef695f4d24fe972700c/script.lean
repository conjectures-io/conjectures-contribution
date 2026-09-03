import FormalConjectures.ErdosProblems.«313»

/-!
# Canonical equivalence and direct prime-successor closure for Erdős 313

The defining reciprocal identity forces the denominator to equal the product
of the witness primes. This identifies solution pairs with primary
pseudoperfect denominators and removes the extra bounded-witness hypothesis
from the classical prime-successor recurrence.
-/

namespace Contribution.Erdos313ClosureStrengthened

open Erdos313

/-- Clearing the product of the denominators in a sum of reciprocal naturals. -/
theorem sum_reciprocals_mul_prod (P : Finset ℕ)
    (hnz : ∀ p ∈ P, p ≠ 0) :
    (∑ p ∈ P, (1 : ℚ) / p) * ((P.prod id : ℕ) : ℚ) =
      ∑ p ∈ P, (((P.erase p).prod id : ℕ) : ℚ) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0q : (p : ℚ) ≠ 0 := by exact_mod_cast hnz p hp
  have hprod : p * (P.erase p).prod id = P.prod id := by
    simpa using Finset.mul_prod_erase P id hp
  have hprodq : ((P.prod id : ℕ) : ℚ) =
      (p : ℚ) * (((P.erase p).prod id : ℕ) : ℚ) := by
    exact_mod_cast hprod.symm
  rw [hprodq]
  field_simp

/-- The defining rational equation, cleared by the squarefree product of its
prime denominators. -/
theorem solution_cleared_identity {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) :
    m * (∑ p ∈ P, (P.erase p).prod id) = (m - 1) * P.prod id := by
  rcases hsol with ⟨hm, _, hprime, hsum⟩
  have hnz : ∀ p ∈ P, p ≠ 0 := fun p hp => (hprime p hp).ne_zero
  have hm0q : (m : ℚ) ≠ 0 := by positivity
  have hclearQ :
      (m : ℚ) * (∑ p ∈ P, (((P.erase p).prod id : ℕ) : ℚ)) =
        (((m - 1) * P.prod id : ℕ) : ℚ) := by
    rw [← sum_reciprocals_mul_prod P hnz, hsum]
    push_cast
    field_simp
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  exact_mod_cast hclearQ

/-- A prime in `P` does not divide the product of the other primes. -/
theorem prime_not_dvd_erased_product {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) :
    ¬ p ∣ (P.erase p).prod id := by
  apply Prime.not_dvd_finset_prod (Nat.prime_iff.mp (hprime p hp))
  intro q hq
  simp only [id_eq]
  rcases Finset.mem_erase.mp hq with ⟨hqp, hqP⟩
  intro hpdq
  have hpq : p = q :=
    (Nat.prime_dvd_prime_iff_eq (hprime p hp) (hprime q hqP)).mp hpdq
  exact hqp hpq.symm

/-- Modulo a chosen prime `p`, every cofactor term except the `p`-term
vanishes. Consequently the sum of all cofactors is not divisible by `p`. -/
theorem prime_not_dvd_sum_erased_products {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) :
    ¬ p ∣ ∑ q ∈ P, (P.erase q).prod id := by
  have hother : p ∣ ∑ q ∈ P.erase p, (P.erase q).prod id := by
    apply Finset.dvd_sum
    intro q hq
    apply Finset.dvd_prod_of_mem id
    rcases Finset.mem_erase.mp hq with ⟨hqp, hqP⟩
    exact Finset.mem_erase.mpr ⟨hqp.symm, hp⟩
  intro hall
  have hsplit :
      (∑ q ∈ P.erase p, (P.erase q).prod id) + (P.erase p).prod id =
        ∑ q ∈ P, (P.erase q).prod id := by
    exact Finset.sum_erase_add P (fun q => (P.erase q).prod id) hp
  have hcofactor : p ∣ (P.erase p).prod id := by
    apply (Nat.dvd_add_iff_left hother).mpr
    rw [Nat.add_comm, hsplit]
    exact hall
  exact prime_not_dvd_erased_product hprime hp hcofactor

/-- Every prime occurring in a solution witness divides its denominator. -/
theorem solution_prime_dvd_denominator {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) {p : ℕ} (hp : p ∈ P) :
    p ∣ m := by
  have hprime : ∀ q ∈ P, q.Prime := hsol.2.2.1
  have hcleared := solution_cleared_identity hsol
  have hpD : p ∣ P.prod id := Finset.dvd_prod_of_mem id hp
  have hpmul : p ∣ m * (∑ q ∈ P, (P.erase q).prod id) := by
    rw [hcleared]
    exact hpD.mul_left (m - 1)
  rcases (hprime p hp).dvd_mul.mp hpmul with hpm | hpA
  · exact hpm
  · exact False.elim (prime_not_dvd_sum_erased_products hprime hp hpA)

/-- A finite set of distinct primes, each dividing `m`, has product dividing
`m`. -/
theorem prod_dvd_of_primes_dvd {m : ℕ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ m) :
    P.prod id ∣ m := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      rw [Finset.prod_insert hpS]
      have hpp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hpdiv : p ∣ m := hdiv p (Finset.mem_insert_self p S)
      have hSprime : ∀ q ∈ S, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hSdiv : ∀ q ∈ S, q ∣ m := by
        intro q hq
        exact hdiv q (Finset.mem_insert_of_mem hq)
      have hSprod : S.prod id ∣ m := ih hSprime hSdiv
      have hpnot : ¬ p ∣ S.prod id := by
        apply Prime.not_dvd_finset_prod (Nat.prime_iff.mp hpp)
        intro q hq
        simp only [id_eq]
        intro hpdq
        have hpq : p = q :=
          (Nat.prime_dvd_prime_iff_eq hpp (hSprime q hq)).mp hpdq
        exact hpS (hpq ▸ hq)
      have hcop : Nat.Coprime p (S.prod id) := hpp.coprime_iff_not_dvd.mpr hpnot
      exact hcop.mul_dvd_of_dvd_of_dvd hpdiv hSprod

/-- A finset product of prime naturals is squarefree. -/
theorem prod_primes_squarefree {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) : Squarefree (P.prod id) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
      rw [Finset.prod_insert hpS, Nat.squarefree_mul_iff]
      have hpp : p.Prime := hprime p (Finset.mem_insert_self p S)
      have hSprime : ∀ q ∈ S, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hpnot : ¬ p ∣ S.prod id := by
        have h := prime_not_dvd_erased_product hprime (Finset.mem_insert_self p S)
        simpa [Finset.erase_insert hpS] using h
      exact ⟨hpp.coprime_iff_not_dvd.mpr hpnot, hpp.squarefree, ih hSprime⟩

/-- The product of all primes in a solution witness is exactly the denominator
`m`; in particular, the witness bound used by the closure construction is not
an additional hypothesis. -/
theorem solution_prod_eq_denominator {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) : P.prod id = m := by
  have hm : 2 ≤ m := hsol.1
  have hprime : ∀ p ∈ P, p.Prime := hsol.2.2.1
  have hDvdM : P.prod id ∣ m :=
    prod_dvd_of_primes_dvd hprime (fun p hp => solution_prime_dvd_denominator hsol hp)
  have hcleared := solution_cleared_identity hsol
  have hma : m ∣ m * (∑ p ∈ P, (P.erase p).prod id) := dvd_mul_right _ _
  have hadd :
      m * (∑ p ∈ P, (P.erase p).prod id) + P.prod id = m * P.prod id := by
    rw [hcleared]
    calc
      (m - 1) * P.prod id + P.prod id = ((m - 1) + 1) * P.prod id := by
        rw [Nat.add_mul, one_mul]
      _ = m * P.prod id := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hMDvdD : m ∣ P.prod id := by
    apply (Nat.dvd_add_iff_right hma).mpr
    rw [hadd]
    exact dvd_mul_right _ _
  exact Nat.dvd_antisymm hDvdM hMDvdD

/-- Every solution denominator is squarefree. -/
theorem solution_denominator_squarefree {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) : Squarefree m := by
  rw [← solution_prod_eq_denominator hsol]
  exact prod_primes_squarefree hsol.2.2.1

/-- Every witness prime is bounded by the denominator. -/
theorem solution_prime_le_denominator {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) {p : ℕ} (hp : p ∈ P) :
    p ≤ m := by
  have hm2 : 2 ≤ m := hsol.1
  have hm : 0 < m := by omega
  exact Nat.le_of_dvd hm (solution_prime_dvd_denominator hsol hp)

/-- The witness finset is uniquely determined: it is exactly the finset of
prime factors of the denominator. -/
theorem solution_witness_eq_primeFactors {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) : P = m.primeFactors := by
  have hm2 : 2 ≤ m := hsol.1
  have hm0 : m ≠ 0 := by omega
  have hprime : ∀ p ∈ P, p.Prime := hsol.2.2.1
  apply Finset.ext
  intro p
  constructor
  · intro hp
    exact (hprime p hp).mem_primeFactors
      (solution_prime_dvd_denominator hsol hp) hm0
  · intro hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ P.prod id := by
      rw [solution_prod_eq_denominator hsol]
      exact Nat.dvd_of_mem_primeFactors hp
    rcases (Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hpp) id).mp hpd with
      ⟨q, hq, hpq⟩
    have hpqeq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpp (hprime q hq)).mp hpq
    exact hpqeq ▸ hq

/-- `IsPrimaryPseudoperfect` has a canonical witness, namely
`m.primeFactors`. -/
theorem isPrimaryPseudoperfect_iff_primeFactors_solution {m : ℕ} :
    IsPrimaryPseudoperfect m ↔ (m, m.primeFactors) ∈ erdos313Solutions := by
  constructor
  · rintro ⟨P, hP⟩
    simpa [solution_witness_eq_primeFactors hP] using hP
  · intro hm
    exact ⟨m.primeFactors, hm⟩

/-- Membership in the pair-valued solution set is completely determined by
the denominator: the witness must be its finset of prime factors. -/
theorem mem_solutions_iff_canonical {m : ℕ} {P : Finset ℕ} :
    (m, P) ∈ erdos313Solutions ↔
      P = m.primeFactors ∧ IsPrimaryPseudoperfect m := by
  constructor
  · intro hsol
    exact ⟨solution_witness_eq_primeFactors hsol, ⟨P, hsol⟩⟩
  · rintro ⟨rfl, hprimary⟩
    exact isPrimaryPseudoperfect_iff_primeFactors_solution.mp hprimary

/-- The subtype of solution pairs is equivalent to the subtype of primary
pseudoperfect denominators. The inverse uses the canonical prime-factor
witness. -/
def solutionEquivPrimaryPseudoperfect :
    {s : ℕ × Finset ℕ // s ∈ erdos313Solutions} ≃
      {m : ℕ // IsPrimaryPseudoperfect m} where
  toFun s := ⟨s.1.1, ⟨s.1.2, s.2⟩⟩
  invFun m :=
    ⟨(m.1, m.1.primeFactors),
      isPrimaryPseudoperfect_iff_primeFactors_solution.mp m.2⟩
  left_inv s := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (solution_witness_eq_primeFactors s.2).symm
  right_inv m := rfl

/-- The original pair-valued infinitude statement is exactly equivalent to
infinitude of primary pseudoperfect denominators. -/
theorem solutions_infinite_iff_primary_pseudoperfect_infinite :
    erdos313Solutions.Infinite ↔
      Set.Infinite {m : ℕ | IsPrimaryPseudoperfect m} := by
  rw [← Set.infinite_coe_iff, ← Set.infinite_coe_iff]
  exact solutionEquivPrimaryPseudoperfect.infinite_iff

/-- Adjoining a fresh prime successor transforms a solution at `m` into a
solution at `m * (m + 1)`. -/
theorem extend_solution {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions)
    (hprime : (m + 1).Prime) (hfresh : m + 1 ∉ P) :
    (m * (m + 1), insert (m + 1) P) ∈ erdos313Solutions := by
  rcases hsol with ⟨hm, hPne, hPprime, hsum⟩
  refine ⟨by nlinarith, Finset.insert_nonempty _ _, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hprime
    · exact hPprime p hp
  · rw [Finset.sum_insert hfresh, hsum]
    push_cast
    field_simp
    ring

/-- Freshness is automatic: the exact witness identity forces every old
prime to divide, hence be at most, `m`. -/
theorem extend_solution_mul_succ {m : ℕ} {P : Finset ℕ}
    (hsol : (m, P) ∈ erdos313Solutions) (hprime : (m + 1).Prime) :
    (m * (m + 1), insert (m + 1) P) ∈ erdos313Solutions := by
  apply extend_solution hsol hprime
  intro hmem
  have := solution_prime_le_denominator hsol hmem
  omega

/-- The classical prime-successor recurrence now applies directly to the
upstream `IsPrimaryPseudoperfect` predicate, with no auxiliary invariant. -/
theorem primary_pseudoperfect_mul_succ {m : ℕ}
    (hsol : IsPrimaryPseudoperfect m) (hprime : (m + 1).Prime) :
    IsPrimaryPseudoperfect (m * (m + 1)) := by
  rcases hsol with ⟨P, hP⟩
  exact ⟨insert (m + 1) P, extend_solution_mul_succ hP hprime⟩

end Contribution.Erdos313ClosureStrengthened
