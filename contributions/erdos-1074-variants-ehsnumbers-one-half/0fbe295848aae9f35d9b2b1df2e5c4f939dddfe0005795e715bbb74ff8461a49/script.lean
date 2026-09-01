import Mathlib
import FormalConjectures.ErdosProblems.«1074»

-- ==== from Wave_erdos1074_EHS.lean ====
/-!
Contribution: proof of `erdos_1074.variants.EHSNumbers_init` from Erdős Problem 1074.

The sequence of EHS numbers begins `8, 9, 13, 14, 15, 16, 17`.
-/

open scoped Nat
open Nat Erdos1074

namespace Contribution.Erdos1074EHSNumbersInit

/-- If `m ! + 1` factors as `q ^ a * r ^ b` with `q`, `r` primes both congruent to `1` mod `m`,
then `m` is not an EHS number. -/
private lemma notMem_of_fac (q a r b : ℕ) {m : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hfac : m ! + 1 = q ^ a * r ^ b)
    (hq1 : q ≡ 1 [MOD m]) (hr1 : r ≡ 1 [MOD m]) : ¬ EHSNumbers m := by
  rintro ⟨-, p, hp, hne, hdvd⟩
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · have hpq := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)
    subst hpq
    exact hne hq1
  · have hpr := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)
    subst hpr
    exact hne hr1

/-- The sequence $S$ begins $8, 9, 13, 14, 15, 16, 17, ...$ -/
theorem erdos_1074.variants.EHSNumbers_init :
    nth EHSNumbers '' (Set.Icc 0 6) = {8, 9, 13, 14, 15, 16, 17} := by
  classical
  -- non-membership of 0, 1, ..., 7, 10, 11, 12
  have h0 : ¬ EHSNumbers 0 := by rintro ⟨h, -⟩; omega
  have h1 : ¬ EHSNumbers 1 := by rintro ⟨-, p, -, hne, -⟩; exact hne Nat.modEq_one
  have h2 : ¬ EHSNumbers 2 :=
    notMem_of_fac 3 1 3 0 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h3 : ¬ EHSNumbers 3 :=
    notMem_of_fac 7 1 7 0 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h4 : ¬ EHSNumbers 4 :=
    notMem_of_fac 5 2 5 0 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h5 : ¬ EHSNumbers 5 :=
    notMem_of_fac 11 2 11 0 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h6 : ¬ EHSNumbers 6 :=
    notMem_of_fac 7 1 103 1 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h7 : ¬ EHSNumbers 7 :=
    notMem_of_fac 71 2 71 0 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h10 : ¬ EHSNumbers 10 :=
    notMem_of_fac 11 1 329891 1 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  have h11 : ¬ EHSNumbers 11 :=
    notMem_of_fac 39916801 1 39916801 0 (by norm_num) (by norm_num) (by decide) (by decide)
      (by decide)
  have h12 : ¬ EHSNumbers 12 :=
    notMem_of_fac 13 2 2834329 1 (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
  -- membership of 8, 9, 13, 14, 15, 16, 17
  have m8 : EHSNumbers 8 := ⟨by norm_num, 61, by norm_num, by decide, by decide⟩
  have m9 : EHSNumbers 9 := ⟨by norm_num, 71, by norm_num, by decide, by decide⟩
  have m13 : EHSNumbers 13 := ⟨by norm_num, 83, by norm_num, by decide, by decide⟩
  have m14 : EHSNumbers 14 := ⟨by norm_num, 23, by norm_num, by decide, by decide⟩
  have m15 : EHSNumbers 15 := ⟨by norm_num, 59, by norm_num, by decide, by decide⟩
  have m16 : EHSNumbers 16 := ⟨by norm_num, 61, by norm_num, by decide, by decide⟩
  have m17 : EHSNumbers 17 := ⟨by norm_num, 661, by norm_num, by decide, by decide⟩
  -- counting
  have c1 : Nat.count EHSNumbers 1 = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.count_succ, Nat.count_zero, if_neg h0]
  have c2 : Nat.count EHSNumbers 2 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.count_succ, c1, if_neg h1]
  have c3 : Nat.count EHSNumbers 3 = 0 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.count_succ, c2, if_neg h2]
  have c4 : Nat.count EHSNumbers 4 = 0 := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, Nat.count_succ, c3, if_neg h3]
  have c5 : Nat.count EHSNumbers 5 = 0 := by
    rw [show (5 : ℕ) = 4 + 1 from rfl, Nat.count_succ, c4, if_neg h4]
  have c6 : Nat.count EHSNumbers 6 = 0 := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, Nat.count_succ, c5, if_neg h5]
  have c7 : Nat.count EHSNumbers 7 = 0 := by
    rw [show (7 : ℕ) = 6 + 1 from rfl, Nat.count_succ, c6, if_neg h6]
  have c8 : Nat.count EHSNumbers 8 = 0 := by
    rw [show (8 : ℕ) = 7 + 1 from rfl, Nat.count_succ, c7, if_neg h7]
  have c9 : Nat.count EHSNumbers 9 = 1 := by
    rw [show (9 : ℕ) = 8 + 1 from rfl, Nat.count_succ, c8, if_pos m8]
  have c10 : Nat.count EHSNumbers 10 = 2 := by
    rw [show (10 : ℕ) = 9 + 1 from rfl, Nat.count_succ, c9, if_pos m9]
  have c11 : Nat.count EHSNumbers 11 = 2 := by
    rw [show (11 : ℕ) = 10 + 1 from rfl, Nat.count_succ, c10, if_neg h10]
  have c12 : Nat.count EHSNumbers 12 = 2 := by
    rw [show (12 : ℕ) = 11 + 1 from rfl, Nat.count_succ, c11, if_neg h11]
  have c13 : Nat.count EHSNumbers 13 = 2 := by
    rw [show (13 : ℕ) = 12 + 1 from rfl, Nat.count_succ, c12, if_neg h12]
  have c14 : Nat.count EHSNumbers 14 = 3 := by
    rw [show (14 : ℕ) = 13 + 1 from rfl, Nat.count_succ, c13, if_pos m13]
  have c15 : Nat.count EHSNumbers 15 = 4 := by
    rw [show (15 : ℕ) = 14 + 1 from rfl, Nat.count_succ, c14, if_pos m14]
  have c16 : Nat.count EHSNumbers 16 = 5 := by
    rw [show (16 : ℕ) = 15 + 1 from rfl, Nat.count_succ, c15, if_pos m15]
  have c17 : Nat.count EHSNumbers 17 = 6 := by
    rw [show (17 : ℕ) = 16 + 1 from rfl, Nat.count_succ, c16, if_pos m16]
  -- the values of `nth`
  have n0 : nth EHSNumbers 0 = 8 := by have h := Nat.nth_count m8; rwa [c8] at h
  have n1 : nth EHSNumbers 1 = 9 := by have h := Nat.nth_count m9; rwa [c9] at h
  have n2 : nth EHSNumbers 2 = 13 := by have h := Nat.nth_count m13; rwa [c13] at h
  have n3 : nth EHSNumbers 3 = 14 := by have h := Nat.nth_count m14; rwa [c14] at h
  have n4 : nth EHSNumbers 4 = 15 := by have h := Nat.nth_count m15; rwa [c15] at h
  have n5 : nth EHSNumbers 5 = 16 := by have h := Nat.nth_count m16; rwa [c16] at h
  have n6 : nth EHSNumbers 6 = 17 := by have h := Nat.nth_count m17; rwa [c17] at h
  have hIcc : (Set.Icc (0 : ℕ) 6) = {0, 1, 2, 3, 4, 5, 6} := by
    ext x
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [hIcc, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    n0, n1, n2, n3, n4, n5, n6]

end Contribution.Erdos1074EHSNumbersInit

-- ==== from Wave_erdos1074_Pillai.lean ====
/-
Contribution: proof of `erdos_1074.variants.PillaiPrimes_init` from Erdős Problem 1074.

The sequence of Pillai primes begins `23, 29, 59, 61, 67, 71`.
-/

open scoped Nat
open Nat Erdos1074

namespace Contribution.Erdos1074PillaiPrimesInit

/-- A decidable predicate that agrees with `Erdos1074.PillaiPrimes`. -/
abbrev PillaiAux : ℕ → Prop := fun p =>
  p.Prime ∧ ∃ m ∈ Finset.Ico 1 p, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1

/-- For a prime `p`, any `m ≥ 1` with `p ∣ m ! + 1` satisfies `m < p`, hence `PillaiPrimes`
agrees with the decidable predicate `PillaiAux`. -/
lemma pillaiPrimes_eq : PillaiPrimes = PillaiAux := by
  ext p
  constructor
  · rintro ⟨hp, m, hm1, hne, hdvd⟩
    refine ⟨hp, m, Finset.mem_Ico.mpr ⟨hm1, ?_⟩, hne, hdvd⟩
    by_contra hle
    push_neg at hle
    have h2 : p ∣ m ! := Nat.dvd_factorial hp.pos hle
    have h1 : p = 1 := by simpa using Nat.dvd_sub hdvd h2
    exact hp.ne_one h1
  · rintro ⟨hp, m, hm, hne, hdvd⟩
    exact ⟨hp, m, (Finset.mem_Ico.mp hm).1, hne, hdvd⟩

/-- The sequence $P$ begins $23, 29, 59, 61, 67, 71, ...$ -/
theorem erdos_1074.variants.PillaiPrimes_init :
    nth PillaiPrimes '' (Set.Icc 0 5) = {23, 29, 59, 61, 67, 71} := by
  have m23 : PillaiAux 23 := by decide
  have m29 : PillaiAux 29 := by decide
  have m59 : PillaiAux 59 := by decide
  have m61 : PillaiAux 61 := by decide
  have m67 : PillaiAux 67 := by decide
  have m71 : PillaiAux 71 := by decide
  have c23 : Nat.count PillaiAux 23 = 0 := by decide
  have c29 : Nat.count PillaiAux 29 = 1 := by decide
  have c59 : Nat.count PillaiAux 59 = 2 := by decide
  have c61 : Nat.count PillaiAux 61 = 3 := by decide
  have c67 : Nat.count PillaiAux 67 = 4 := by decide
  have c71 : Nat.count PillaiAux 71 = 5 := by decide
  have n0 : nth PillaiAux 0 = 23 := by have h := Nat.nth_count m23; rwa [c23] at h
  have n1 : nth PillaiAux 1 = 29 := by have h := Nat.nth_count m29; rwa [c29] at h
  have n2 : nth PillaiAux 2 = 59 := by have h := Nat.nth_count m59; rwa [c59] at h
  have n3 : nth PillaiAux 3 = 61 := by have h := Nat.nth_count m61; rwa [c61] at h
  have n4 : nth PillaiAux 4 = 67 := by have h := Nat.nth_count m67; rwa [c67] at h
  have n5 : nth PillaiAux 5 = 71 := by have h := Nat.nth_count m71; rwa [c71] at h
  have hIcc : (Set.Icc (0 : ℕ) 5) = {0, 1, 2, 3, 4, 5} := by
    ext x
    simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rw [pillaiPrimes_eq, hIcc, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, n0, n1, n2, n3, n4, n5]

end Contribution.Erdos1074PillaiPrimesInit
