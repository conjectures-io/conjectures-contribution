/-
Copyright (c) 2026 davidichalfyorov-wq.
Released under Apache 2.0 license; see license.txt.
-/
import Mathlib
import FormalConjectures.ErdosProblems.«274»

/-!
# Finite reduction and maximal-index multiplicities for Erdős 274

Every finite exact coset partition of an arbitrary group descends to a canonical
finite quotient preserving all indices. This gives the reciprocal-index identity
and a full equivalence with the finite-group target. A largest index p^a has
multiplicity divisible by p when p is prime; no condition is imposed on the
smaller indices. Common-base power indices have maximal multiplicity divisible
by the base, including composite bases. The general conjecture remains open.
-/

open scoped Pointwise
open Finset

namespace Contribution.Erdos274Finite

universe u v

variable {G ι : Type*} [Group G] [Fintype ι]

/-- Every subgroup in an exact finite coset partition has finite index. -/
theorem finiteIndex_part (P : Erdos274.Group.ExactCovering G ι) (i : ι) :
    (P.parts i).FiniteIndex := by
  classical
  have hc : ⋃ j ∈ (univ.filter fun j => (P.parts j).FiniteIndex),
      P.reps j • (P.parts j : Set G) = Set.univ :=
    Subgroup.leftCoset_cover_filter_FiniteIndex (by simpa using P.covers)
  have hm := hc.symm ▸ Set.mem_univ (P.reps i)
  obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
  have hij : i = j := by
    by_contra h
    exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ i) (Set.mem_univ j) h)
      (show P.reps i ∈ P.reps i • (P.parts i : Set G) from
        ⟨1, (P.parts i).one_mem, mul_one _⟩) hmj
  subst j
  exact (Finset.mem_filter.mp hj).2

/-- A homomorphism with kernel inside a subgroup reflects its coset membership. -/
theorem mem_map_coset_iff {K : Type*} [Group K] (f : G →* K)
    (H : Subgroup G) (hk : f.ker ≤ H) (a x : G) :
    f x ∈ f a • (H.map f : Set K) ↔ x ∈ a • (H : Set G) := by
  simp only [mem_leftCoset_iff, ← map_inv, ← map_mul]
  change a⁻¹ * x ∈ (H.map f).comap f ↔ a⁻¹ * x ∈ H
  rw [Subgroup.comap_map_eq_self hk]

/-- Push an exact covering through a surjective homomorphism absorbed by every part. -/
def mapCover {K : Type*} [Group K] (P : Erdos274.Group.ExactCovering G ι)
    (f : G →* K) (hf : Function.Surjective f) (hk : ∀ i, f.ker ≤ P.parts i) :
    Erdos274.Group.ExactCovering K ι where
  parts i := (P.parts i).map f
  reps i := f (P.reps i)
  nonempty i := ⟨1, ((P.parts i).map f).one_mem⟩
  disjoint := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    obtain ⟨x, rfl⟩ := hf y
    exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hij)
      ((mem_map_coset_iff f (P.parts i) (hk i) _ _).mp hyi)
      ((mem_map_coset_iff f (P.parts j) (hk j) _ _).mp hyj)
  covers := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have hx := P.covers.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, (mem_map_coset_iff f (P.parts i) (hk i) _ _).mpr hi⟩

/-- Transport preserves every subgroup index, not just its finiteness. -/
theorem mapCover_index {K : Type*} [Group K] (P : Erdos274.Group.ExactCovering G ι)
    (f : G →* K) (hf : Function.Surjective f) (hk : ∀ i, f.ker ≤ P.parts i) (i : ι) :
    ((mapCover P f hf hk).parts i).index = (P.parts i).index :=
  (P.parts i).index_map_eq hf (hk i)

/-- The canonical normal subgroup absorbed by all parts of the covering. -/
abbrev finiteCore (P : Erdos274.Group.ExactCovering G ι) : Subgroup G :=
  (⨅ i, P.parts i).normalCore

theorem finiteCore_normal (P : Erdos274.Group.ExactCovering G ι) :
    (finiteCore P).Normal := by
  infer_instance

theorem finiteCore_finiteIndex (P : Erdos274.Group.ExactCovering G ι) :
    (finiteCore P).FiniteIndex := by
  let : (⨅ i, P.parts i).FiniteIndex := Subgroup.finiteIndex_iInf (finiteIndex_part P)
  infer_instance

theorem finiteCore_le (P : Erdos274.Group.ExactCovering G ι) (i : ι) :
    finiteCore P ≤ P.parts i :=
  (⨅ i, P.parts i).normalCore_le.trans (iInf_le P.parts i)

/-- The exact covering induced on the canonical finite quotient. -/
def finiteQuotientCover (P : Erdos274.Group.ExactCovering G ι) :
    Erdos274.Group.ExactCovering (G ⧸ finiteCore P) ι :=
  mapCover P (QuotientGroup.mk' (finiteCore P)) (QuotientGroup.mk'_surjective _) (by
    intro i
    rw [QuotientGroup.ker_mk']
    exact finiteCore_le P i)

/-- The canonical quotient is finite even when the original ambient group is infinite. -/
theorem finite_quotient (P : Erdos274.Group.ExactCovering G ι) :
    Finite (G ⧸ finiteCore P) := by
  let := finiteCore_finiteIndex P
  infer_instance

theorem finiteQuotientCover_index (P : Erdos274.Group.ExactCovering G ι) (i : ι) :
    ((finiteQuotientCover P).parts i).index = (P.parts i).index :=
  mapCover_index P _ _ _ i

/-- Counting the disjoint cosets in a finite ambient group. -/
theorem sum_card_parts [Finite G] (P : Erdos274.Group.ExactCovering G ι) :
    ∑ i, Nat.card (P.parts i) = Nat.card G := by
  have h := Set.ncard_iUnion_of_finite
    (fun i => Set.toFinite (P.reps i • (P.parts i : Set G)))
    (Set.pairwise_univ.mp P.disjoint)
  rw [P.covers, Set.ncard_univ, finsum_eq_sum_of_fintype] at h
  simp_rw [Set.ncard_smul_set] at h
  have hc (i : ι) : (P.parts i : Set G).ncard = Nat.card (P.parts i) := rfl
  simpa only [hc] using h.symm

/-- The exact reciprocal-index identity, initially in the finite ambient case. -/
theorem sum_inv_index_finite [Finite G] (P : Erdos274.Group.ExactCovering G ι) :
    ∑ i, ((P.parts i).index : ℚ)⁻¹ = 1 := by
  have hn : 0 < Nat.card G := Nat.card_pos
  have hn0 : (Nat.card G : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  apply mul_right_cancel₀ hn0
  rw [Finset.sum_mul, one_mul]
  calc
    ∑ i, ((P.parts i).index : ℚ)⁻¹ * (Nat.card G : ℚ) =
        ∑ i, (Nat.card (P.parts i) : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi0 : ((P.parts i).index : ℚ) ≠ 0 := by
        exact_mod_cast (finiteIndex_part P i).index_ne_zero
      have hi : ((P.parts i).index : ℚ) * (Nat.card (P.parts i) : ℚ) = Nat.card G := by
        exact_mod_cast (P.parts i).index_mul_card
      rw [← hi, inv_mul_cancel_left₀ hi0]
    _ = (Nat.card G : ℚ) := by exact_mod_cast sum_card_parts P

/-- The reciprocal indices of any finite exact coset partition sum to one. -/
theorem sum_inv_index (P : Erdos274.Group.ExactCovering G ι) :
    ∑ i, ((P.parts i).index : ℚ)⁻¹ = 1 := by
  let := finite_quotient P
  simpa only [finiteQuotientCover_index] using sum_inv_index_finite (finiteQuotientCover P)

/-- In an integral power partition, the number of maximal exponents is divisible by the base. -/
theorem base_dvd_maximal_count (b M : ℕ) (e : ι → ℕ)
    (hM : 0 < M) (he : ∀ i, e i ≤ M)
    (hsum : ∑ i, b ^ (M - e i) = b ^ M) :
    b ∣ (univ.filter fun i => e i = M).card := by
  classical
  have hs : (∑ i ∈ univ.filter (fun i => e i = M), b ^ (M - e i)) =
      (univ.filter fun i => e i = M).card := by
    calc
      (∑ i ∈ univ.filter (fun i => e i = M), b ^ (M - e i)) =
          ∑ i ∈ univ.filter (fun i => e i = M), 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp
  have hlower : b ∣ ∑ i ∈ univ.filter (fun i => e i ≠ M), b ^ (M - e i) := by
    apply Finset.dvd_sum
    intro i hi
    have hne := (Finset.mem_filter.mp hi).2
    have hle := he i
    apply dvd_pow_self
    omega
  apply (Nat.dvd_add_iff_left hlower).mpr
  rw [← hs, Finset.sum_filter_add_sum_filter_not, hsum]
  exact dvd_pow_self b hM.ne'


/-- Clear denominators in a reciprocal power identity. -/
theorem power_mass_integral (b M : ℕ) (e : ι → ℕ) (hb : 0 < b)
    (he : ∀ i, e i ≤ M) (hs : ∑ i, ((b ^ e i : ℕ) : ℚ)⁻¹ = 1) :
    ∑ i, b ^ (M - e i) = b ^ M := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have h := congrArg (fun x : ℚ => x * (b : ℚ) ^ M) hs
  rw [Finset.sum_mul, one_mul] at h
  have ht (i : ι) : ((b ^ e i : ℕ) : ℚ)⁻¹ * (b : ℚ) ^ M =
      (b : ℚ) ^ (M - e i) := by
    push_cast
    have hp : (b : ℚ) ^ M = (b : ℚ) ^ e i * (b : ℚ) ^ (M - e i) := by
      rw [← pow_add, Nat.add_sub_of_le (he i)]
    rw [hp, inv_mul_cancel_left₀ (pow_ne_zero _ hb0)]
  simp_rw [ht] at h
  exact_mod_cast h

/-- Index one is impossible in a nontrivial exact partition. -/
theorem index_ne_one (P : Erdos274.Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι) (i : ι) : (P.parts i).index ≠ 1 := by
  classical
  let : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp hι
  obtain ⟨j, hji⟩ := exists_ne i
  intro hi
  have htop := Subgroup.index_eq_one.mp hi
  have hx : P.reps j ∈ P.reps i • (P.parts i : Set G) := by
    simp [htop]
  have hy : P.reps j ∈ P.reps j • (P.parts j : Set G) :=
    ⟨1, (P.parts j).one_mem, mul_one _⟩
  exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hji.symm) hx hy

/-- A common-base index partition has at least that many maximal-index parts. -/
theorem common_base_multiplicity (P : Erdos274.Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι) (b : ℕ) (hb : 2 ≤ b) (e : ι → ℕ)
    (hind : ∀ i, (P.parts i).index = b ^ e i) :
    ∃ M, 0 < M ∧ (∀ i, e i ≤ M) ∧
      b ∣ (univ.filter fun i => e i = M).card ∧
      b ≤ (univ.filter fun i => e i = M).card := by
  classical
  have huniv : (univ : Finset ι).Nonempty := by
    apply Finset.card_pos.mp
    simpa only [Finset.card_univ] using (show 0 < Fintype.card ι by omega)
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image univ e huniv
  have hM : 0 < e j := by
    by_contra h
    have hz : e j = 0 := by omega
    exact index_ne_one P hι j (by rw [hind j, hz, pow_zero])
  have he : ∀ i, e i ≤ e j := fun i => hmax i (mem_univ i)
  have hs : ∑ i, ((b ^ e i : ℕ) : ℚ)⁻¹ = 1 := by
    simpa only [hind] using sum_inv_index P
  have hd := base_dvd_maximal_count b (e j) e hM he
    (power_mass_integral b (e j) e (by omega) he hs)
  have hpos : 0 < (univ.filter fun i => e i = e j).card :=
    Finset.card_pos.mpr ⟨j, by simp⟩
  exact ⟨e j, hM, he, hd, Nat.le_of_dvd hpos hd⟩

/-- The exact Herzog–Schönheim conclusion when all indices are powers of one base. -/
theorem herzog_schonheim_common_base (P : Erdos274.Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι) (b : ℕ) (hb : 2 ≤ b) (e : ι → ℕ)
    (hind : ∀ i, (P.parts i).index = b ^ e i) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  classical
  obtain ⟨M, _, _, _, hcount⟩ := common_base_multiplicity P hι b hb e hind
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show
      1 < (univ.filter fun i => e i = M).card by omega)
  refine ⟨i, j, hij, ?_⟩
  rw [hind i, hind j, (mem_filter.mp hi).2, (mem_filter.mp hj).2]

/-- Distinct parts have distinct representatives. -/
theorem reps_injective (P : Erdos274.Group.ExactCovering G ι) :
    Function.Injective P.reps := by
  intro i j hij
  by_contra hne
  have hx : P.reps i ∈ P.reps i • (P.parts i : Set G) :=
    ⟨1, (P.parts i).one_mem, mul_one _⟩
  have hy : P.reps i ∈ P.reps j • (P.parts j : Set G) := by
    rw [hij]
    exact ⟨1, (P.parts j).one_mem, mul_one _⟩
  exact Set.disjoint_left.mp (P.disjoint (Set.mem_univ i) (Set.mem_univ j) hne) hx hy

/-- A counterexample retains its distinct indices in the canonical finite quotient. -/
theorem finite_counterexample (P : Erdos274.Group.ExactCovering G ι)
    (hinj : Function.Injective fun i => (P.parts i).index) :
    Finite (G ⧸ finiteCore P) ∧
    Function.Injective (fun i => ((finiteQuotientCover P).parts i).index) := by
  refine ⟨finite_quotient P, ?_⟩
  simpa only [finiteQuotientCover_index] using hinj

/-- The full target is equivalent to its restriction to finite groups. -/
theorem herzog_schonheim_iff_finite :
    (∀ {K : Type u} [Group K], 1 < ENat.card K →
      ∀ {κ : Type v} [Fintype κ], 1 < Fintype.card κ →
        ∀ Q : Erdos274.Group.ExactCovering K κ,
          ∃ i j, i ≠ j ∧ (Q.parts i).index = (Q.parts j).index) ↔
    (∀ {K : Type u} [Group K] [Finite K], 1 < ENat.card K →
      ∀ {κ : Type v} [Fintype κ], 1 < Fintype.card κ →
        ∀ Q : Erdos274.Group.ExactCovering K κ,
          ∃ i j, i ≠ j ∧ (Q.parts i).index = (Q.parts j).index) := by
  constructor
  · intro h K _ _ hK κ _ hκ Q
    exact h hK hκ Q
  · intro h K _ _ κ _ hκ Q
    let : Finite (K ⧸ finiteCore Q) := finite_quotient Q
    let : Nontrivial κ := Fintype.one_lt_card_iff_nontrivial.mp hκ
    have hnt : Nontrivial (K ⧸ finiteCore Q) :=
      (reps_injective (finiteQuotientCover Q)).nontrivial
    have hK : 1 < ENat.card (K ⧸ finiteCore Q) :=
      (ENat.one_lt_card_iff_nontrivial _).mpr hnt
    obtain ⟨i, j, hij, heq⟩ := h hK hκ (finiteQuotientCover Q)
    exact ⟨i, j, hij, by simpa only [finiteQuotientCover_index] using heq⟩

/-- In particular the exact target holds for every finite prime-power order group. -/
theorem herzog_schonheim_prime_power_order [Finite G]
    (P : Erdos274.Group.ExactCovering G ι) (hι : 1 < Fintype.card ι)
    (p n : ℕ) (hp : p.Prime) (horder : Nat.card G = p ^ n) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  have hpow (i : ι) : ∃ k ≤ n, (P.parts i).index = p ^ k := by
    apply (Nat.dvd_prime_pow hp).mp
    rw [← horder]
    exact (P.parts i).index_dvd_card
  choose e _ he using hpow
  exact herzog_schonheim_common_base P hι p hp.two_le e he

/-- A reciprocal identity becomes an integer identity at any common denominator. -/
theorem reciprocal_mass_integral (d : ι → ℕ) (L : ℕ)
    (hd : ∀ i, 0 < d i) (hdiv : ∀ i, d i ∣ L)
    (hs : ∑ i, (d i : ℚ)⁻¹ = 1) : ∑ i, L / d i = L := by
  have h := congrArg (fun x : ℚ => x * L) hs
  rw [Finset.sum_mul, one_mul] at h
  have ht (i : ι) : (d i : ℚ)⁻¹ * L = (L / d i : ℕ) := by
    have hi0 : (d i : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have hm : (d i : ℚ) * (L / d i : ℕ) = L := by
      exact_mod_cast Nat.mul_div_cancel' (hdiv i)
    rw [← hm, inv_mul_cancel_left₀ hi0]
  simp_rw [ht] at h
  exact_mod_cast h

/-- A smaller positive integer has smaller valuation than a given prime power. -/
theorem factorization_lt_of_lt_prime_pow (p a n : ℕ) (hp : p.Prime)
    (hn : 0 < n) (hlt : n < p ^ a) : n.factorization p < a := by
  by_contra! h
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hn
    ((hp.pow_dvd_iff_le_factorization hn.ne').mpr h))

/-- A maximal prime-power denominator has multiplicity divisible by that prime. -/
theorem prime_dvd_maximal_count (d : ι → ℕ) (p a : ℕ) (hp : p.Prime)
    (ha : 0 < a) (hd : ∀ i, 0 < d i) (hmax : ∀ i, d i ≤ p ^ a)
    (hex : ∃ j, d j = p ^ a) (hsum : ∑ i, (d i : ℚ)⁻¹ = 1) :
    p ∣ (univ.filter fun i => d i = p ^ a).card := by
  classical
  let L := univ.lcm d
  have hL0 : L ≠ 0 := Finset.lcm_ne_zero_iff.mpr fun i _ => (hd i).ne'
  have hdiv (i : ι) : d i ∣ L := Finset.dvd_lcm (mem_univ i)
  obtain ⟨j, hj⟩ := hex
  have hpa : p ^ a ∣ L := by simpa only [hj] using hdiv j
  have hfac (i : ι) : (d i).factorization p ≤ a := by
    by_cases hi : d i = p ^ a
    · simp [hi, Nat.factorization_pow, hp.factorization_self]
    · exact (factorization_lt_of_lt_prime_pow p a (d i) hp (hd i)
        (lt_of_le_of_ne (hmax i) hi)).le
  have hLf : L.factorization p = a := by
    change (univ.lcm d).factorization p = a
    rw [Finset.factorization_lcm (fun i _ => (hd i).ne')]
    apply le_antisymm (Finset.sup_le fun i _ => hfac i)
    have h := Finset.le_sup (s := univ) (f := fun i => (d i).factorization p) (mem_univ j)
    simpa [hj, Nat.factorization_pow, hp.factorization_self] using h
  have hq0 (i : ι) : L / d i ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) (hdiv i)) (hd i)).ne'
  have hC0 : L / p ^ a ≠ 0 := by simpa only [hj] using hq0 j
  have hC : ¬p ∣ L / p ^ a := by
    have hf : (L / p ^ a).factorization p = 0 := by
      rw [Nat.factorization_div hpa]
      simp [hLf, Nat.factorization_pow, hp.factorization_self]
    intro hh
    have := (hp.dvd_iff_one_le_factorization hC0).mp hh
    omega
  have hlo : p ∣ ∑ i ∈ univ.filter (fun i => d i ≠ p ^ a), L / d i := by
    apply Finset.dvd_sum
    intro i hi
    have hne := (mem_filter.mp hi).2
    have hlt := factorization_lt_of_lt_prime_pow p a (d i) hp (hd i)
      (lt_of_le_of_ne (hmax i) hne)
    apply (hp.dvd_iff_one_le_factorization (hq0 i)).mpr
    rw [Nat.factorization_div (hdiv i), Finsupp.tsub_apply, hLf]
    omega
  have htop : (∑ i ∈ univ.filter (fun i => d i = p ^ a), L / d i) =
      (univ.filter fun i => d i = p ^ a).card * (L / p ^ a) := by
    calc
      (∑ i ∈ univ.filter (fun i => d i = p ^ a), L / d i) =
          ∑ i ∈ univ.filter (fun i => d i = p ^ a), L / p ^ a := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(mem_filter.mp hi).2]
      _ = _ := by simp
  have hpL : p ∣ L := (dvd_pow_self p ha.ne').trans hpa
  have htotal := reciprocal_mass_integral d L hd hdiv hsum
  have ht : p ∣ ∑ i ∈ univ.filter (fun i => d i = p ^ a), L / d i := by
    apply (Nat.dvd_add_iff_left hlo).mpr
    rw [Finset.sum_filter_add_sum_filter_not, htotal]
    exact hpL
  rw [htop] at ht
  exact (hp.dvd_mul.mp ht).resolve_right hC

/-- A largest prime-power index occurs a positive multiple of its prime many times. -/
theorem maximal_prime_power_multiplicity (P : Erdos274.Group.ExactCovering G ι)
    (p a : ℕ) (hp : p.Prime) (ha : 0 < a)
    (hmax : ∀ i, (P.parts i).index ≤ p ^ a)
    (hex : ∃ j, (P.parts j).index = p ^ a) :
    p ∣ (univ.filter fun i => (P.parts i).index = p ^ a).card ∧
    p ≤ (univ.filter fun i => (P.parts i).index = p ^ a).card := by
  classical
  have hd (i : ι) : 0 < (P.parts i).index :=
    Nat.pos_of_ne_zero (finiteIndex_part P i).index_ne_zero
  have hdiv := prime_dvd_maximal_count (fun i => (P.parts i).index)
    p a hp ha hd hmax hex (sum_inv_index P)
  obtain ⟨j, hj⟩ := hex
  have hpos : 0 < (univ.filter fun i => (P.parts i).index = p ^ a).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  exact ⟨hdiv, Nat.le_of_dvd hpos hdiv⟩

/-- The exact target conclusion when the largest index is a prime power. -/
theorem herzog_schonheim_maximal_prime_power (P : Erdos274.Group.ExactCovering G ι)
    (hι : 1 < Fintype.card ι) (p a : ℕ) (hp : p.Prime)
    (hmax : ∀ i, (P.parts i).index ≤ p ^ a)
    (hex : ∃ j, (P.parts j).index = p ^ a) :
    ∃ i j, i ≠ j ∧ (P.parts i).index = (P.parts j).index := by
  classical
  have ha : 0 < a := by
    obtain ⟨j, hj⟩ := hex
    by_contra h
    have hz : a = 0 := by omega
    exact index_ne_one P hι j (by simpa only [hz, pow_zero] using hj)
  have hcount := (maximal_prime_power_multiplicity P p a hp ha hmax hex).2
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show
      1 < (univ.filter fun i => (P.parts i).index = p ^ a).card from
        lt_of_lt_of_le hp.one_lt hcount)
  exact ⟨i, j, hij, (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm⟩

/-- Use site with arbitrary smaller indices and largest index nine. -/
example (P : Erdos274.Group.ExactCovering G ι)
    (hmax : ∀ i, (P.parts i).index ≤ 9)
    (hex : ∃ i, (P.parts i).index = 9) :
    3 ≤ (univ.filter fun i => (P.parts i).index = 9).card := by
  simpa using (maximal_prime_power_multiplicity P 3 2 (by norm_num)
    (by norm_num) (by simpa using hmax) (by simpa using hex)).2

end Contribution.Erdos274Finite
