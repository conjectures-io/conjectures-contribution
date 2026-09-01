import Mathlib
import FormalConjectures.ErdosProblems.«859»

/-!
# Erdős Problem 859, textbook variant `positive_density`

For every natural number `t`, the set `DivisorSumSet t` of numbers `n` such that `t` is a
sum of distinct divisors of `n` has positive natural density.

Proof sketch: for `t = 0` the set is all of `ℕ` (density `1`).  For `t ≥ 1`, every part of a
witnessing sum is a divisor of `n` that is at most `t`, hence divides `L := t!`.  Therefore for
`n ≥ 1` membership depends only on `n % L`, so the set is (away from `0`) a finite union of
residue classes mod `L`; such a union of `k` classes has density `k / L`.  The class of `0`
is always good because every positive multiple of `L` is divisible by `t`, so `k ≥ 1`.
-/

namespace Contribution.Erdos859PositiveDensity

open Erdos859 Filter Topology

/-- Counting upper bound: at most `R.card * (N / L + 1)` numbers `n < N` have `n % L ∈ R`. -/
lemma count_upper (L : ℕ) (R : Finset ℕ) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % L ∈ R)).card ≤ R.card * (N / L + 1) := by
  have h : ((Finset.range N).filter (fun n => n % L ∈ R)).card
      ≤ (R ×ˢ Finset.range (N / L + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun n => (n % L, n / L))
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      exact ⟨hn.2, Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)⟩
    · intro a _ b _ hab
      have h1 : a % L = b % L := congrArg Prod.fst hab
      have h2 : a / L = b / L := congrArg Prod.snd hab
      calc a = L * (a / L) + a % L := (Nat.div_add_mod a L).symm
        _ = L * (b / L) + b % L := by rw [h1, h2]
        _ = b := Nat.div_add_mod b L
  simpa [Finset.card_product, Finset.card_range] using h

/-- Counting lower bound: at least `R.card * (N / L)` numbers `n < N` have `n % L ∈ R`. -/
lemma count_lower {L : ℕ} (hL : 0 < L) {R : Finset ℕ} (hR : R ⊆ Finset.range L) (N : ℕ) :
    R.card * (N / L) ≤ ((Finset.range N).filter (fun n => n % L ∈ R)).card := by
  have h : (R ×ˢ Finset.range (N / L)).card
      ≤ ((Finset.range N).filter (fun n => n % L ∈ R)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => L * p.2 + p.1)
    · rintro ⟨r, m⟩ hp
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨hr, hm⟩ := hp
      have hrL : r < L := Finset.mem_range.mp (hR hr)
      have hmN : L * m + L ≤ N := by
        have h1 : L * (m + 1) ≤ L * (N / L) := Nat.mul_le_mul le_rfl hm
        rw [Nat.mul_succ] at h1
        calc L * m + L ≤ L * (N / L) := h1
          _ = N / L * L := Nat.mul_comm _ _
          _ ≤ N := Nat.div_mul_le_self N L
      have hlt : L * m + r < N := lt_of_lt_of_le (Nat.add_lt_add_left hrL _) hmN
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt, ?_⟩
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrL]
      exact hr
    · rintro ⟨r, m⟩ hp ⟨r', m'⟩ hp' hEq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hp hp'
      have hrL : r < L := Finset.mem_range.mp (hR hp.1)
      have hrL' : r' < L := Finset.mem_range.mp (hR hp'.1)
      have hEq' : L * m + r = L * m' + r' := hEq
      have hr : r = r' := by
        have h1 : (L * m + r) % L = (L * m' + r') % L := by rw [hEq']
        rwa [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hrL,
          Nat.mod_eq_of_lt hrL'] at h1
      subst hr
      have hm : m = m' := Nat.eq_of_mul_eq_mul_left hL (Nat.add_right_cancel hEq')
      rw [hm]
  simpa [Finset.card_product, Finset.card_range] using h

/-- A union of `R.card` residue classes mod `L` has natural density `R.card / L`. -/
lemma hasDensity_mod_mem {L : ℕ} (hL : 0 < L) {R : Finset ℕ} (hR : R ⊆ Finset.range L) :
    Set.HasDensity {n : ℕ | n % L ∈ R} ((R.card : ℝ) / (L : ℝ)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Set.HasDensity]
  have hpd : ∀ N : ℕ, Set.partialDensity {n : ℕ | n % L ∈ R} Set.univ N
      = (((Finset.range N).filter (fun n => n % L ∈ R)).card : ℝ) / N := by
    intro N
    have h1 : ({n : ℕ | n % L ∈ R} ∩ Set.univ) ∩ Set.Iio N
        = (((Finset.range N).filter (fun n => n % L ∈ R) : Finset ℕ) : Set ℕ) := by
      ext n
      constructor
      · rintro ⟨⟨hmem, -⟩, hlt⟩
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Set.mem_Iio.mp hlt), hmem⟩)
      · intro hn
        have hn' := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
        exact ⟨⟨hn'.2, Set.mem_univ n⟩, Set.mem_Iio.mpr (Finset.mem_range.mp hn'.1)⟩
    have h2 : (Set.univ ∩ Set.Iio N : Set ℕ).ncard = N := by
      rw [Set.univ_inter, Nat.ncard_Iio]
    rw [Set.partialDensity, h1, h2, Set.ncard_coe_finset]
  rw [tendsto_congr hpd]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun N : ℕ => (R.card : ℝ) / L - (R.card : ℝ) / N)
    (h := fun N : ℕ => (R.card : ℝ) / L + (R.card : ℝ) / N) ?_ ?_ ?_ ?_
  · simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (R.card : ℝ))
  · simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (R.card : ℝ))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc1 : (R.card : ℝ) * ((N / L : ℕ) : ℝ)
        ≤ (((Finset.range N).filter (fun n => n % L ∈ R)).card : ℝ) := by
      exact_mod_cast count_lower hL hR N
    have hkey : (N : ℝ) < L * ((N / L : ℕ) : ℝ) + L := by
      have h3 : N < L * (N / L) + L := by
        conv_lhs => rw [← Nat.div_add_mod N L]
        exact Nat.add_lt_add_left (Nat.mod_lt N hL) _
      exact_mod_cast h3
    have hfloor : (N : ℝ) / L - 1 ≤ ((N / L : ℕ) : ℝ) := by
      have h4 : (N : ℝ) / L < ((N / L : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hL0]
        calc (N : ℝ) < L * ((N / L : ℕ) : ℝ) + L := hkey
          _ = (((N / L : ℕ) : ℝ) + 1) * L := by ring
      linarith
    have hstep : (R.card : ℝ) * ((N : ℝ) / L - 1)
        ≤ (((Finset.range N).filter (fun n => n % L ∈ R)).card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)) hc1
    have heq : (R.card : ℝ) / L - (R.card : ℝ) / N = (R.card : ℝ) * ((N : ℝ) / L - 1) / N := by
      field_simp
    rw [heq]
    gcongr
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc2 : (((Finset.range N).filter (fun n => n % L ∈ R)).card : ℝ)
        ≤ (R.card : ℝ) * (((N / L : ℕ) : ℝ) + 1) := by
      have h5 : ((R.card * (N / L + 1) : ℕ) : ℝ) = (R.card : ℝ) * (((N / L : ℕ) : ℝ) + 1) := by
        push_cast
        ring
      rw [← h5]
      exact_mod_cast count_upper L R N
    have hcast : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / L := Nat.cast_div_le
    have hstep2 : (((Finset.range N).filter (fun n => n % L ∈ R)).card : ℝ)
        ≤ (R.card : ℝ) * ((N : ℝ) / L + 1) :=
      le_trans hc2 (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
    have heq2 : (R.card : ℝ) / L + (R.card : ℝ) / N
        = (R.card : ℝ) * ((N : ℝ) / L + 1) / N := by
      field_simp
    rw [heq2]
    gcongr

/-- Removing a single point does not change the natural density. -/
lemma hasDensity_diff_singleton {S : Set ℕ} {α : ℝ} (hd : S.HasDensity α) (a : ℕ) :
    (S \ {a}).HasDensity α := by
  rw [Set.HasDensity] at hd ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun N : ℕ => Set.partialDensity S Set.univ N - 1 / N)
    (h := fun N : ℕ => Set.partialDensity S Set.univ N) ?_ ?_ ?_ ?_
  · simpa using hd.sub tendsto_one_div_atTop_nhds_zero_nat
  · exact hd
  · refine Eventually.of_forall fun N => ?_
    have hfin : ((S \ {a}) ∩ Set.Iio N).Finite :=
      (Set.finite_Iio N).subset Set.inter_subset_right
    have hsub : (S ∩ Set.Iio N) ⊆ ((S \ {a}) ∩ Set.Iio N) ∪ {a} := by
      intro x hx
      by_cases hxa : x = a
      · exact Or.inr (by simp [hxa])
      · exact Or.inl ⟨⟨hx.1, by simp [hxa]⟩, hx.2⟩
    have hcard : (S ∩ Set.Iio N).ncard ≤ ((S \ {a}) ∩ Set.Iio N).ncard + 1 := by
      calc (S ∩ Set.Iio N).ncard
          ≤ (((S \ {a}) ∩ Set.Iio N) ∪ {a}).ncard :=
            Set.ncard_le_ncard hsub (hfin.union (Set.finite_singleton a))
        _ ≤ ((S \ {a}) ∩ Set.Iio N).ncard + ({a} : Set ℕ).ncard := Set.ncard_union_le _ _
        _ = ((S \ {a}) ∩ Set.Iio N).ncard + 1 := by rw [Set.ncard_singleton]
    have hcast : ((S ∩ Set.Iio N).ncard : ℝ) ≤ (((S \ {a}) ∩ Set.Iio N).ncard : ℝ) + 1 := by
      exact_mod_cast hcard
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    rw [div_sub_div_same]
    gcongr
    linarith
  · refine Eventually.of_forall fun N => ?_
    have hfin : (S ∩ Set.Iio N).Finite :=
      (Set.finite_Iio N).subset Set.inter_subset_right
    have hsub : ((S \ {a}) ∩ Set.Iio N) ⊆ (S ∩ Set.Iio N) :=
      Set.inter_subset_inter Set.diff_subset Set.Subset.rfl
    have hcard : ((S \ {a}) ∩ Set.Iio N).ncard ≤ (S ∩ Set.Iio N).ncard :=
      Set.ncard_le_ncard hsub hfin
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    gcongr

/-- For positive `t`, `0` is not in `DivisorSumSet t`. -/
lemma zero_not_mem {t : ℕ} (ht : 0 < t) : 0 ∉ DivisorSumSet t := by
  intro h
  simp only [DivisorSumSet, Set.mem_setOf_eq] at h
  obtain ⟨s, hs, hsum⟩ := h
  rw [Nat.divisors_zero, Finset.subset_empty] at hs
  subst hs
  simp only [Finset.sum_empty] at hsum
  omega

/-- Membership in `DivisorSumSet t` only depends on the residue class mod `t!`
(among nonzero numbers). -/
lemma mem_of_mod_eq {t : ℕ} (ht : 0 < t) {m n : ℕ} (hn : n ≠ 0)
    (hmod : m % t.factorial = n % t.factorial) (hm : m ∈ DivisorSumSet t) :
    n ∈ DivisorSumSet t := by
  simp only [DivisorSumSet, Set.mem_setOf_eq] at hm ⊢
  obtain ⟨s, hs, hsum⟩ := hm
  refine ⟨s, fun i hi => ?_, hsum⟩
  have hidiv := hs hi
  have hipos : 0 < i := Nat.pos_of_mem_divisors hidiv
  have hile : i ≤ t := by
    have h1 : i ≤ ∑ j ∈ s, j :=
      Finset.single_le_sum (f := fun j => j) (fun j _ => Nat.zero_le j) hi
    omega
  obtain ⟨hidvd, hm0⟩ := Nat.mem_divisors.mp hidiv
  have hiL : i ∣ t.factorial := Nat.dvd_factorial hipos hile
  have h2 : n % i = 0 := by
    have e1 : n % t.factorial % i = n % i := Nat.mod_mod_of_dvd n hiL
    have e2 : m % t.factorial % i = m % i := Nat.mod_mod_of_dvd m hiL
    have e3 : m % i = 0 := Nat.mod_eq_zero_of_dvd hidvd
    rw [← e1, ← hmod, e2, e3]
  exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mod_eq_zero h2, hn⟩

/-- Erdős Problem 859, textbook variant: for every natural number `t` the set
`DivisorSumSet t` has positive natural density. -/
theorem positive_density (t : ℕ) : (DivisorSumSet t).HasPosDensity := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine ⟨1, one_pos, ?_⟩
    rw [erdos_859.variants.trivial_case]
    exact Set.HasDensity.univ
  · set L := t.factorial with hLdef
    have hL : 0 < L := by rw [hLdef]; exact t.factorial_pos
    set R : Finset ℕ := (Finset.range L).filter (fun r => (r + L) ∈ DivisorSumSet t) with hRdef
    have hRsub : R ⊆ Finset.range L := Finset.filter_subset _ _
    have hSeq : DivisorSumSet t = {n : ℕ | n % L ∈ R} \ {0} := by
      ext n
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hn
        have hn0 : n ≠ 0 := by
          intro h
          exact zero_not_mem ht (h ▸ hn)
        refine ⟨?_, hn0⟩
        rw [hRdef, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.mod_lt n hL, ?_⟩
        refine mem_of_mod_eq ht (Nat.add_pos_right _ hL).ne' ?_ hn
        rw [← hLdef, Nat.add_mod_right]
        exact (Nat.mod_mod_of_dvd n dvd_rfl).symm
      · rintro ⟨hr, hn0⟩
        rw [hRdef, Finset.mem_filter, Finset.mem_range] at hr
        refine mem_of_mod_eq ht hn0 ?_ hr.2
        rw [← hLdef, Nat.add_mod_right]
        exact Nat.mod_mod_of_dvd n dvd_rfl
    have hR0 : (0 : ℕ) ∈ R := by
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      refine ⟨hL, ?_⟩
      rw [zero_add]
      show ∃ s ⊆ Nat.divisors L, t = ∑ i ∈ s, i
      refine ⟨{t}, ?_, by simp⟩
      rw [Finset.singleton_subset_iff, Nat.mem_divisors]
      refine ⟨?_, hL.ne'⟩
      rw [hLdef]
      exact Nat.dvd_factorial ht le_rfl
    have hcard : 0 < R.card := Finset.card_pos.mpr ⟨0, hR0⟩
    refine ⟨(R.card : ℝ) / L, ?_, ?_⟩
    · exact div_pos (by exact_mod_cast hcard) (by exact_mod_cast hL)
    · rw [hSeq]
      exact hasDensity_diff_singleton (hasDensity_mod_mem hL hRsub) 0

end Contribution.Erdos859PositiveDensity
