import FormalConjectures.GreensOpenProblems.«40»

-- ==== from Harvest4_sanity_f_one.lean ====
/-!
Proof that `f 1 = 1` (Green's Open Problem 40, `green_40.sanity_f_one`).

Lower bound: any covering subspace `V` satisfies `|V| * |H(r)| ≥ 2 ^ n` by a
counting argument, so `minDensity n r ≥ 1` for every `n`, hence `f 1 ≥ 1`.

Upper bound: for `n = 2 ^ m - 1` the Hamming code (the kernel of the syndrome
map sending `x` to `∑ i, x i • c i`, where the `c i` enumerate the nonzero
vectors of `𝔽₂^m`) is a perfect 1-covering with `|V| * 2 ^ m = 2 ^ n` and
`|H(1)| ≤ n + 1 = 2 ^ m`, so `minDensity n 1 ≤ 1` along this subsequence,
hence `f 1 ≤ 1`.
-/

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Contribution.SanityFOne

open Green40

/-- The cardinality of `𝔽₂ n` is `2 ^ n`. -/
lemma card_F2 (n : ℕ) : Nat.card (𝔽₂ n) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]
  simp [ZMod.card]

/-- In `𝔽₂ n` every vector is its own negative. -/
lemma add_self (N : ℕ) (v : 𝔽 2 N) : v + v = 0 := by
  funext j
  show v j + v j = 0
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h _

/-- A standard basis vector has Hamming norm at most 1. -/
lemma hammingNorm_single_le {N : ℕ} (i : Fin N) (c : ZMod 2) :
    hammingNorm (Pi.single i c : 𝔽₂ N) ≤ 1 := by
  refine Finset.card_le_one.mpr fun j hj k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
  have hji : j = i := by
    by_contra hcon
    rw [Pi.single_eq_of_ne hcon] at hj
    exact hj rfl
  have hki : k = i := by
    by_contra hcon
    rw [Pi.single_eq_of_ne hcon] at hk
    exact hk rfl
  rw [hji, hki]

/-- The Hamming ball of radius 1 has at most `n + 1` elements. -/
lemma card_ball_one_le (n : ℕ) : Nat.card (hammingBall n 1) ≤ n + 1 := by
  classical
  have hsub : hammingBall n 1 ⊆
      insert (0 : 𝔽₂ n) (Set.range fun i : Fin n => (Pi.single i 1 : 𝔽₂ n)) := by
    intro x hx
    have hx' : hammingNorm x ≤ 1 := hx
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx' with h0 | h1
    · exact Set.mem_insert_iff.mpr (Or.inl (hammingNorm_eq_zero.mp h0))
    · refine Set.mem_insert_iff.mpr (Or.inr ?_)
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
      refine ⟨i, ?_⟩
      show Pi.single i (1 : ZMod 2) = x
      funext j
      by_cases hji : j = i
      · subst hji
        have hxj : x j ≠ 0 := by
          have hmem : j ∈ ({j} : Finset (Fin n)) := Finset.mem_singleton_self j
          rw [← hi, Finset.mem_filter] at hmem
          exact hmem.2
        have h2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
        rw [Pi.single_eq_same]
        exact (h2 _ hxj).symm
      · rw [Pi.single_eq_of_ne hji]
        have hj : j ∉ ({i} : Finset (Fin n)) := by simpa using hji
        rw [← hi, Finset.mem_filter] at hj
        push_neg at hj
        exact (hj (Finset.mem_univ j)).symm
  have hinj : Function.Injective (fun i : Fin n => (Pi.single i 1 : 𝔽₂ n)) := by
    intro a b hab
    have hab' : (Pi.single a 1 : 𝔽₂ n) = Pi.single b 1 := hab
    by_contra hne
    have h := congrFun hab' a
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h
    exact one_ne_zero h
  calc Nat.card (hammingBall n 1)
      ≤ Nat.card ↥(insert (0 : 𝔽₂ n) (Set.range fun i : Fin n => (Pi.single i 1 : 𝔽₂ n))) :=
        Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card ↥(Set.range fun i : Fin n => (Pi.single i 1 : 𝔽₂ n)) + 1 := by
        rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
        exact Set.ncard_insert_le _ _
    _ = n + 1 := by
        rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Every `minDensity` is at least 1: a covering needs `|V| * |H(r)| ≥ 2 ^ n`. -/
lemma one_le_minDensity (n r : ℕ) : 1 ≤ minDensity n r := by
  refine le_iInf₂ fun V hV => ?_
  have hV' : (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ := hV
  have hcard : (2 : ℕ) ^ n ≤ Nat.card V * Nat.card (hammingBall n r) := by
    calc (2 : ℕ) ^ n = Nat.card (𝔽₂ n) := (card_F2 n).symm
      _ = Nat.card (Set.univ : Set (𝔽₂ n)) := Nat.card_univ.symm
      _ = Nat.card ((V : Set (𝔽₂ n)) + hammingBall n r) := by rw [hV']
      _ ≤ Nat.card (V : Set (𝔽₂ n)) * Nat.card (hammingBall n r) := Set.natCard_add_le
      _ = Nat.card V * Nat.card (hammingBall n r) := rfl
  rw [ENNReal.le_div_iff_mul_le
      (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    one_mul]
  exact_mod_cast hcard

section HammingCode

/-- The number of nonzero vectors in `𝔽₂ m` is `2 ^ m - 1`. -/
lemma card_nonzero (m : ℕ) : Fintype.card {s : 𝔽 2 m // s ≠ 0} = 2 ^ m - 1 := by
  classical
  have h := Fintype.card_subtype_compl (fun s : 𝔽 2 m => s = 0)
  simp only [Fintype.card_subtype_eq] at h
  calc Fintype.card {s : 𝔽 2 m // s ≠ 0} = Fintype.card (𝔽 2 m) - 1 := h
    _ = 2 ^ m - 1 := by
        rw [← Nat.card_eq_fintype_card, card_F2]

/-- An enumeration of the nonzero vectors of `𝔽₂ m` by `Fin (2 ^ m - 1)`. -/
noncomputable def e (m : ℕ) : Fin (2 ^ m - 1) ≃ {s : 𝔽 2 m // s ≠ 0} :=
  (Fintype.equivFinOfCardEq (card_nonzero m)).symm

/-- The syndrome map of the Hamming code: parity checks indexed by the
nonzero vectors of `𝔽₂ m`. -/
noncomputable def φ (m : ℕ) : 𝔽₂ (2 ^ m - 1) →ₗ[ZMod 2] 𝔽 2 m where
  toFun x := ∑ i : Fin (2 ^ m - 1), x i • ((e m i : 𝔽 2 m))
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

lemma φ_single (m : ℕ) (i : Fin (2 ^ m - 1)) (c : ZMod 2) :
    φ m (Pi.single i c) = c • (e m i : 𝔽 2 m) := by
  have h : φ m (Pi.single i c) =
      ∑ j : Fin (2 ^ m - 1), (Pi.single i c : 𝔽₂ (2 ^ m - 1)) j • (e m j : 𝔽 2 m) := rfl
  rw [h, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, zero_smul]
  · intro hmem
    exact absurd (Finset.mem_univ i) hmem

lemma φ_surj (m : ℕ) : Function.Surjective (φ m) := by
  intro s
  by_cases hs : s = 0
  · exact ⟨0, by rw [map_zero, hs]⟩
  · refine ⟨Pi.single ((e m).symm ⟨s, hs⟩) 1, ?_⟩
    rw [φ_single, one_smul, Equiv.apply_symm_apply]

/-- The Hamming code is a 1-covering subspace. -/
lemma covering (m : ℕ) : IsCoveringSubspace (2 ^ m - 1) 1 (LinearMap.ker (φ m)) := by
  show (LinearMap.ker (φ m) : Set (𝔽₂ (2 ^ m - 1))) + hammingBall (2 ^ m - 1) 1 = Set.univ
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_add]
  by_cases hx : φ m x = 0
  · refine ⟨x, ?_, 0, ?_, add_zero x⟩
    · exact LinearMap.mem_ker.mpr hx
    · show hammingNorm (0 : 𝔽₂ (2 ^ m - 1)) ≤ 1
      rw [hammingNorm_zero]
      exact Nat.zero_le 1
  · refine ⟨x + Pi.single ((e m).symm ⟨φ m x, hx⟩) 1,
      ?_, Pi.single ((e m).symm ⟨φ m x, hx⟩) 1, ?_, ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_add, φ_single, one_smul,
        Equiv.apply_symm_apply]
      exact add_self m (φ m x)
    · exact hammingNorm_single_le _ _
    · rw [add_assoc, add_self, add_zero]

/-- The Hamming code has index `2 ^ m` in `𝔽₂ (2 ^ m - 1)`. -/
lemma card_ker_mul (m : ℕ) :
    Nat.card (LinearMap.ker (φ m)) * 2 ^ m = 2 ^ (2 ^ m - 1) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (φ m))
  have h2 : Nat.card (𝔽₂ (2 ^ m - 1) ⧸ LinearMap.ker (φ m)) = 2 ^ m := by
    have e1 : (𝔽₂ (2 ^ m - 1) ⧸ LinearMap.ker (φ m)) ≃ₗ[ZMod 2] LinearMap.range (φ m) :=
      (φ m).quotKerEquivRange
    have hr : LinearMap.range (φ m) = ⊤ := LinearMap.range_eq_top.mpr (φ_surj m)
    rw [Nat.card_congr e1.toEquiv, hr,
      Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := 𝔽 2 m)).toEquiv]
    exact card_F2 m
  rw [h2] at h1
  rw [card_F2] at h1
  omega

/-- Along the subsequence `n = 2 ^ m - 1`, the covering density is at most 1. -/
lemma minDensity_le_one (m : ℕ) : minDensity (2 ^ m - 1) 1 ≤ 1 := by
  refine le_trans (iInf₂_le (LinearMap.ker (φ m)) (covering m)) ?_
  have hpos : (0 : ℕ) < 2 ^ m := Nat.two_pow_pos m
  have hn1 : (2 ^ m - 1) + 1 = 2 ^ m := by omega
  have key : Nat.card (LinearMap.ker (φ m)) * Nat.card (hammingBall (2 ^ m - 1) 1)
      ≤ 2 ^ (2 ^ m - 1) := by
    calc Nat.card (LinearMap.ker (φ m)) * Nat.card (hammingBall (2 ^ m - 1) 1)
        ≤ Nat.card (LinearMap.ker (φ m)) * 2 ^ m := by
          refine Nat.mul_le_mul le_rfl ?_
          rw [← hn1]
          exact card_ball_one_le _
      _ = 2 ^ (2 ^ m - 1) := card_ker_mul m
  apply ENNReal.div_le_of_le_mul
  rw [one_mul]
  exact_mod_cast key

end HammingCode

theorem sanity_f_one : f 1 = 1 := by
  have hle : f 1 ≤ 1 := by
    have hfreq : ∃ᶠ n in atTop, minDensity n 1 ≤ 1 := by
      rw [Filter.frequently_atTop]
      intro N
      refine ⟨2 ^ (N + 1) - 1, ?_, minDensity_le_one (N + 1)⟩
      have h : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
      omega
    exact Filter.liminf_le_of_frequently_le' hfreq
  have hge : (1 : ℝ≥0∞) ≤ f 1 :=
    Filter.le_liminf_of_le (h := Filter.Eventually.of_forall fun n => one_le_minDensity n 1)
  exact le_antisymm hle hge

end Contribution.SanityFOne

-- ==== from Harvest4_ftilde_le_f.lean ====
/-
Proof that `f_tilde r ≤ f r` (Green's Open Problem 40, `green_40.f_tilde_le_f`).

Every covering subspace is in particular a covering subset of the same cardinality,
so the infimum defining `minDensityFinset` is over a larger family and is pointwise
bounded by `minDensity`; the liminf inequality follows.
-/

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Contribution.FTildeLeF

open Green40

theorem f_tilde_le_f (r : ℕ) : f_tilde r ≤ f r := by
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  refine le_iInf₂ fun V hV => ?_
  classical
  have hball : (hammingBallFinset n r : Set (𝔽₂ n)) = hammingBall n r := by
    ext x
    simp [hammingBallFinset, hammingBall]
  have hV' : (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ := hV
  have hcov : IsCoveringFinset n r (V : Set (𝔽₂ n)).toFinset := by
    unfold IsCoveringFinset
    apply Finset.coe_injective
    rw [Finset.coe_add, Set.coe_toFinset, hball, hV', Finset.coe_univ]
  have hcard : ((V : Set (𝔽₂ n)).toFinset.card : ℕ) = Nat.card V := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  calc minDensityFinset n r
      ≤ ((V : Set (𝔽₂ n)).toFinset.card : ℝ≥0∞) *
          (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := iInf₂_le _ hcov
    _ = (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := by
        rw [hcard]

end Contribution.FTildeLeF
