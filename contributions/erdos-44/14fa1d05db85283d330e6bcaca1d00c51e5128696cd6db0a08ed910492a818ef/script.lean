import Mathlib
import FormalConjectures.ErdosProblems.«44»

/-!
# Erdős Problem 44: the textbook bound `maxSidonSubsetCard (Icc 1 N) ≤ 2√N`

A Sidon set `B ⊆ {1,…,N}` of size `k` has all `k(k−1)/2` pairwise differences distinct
and lying in `{1,…,N−1}`, so `k(k−1) ≤ 2(N−1) + 1`; with `k ≤ N` this yields `k² ≤ 4N`,
i.e. `k ≤ 2√N`. The difference of a 2-element set `{a, b}` is extracted by the total map
`s ↦ 2 * s.sup id − s.sum id` (`= max − min`), avoiding partial `min'`/`max'`.
-/

open Function Set Finset

namespace Contribution.Erdos44Bound

/-- Any Sidon subset of `Icc 1 N` has at most `2√N` elements. -/
lemma card_le {N : ℕ} (hN : 1 ≤ N) {B : Finset ℕ} (hBsub : B ⊆ Finset.Icc 1 N)
    (hB : IsSidon (B : Set ℕ)) : (B.card : ℝ) ≤ 2 * Real.sqrt N := by
  set f : Finset ℕ → ℕ := fun s => 2 * s.sup id - s.sum id with hf
  have hpair : ∀ a b : ℕ, a < b → f {a, b} = b - a := by
    intro a b hab
    have hsup : ({a, b} : Finset ℕ).sup id = b := by
      simp [Finset.sup_insert, Finset.sup_singleton, max_eq_right hab.le]
    have hsum : ({a, b} : Finset ℕ).sum id = a + b := Finset.sum_pair (by omega)
    simp only [hf, hsup, hsum]
    omega
  have hmaps : Set.MapsTo f ↑(B.powersetCard 2) ↑(Finset.Icc 1 (N - 1)) := by
    intro s hs
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨hsub, hcard⟩ := hs
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha := Finset.mem_Icc.mp (hBsub (hsub (by simp : a ∈ ({a, b} : Finset ℕ))))
    have hb := Finset.mem_Icc.mp (hBsub (hsub (by simp : b ∈ ({a, b} : Finset ℕ))))
    rw [Finset.mem_coe, Finset.mem_Icc]
    rcases Nat.lt_or_ge a b with h | h
    · rw [hpair a b h]; omega
    · have h' : b < a := by omega
      rw [Finset.pair_comm, hpair b a h']; omega
  have hinj : Set.InjOn f ↑(B.powersetCard 2) := by
    have key : ∀ a b c d : ℕ, a < b → c < d → a ∈ B → b ∈ B → c ∈ B → d ∈ B →
        f {a, b} = f {c, d} → ({a, b} : Finset ℕ) = {c, d} := by
      intro a b c d hab hcd ha hb hc hd hst
      rw [hpair a b hab, hpair c d hcd] at hst
      have hsum : b + c = d + a := by omega
      rcases hB b hb d hd c hc a ha hsum with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2; rfl
      · omega
    intro s hs t ht hst
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs ht
    obtain ⟨hssub, hscard⟩ := hs
    obtain ⟨htsub, htcard⟩ := ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hscard
    obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp htcard
    have ha : a ∈ B := hssub (by simp : a ∈ ({a, b} : Finset ℕ))
    have hb : b ∈ B := hssub (by simp : b ∈ ({a, b} : Finset ℕ))
    have hc : c ∈ B := htsub (by simp : c ∈ ({c, d} : Finset ℕ))
    have hd : d ∈ B := htsub (by simp : d ∈ ({c, d} : Finset ℕ))
    rcases Nat.lt_or_ge a b with h1 | h1
    · rcases Nat.lt_or_ge c d with h2 | h2
      · exact key a b c d h1 h2 ha hb hc hd hst
      · have h2' : d < c := by omega
        rw [Finset.pair_comm c d]
        exact key a b d c h1 h2' ha hb hd hc (by rwa [Finset.pair_comm c d] at hst)
    · have h1' : b < a := by omega
      rcases Nat.lt_or_ge c d with h2 | h2
      · rw [Finset.pair_comm a b]
        exact key b a c d h1' h2 hb ha hc hd (by rwa [Finset.pair_comm a b] at hst)
      · have h2' : d < c := by omega
        rw [Finset.pair_comm a b, Finset.pair_comm c d]
        exact key b a d c h1' h2' hb ha hd hc
          (by rwa [Finset.pair_comm a b, Finset.pair_comm c d] at hst)
  have hcount : (B.powersetCard 2).card ≤ (Finset.Icc 1 (N - 1)).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_powersetCard, Nat.choose_two_right, Nat.card_Icc] at hcount
  have hkN : B.card ≤ N := by
    calc B.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hBsub
    _ = N := by rw [Nat.card_Icc]; omega
  have hquad : B.card * (B.card - 1) ≤ 2 * (N - 1) + 1 := by omega
  have hsq : (B.card : ℝ) ^ 2 ≤ 4 * N := by
    rcases Nat.eq_zero_or_pos B.card with h0 | hpos
    · rw [h0]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) N]
    · have hcast : (B.card : ℝ) * ((B.card : ℝ) - 1) ≤ 2 * ((N : ℝ) - 1) + 1 := by
        have h := Nat.cast_le (α := ℝ).mpr hquad
        push_cast [Nat.cast_sub hpos, Nat.cast_sub hN] at h
        linarith [h]
      have hkNR : (B.card : ℝ) ≤ N := by exact_mod_cast hkN
      nlinarith [hcast, hkNR]
  have h4N : (2 : ℝ) * Real.sqrt N = Real.sqrt (4 * N) := by
    rw [show (4 : ℝ) * N = 2 ^ 2 * N by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2) (N : ℝ),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h4N]
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr hsq

/-- The textbook bound: the maximum Sidon subset of `{1,…,N}` has at most `2√N` elements. -/
theorem maxSidonSubsetCard_icc_bound (N : ℕ) (hN : 1 ≤ N) :
    maxSidonSubsetCard (Finset.Icc 1 N) ≤ 2 * Real.sqrt N := by
  have hne : ((Finset.Icc 1 N).powerset.filter
      fun B : Finset ℕ ↦ IsSidon (B : Set ℕ)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp [IsSidon]⟩⟩
  obtain ⟨B, hBmem, hBeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  obtain ⟨hBpow, hBsidon⟩ := Finset.mem_filter.mp hBmem
  rw [maxSidonSubsetCard, hBeq]
  exact card_le hN (Finset.mem_powerset.mp hBpow) hBsidon

end Contribution.Erdos44Bound

