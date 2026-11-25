import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 1056: Verified Finite Witnesses `k = 2..8`

Self-contained Lean 4 formalization verifying explicit primes `p` and strictly monotone
boundary sequences `boundaries : Fin (k + 1) → ℕ` satisfying `AllModProdEqualsOne p boundaries`
for `k = 2, 3, 4, 5, 6, 7, 8`, together with a binary-splitting modular product helper
`prodModBin` so interval products up to length `1024` reduce with recursion depth `≤ 10`
and without multi-hundred-digit integer arithmetic in the kernel.
-/

namespace Contribution.Erdos1056

/--
The proposition that the modular product of a collection of consecutive intervals equals `1`
modulo `p`, where intervals are defined by a function specifying the consecutive boundaries.
Matches `Erdos1056.AllModProdEqualsOne` definitionally.
-/
def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

private def prodModBin (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, len => if len = 0 then 1 % p else a % p
  | fuel + 1, a, len =>
    if len ≤ 1 then
      if len = 0 then 1 % p else a % p
    else
      let half := len / 2
      (prodModBin p fuel a half * prodModBin p fuel (a + half) (len - half)) % p

private lemma prod_Ico_mod_eq_bin (p : ℕ) :
    ∀ fuel a len : ℕ, len ≤ 2 ^ fuel →
      (∏ n ∈ Finset.Ico a (a + len), n) % p = prodModBin p fuel a len
  | 0, a, len, hlen => by
    simp only [pow_zero] at hlen
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hlen with rfl | rfl
    · simp [prodModBin]
    · simp [prodModBin]
  | fuel + 1, a, len, hlen => by
    unfold prodModBin
    split_ifs with h1 h0
    · subst h0; simp
    · have hlen1 : len = 1 := by omega
      subst hlen1; simp
    · have hp2 : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      have hhalf1 : len / 2 ≤ 2 ^ fuel := by omega
      have hhalf2 : len - len / 2 ≤ 2 ^ fuel := by omega
      have hsplit : (∏ n ∈ Finset.Ico a (a + len), n) =
          (∏ n ∈ Finset.Ico a (a + len / 2), n) *
            (∏ n ∈ Finset.Ico (a + len / 2) ((a + len / 2) + (len - len / 2)), n) := by
        rw [show (a + len / 2) + (len - len / 2) = a + len by omega]
        exact (Finset.prod_Ico_consecutive id (Nat.le_add_right a _) (by omega)).symm
      rw [hsplit, Nat.mul_mod,
        prod_Ico_mod_eq_bin p fuel a (len / 2) hhalf1,
        prod_Ico_mod_eq_bin p fuel (a + len / 2) (len - len / 2) hhalf2]

private lemma prod_Ico_mod_eq_one {p a b : ℕ} (hab : a ≤ b) (hle : b - a ≤ 1024)
    (h : prodModBin p 10 a (b - a) = 1 % p) :
    (∏ n ∈ Finset.Ico a b, n) ≡ 1 [MOD p] := by
  change (∏ n ∈ Finset.Ico a b, n) % p = 1 % p
  rw [← Nat.add_sub_cancel' hab]
  exact (prod_Ico_mod_eq_bin p 10 a (b - a) (by simpa using hle)).trans h

private lemma allModProdEqualsOne_of_check {p k : ℕ} (boundaries : Fin (k + 1) → ℕ)
    (hle : ∀ i : Fin k, boundaries i.castSucc ≤ boundaries (i.castSucc + 1))
    (hbound : ∀ i : Fin k, boundaries (i.castSucc + 1) - boundaries i.castSucc ≤ 1024)
    (hmod : ∀ i : Fin k,
      prodModBin p 10 (boundaries i.castSucc)
        (boundaries (i.castSucc + 1) - boundaries i.castSucc) = 1 % p) :
    AllModProdEqualsOne p boundaries := fun i =>
  prod_Ico_mod_eq_one (hle i) (hbound i) (hmod i)

/-- Erdős (1979) `k = 2` witness modulo `11`: `3*4 ≡ 5*6*7 ≡ 1 [MOD 11]`.
Matches `Erdos1056.erdos_1056.variants.k2` definitionally. -/
theorem erdos_1056_k2 : AllModProdEqualsOne 11 ![3, 5, 8] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/-- Makowski (1983) `k = 3` witness modulo `17`.
Matches `Erdos1056.erdos_1056.variants.k3` definitionally. -/
theorem erdos_1056_k3 : AllModProdEqualsOne 17 ![2, 6, 12, 16] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/-- Verified `k = 4` witness modulo `17`: `[1, 2), [2, 6), [6, 12), [12, 16)`. -/
theorem erdos_1056_k4 : AllModProdEqualsOne 17 ![1, 2, 6, 12, 16] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/-- Verified `k = 5` witness modulo `23`: `[1, 2), [2, 5), [5, 9), [9, 12), [12, 22)`. -/
theorem erdos_1056_k5 : AllModProdEqualsOne 23 ![1, 2, 5, 9, 12, 22] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/-- Verified `k = 6` witness modulo `71`: `[8, 10), [10, 20), [20, 52), [52, 62), [62, 64), [64, 71)`. -/
theorem erdos_1056_k6 : AllModProdEqualsOne 71 ![8, 10, 20, 52, 62, 64, 71] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/-- Verified `k = 7` witness modulo `619`:
`[1, 2), [2, 112), [112, 190), [190, 295), [295, 430), [430, 508), [508, 618)`. -/
theorem erdos_1056_k7 : AllModProdEqualsOne 619 ![1, 2, 112, 190, 295, 430, 508, 618] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/-- Verified `k = 8` witness modulo `599`:
`[29, 51), [51, 123), [123, 184), [184, 251), [251, 290), [290, 501), [501, 540), [540, 556)`. -/
theorem erdos_1056_k8 :
    AllModProdEqualsOne 599 ![29, 51, 123, 184, 251, 290, 501, 540, 556] :=
  allModProdEqualsOne_of_check _ (by decide) (by decide) (by decide)

/--
Existence of a prime `p` and strictly monotone boundary sequence `boundaries : Fin (k + 1) → ℕ`
satisfying `AllModProdEqualsOne p boundaries` for all `2 ≤ k ≤ 8`.
-/
theorem erdos_1056_le_eight :
    ∀ k, 2 ≤ k → k ≤ 8 →
      ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
        AllModProdEqualsOne p boundaries := by
  intro k hk2 hk8
  interval_cases k
  · exact ⟨11, by norm_num, ![3, 5, 8], Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k2⟩
  · exact ⟨17, by norm_num, ![2, 6, 12, 16], Fin.strictMono_iff_lt_succ.mpr (by decide),
      erdos_1056_k3⟩
  · exact ⟨17, by norm_num, ![1, 2, 6, 12, 16], Fin.strictMono_iff_lt_succ.mpr (by decide),
      erdos_1056_k4⟩
  · exact ⟨23, by norm_num, ![1, 2, 5, 9, 12, 22], Fin.strictMono_iff_lt_succ.mpr (by decide),
      erdos_1056_k5⟩
  · exact ⟨71, by norm_num, ![8, 10, 20, 52, 62, 64, 71],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k6⟩
  · exact ⟨619, by norm_num, ![1, 2, 112, 190, 295, 430, 508, 618],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k7⟩
  · exact ⟨599, by norm_num, ![29, 51, 123, 184, 251, 290, 501, 540, 556],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k8⟩

end Contribution.Erdos1056
