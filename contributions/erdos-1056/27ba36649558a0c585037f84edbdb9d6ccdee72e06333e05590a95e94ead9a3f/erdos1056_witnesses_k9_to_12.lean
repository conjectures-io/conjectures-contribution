import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# Erdős Problem 1056: Verified Finite Witnesses `k = 9..12`

Self-contained Lean 4 formalization verifying explicit primes `p` and strictly monotone
boundary sequences `boundaries : Fin (k + 1) → ℕ` satisfying `AllModProdEqualsOne p boundaries`
for `k = 9, 10, 11, 12`:
- `k = 9`: `p = 4093`, boundaries `[1, 2, 558, 576, 872, 2313, 3222, 3518, 3536, 4092]`
- `k = 10`: `p = 3011`, boundaries `[1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400, 3010]`
- `k = 11`: `p = 109379`, boundaries `[7300, 21086, 50440, 70049, 83189, 87820, 87967, 90846, 93485, 94442, 105229, 108418]`
- `k = 12`: `p = 52163`, boundaries `[1, 2, 3925, 7292, 7428, 18520, 24932, 26082, 27232, 33644, 44736, 44872, 52162]`

Uses a 16-factor block-unrolled binary-splitting modular product evaluator `prodModFast`
(capacity up to `65536` consecutive integers per interval) so kernel reduction remains fast
without native compilation.
-/

namespace Contribution.Erdos1056K9To12

/--
The proposition that the modular product of a collection of consecutive intervals equals `1`
modulo `p`, where intervals are defined by a function specifying the consecutive boundaries.
Matches `Erdos1056.AllModProdEqualsOne` definitionally.
-/
def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

private def prodBlock16 (p a : ℕ) : ℕ :=
  ((a * (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) * (a + 6) * (a + 7) % p) *
   ((a + 8) * (a + 9) * (a + 10) * (a + 11) * (a + 12) * (a + 13) * (a + 14) * (a + 15) % p)) % p

private def prodSmall (p : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1 % p
  | a, n + 1 => (prodSmall p a n * (a + n)) % p

private def prodBlocks (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, a, m => if m = 0 then 1 % p else prodBlock16 p a
  | fuel + 1, a, m =>
    if m ≤ 1 then
      if m = 0 then 1 % p else prodBlock16 p a
    else
      let half := m / 2
      (prodBlocks p fuel a half * prodBlocks p fuel (a + 16 * half) (m - half)) % p

private def prodModFast (p a len : ℕ) : ℕ :=
  let m := len / 16
  (prodBlocks p 12 a m * prodSmall p (a + 16 * m) (len % 16)) % p

private def checkAll (p : ℕ) {k : ℕ} (b : Fin (k + 1) → ℕ) : Bool :=
  (List.finRange k).all fun i =>
    prodModFast p (b i.castSucc) (b (i.castSucc + 1) - b i.castSucc) == 1 % p

private lemma prod_Ico_eight (a : ℕ) :
    (∏ n ∈ Finset.Ico a (a + 8), n) =
      a * (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) * (a + 6) * (a + 7) := by
  rw [show a + 8 = (a + 7) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [show a + 7 = (a + 6) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [show a + 6 = (a + 5) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [show a + 5 = (a + 4) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [show a + 4 = (a + 3) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [show a + 3 = (a + 2) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [show a + 2 = (a + 1) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
  rw [Finset.prod_Ico_succ_top (le_refl a), Finset.Ico_self, Finset.prod_empty]
  ring

private lemma prod_Ico_sixteen_mod (p a : ℕ) :
    (∏ n ∈ Finset.Ico a (a + 16), n) % p = prodBlock16 p a := by
  have hsplit : (∏ n ∈ Finset.Ico a (a + 16), n) =
      (∏ n ∈ Finset.Ico a (a + 8), n) * (∏ n ∈ Finset.Ico (a + 8) ((a + 8) + 8), n) := by
    rw [show (a + 8) + 8 = a + 16 by omega]
    exact (Finset.prod_Ico_consecutive id (by omega) (by omega)).symm
  have h1 : (∏ n ∈ Finset.Ico (a + 8) ((a + 8) + 8), n) =
      (a + 8) * (a + 9) * (a + 10) * (a + 11) * (a + 12) * (a + 13) * (a + 14) * (a + 15) := by
    rw [prod_Ico_eight (a + 8)]
  rw [hsplit, Nat.mul_mod, prod_Ico_eight a, h1]
  rfl

private lemma prod_Ico_small_mod (p a : ℕ) :
    ∀ n : ℕ, (∏ x ∈ Finset.Ico a (a + n), x) % p = prodSmall p a n
  | 0 => by simp [prodSmall]
  | n + 1 => by
    rw [show a + (n + 1) = (a + n) + 1 by omega, Finset.prod_Ico_succ_top (by omega)]
    rw [Nat.mul_mod, prod_Ico_small_mod p a n]
    conv_rhs => unfold prodSmall; rw [Nat.mul_mod]
    cases n <;> simp [prodSmall]

private lemma prod_Ico_blocks_mod (p : ℕ) :
    ∀ fuel a m : ℕ, m ≤ 2 ^ fuel →
      (∏ x ∈ Finset.Ico a (a + 16 * m), x) % p = prodBlocks p fuel a m
  | 0, a, m, hm => by
    simp only [pow_zero] at hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · simp [prodBlocks]
    · simp only [prodBlocks, mul_one, Nat.one_ne_zero, ↓reduceIte]
      exact prod_Ico_sixteen_mod p a
  | fuel + 1, a, m, hm => by
    unfold prodBlocks
    split_ifs with h1 h0
    · subst h0
      simp
    · have hm1 : m = 1 := by omega
      subst hm1
      simpa using prod_Ico_sixteen_mod p a
    · have hp2 : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      have hhalf1 : m / 2 ≤ 2 ^ fuel := by omega
      have hhalf2 : m - m / 2 ≤ 2 ^ fuel := by omega
      have hsplit : (∏ x ∈ Finset.Ico a (a + 16 * m), x) =
          (∏ x ∈ Finset.Ico a (a + 16 * (m / 2)), x) *
            (∏ x ∈ Finset.Ico (a + 16 * (m / 2)) ((a + 16 * (m / 2)) + 16 * (m - m / 2)), x) := by
        rw [show (a + 16 * (m / 2)) + 16 * (m - m / 2) = a + 16 * m by omega]
        exact (Finset.prod_Ico_consecutive id (Nat.le_add_right a _) (by omega)).symm
      rw [hsplit, Nat.mul_mod,
        prod_Ico_blocks_mod p fuel a (m / 2) hhalf1,
        prod_Ico_blocks_mod p fuel (a + 16 * (m / 2)) (m - m / 2) hhalf2]

private lemma prod_Ico_fast_mod {p a len : ℕ} (hlen : len / 16 ≤ 4096) :
    (∏ x ∈ Finset.Ico a (a + len), x) % p = prodModFast p a len := by
  have hdiv : 16 * (len / 16) + len % 16 = len := Nat.div_add_mod len 16
  have hsplit : (∏ x ∈ Finset.Ico a (a + len), x) =
      (∏ x ∈ Finset.Ico a (a + 16 * (len / 16)), x) *
        (∏ x ∈ Finset.Ico (a + 16 * (len / 16)) ((a + 16 * (len / 16)) + len % 16), x) := by
    rw [show (a + 16 * (len / 16)) + len % 16 = a + len by omega]
    exact (Finset.prod_Ico_consecutive id (Nat.le_add_right a _) (by omega)).symm
  rw [hsplit, Nat.mul_mod]
  rw [prod_Ico_blocks_mod p 12 a (len / 16) (by simpa using hlen)]
  rw [prod_Ico_small_mod p (a + 16 * (len / 16)) (len % 16)]
  rfl

private lemma allModProdEqualsOne_of_checkAll {p k : ℕ} (b : Fin (k + 1) → ℕ)
    (hle : ∀ i : Fin k, b i.castSucc ≤ b (i.castSucc + 1))
    (hbound : ∀ i : Fin k, (b (i.castSucc + 1) - b i.castSucc) / 16 ≤ 4096)
    (hcheck : checkAll p b = true) :
    AllModProdEqualsOne p b := by
  intro i
  change (∏ n ∈ Finset.Ico (b i.castSucc) (b (i.castSucc + 1)), n) % p = 1 % p
  rw [← Nat.add_sub_cancel' (hle i), prod_Ico_fast_mod (hbound i)]
  have hall := List.all_eq_true.mp hcheck i (List.mem_finRange i)
  exact beq_iff_eq.mp hall

/--
Verified `k = 9` witness modulo `4093`:
`[1, 2), [2, 558), ..., [3536, 4092)`.
-/
theorem erdos_1056_k9 :
    AllModProdEqualsOne 4093 ![1, 2, 558, 576, 872, 2313, 3222, 3518, 3536, 4092] :=
  allModProdEqualsOne_of_checkAll _ (by decide) (by decide) rfl

/--
Verified `k = 10` witness modulo `3011`:
`[1, 2), [2, 612), ..., [2400, 3010)`.
-/
theorem erdos_1056_k10 :
    AllModProdEqualsOne 3011 ![1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400, 3010] :=
  allModProdEqualsOne_of_checkAll _ (by decide) (by decide) rfl

/--
Verified `k = 11` witness modulo `109379`:
`[7300, 21086), ..., [105229, 108418)`.
-/
theorem erdos_1056_k11 :
    AllModProdEqualsOne 109379
      ![7300, 21086, 50440, 70049, 83189, 87820, 87967, 90846, 93485, 94442, 105229, 108418] :=
  allModProdEqualsOne_of_checkAll _ (by decide) (by decide) rfl

/--
Verified `k = 12` witness modulo `52163`:
`[1, 2), [2, 3925), ..., [44872, 52162)`.
-/
theorem erdos_1056_k12 :
    AllModProdEqualsOne 52163
      ![1, 2, 3925, 7292, 7428, 18520, 24932, 26082, 27232, 33644, 44736, 44872, 52162] :=
  allModProdEqualsOne_of_checkAll _ (by decide) (by decide) rfl

/--
Existence of a prime `p` and strictly monotone boundary sequence `boundaries : Fin (k + 1) → ℕ`
satisfying `AllModProdEqualsOne p boundaries` for all `9 ≤ k ≤ 12`.
-/
theorem erdos_1056_nine_to_twelve :
    ∀ k, 9 ≤ k → k ≤ 12 →
      ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ) (_ : StrictMono boundaries),
        AllModProdEqualsOne p boundaries := by
  intro k hk9 hk12
  interval_cases k
  · exact ⟨4093, by norm_num, ![1, 2, 558, 576, 872, 2313, 3222, 3518, 3536, 4092],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k9⟩
  · exact ⟨3011, by norm_num, ![1, 2, 612, 724, 750, 806, 2206, 2262, 2288, 2400, 3010],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k10⟩
  · exact ⟨109379, by norm_num,
      ![7300, 21086, 50440, 70049, 83189, 87820, 87967, 90846, 93485, 94442, 105229, 108418],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k11⟩
  · exact ⟨52163, by norm_num,
      ![1, 2, 3925, 7292, 7428, 18520, 24932, 26082, 27232, 33644, 44736, 44872, 52162],
      Fin.strictMono_iff_lt_succ.mpr (by decide), erdos_1056_k12⟩

end Contribution.Erdos1056K9To12
