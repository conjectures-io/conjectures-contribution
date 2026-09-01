import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FinCases
import FormalConjectures.ErdosProblems.«236»

/-!
# Finite divisor covers for Erdős problem 236

`Erdos236.f n` counts exponents `k` for which `n - 2^k` is prime.  This
contribution separates that count into a reusable finite-set interface:

* `validExponents` exposes the filtered exponent list and proves its basic API;
* `f_le_card_of_candidate_mem` bounds `f n` by a finite set of possible prime
  candidate values;
* `f_le_card_add_card_of_partial_divisor_cover` permits finitely many untreated
  exponents while covering every other candidate by nontrivial divisors.

Two complete special cases demonstrate the handoff.  Every even input satisfies
`f n ≤ 2`, giving the target-shaped little-o result along `n = 2 * t`.  A
24-class covering system with modulus `2^24 - 1`, residue `509203`, and divisors
`{3, 5, 7, 13, 17, 241}` proves the stronger identity
`f (509203 + (2^24 - 1) * t) = 0` for every `t`; in particular there are
arbitrarily large odd zero inputs and an exact little-o result along an odd
arithmetic progression.

All 24 residue certificates and all exceptional-prime exclusions are discharged
by kernel-checked `decide` proofs.  No unverified search result is imported.
-/

namespace Contribution.Erdos236FiniteCover

/-- The prime candidate attached to an exponent in Erdős problem 236. -/
def candidate (n k : ℕ) : ℕ := n - 2 ^ k

/-- The list of exponents counted by `Erdos236.f`. -/
def validExponents (n : ℕ) : List ℕ :=
  (List.range (Nat.log2 n + 1)).filter (fun k => Nat.Prime (candidate n k))

@[simp]
theorem f_eq_validExponents_length (n : ℕ) :
    Erdos236.f n = (validExponents n).length := by
  rfl

@[simp]
theorem mem_validExponents_iff {n k : ℕ} :
    k ∈ validExponents n ↔
      k < Nat.log2 n + 1 ∧ Nat.Prime (candidate n k) := by
  simp [validExponents]

lemma validExponents_nodup (n : ℕ) : (validExponents n).Nodup := by
  unfold validExponents
  exact List.nodup_range.filter _

/-- Distinct valid exponents give distinct prime candidate values. -/
lemma exponent_eq_of_candidate_eq {n k l : ℕ}
    (hk : k ∈ validExponents n) (hl : l ∈ validExponents n)
    (h : candidate n k = candidate n l) :
    k = l := by
  have hpk : Nat.Prime (candidate n k) := (mem_validExponents_iff.mp hk).2
  have hpl : Nat.Prime (candidate n l) := (mem_validExponents_iff.mp hl).2
  dsimp [candidate] at hpk hpl h
  have hklt : 2 ^ k < n := Nat.sub_pos_iff_lt.mp hpk.pos
  have hllt : 2 ^ l < n := Nat.sub_pos_iff_lt.mp hpl.pos
  have hpows : 2 ^ k = 2 ^ l := by
    omega
  exact Nat.pow_right_injective (by decide) hpows

/-- Candidate values occurring in `Erdos236.f` have no repetitions. -/
lemma candidateValues_nodup (n : ℕ) :
    ((validExponents n).map (candidate n)).Nodup := by
  apply List.Nodup.map_on
  · intro k hk l hl h
    exact exponent_eq_of_candidate_eq hk hl h
  · exact validExponents_nodup n

/--
If every prime candidate value for `n` lies in a finite set `P`, then
`Erdos236.f n ≤ P.card`.
-/
theorem f_le_card_of_candidate_mem (n : ℕ) (P : Finset ℕ)
    (hP : ∀ k, k ∈ validExponents n → candidate n k ∈ P) :
    Erdos236.f n ≤ P.card := by
  let ys := (validExponents n).map (candidate n)
  have hys : ys.Nodup := by
    simpa [ys] using candidateValues_nodup n
  have hsub : ys.toFinset ⊆ P := by
    intro q hq
    have hq' : q ∈ ys := by
      simpa using hq
    rcases List.mem_map.mp hq' with ⟨k, hk, rfl⟩
    exact hP k hk
  calc
    Erdos236.f n = (validExponents n).length := f_eq_validExponents_length n
    _ = ys.length := by simp [ys]
    _ = ys.toFinset.card := (List.toFinset_card_of_nodup hys).symm
    _ ≤ P.card := Finset.card_le_card hsub

/--
A reusable finite-divisor-cover bound. Exponents in `U` are left untreated.
Every other valid exponent only needs a nontrivial divisor drawn from `P`.
-/
theorem f_le_card_add_card_of_partial_divisor_cover
    (n : ℕ) (U P : Finset ℕ)
    (hcover : ∀ k, k ∈ validExponents n →
      k ∈ U ∨ ∃ p ∈ P, 1 < p ∧ p ∣ candidate n k) :
    Erdos236.f n ≤ U.card + P.card := by
  let Q := U.image (candidate n) ∪ P
  have hQ : ∀ k, k ∈ validExponents n → candidate n k ∈ Q := by
    intro k hk
    rcases hcover k hk with hkU | ⟨p, hpP, hpgt, hpdvd⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨k, hkU, rfl⟩
    · apply Finset.mem_union_right
      have hprime : Nat.Prime (candidate n k) :=
        (mem_validExponents_iff.mp hk).2
      have hpEq : p = candidate n k :=
        (hprime.eq_one_or_self_of_dvd p hpdvd).resolve_left (Nat.ne_of_gt hpgt)
      simpa [hpEq] using hpP
  have hbound := f_le_card_of_candidate_mem n Q hQ
  have himage : (U.image (candidate n)).card ≤ U.card :=
    Finset.card_image_le
  calc
    Erdos236.f n ≤ Q.card := hbound
    _ ≤ (U.image (candidate n)).card + P.card := by
      dsimp [Q]
      exact Finset.card_union_le _ _
    _ ≤ U.card + P.card := Nat.add_le_add_right himage P.card

/-- Subtracting a positive power of two from an even natural number stays even. -/
lemma even_candidate_of_pos {n k : ℕ} (hn : Even n) (hk : 0 < k) :
    Even (candidate n k) := by
  dsimp [candidate]
  obtain ⟨m, rfl⟩ := hn
  cases k with
  | zero => omega
  | succ j =>
      rw [pow_succ]
      exact ⟨m - 2 ^ j, by omega⟩

/-- Complete even-input special case: the count is uniformly at most two. -/
theorem f_even_le_two (n : ℕ) (hn : Even n) : Erdos236.f n ≤ 2 := by
  have hbound :=
    f_le_card_add_card_of_partial_divisor_cover n ({0} : Finset ℕ) ({2} : Finset ℕ) (by
      intro k hk
      by_cases hk0 : k = 0
      · left
        simp [hk0]
      · right
        refine ⟨2, by simp, by decide, ?_⟩
        exact even_iff_two_dvd.mp
          (even_candidate_of_pos hn (Nat.pos_of_ne_zero hk0)))
  simpa using hbound

/-- The exact target-shaped little-o statement along all even inputs. -/
theorem erdos_236_on_even_inputs :
    (fun t : ℕ => (Erdos236.f (2 * t) : ℝ))
      =o[Filter.atTop]
    (fun t : ℕ => Real.log ((2 * t : ℕ) : ℝ)) := by
  have hdouble :
      Filter.Tendsto (fun t : ℕ => 2 * t) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with a ha
    omega
  have hconst :
      (fun _ : ℕ => (2 : ℝ)) =o[Filter.atTop]
        (fun t : ℕ => Real.log ((2 * t : ℕ) : ℝ)) := by
    have hnat :
        (fun _ : ℕ => (2 : ℝ)) =o[Filter.atTop]
          (fun n : ℕ => Real.log (n : ℝ)) :=
      Asymptotics.IsLittleO.natCast_atTop
        (Real.isLittleO_const_log_atTop (c := (2 : ℝ)))
    simpa only [Function.comp_apply] using hnat.comp_tendsto hdouble
  have hbounded :
      (fun t : ℕ => (Erdos236.f (2 * t) : ℝ)) =O[Filter.atTop]
        (fun _ : ℕ => (2 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall ?_)
    intro t
    have hf : Erdos236.f (2 * t) ≤ 2 :=
      f_even_le_two (2 * t) ⟨t, by omega⟩
    have hfReal : (Erdos236.f (2 * t) : ℝ) ≤ 2 := by
      exact_mod_cast hf
    simpa using hfReal
  exact hbounded.trans_isLittleO hconst

namespace RieselCover

/-- The modulus `2^24 - 1` used by the covering system. -/
def coveringModulus : ℕ := 16777215

/-- The classical Riesel-cover constant `509203`, used here as a residue rather than a multiplier. -/
def coveringResidue : ℕ := 509203

/-- The six divisors in the covering system. -/
def coveringDivisors : Finset ℕ := {3, 5, 7, 13, 17, 241}

/-- Select the divisor assigned to one exponent class modulo 24. -/
def coverDivisor (r : Fin 24) : ℕ :=
  if (r : ℕ) % 2 = 0 then 3
  else if (r : ℕ) % 4 = 3 then 5
  else if (r : ℕ) % 8 = 1 then 17
  else if (r : ℕ) % 12 = 5 then 13
  else if (r : ℕ) % 3 = 1 then 7
  else 241

/-- The residue class of an exponent modulo 24. -/
def residue24 (k : ℕ) : Fin 24 :=
  ⟨k % 24, Nat.mod_lt _ (by decide)⟩

/-- Kernel-checked certificate for all 24 classes of the divisor cover. -/
lemma coverDivisor_spec (r : Fin 24) :
    coverDivisor r ∈ coveringDivisors ∧
    1 < coverDivisor r ∧
    coverDivisor r ∣ coveringModulus ∧
    coveringResidue ≡ 2 ^ (r : ℕ) [MOD coverDivisor r] ∧
    2 ^ 24 ≡ 1 [MOD coverDivisor r] := by
  fin_cases r <;> decide

/--
The exceptional equality `n - 2^k = p` is incompatible with the large modulus.
This is checked for all 24 exponent classes.
-/
lemma coverDivisor_no_sum (r : Fin 24) :
    ¬ coveringResidue ≡
      2 ^ (r : ℕ) + coverDivisor r [MOD coveringModulus] := by
  fin_cases r <;> decide

/-- Powers of two may be reduced modulo any certified exponent period. -/
lemma two_pow_mod_period {m p k : ℕ} (hperiod : 2 ^ m ≡ 1 [MOD p]) :
    2 ^ k ≡ 2 ^ (k % m) [MOD p] := by
  calc
    2 ^ k = 2 ^ (m * (k / m) + k % m) := by rw [Nat.div_add_mod]
    _ = (2 ^ m) ^ (k / m) * 2 ^ (k % m) := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (k / m) * 2 ^ (k % m) [MOD p] :=
      (hperiod.pow (k / m)).mul (Nat.ModEq.refl _)
    _ = 2 ^ (k % m) := by simp

lemma selectedDivisor_spec (k : ℕ) :
    coverDivisor (residue24 k) ∈ coveringDivisors ∧
    1 < coverDivisor (residue24 k) ∧
    coverDivisor (residue24 k) ∣ coveringModulus ∧
    coveringResidue ≡ 2 ^ (k % 24) [MOD coverDivisor (residue24 k)] ∧
    2 ^ 24 ≡ 1 [MOD coverDivisor (residue24 k)] := by
  simpa [residue24] using coverDivisor_spec (residue24 k)

lemma selectedDivisor_no_sum (k : ℕ) :
    ¬ coveringResidue ≡
      2 ^ (k % 24) + coverDivisor (residue24 k) [MOD coveringModulus] := by
  simpa [residue24] using coverDivisor_no_sum (residue24 k)

lemma two_pow_mod_coveringModulus (k : ℕ) :
    2 ^ k ≡ 2 ^ (k % 24) [MOD coveringModulus] := by
  apply two_pow_mod_period
  decide

/-- The selected small divisor divides every nontruncated candidate. -/
lemma selectedDivisor_dvd_candidate {n k : ℕ}
    (hn : n ≡ coveringResidue [MOD coveringModulus])
    (hk : 2 ^ k ≤ n) :
    coverDivisor (residue24 k) ∣ candidate n k := by
  rcases selectedDivisor_spec k with
    ⟨_, _, hpM, hAr, hperiod⟩
  have hnp :
      n ≡ coveringResidue [MOD coverDivisor (residue24 k)] :=
    hn.of_dvd hpM
  have hpow :
      2 ^ k ≡ 2 ^ (k % 24) [MOD coverDivisor (residue24 k)] :=
    two_pow_mod_period hperiod
  have hkn :
      2 ^ k ≡ n [MOD coverDivisor (residue24 k)] :=
    hpow.trans (hnp.trans hAr).symm
  change coverDivisor (residue24 k) ∣ n - 2 ^ k
  exact (Nat.modEq_iff_dvd' hk).mp hkn

/-- The six-divisor API alone gives the uniform bound `f(n) ≤ 6`. -/
theorem f_le_six_of_modEq_coveringResidue {n : ℕ}
    (hn : n ≡ coveringResidue [MOD coveringModulus]) :
    Erdos236.f n ≤ 6 := by
  have hbound :=
    f_le_card_add_card_of_partial_divisor_cover
      n (∅ : Finset ℕ) coveringDivisors (by
        intro k hkValid
        right
        have hs := selectedDivisor_spec k
        refine ⟨coverDivisor (residue24 k), hs.1, hs.2.1, ?_⟩
        have hprime : Nat.Prime (candidate n k) :=
          (mem_validExponents_iff.mp hkValid).2
        have hklt : 2 ^ k < n :=
          Nat.sub_pos_iff_lt.mp (by simpa [candidate] using hprime.pos)
        exact selectedDivisor_dvd_candidate hn hklt.le)
  have hcard : coveringDivisors.card = 6 := by decide
  simpa [hcard] using hbound

/-- In fact no prime candidate survives on this residue class. -/
theorem not_prime_candidate_of_modEq_coveringResidue {n : ℕ}
    (hn : n ≡ coveringResidue [MOD coveringModulus]) (k : ℕ) :
    ¬ Nat.Prime (candidate n k) := by
  intro hprime
  have hs := selectedDivisor_spec k
  let p := coverDivisor (residue24 k)
  have hpgt : 1 < p := by
    simpa [p] using hs.2.1
  have hklt : 2 ^ k < n :=
    Nat.sub_pos_iff_lt.mp (by simpa [candidate] using hprime.pos)
  have hpdvd : p ∣ candidate n k := by
    simpa [p] using selectedDivisor_dvd_candidate hn hklt.le
  have hpEq : p = candidate n k :=
    (hprime.eq_one_or_self_of_dvd p hpdvd).resolve_left (Nat.ne_of_gt hpgt)
  have hnEq : n = 2 ^ k + p := by
    dsimp [candidate] at hpEq
    calc
      n = (n - 2 ^ k) + 2 ^ k := (Nat.sub_add_cancel hklt.le).symm
      _ = p + 2 ^ k := by rw [← hpEq]
      _ = 2 ^ k + p := Nat.add_comm _ _
  have hsum :
      n ≡ 2 ^ (k % 24) + p [MOD coveringModulus] := by
    rw [hnEq]
    exact (two_pow_mod_coveringModulus k).add (Nat.ModEq.refl p)
  have hbad :
      coveringResidue ≡ 2 ^ (k % 24) + p [MOD coveringModulus] :=
    hn.symm.trans hsum
  exact selectedDivisor_no_sum k (by simpa [p] using hbad)

/-- Every integer in the certified residue class has no representation at all. -/
theorem f_eq_zero_of_modEq_coveringResidue {n : ℕ}
    (hn : n ≡ coveringResidue [MOD coveringModulus]) :
    Erdos236.f n = 0 := by
  have hnil : validExponents n = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro k hk
    exact not_prime_candidate_of_modEq_coveringResidue hn k
      (mem_validExponents_iff.mp hk).2
  rw [f_eq_validExponents_length, hnil]
  rfl

/-- A concrete infinite arithmetic progression on which `f` vanishes. -/
theorem f_coveringProgression_eq_zero (t : ℕ) :
    Erdos236.f (coveringResidue + coveringModulus * t) = 0 := by
  apply f_eq_zero_of_modEq_coveringResidue
  rw [Nat.add_comm coveringResidue]
  exact Nat.ModEq.modulus_mul_add

/-- The even-indexed part of the progression consists entirely of odd integers. -/
theorem odd_coveringProgression (t : ℕ) :
    Odd (coveringResidue + coveringModulus * (2 * t)) := by
  refine ⟨254601 + coveringModulus * t, ?_⟩
  dsimp [coveringResidue, coveringModulus]
  omega

/-- An explicit infinite odd progression on which `f` vanishes. -/
theorem f_oddCoveringProgression_eq_zero (t : ℕ) :
    Erdos236.f (coveringResidue + coveringModulus * (2 * t)) = 0 := by
  exact f_coveringProgression_eq_zero (2 * t)

/-- There are arbitrarily large odd inputs with `f(n) = 0`. -/
theorem f_eq_zero_unbounded_odd (B : ℕ) :
    ∃ n ≥ B, Odd n ∧ Erdos236.f n = 0 := by
  refine ⟨coveringResidue + coveringModulus * (2 * B), ?_, ?_, ?_⟩
  · dsimp [coveringResidue, coveringModulus]
    omega
  · exact odd_coveringProgression B
  · exact f_oddCoveringProgression_eq_zero B

/-- The exact target-shaped little-o statement on the certified odd progression. -/
theorem erdos_236_on_odd_coveringProgression :
    (fun t : ℕ =>
      (Erdos236.f (coveringResidue + coveringModulus * (2 * t)) : ℝ))
      =o[Filter.atTop]
    (fun t : ℕ =>
      Real.log
        ((coveringResidue + coveringModulus * (2 * t) : ℕ) : ℝ)) := by
  refine (Asymptotics.isLittleO_zero _ Filter.atTop).congr_left ?_
  intro t
  exact_mod_cast (f_oddCoveringProgression_eq_zero t).symm

end RieselCover
end Contribution.Erdos236FiniteCover
