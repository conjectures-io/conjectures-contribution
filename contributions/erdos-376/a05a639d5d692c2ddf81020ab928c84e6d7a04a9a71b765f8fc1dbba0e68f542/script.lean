import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Set.Finite.Lattice

open Finset

namespace Contribution.Erdos376

/-- Coprimality with `105 = 3 * 5 * 7` is equivalent to excluding its three
prime divisors from the central binomial coefficient. -/
theorem centralBinom_coprime_105_iff (n : ℕ) :
    n.centralBinom.Coprime 105 ↔
      ¬ 3 ∣ n.centralBinom ∧ ¬ 5 ∣ n.centralBinom ∧ ¬ 7 ∣ n.centralBinom := by
  rw [show 105 = 3 * 5 * 7 by norm_num, Nat.coprime_mul_iff_right,
    Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨⟨h3, h5⟩, h7⟩
    exact ⟨(Nat.prime_three.coprime_iff_not_dvd.mp h3.symm),
      (Nat.prime_five.coprime_iff_not_dvd.mp h5.symm),
      (Nat.prime_seven.coprime_iff_not_dvd.mp h7.symm)⟩
  · rintro ⟨h3, h5, h7⟩
    exact ⟨⟨(Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm,
      (Nat.prime_five.coprime_iff_not_dvd.mpr h5).symm⟩,
      (Nat.prime_seven.coprime_iff_not_dvd.mpr h7).symm⟩

theorem centralBinom_emultiplicity_eq_carries {p n b : ℕ} (hp : p.Prime)
    (hbound : Nat.log p (2 * n) < b) :
    emultiplicity p n.centralBinom =
      #{i ∈ Ico 1 b | p ^ i ≤ n % p ^ i + n % p ^ i} := by
  simpa [Nat.centralBinom, Nat.two_mul, Nat.add_sub_cancel_left] using
    (Nat.Prime.emultiplicity_choose hp (Nat.le_mul_of_pos_left n Nat.zero_lt_two) hbound)

theorem centralBinom_not_dvd_iff_no_carry {p n b : ℕ} (hp : p.Prime)
    (hbound : Nat.log p (2 * n) < b) :
    ¬ p ∣ n.centralBinom ↔
      ∀ i ∈ Ico 1 b, ¬ p ^ i ≤ n % p ^ i + n % p ^ i := by
  rw [← emultiplicity_eq_zero, centralBinom_emultiplicity_eq_carries hp hbound]
  simp

/-- Exact Kummer-carry characterization for coprimality with `105`. -/
theorem centralBinom_coprime_105_iff_no_carries {n b3 b5 b7 : ℕ}
    (h3 : Nat.log 3 (2 * n) < b3) (h5 : Nat.log 5 (2 * n) < b5)
    (h7 : Nat.log 7 (2 * n) < b7) :
    n.centralBinom.Coprime 105 ↔
      (∀ i ∈ Ico 1 b3, ¬ 3 ^ i ≤ n % 3 ^ i + n % 3 ^ i) ∧
      (∀ i ∈ Ico 1 b5, ¬ 5 ^ i ≤ n % 5 ^ i + n % 5 ^ i) ∧
      (∀ i ∈ Ico 1 b7, ¬ 7 ^ i ≤ n % 7 ^ i + n % 7 ^ i) := by
  rw [centralBinom_coprime_105_iff,
    centralBinom_not_dvd_iff_no_carry Nat.prime_three h3,
    centralBinom_not_dvd_iff_no_carry Nat.prime_five h5,
    centralBinom_not_dvd_iff_no_carry Nat.prime_seven h7]

/-- Digitwise smallness prevents a carry in every finite prefix. -/
theorem digit_bounds_imply_prefix_no_carry (p n : ℕ) :
    ∀ i : ℕ,
      (∀ j < i, 2 * (n / p ^ j % p) < p) →
        n % p ^ i + n % p ^ i < p ^ i := by
  intro i hdigit
  induction i with
  | zero => simp [Nat.mod_one]
  | succ i ih =>
      rw [Nat.mod_pow_succ]
      let r := n % p ^ i
      let d := n / p ^ i % p
      have hprefix : r + r < p ^ i := by
        simpa only [r] using ih (fun j hj => hdigit j (Nat.lt_trans hj (Nat.lt_succ_self i)))
      have hdigit_i : d + d < p := by
        simpa only [d, two_mul] using hdigit i (Nat.lt_succ_self i)
      calc
        (r + p ^ i * d) + (r + p ^ i * d) = (r + r) + p ^ i * (d + d) := by ring
        _ < p ^ i + p ^ i * (d + d) := Nat.add_lt_add_right hprefix _
        _ = p ^ i * (d + d + 1) := by ring
        _ ≤ p ^ i * p := Nat.mul_le_mul_left _ (Nat.succ_le_iff.mpr hdigit_i)

/-- The digit restriction needed by explicit infinite-family constructions. -/
def DigitGood357 (n : ℕ) : Prop :=
  (∀ j : ℕ, 2 * (n / 3 ^ j % 3) < 3) ∧
  (∀ j : ℕ, 2 * (n / 5 ^ j % 5) < 5) ∧
  (∀ j : ℕ, 2 * (n / 7 ^ j % 7) < 7)

theorem digitGood357_implies_coprime_105 (n : ℕ) (h : DigitGood357 n) :
    n.centralBinom.Coprime 105 := by
  refine (centralBinom_coprime_105_iff_no_carries
    (Nat.lt_succ_self (Nat.log 3 (2 * n)))
    (Nat.lt_succ_self (Nat.log 5 (2 * n)))
    (Nat.lt_succ_self (Nat.log 7 (2 * n)))).mpr ?_
  constructor
  · intro i _
    exact not_le_of_gt (digit_bounds_imply_prefix_no_carry 3 n i fun j _ ↦ h.1 j)
  constructor
  · intro i _
    exact not_le_of_gt (digit_bounds_imply_prefix_no_carry 5 n i fun j _ ↦ h.2.1 j)
  · intro i _
    exact not_le_of_gt (digit_bounds_imply_prefix_no_carry 7 n i fun j _ ↦ h.2.2 j)

/-- Arbitrarily large witnesses imply infinitude of a subset of `ℕ`. -/
theorem infinite_of_arbitrarily_large {P : ℕ → Prop}
    (hlarge : ∀ B : ℕ, ∃ n : ℕ, B < n ∧ P n) :
    {n : ℕ | P n}.Infinite := by
  intro hfinite
  rcases hfinite.bddAbove with ⟨B, hB⟩
  rcases hlarge B with ⟨n, hnB, hnP⟩
  exact (not_le_of_gt hnB) (hB hnP)

/-- Positive counts above all sufficiently large cutoffs produce arbitrarily
large digit-good witnesses once the count's witness semantics is supplied. -/
theorem arbitrarily_large_of_eventually_positive_counts
    (count : ℕ → ℕ)
    (realizes : ∀ N : ℕ, 0 < count N → ∃ n : ℕ, N < n ∧ DigitGood357 n)
    (eventuallyPositive : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < count N) :
    ∀ B : ℕ, ∃ n : ℕ, B < n ∧ DigitGood357 n := by
  rcases eventuallyPositive with ⟨N₀, hpositive⟩
  intro B
  rcases realizes (max B N₀) (hpositive _ (Nat.le_max_right _ _)) with ⟨n, hn, hgood⟩
  exact ⟨n, (Nat.le_max_left _ _).trans_lt hn, hgood⟩

/-- Exact target bridge from infinitely many simultaneous digit-good values. -/
theorem target_of_digitGood357_infinite
    (hinf : {n : ℕ | DigitGood357 n}.Infinite) :
    True ↔ {n : ℕ | n.centralBinom.Coprime 105}.Infinite := by
  constructor
  · intro _
    exact hinf.mono fun n hn ↦ digitGood357_implies_coprime_105 n hn
  · intro _
    trivial

/-- Count-positive form of the same exact target bridge. -/
theorem target_of_eventually_positive_counts
    (count : ℕ → ℕ)
    (realizes : ∀ N : ℕ, 0 < count N → ∃ n : ℕ, N < n ∧ DigitGood357 n)
    (eventuallyPositive : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < count N) :
    True ↔ {n : ℕ | n.centralBinom.Coprime 105}.Infinite :=
  target_of_digitGood357_infinite
    (infinite_of_arbitrarily_large
      (arbitrarily_large_of_eventually_positive_counts count realizes eventuallyPositive))

end Contribution.Erdos376
