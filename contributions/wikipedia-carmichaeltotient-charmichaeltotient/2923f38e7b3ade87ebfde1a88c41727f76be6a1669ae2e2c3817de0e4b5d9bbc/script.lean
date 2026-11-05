import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Structural constraints for Carmichael's totient conjecture

A partial contribution for `wikipedia-carmichaeltotient-charmichaeltotient`.
The prime-square forcing argument is an elementary case of the classical
Carmichael--Klee method; see Kevin Ford, The distribution of totients,
Section 7.3, https://arxiv.org/abs/1104.3264.

All results below are proved directly from Mathlib. The global conjecture
and the historical large lower bounds are not assumed or proved here.
-/

namespace Contribution.CarmichaelTotient

/-- A positive integer whose totient has no other natural-number preimage. -/
def UniqueTotient (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n

/-- Global uniqueness is the exact obstruction in Carmichael's conjecture. -/
theorem uniqueTotient_iff {n : ℕ} :
    UniqueTotient n ↔ 0 < n ∧ ¬ ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  simp only [UniqueTotient]
  constructor
  · rintro ⟨hn, hu⟩
    exact ⟨hn, fun ⟨m, hmn, hφ⟩ => hmn (hu m hφ)⟩
  · rintro ⟨hn, hu⟩
    refine ⟨hn, fun m hφ => ?_⟩
    by_contra hmn
    exact hu ⟨m, hmn, hφ⟩

/-- A hypothetical unique preimage is divisible by four. -/
theorem four_dvd_of_unique {n : ℕ} (hn : 0 < n)
    (hu : ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n) : 4 ∣ n := by
  have htwo : 2 ∣ n := by
    by_contra h
    have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => h he.two_dvd)
    have he := hu (2 * n) (Nat.totient_two_mul_of_odd ho)
    omega
  obtain ⟨k, rfl⟩ := htwo
  have htwo : 2 ∣ k := by
    by_contra h
    have ho : Odd k := Nat.not_even_iff_odd.mp (fun he => h he.two_dvd)
    have he := hu k (Nat.totient_two_mul_of_odd ho).symm
    omega
  obtain ⟨j, rfl⟩ := htwo
  exact ⟨j, by omega⟩

/-- Every positive integer not divisible by four satisfies the conjecture. -/
theorem collision_of_not_four_dvd {n : ℕ} (hn : 0 < n) (hfour : ¬4 ∣ n) :
    ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  by_contra h
  have hu : ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n := by
    intro m hφ
    by_contra hmn
    exact h ⟨m, hmn, hφ⟩
  exact hfour (four_dvd_of_unique hn hu)

/-- Multiplying by a divisor introduces no new prime divisors. -/
theorem totient_mul_of_dvd {a k : ℕ} (hk : 0 < k) (hka : k ∣ a) :
    (k * a).totient = k * a.totient := by
  have h := Nat.totient_gcd_mul_totient_mul k a
  rw [Nat.gcd_eq_left hka] at h
  have ht : 0 < k.totient := Nat.totient_pos.mpr hk
  nlinarith

/-- Replacing a prime by its predecessor preserves the totient when the
predecessor already divides the remaining factor. -/
theorem totient_prime_mul_eq_pred_mul {p a : ℕ} (hp : p.Prime)
    (hpa : ¬ p ∣ a) (hpred : p - 1 ∣ a) :
    (p * a).totient = ((p - 1) * a).totient := by
  rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa,
    totient_mul_of_dvd (by have := hp.two_le; omega) hpred]

/-- A prime dividing a global singleton totient fiber must occur at least twice
if its predecessor also divides the integer. -/
theorem prime_sq_dvd_of_prime_and_pred_dvd {n p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hpn : p ∣ n) (hpred : p - 1 ∣ n) : p ^ 2 ∣ n := by
  obtain ⟨a, rfl⟩ := hpn
  by_cases hpa : p ∣ a
  · simpa [pow_two] using Nat.mul_dvd_mul_left p hpa
  have hcop : (p - 1).Coprime p :=
    (Nat.coprime_self_sub_left (by have := hp.two_le; omega)).mpr (Nat.coprime_one_left p)
  have hpreda : p - 1 ∣ a := hcop.dvd_of_dvd_mul_left hpred
  have heq := huniq ((p - 1) * a) (totient_prime_mul_eq_pred_mul hp hpa hpreda).symm
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have ha : 0 < a := Nat.pos_of_mul_pos_left hn
  nlinarith

/-- If the square of a prime's predecessor divides a global singleton totient
fiber, then the square of that prime divides it as well. -/
theorem prime_sq_dvd_of_pred_sq_dvd {n p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hpred : (p - 1) ^ 2 ∣ n) : p ^ 2 ∣ n := by
  have hpredn : p - 1 ∣ n := Nat.dvd_of_pow_dvd (by decide) hpred
  apply prime_sq_dvd_of_prime_and_pred_dvd hn huniq hp _ hpredn
  by_contra hpn
  obtain ⟨a, rfl⟩ := hpredn
  have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
  have hpreda : p - 1 ∣ a := by
    apply Nat.dvd_of_mul_dvd_mul_left hpredpos
    simpa [pow_two] using hpred
  have hpa : ¬ p ∣ a := fun h => hpn (dvd_mul_of_dvd_right h _)
  have heq := huniq (p * a) (totient_prime_mul_eq_pred_mul hp hpa hpreda)
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have ha : 0 < a := Nat.pos_of_mul_pos_left hn
  nlinarith

/-- The first forced prime squares in the predecessor-square descent. -/
theorem forced_prime_squares {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    4 ∣ n ∧ 9 ∣ n ∧ 49 ∣ n ∧ 1849 ∣ n := by
  have h4 : 4 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 2)
      (by norm_num : (2 - 1) ^ 2 ∣ n)
  have h9 : 9 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 3)
      (by simpa using h4)
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have h49 : 49 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 7)
      (by simpa using h36)
  have h1764 : 1764 ∣ n := by
    simpa using (show Nat.Coprime 36 49 by norm_num).mul_dvd_of_dvd_of_dvd h36 h49
  have h1849 : 1849 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 43)
      (by simpa using h1764)
  exact ⟨h4, h9, h49, h1849⟩

/-- An elementary lower bound obtained solely from the four forced prime squares.
This does not claim Klee's substantially stronger historical bound. -/
theorem elementary_divisibility_bound {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    3261636 ∣ n ∧ 3261636 ≤ n := by
  obtain ⟨h4, h9, h49, h1849⟩ := forced_prime_squares hn huniq
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have h1764 : 1764 ∣ n := by
    simpa using (show Nat.Coprime 36 49 by norm_num).mul_dvd_of_dvd_of_dvd h36 h49
  have h : 3261636 ∣ n := by
    simpa using (show Nat.Coprime 1764 1849 by norm_num).mul_dvd_of_dvd_of_dvd h1764 h1849
  exact ⟨h, Nat.le_of_dvd hn h⟩

/-- Every positive integer below the elementary bound has a different totient
preimage. This follows by contradiction from the structural divisibility bound. -/
theorem exists_companion_below_elementary_bound {n : ℕ} (hn : 0 < n)
    (hbound : n < 3261636) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  by_contra h
  have huniq : ∀ m : ℕ, m.totient = n.totient → m = n := by
    intro m hm
    by_contra hne
    exact h ⟨m, hne, hm⟩
  have := (elementary_divisibility_bound hn huniq).2
  omega

/-- Equal totients persist on adjoining a factor coprime to both inputs. -/
theorem totient_collision_mul {a b c : ℕ}
    (ha : a.Coprime c) (hb : b.Coprime c)
    (hφ : Nat.totient a = Nat.totient b) :
    Nat.totient (a * c) = Nat.totient (b * c) := by
  rw [Nat.totient_mul ha, Nat.totient_mul hb, hφ]

/-- A nontrivial collision stays nontrivial after multiplication by a positive
common factor, provided both totients are multiplicative there. -/
theorem collision_mul {a b c : ℕ} (hc : 0 < c) (hab : a ≠ b)
    (ha : a.Coprime c) (hb : b.Coprime c)
    (hφ : Nat.totient a = Nat.totient b) :
    a * c ≠ b * c ∧ Nat.totient (a * c) = Nat.totient (b * c) := by
  constructor
  · exact fun h => hab (Nat.eq_of_mul_eq_mul_right hc h)
  · exact totient_collision_mul ha hb hφ

/-- Every collision of one factor of a hypothetical unique preimage must
introduce a common prime with the complementary factor. -/
theorem unique_factor_replacement {a b c : ℕ} (hc : 0 < c)
    (hac : a.Coprime c)
    (huniq : ∀ m : ℕ, Nat.totient m = Nat.totient (a * c) → m = a * c)
    (hφ : Nat.totient b = Nat.totient a) (hbc : b.Coprime c) : b = a := by
  apply Nat.eq_of_mul_eq_mul_right hc
  apply huniq
  exact totient_collision_mul hbc hac hφ

/-- Contrapositive form of the replacement-factor restriction. -/
theorem unique_factor_collision_not_coprime {a b c : ℕ} (hc : 0 < c)
    (hac : a.Coprime c)
    (huniq : ∀ m : ℕ, Nat.totient m = Nat.totient (a * c) → m = a * c)
    (hφ : Nat.totient b = Nat.totient a) (hba : b ≠ a) :
    ¬ b.Coprime c := by
  intro hbc
  exact hba (unique_factor_replacement hc hac huniq hφ hbc)

/-- The powers of two starting at four have the explicit partner
`3 * 2^(k+1)`. -/
theorem two_power_collision (k : ℕ) :
    3 * 2 ^ (k + 1) ≠ 2 ^ (k + 2) ∧
    Nat.totient (3 * 2 ^ (k + 1)) = Nat.totient (2 ^ (k + 2)) := by
  have hc : Nat.Coprime 3 (2 ^ (k + 1)) := by
    exact (show Nat.Coprime 3 2 by decide).pow_right _
  have hpos : 0 < 2 ^ (k + 1) := by positivity
  have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, Nat.mul_comm]
  constructor
  · rw [hpow]
    intro h
    have : 3 = 2 := Nat.eq_of_mul_eq_mul_right hpos h
    omega
  · rw [Nat.totient_mul hc, Nat.totient_prime (by decide : Nat.Prime 3),
      Nat.totient_prime_pow_succ Nat.prime_two,
      show k + 2 = (k + 1) + 1 by omega,
      Nat.totient_prime_pow_succ Nat.prime_two]
    simp [pow_succ, Nat.mul_comm]

/-- Every power of two has a second preimage under the totient function. -/
theorem two_power_has_collision (k : ℕ) :
    ∃ m : ℕ, m ≠ 2 ^ k ∧ Nat.totient m = Nat.totient (2 ^ k) := by
  rcases k with _ | k
  · exact ⟨2, by norm_num, by norm_num⟩
  rcases k with _ | k
  · exact ⟨1, by norm_num, by norm_num⟩
  · exact ⟨3 * 2 ^ (k + 1), two_power_collision k⟩

/-- An odd positive input always has its double as a second preimage. -/
theorem odd_has_collision {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  exact ⟨2 * n, by omega, Nat.totient_two_mul_of_odd hodd⟩

/-- No power of a prime can be a counterexample to Carmichael's conjecture. -/
theorem prime_power_has_collision {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    ∃ m : ℕ, m ≠ p ^ k ∧ Nat.totient m = Nat.totient (p ^ k) := by
  by_cases hp2 : p = 2
  · subst p
    exact two_power_has_collision k
  · apply odd_has_collision (pow_pos hp.pos _)
    exact (hp.odd_of_ne_two hp2).pow

/-- A hypothetical unique preimage is unequal to every prime power. -/
theorem unique_ne_prime_power {n p : ℕ} (hp : Nat.Prime p) (k : ℕ)
    (huniq : ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n) : n ≠ p ^ k := by
  intro hn
  rcases prime_power_has_collision hp k with ⟨m, hne, hφ⟩
  exact hne (by rw [← hn]; exact huniq m (by simpa [hn] using hφ))

section FiniteChecks

set_option maxRecDepth 4096

lemma totient_3261636 : Nat.totient 3261636 = 910224 := by
  rw [show 3261636 = (2 ^ 2 * 3 ^ 2) * (7 ^ 2 * 43 ^ 2) by norm_num]
  rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2 * 3 ^ 2) (7 ^ 2 * 43 ^ 2)),
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 ^ 2)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7 ^ 2) (43 ^ 2)),
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 2) 1,
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3) 1,
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 7) 1,
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 43) 1]
  norm_num

lemma totient_6523272 : Nat.totient 6523272 = 1820448 := by
  change Nat.totient (2 * 3261636) = _
  rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two (by norm_num), totient_3261636]

lemma totient_9784908 : Nat.totient 9784908 = 2730672 := by
  change Nat.totient (3 * 3261636) = _
  rw [Nat.totient_mul_of_prime_of_dvd (by norm_num : Nat.Prime 3) (by norm_num),
    totient_3261636]

lemma totient_912139 : Nat.totient 912139 = 910224 := by
  change Nat.totient (883 * 1033) = _
  rw [Nat.totient_mul (by norm_num : Nat.Coprime 883 1033),
    Nat.totient_prime (by norm_num : Nat.Prime 883),
    Nat.totient_prime (by norm_num : Nat.Prime 1033)]

lemma totient_1820449 : Nat.totient 1820449 = 1820448 := by
  exact Nat.totient_prime (by norm_num : Nat.Prime 1820449)

lemma totient_2734351 : Nat.totient 2734351 = 2730672 := by
  change Nat.totient (1033 * 2647) = _
  rw [Nat.totient_mul (by norm_num : Nat.Coprime 1033 2647),
    Nat.totient_prime (by norm_num : Nat.Prime 1033),
    Nat.totient_prime (by norm_num : Nat.Prime 2647)]

/-- Three explicit collisions eliminate the first three multiples of the
structurally forced divisor. -/
theorem checked_divisibility_bound {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    13046544 ≤ n := by
  have hnot1 : n ≠ 3261636 := by
    intro heq
    subst n
    have := huniq 912139 (totient_912139.trans totient_3261636.symm)
    norm_num at this
  have hnot2 : n ≠ 6523272 := by
    intro heq
    subst n
    have := huniq 1820449 (totient_1820449.trans totient_6523272.symm)
    norm_num at this
  have hnot3 : n ≠ 9784908 := by
    intro heq
    subst n
    have := huniq 2734351 (totient_2734351.trans totient_9784908.symm)
    norm_num at this
  obtain ⟨k, hk⟩ := (elementary_divisibility_bound hn huniq).1
  omega

/-- Carmichael's conclusion is proved for every positive input below 13,046,544
using structural lemmas and three explicit arithmetically checked collisions. -/
theorem exists_companion_below_checked_bound {n : ℕ} (hn : 0 < n)
    (hbound : n < 13046544) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  by_contra h
  have huniq : ∀ m : ℕ, m.totient = n.totient → m = n := by
    intro m hm
    by_contra hne
    exact h ⟨m, hne, hm⟩
  have := checked_divisibility_bound hn huniq
  omega

/-- The entire ten-million-input computational scan is subsumed by a Lean proof. -/
theorem exists_companion_through_ten_million {n : ℕ} (hn : 0 < n)
    (hbound : n ≤ 10000000) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient :=
  exists_companion_below_checked_bound hn (by omega)

end FiniteChecks

end Contribution.CarmichaelTotient

namespace Contribution.CarmichaelTotient.GlobalStrongerForcing

/-- The totient scales linearly when a multiplier introduces no new primes. -/
theorem totient_mul_of_prime_support {a k : ℕ}
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ k → p ∣ a) :
    (k * a).totient = k * a.totient := by
  induction k using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p k hp ih =>
    have hpa : p ∣ a := hsupport p hp (dvd_mul_right p k)
    have hka : (k * a).totient = k * a.totient :=
      ih (fun q hq hqk => hsupport q hq (dvd_mul_of_dvd_right hqk p))
    rw [mul_assoc, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_right hpa k), hka]
    simp only [mul_assoc]

/-- Carmichael's stronger predecessor criterion: it suffices that the quotient
by the predecessor still contain every prime of the predecessor. -/
theorem prime_sq_dvd_of_pred_quotient_support {n p a : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hdecomp : n = (p - 1) * a)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ a) :
    p ^ 2 ∣ n := by
  have hpredn : p - 1 ∣ n := ⟨a, hdecomp⟩
  apply prime_sq_dvd_of_prime_and_pred_dvd hn huniq hp _ hpredn
  by_contra hpn
  have hpa : ¬ p ∣ a := by
    intro h
    apply hpn
    rw [hdecomp]
    exact dvd_mul_of_dvd_right h _
  have hφ : (p * a).totient = n.totient := by
    rw [hdecomp, Nat.totient_mul_of_prime_of_not_dvd hp hpa,
      totient_mul_of_prime_support hsupport]
  have heq := huniq (p * a) hφ
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have ha : 0 < a := by rw [hdecomp] at hn; exact Nat.pos_of_mul_pos_left hn
  rw [hdecomp] at heq
  nlinarith

/-- When the 3-adic valuation is exactly two, a factor replacement forces 13². -/
theorem thirteen_sq_dvd_of_not_twenty_seven_dvd {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (h27 : ¬ 27 ∣ n) : 13 ^ 2 ∣ n := by
  obtain ⟨h4, h9, -, -⟩ := forced_prime_squares hn huniq
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have h12 : 13 - 1 ∣ n := dvd_trans (by norm_num : 12 ∣ 36) h36
  apply prime_sq_dvd_of_prime_and_pred_dvd hn huniq (by norm_num) _ h12
  by_contra h13
  obtain ⟨k, rfl⟩ := h36
  have h3k : ¬ 3 ∣ k := by
    intro h
    obtain ⟨j, rfl⟩ := h
    apply h27
    exact ⟨4 * j, by ring⟩
  have hcop : Nat.Coprime 9 (4 * k) := by
    have h3 : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3k
    exact (show Nat.Coprime 3 4 by norm_num).mul_right h3 |>.pow_left 2
  have h13k : ¬ 13 ∣ 2 * k := by
    intro h
    apply h13
    exact dvd_trans h ⟨18, by ring⟩
  have hphi : (13 * (2 * k)).totient = (36 * k).totient := by
    rw [Nat.totient_mul_of_prime_of_not_dvd (by norm_num : Nat.Prime 13) h13k]
    rw [show 36 * k = 9 * (4 * k) by ring, Nat.totient_mul hcop]
    rw [show 4 * k = 2 * (2 * k) by ring,
      Nat.totient_mul_of_prime_of_dvd Nat.prime_two (dvd_mul_right 2 k)]
    have hphi9 : Nat.totient 9 = 6 := by
      simpa using Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3) 1
    rw [hphi9]
    ring
  have heq := huniq (13 * (2 * k)) hphi
  omega

/-- When 27 divides a singleton preimage, the support form of Carmichael's
criterion forces 19²; the weaker predecessor-square rule does not suffice. -/
theorem nineteen_sq_dvd_of_twenty_seven_dvd {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (h27 : 27 ∣ n) : 19 ^ 2 ∣ n := by
  obtain ⟨h4, -, -, -⟩ := forced_prime_squares hn huniq
  have h108 : 108 ∣ n := by
    simpa using (show Nat.Coprime 4 27 by norm_num).mul_dvd_of_dvd_of_dvd h4 h27
  obtain ⟨k, rfl⟩ := h108
  apply prime_sq_dvd_of_pred_quotient_support hn huniq (by norm_num : Nat.Prime 19)
    (show 108 * k = (19 - 1) * (6 * k) by ring) _
  intro q hq hqd
  have hqdiv : q ∣ 2 * 3 ^ 2 := by simpa using hqd
  rcases hq.dvd_mul.mp hqdiv with h2 | h9
  · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
    subst q
    exact dvd_trans (by norm_num : 2 ∣ 6) (dvd_mul_right 6 k)
  · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp
      (hq.dvd_of_dvd_pow h9)
    subst q
    exact dvd_trans (by norm_num : 3 ∣ 6) (dvd_mul_right 6 k)

/-- The first genuine branch beyond the finite 2,3,7,43 predecessor-square
closure. This is a divisibility restriction, not an infinitude theorem. -/
theorem thirteen_or_nineteen_sq_dvd {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    13 ^ 2 ∣ n ∨ 19 ^ 2 ∣ n := by
  by_cases h27 : 27 ∣ n
  · exact Or.inr (nineteen_sq_dvd_of_twenty_seven_dvd hn huniq h27)
  · exact Or.inl (thirteen_sq_dvd_of_not_twenty_seven_dvd hn huniq h27)

end Contribution.CarmichaelTotient.GlobalStrongerForcing

namespace Contribution.CarmichaelTotient

/-- Multiplying a positive equal-totient pair by a prime preserves its common
totient exactly when that prime divides both inputs or neither input. -/
theorem prime_scaling_totient_iff {a b p : ℕ} (ha : 0 < a)
    (hφ : a.totient = b.totient) (hp : p.Prime) :
    (p * a).totient = (p * b).totient ↔ (p ∣ a ↔ p ∣ b) := by
  have hφpos : 0 < a.totient := Nat.totient_pos.mpr ha
  have hpred : p - 1 + 1 = p := by have := hp.two_le; omega
  by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b
  · simp only [hpa, hpb, iff_true]
    rw [Nat.totient_mul_of_prime_of_dvd hp hpa,
      Nat.totient_mul_of_prime_of_dvd hp hpb, hφ]
  · simp only [hpa, hpb, iff_false, not_true_eq_false, iff_false]
    rw [Nat.totient_mul_of_prime_of_dvd hp hpa,
      Nat.totient_mul_of_prime_of_not_dvd hp hpb, ← hφ]
    nlinarith
  · simp only [hpa, hpb, iff_true, iff_false]
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa,
      Nat.totient_mul_of_prime_of_dvd hp hpb, ← hφ]
    nlinarith
  · simp only [hpa, hpb, iff_true]
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa,
      Nat.totient_mul_of_prime_of_not_dvd hp hpb, hφ]

/-- The prime-scaling criterion suffices for every exponent, without requiring
the complementary factor to be coprime to the collision pair. -/
theorem prime_power_scaling_totient {a b p : ℕ} (ha : 0 < a)
    (hφ : a.totient = b.totient) (hp : p.Prime)
    (hdiv : p ∣ a ↔ p ∣ b) (k : ℕ) :
    (p ^ k * a).totient = (p ^ k * b).totient := by
  induction k with
  | zero => simpa using hφ
  | succ k ih =>
    have hdiv' : p ∣ p ^ k * a ↔ p ∣ p ^ k * b := by
      simp only [hp.dvd_mul, hdiv]
    have hpos : 0 < p ^ k * a := Nat.mul_pos (pow_pos hp.pos k) ha
    have h := (prime_scaling_totient_iff hpos ih hp).mpr hdiv'
    simpa only [pow_succ', mul_assoc] using h

/-- A genuine collision generates a distinct equal-totient pair at every
prime-power scale satisfying the exact divisibility criterion. -/
theorem prime_power_scaling_collision {a b p : ℕ} (ha : 0 < a)
    (hab : a ≠ b) (hφ : a.totient = b.totient) (hp : p.Prime)
    (hdiv : p ∣ a ↔ p ∣ b) (k : ℕ) :
    p ^ k * a ≠ p ^ k * b ∧
    (p ^ k * a).totient = (p ^ k * b).totient := by
  constructor
  · intro h
    exact hab (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) h)
  · exact prime_power_scaling_totient ha hφ hp hdiv k

end Contribution.CarmichaelTotient

namespace Contribution.CarmichaelTotient.ClosureAudit

theorem divisor_1806_cases {d : ℕ} (hd : d ∣ 1806) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ d = 7 ∨ d = 14 ∨
    d = 21 ∨ d = 42 ∨ d = 43 ∨ d = 86 ∨ d = 129 ∨ d = 258 ∨
    d = 301 ∨ d = 602 ∨ d = 903 ∨ d = 1806 := by
  have hfac : d ∣ 2 * (3 * (7 * 43)) := hd
  rcases Nat.dvd_mul.mp hfac with ⟨a, b, ha, hb, rfl⟩
  rcases Nat.dvd_mul.mp hb with ⟨c, e, hc, he, rfl⟩
  rcases Nat.dvd_mul.mp he with ⟨f, g, hf, hg, rfl⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hc with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hf with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 43)).mp hg with rfl | rfl <;>
    norm_num

/-- Every prime eligible under the weak rule already belongs to the seed set. -/
theorem eligible_prime_cases {p : ℕ} (hp : Nat.Prime p)
    (hpred : (p - 1) ^ 2 ∣ 3261636) :
    p = 2 ∨ p = 3 ∨ p = 7 ∨ p = 43 := by
  have hd : p - 1 ∣ 1806 :=
    (Nat.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hpred
  have hcases := divisor_1806_cases hd
  have hpos := hp.two_le
  have hpval : p = (p - 1) + 1 := by omega
  rcases hcases with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;>
    rw [h] at hpval <;> norm_num at hpval <;> subst p <;>
    norm_num at hp <;> norm_num

/-- Iterating this rule cannot add a prime square to this positive seed. -/
theorem predecessor_square_fixed_point :
    0 < (3261636 : ℕ) ∧
      ∀ p : ℕ, p.Prime → (p - 1) ^ 2 ∣ 3261636 → p ^ 2 ∣ 3261636 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hpred
  rcases eligible_prime_cases hp hpred with rfl | rfl | rfl | rfl <;> norm_num

/-- In particular, the weak rule alone cannot require more than these four primes. -/
theorem no_new_prime_from_seed :
    ¬ ∃ p : ℕ, p.Prime ∧ (p - 1) ^ 2 ∣ 3261636 ∧ ¬ p ∣ 3261636 := by
  rintro ⟨p, hp, hpred, hnot⟩
  exact hnot (Nat.dvd_of_pow_dvd (by decide)
    (predecessor_square_fixed_point.2 p hp hpred))

end Contribution.CarmichaelTotient.ClosureAudit

namespace Contribution.CarmichaelTotient.Klee

open GlobalStrongerForcing

/-- A prime already present in a singleton preimage has exponent at least two
when every prime factor of its predecessor is also present. -/
theorem prime_sq_dvd_of_prime_and_pred_support {n p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hpn : p ∣ n)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ n) : p ^ 2 ∣ n := by
  obtain ⟨a, rfl⟩ := hpn
  by_cases hpa : p ∣ a
  · simpa [pow_two] using Nat.mul_dvd_mul_left p hpa
  have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
  have hsupporta : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ a := by
    intro q hq hqd
    have hqp : ¬ q ∣ p := by
      intro h
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
      subst q
      have := Nat.le_of_dvd hpredpos hqd
      omega
    exact (hq.dvd_mul.mp (hsupport q hq hqd)).resolve_left hqp
  have hphi : ((p - 1) * a).totient = (p * a).totient := by
    rw [totient_mul_of_prime_support hsupporta,
      Nat.totient_mul_of_prime_of_not_dvd hp hpa]
  have heq := huniq ((p - 1) * a) hphi
  have ha : 0 < a := Nat.pos_of_mul_pos_left hn
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  nlinarith

/-- Carmichael--Klee forcing in a factorized prime-support form. Writing
`n = d * (e * a)` expresses the quotient in Ford's lemma without natural
division. The multiplier `e` introduces no new primes into `a`.

This is an unbounded implication; it does not assert that infinitely many
primes satisfy its hypotheses. -/
theorem carmichael_klee_support {n d e a p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hdecomp : n = d * (e * a)) (hcop : d.Coprime (e * a))
    (hsupporte : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ a)
    (hsupportphi : ∀ q : ℕ, q.Prime → q ∣ d.totient → q ∣ n)
    (hp : p.Prime) (hprime : p = 1 + e * d.totient) : p ^ 2 ∣ n := by
  have hpred : p - 1 = e * d.totient := by omega
  have hen : e ∣ n := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_right e a) d
  have hpredsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ n := by
    intro q hq hqd
    rw [hpred] at hqd
    rcases hq.dvd_mul.mp hqd with hqe | hqphi
    · exact dvd_trans hqe hen
    · exact hsupportphi q hq hqphi
  apply prime_sq_dvd_of_prime_and_pred_support hn huniq hp _ hpredsupport
  by_contra hpn
  have han : a ∣ n := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_left a e) d
  have hpa : ¬ p ∣ a := fun h => hpn (dvd_trans h han)
  have hphi : (p * a).totient = n.totient := by
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa, hpred, hdecomp,
      Nat.totient_mul hcop, totient_mul_of_prime_support hsupporte]
    ring
  have heq := huniq (p * a) hphi
  exact hpn (heq ▸ dvd_mul_right p a)

open scoped BigOperators

/-- The quotient and squarefree-kernel formulation of Carmichael--Klee,
matching the hypotheses of Ford, The distribution of totients, Lemma 7.2. -/
theorem carmichael_klee {n d e p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hd : d ∣ n) (hcop : d.Coprime (n / d))
    (hphi : (∏ q ∈ d.totient.primeFactors, q) ∣ n)
    (he : e ∣ (n / d) / (∏ q ∈ (n / d).primeFactors, q))
    (hp : p.Prime) (hprime : p = 1 + e * d.totient) : p ^ 2 ∣ n := by
  let y := n / d
  let r := ∏ q ∈ y.primeFactors, q
  have hr : r ∣ y := Nat.prod_primeFactors_dvd y
  have hnprod : d * y = n := Nat.mul_div_cancel' hd
  have hypos : 0 < y := Nat.pos_of_mul_pos_left (hnprod ▸ hn)
  have hdpos : 0 < d := Nat.pos_of_mul_pos_right (hnprod ▸ hn)
  obtain ⟨a, ha⟩ := he
  have hy : y = e * (r * a) := by
    calc
      y = r * (y / r) := (Nat.mul_div_cancel' hr).symm
      _ = r * (e * a) := by rw [show y / r = e * a from ha]
      _ = e * (r * a) := by ring
  have hnrepr : n = d * (e * (r * a)) := by rw [← hnprod, hy]
  have hsupporte : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ r * a := by
    intro q hq hqe
    have hqy : q ∣ y := by rw [hy]; exact dvd_mul_of_dvd_left hqe _
    have hmem : q ∈ y.primeFactors := hq.mem_primeFactors hqy hypos.ne'
    have hqr : q ∣ r := Finset.dvd_prod_of_mem (fun q => q) hmem
    exact dvd_mul_of_dvd_left hqr a
  have hsupportphi : ∀ q : ℕ, q.Prime → q ∣ d.totient → q ∣ n := by
    intro q hq hqd
    have hmem : q ∈ d.totient.primeFactors :=
      hq.mem_primeFactors hqd (Nat.totient_pos.mpr hdpos).ne'
    exact dvd_trans (Finset.dvd_prod_of_mem (fun q => q) hmem) hphi
  apply carmichael_klee_support hn huniq hnrepr _ hsupporte hsupportphi hp hprime
  simpa only [← hy] using hcop

end Contribution.CarmichaelTotient.Klee

namespace Contribution.CarmichaelTotient.PomeranceSupport

/-- Euler's product has positive predecessor factors because all its factors are prime. -/
theorem predecessor_product_pos (n : ℕ) :
    0 < ∏ p ∈ n.primeFactors, (p - 1) := by
  apply Finset.prod_pos
  intro p hp
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  omega

/-- Equal totients determine the input once the set of prime divisors is fixed. -/
theorem eq_of_totient_eq_of_primeFactors_eq {a b : ℕ}
    (hφ : a.totient = b.totient) (hprimes : a.primeFactors = b.primeFactors) :
    a = b := by
  have ha := Nat.totient_mul_prod_primeFactors a
  have hb := Nat.totient_mul_prod_primeFactors b
  rw [hφ, hprimes] at ha
  apply Nat.eq_of_mul_eq_mul_right (predecessor_product_pos b)
  exact ha.symm.trans hb

/-- Cancelling common prime factors in Euler's product isolates exactly the
prime divisors present in `n` but missing from `m`. -/
theorem missing_prime_product_identity {m n : ℕ}
    (hφ : m.totient = n.totient) (hsubset : m.primeFactors ⊆ n.primeFactors) :
    n * (∏ p ∈ n.primeFactors \ m.primeFactors, (p - 1)) =
      m * (∏ p ∈ n.primeFactors \ m.primeFactors, p) := by
  have hm := Nat.totient_mul_prod_primeFactors m
  have hn := Nat.totient_mul_prod_primeFactors n
  have hrad : (∏ p ∈ n.primeFactors \ m.primeFactors, p) *
      (∏ p ∈ m.primeFactors, p) = ∏ p ∈ n.primeFactors, p :=
    Finset.prod_sdiff hsubset
  have hpred : (∏ p ∈ n.primeFactors \ m.primeFactors, (p - 1)) *
      (∏ p ∈ m.primeFactors, (p - 1)) = ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_sdiff hsubset
  rw [← hφ, ← hrad, ← hpred] at hn
  apply Nat.eq_of_mul_eq_mul_right (predecessor_product_pos m)
  nlinarith [congrArg (fun t => t * (∏ p ∈ n.primeFactors \ m.primeFactors, p)) hm]

end Contribution.CarmichaelTotient.PomeranceSupport


namespace Contribution.CarmichaelTotient.PomeranceCriterion

open Finset

lemma prime_dvd_prod_exists {s : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hd : p ∣ ∏ q ∈ s, q) : ∃ q ∈ s, p ∣ q := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at hd
    exact (hp.not_dvd_one hd).elim
  | @insert q s hqs ih =>
    rw [Finset.prod_insert hqs] at hd
    rcases hp.dvd_mul.mp hd with hq | hs
    · exact ⟨q, Finset.mem_insert_self q s, hq⟩
    · obtain ⟨r, hrs, hpr⟩ := ih hs
      exact ⟨r, Finset.mem_insert_of_mem hrs, hpr⟩

/-- A product of distinct primes is divisible by no prime square. -/
lemma prime_sq_not_dvd_prime_prod {s : Finset ℕ}
    (hs : ∀ q ∈ s, Nat.Prime q) {p : ℕ} (hp : Nat.Prime p) :
    ¬ p ^ 2 ∣ ∏ q ∈ s, q := by
  intro hsq
  have hd : p ∣ ∏ q ∈ s, q := Nat.dvd_of_pow_dvd (by decide) hsq
  obtain ⟨q, hqs, hpq⟩ := prime_dvd_prod_exists hp hd
  have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).mp hpq
  have hps : p ∈ s := hpqeq ▸ hqs
  have hprod : (∏ q ∈ s, q) = p * ∏ q ∈ s.erase p, q := by
    exact (Finset.mul_prod_erase s (fun q : ℕ => q) hps).symm
  rw [hprod, pow_two] at hsq
  have hd' : p ∣ ∏ q ∈ s.erase p, q := Nat.dvd_of_mul_dvd_mul_left hp.pos hsq
  obtain ⟨q, hqs, hpq⟩ := prime_dvd_prod_exists hp hd'
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (hs q (Finset.mem_of_mem_erase hqs))).mp hpq
  exact (Finset.ne_of_mem_erase hqs) heq.symm

/-- No new square of a prime can appear by multiplying a number coprime to
that prime by a product of distinct primes. -/
lemma prime_sq_not_dvd_mul_prime_prod {s : Finset ℕ}
    (hs : ∀ q ∈ s, Nat.Prime q) {p m : ℕ} (hp : Nat.Prime p) (hpm : ¬ p ∣ m) :
    ¬ p ^ 2 ∣ m * ∏ q ∈ s, q := by
  intro hsq
  have hcop : Nat.Coprime (p ^ 2) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left 2
  exact prime_sq_not_dvd_prime_prod hs hp (hcop.dvd_of_dvd_mul_left hsq)

/-- Pomerance's finite divisibility criterion is sufficient for global
uniqueness of a positive totient preimage. Its hypothesis is substantially
stronger than predecessor-square closure. -/
theorem singleton_of_prime_predecessor_criterion {n : ℕ} (hn : 0 < n)
    (hcriterion : ∀ p : ℕ, Nat.Prime p → p - 1 ∣ n.totient → p ^ 2 ∣ n) :
    ∀ m : ℕ, m.totient = n.totient → m = n := by
  intro m hφ
  have hm : 0 < m := Nat.totient_pos.mp (by rw [hφ]; exact Nat.totient_pos.mpr hn)
  have hpred {a p : ℕ} (hp : Nat.Prime p) (hpa : p ∣ a) : p - 1 ∣ a.totient := by
    simpa only [Nat.totient_prime hp] using Nat.totient_dvd_of_dvd hpa
  have hsub : m.primeFactors ⊆ n.primeFactors := by
    intro p hpm
    have hp := Nat.prime_of_mem_primeFactors hpm
    have hpφ : p - 1 ∣ n.totient := by
      rw [← hφ]
      exact hpred hp (Nat.dvd_of_mem_primeFactors hpm)
    exact Nat.mem_primeFactors.mpr ⟨hp,
      Nat.dvd_of_pow_dvd (by decide) (hcriterion p hp hpφ), hn.ne'⟩
  have hidentity := PomeranceSupport.missing_prime_product_identity hφ hsub
  have hrev : n.primeFactors ⊆ m.primeFactors := by
    intro p hpn
    by_contra hpm
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hpnot : ¬ p ∣ m := by
      intro hdiv
      exact hpm (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hm.ne'⟩)
    have hpsq : p ^ 2 ∣ n :=
      hcriterion p hp (hpred hp (Nat.dvd_of_mem_primeFactors hpn))
    have hdiv : p ^ 2 ∣ m * ∏ q ∈ n.primeFactors \ m.primeFactors, q := by
      rw [← hidentity]
      exact dvd_mul_of_dvd_left hpsq _
    exact prime_sq_not_dvd_mul_prime_prod
      (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1) hp hpnot hdiv
  exact PomeranceSupport.eq_of_totient_eq_of_primeFactors_eq hφ (Finset.Subset.antisymm hsub hrev)

/-- The criterion can be checked on the finite divisor set of `φ(n)`.
No search cutoff occurs in the resulting uniqueness conclusion. -/
theorem singleton_of_divisor_certificate {n : ℕ} (hn : 0 < n)
    (hcertificate : ∀ d ∈ n.totient.divisors,
      Nat.Prime (d + 1) → (d + 1) ^ 2 ∣ n) :
    ∀ m : ℕ, m.totient = n.totient → m = n := by
  apply singleton_of_prime_predecessor_criterion hn
  intro p hp hpred
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have hd : p - 1 ∈ n.totient.divisors :=
    Nat.mem_divisors.mpr ⟨hpred, (Nat.totient_pos.mpr hn).ne'⟩
  simpa only [hpadd] using hcertificate (p - 1) hd (by simpa only [hpadd] using hp)

/-- A positive integer satisfying the finite certificate would globally
refute Carmichael's conjecture. This theorem does not assert that such an
integer exists. -/
theorem refutes_carmichael_of_divisor_certificate {n : ℕ} (hn : 0 < n)
    (hcertificate : ∀ d ∈ n.totient.divisors,
      Nat.Prime (d + 1) → (d + 1) ^ 2 ∣ n) :
    ¬ (∀ a : ℕ, 0 < a → ∃ b : ℕ, b ≠ a ∧ b.totient = a.totient) := by
  intro hall
  obtain ⟨m, hmn, hφ⟩ := hall n hn
  exact hmn (singleton_of_divisor_certificate hn hcertificate m hφ)

end Contribution.CarmichaelTotient.PomeranceCriterion

namespace Contribution.CarmichaelTotient.SquareKernelCriterion

/-- Pomerance's sufficient criterion for a singleton totient fiber. -/
def Criterion (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p - 1 ∣ n.totient → p ^ 2 ∣ n

/-- The square of the product of the distinct prime divisors. -/
def squareKernel (n : ℕ) : ℕ := (∏ p ∈ n.primeFactors, p) ^ 2

/-- Every prime divisor of a witness to the criterion occurs at least twice. -/
theorem prime_sq_dvd_of_criterion {n p : ℕ} (h : Criterion n)
    (hp : p.Prime) (hpn : p ∣ n) : p ^ 2 ∣ n := by
  apply h p hp
  rw [← Nat.totient_prime hp]
  exact Nat.totient_dvd_of_dvd hpn

/-- The square-kernel of a positive witness to the criterion divides it. -/
theorem squareKernel_dvd {n : ℕ} (hn : 0 < n) (h : Criterion n) :
    squareKernel n ∣ n := by
  unfold squareKernel
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn.ne']
  apply Finset.prod_dvd_prod_of_dvd
  intro p hpn
  have hp := Nat.prime_of_mem_primeFactors hpn
  apply Nat.pow_dvd_pow
  exact (hp.pow_dvd_iff_le_factorization hn.ne').mp
    (prime_sq_dvd_of_criterion h hp (Nat.dvd_of_mem_primeFactors hpn))

/-- A product of primes, including the empty product, is positive. -/
theorem squareKernel_pos (n : ℕ) : 0 < squareKernel n := by
  unfold squareKernel
  apply pow_pos
  exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)

/-- Passing to the square-kernel preserves Pomerance's sufficient criterion. -/
theorem criterion_squareKernel {n : ℕ} (hn : 0 < n) (h : Criterion n) :
    Criterion (squareKernel n) := by
  intro p hp hpred
  have hp2n : p ^ 2 ∣ n :=
    h p hp (dvd_trans hpred (Nat.totient_dvd_of_dvd (squareKernel_dvd hn h)))
  have hpn : p ∣ n := Nat.dvd_of_pow_dvd (by decide) hp2n
  have hmem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn.ne'
  have hprad : p ∣ ∏ q ∈ n.primeFactors, q :=
    Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem
  exact pow_dvd_pow_of_dvd hprad 2

/-- Existence of a positive criterion witness reduces exactly to witnesses
that are squares of products of distinct primes. No infinitude or existence
assumption is hidden in this equivalence. -/
theorem exists_criterion_iff_squareKernel :
    (∃ n : ℕ, 0 < n ∧ Criterion n) ↔
      ∃ n : ℕ, 0 < n ∧ Criterion (squareKernel n) := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, criterion_squareKernel hn h⟩
  · rintro ⟨n, _, h⟩
    exact ⟨squareKernel n, squareKernel_pos n, h⟩

end Contribution.CarmichaelTotient.SquareKernelCriterion

namespace Contribution.CarmichaelTotient.MinimalDescent

/-- Dividing an alleged singleton input by two preserves uniqueness once
the input is divisible by eight. This is an actual decreasing step. -/
theorem unique_four_mul_of_unique_eight_mul {a : ℕ}
    (h : UniqueTotient (8 * a)) : UniqueTotient (4 * a) := by
  refine ⟨by have := h.1; omega, ?_⟩
  intro m hm
  have hbase : (8 * a).totient = 2 * (4 * a).totient := by
    rw [show 8 * a = 2 * (4 * a) by ring]
    exact Nat.totient_mul_of_prime_of_dvd Nat.prime_two ⟨2 * a, by ring⟩
  by_cases heven : 2 ∣ m
  · have hlift : (2 * m).totient = (8 * a).totient := by
      rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two heven, hm, hbase]
    have heq := h.2 (2 * m) hlift
    omega
  · have hodd : Odd m := Nat.not_even_iff_odd.mp (fun he => heven he.two_dvd)
    have hlift : (4 * m).totient = (8 * a).totient := by
      rw [show 4 * m = 2 * (2 * m) by ring,
        Nat.totient_mul_of_prime_of_dvd Nat.prime_two (dvd_mul_right 2 m),
        Nat.totient_two_mul_of_odd hodd, hm, hbase]
    have heq := h.2 (4 * m) hlift
    have hmeq : m = 2 * a := by omega
    exact (heven ⟨a, hmeq⟩).elim

/-- Every hypothetical counterexample has a counterexample divisor
congruent to four modulo eight. No finite upper cutoff is used. -/
theorem exists_reduced_counterexample {n : ℕ} (h : UniqueTotient n) :
    ∃ r : ℕ, r ∣ n ∧ UniqueTotient r ∧ r % 8 = 4 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h8 : 8 ∣ n
    · obtain ⟨a, rfl⟩ := h8
      have ha : 0 < a := by have := h.1; omega
      have hsmall : 4 * a < 8 * a := by omega
      obtain ⟨r, hr, hu, hmod⟩ :=
        ih (4 * a) hsmall (unique_four_mul_of_unique_eight_mul h)
      exact ⟨r, dvd_trans hr ⟨2, by ring⟩, hu, hmod⟩
    · have h4 := four_dvd_of_unique h.1 h.2
      exact ⟨n, dvd_refl n, h, by omega⟩

/-- The full conjecture is equivalent to its unbounded restriction to
inputs congruent to four modulo eight. The restricted statement remains
unproved; this equivalence does not close the conjecture. -/
theorem carmichael_iff_four_mod_eight :
    (∀ n : ℕ, 0 < n → ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient) ↔
      (∀ n : ℕ, n % 8 = 4 → ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient) := by
  constructor
  · intro hall n hn
    exact hall n (by omega)
  · intro hrestricted n hn
    by_contra hnone
    have hu : UniqueTotient n := uniqueTotient_iff.mpr ⟨hn, hnone⟩
    obtain ⟨r, _, hr, hmod⟩ := exists_reduced_counterexample hu
    obtain ⟨m, hmr, hm⟩ := hrestricted r hmod
    exact hmr (hr.2 m hm)

end Contribution.CarmichaelTotient.MinimalDescent

namespace Contribution.CarmichaelTotient.FermatDescent

/-- Repeated scaling by a prime already present multiplies the totient linearly. -/
lemma totient_prime_pow_mul_of_dvd {p b : ℕ} (hp : p.Prime) (hb : p ∣ b)
    (a : ℕ) : (p ^ a * b).totient = p ^ a * b.totient := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show p ^ (a + 1) * b = p * (p ^ a * b) by ring,
      Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_right hb _), ih,
      pow_succ]
    ring

/-- Removing the full power of a prime whose predecessor is a power of two
preserves uniqueness, provided the original input is not divisible by eight
and the predecessor is divisible by four. This is a genuine divisor descent. -/
theorem unique_cofactor_of_fermat_prime {p r a c : ℕ}
    (hp : p.Prime) (hform : p = 2 ^ r + 1) (hr : 2 ≤ r)
    (hpc : ¬ p ∣ c) (h : UniqueTotient (p ^ (a + 1) * c))
    (h8 : ¬ 8 ∣ p ^ (a + 1) * c) : UniqueTotient c := by
  have hc : 0 < c := Nat.pos_of_mul_pos_left h.1
  have hpow : 0 < p ^ (a + 1) := pow_pos hp.pos _
  have hpred : p - 1 = 2 ^ r := by simp [hform]
  have hbase : (p ^ (a + 1) * c).totient =
      p ^ a * (2 ^ r) * c.totient := by
    rw [Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpc).pow_left _),
      Nat.totient_prime_pow_succ hp, hpred]
  refine ⟨hc, ?_⟩
  intro b hb
  by_cases hpb : p ∣ b
  · obtain ⟨b', hb'even, hpb', hb'phi⟩ :
        ∃ b' : ℕ, 2 ∣ b' ∧ p ∣ b' ∧ b'.totient = c.totient := by
      by_cases hb2 : 2 ∣ b
      · exact ⟨b, hb2, hpb, hb⟩
      · have ho : Odd b := Nat.not_even_iff_odd.mp (fun he => hb2 he.two_dvd)
        exact ⟨2 * b, dvd_mul_right _ _, dvd_mul_of_dvd_right hpb _,
          (Nat.totient_two_mul_of_odd ho).trans hb⟩
    have hxphi : (2 ^ r * (p ^ a * b')).totient =
        (p ^ (a + 1) * c).totient := by
      rw [totient_prime_pow_mul_of_dvd Nat.prime_two
          (dvd_mul_of_dvd_right hb'even _) r,
        totient_prime_pow_mul_of_dvd hp hpb' a, hb'phi, hbase]
      ring
    have hxeq := h.2 (2 ^ r * (p ^ a * b')) hxphi
    have hfour : 4 ∣ 2 ^ r := by
      simpa using (Nat.pow_dvd_pow 2 hr)
    obtain ⟨u, hu⟩ := hfour
    obtain ⟨v, hv⟩ := hb'even
    have hx8 : 8 ∣ 2 ^ r * (p ^ a * b') := by
      refine ⟨u * p ^ a * v, ?_⟩
      rw [hu, hv]
      ring
    exact (h8 (hxeq ▸ hx8)).elim
  · have hphi : (p ^ (a + 1) * b).totient =
        (p ^ (a + 1) * c).totient := by
      rw [Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpb).pow_left _),
        Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpc).pow_left _), hb]
    exact Nat.eq_of_mul_eq_mul_left hpow (h.2 _ hphi)

/-- The cofactor reached by the previous theorem is a positive proper divisor. -/
theorem fermat_prime_descent {p r a c : ℕ}
    (hp : p.Prime) (hform : p = 2 ^ r + 1) (hr : 2 ≤ r)
    (hpc : ¬ p ∣ c) (h : UniqueTotient (p ^ (a + 1) * c))
    (h8 : ¬ 8 ∣ p ^ (a + 1) * c) :
    0 < c ∧ c ∣ p ^ (a + 1) * c ∧ c < p ^ (a + 1) * c ∧ UniqueTotient c := by
  have hc := unique_cofactor_of_fermat_prime hp hform hr hpc h h8
  refine ⟨hc.1, dvd_mul_left _ _, ?_, hc⟩
  have hppow : 1 < p ^ (a + 1) := one_lt_pow₀ hp.one_lt (by omega)
  nlinarith [hc.1]

/-- The factorized descent applies to any positive singleton input containing
one of these Fermat primes. -/
theorem exists_fermat_prime_descent {n p r : ℕ}
    (hp : p.Prime) (hform : p = 2 ^ r + 1) (hr : 2 ≤ r)
    (hpn : p ∣ n) (h : UniqueTotient n) (h8 : ¬ 8 ∣ n) :
    ∃ c : ℕ, c ∣ n ∧ c < n ∧ UniqueTotient c := by
  obtain ⟨a, c, hpc, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd h.1.ne' p hp.ne_one
  cases a with
  | zero =>
    simp only [pow_zero, one_mul] at hn
    exact (hpc (hn ▸ hpn)).elim
  | succ a =>
    subst n
    obtain ⟨_, hdiv, hlt, hc⟩ := fermat_prime_descent hp hform hr hpc h h8
    exact ⟨c, hdiv, hlt, hc⟩

/-- A least singleton input, if one exists, is not divisible by eight. -/
theorem not_eight_dvd_of_minimal_unique {n : ℕ} (h : UniqueTotient n)
    (hmin : ∀ c : ℕ, UniqueTotient c → n ≤ c) : ¬ 8 ∣ n := by
  rintro ⟨a, rfl⟩
  have ha : 0 < a := by have := h.1; omega
  have hsmall := hmin (4 * a) (MinimalDescent.unique_four_mul_of_unique_eight_mul h)
  omega

/-- Every Fermat prime larger than three is excluded from a least singleton
input. This is a restriction on a hypothetical counterexample, not a contradiction. -/
theorem fermat_prime_not_dvd_of_minimal_unique {n p r : ℕ}
    (h : UniqueTotient n) (hmin : ∀ c : ℕ, UniqueTotient c → n ≤ c)
    (hp : p.Prime) (hform : p = 2 ^ r + 1) (hr : 2 ≤ r) : ¬ p ∣ n := by
  intro hpn
  obtain ⟨c, _, hlt, hc⟩ := exists_fermat_prime_descent hp hform hr hpn h
    (not_eight_dvd_of_minimal_unique h hmin)
  exact (Nat.not_le_of_lt hlt) (hmin c hc)

/-- Every singleton input has a totient divisible by four, using the already
proved forced divisibility by 36. -/
lemma four_dvd_totient_of_unique {n : ℕ} (h : UniqueTotient n) :
    4 ∣ n.totient := by
  obtain ⟨h4, h9, _, _⟩ := forced_prime_squares h.1 h.2
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have hphi36 : Nat.totient 36 = 12 := by
    change (2 ^ 2 * 3 ^ 2).totient = 12
    rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 ^ 2)),
      Nat.totient_prime_pow_succ Nat.prime_two,
      Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3)]
    norm_num
  have h12 : 12 ∣ n.totient := by
    simpa [hphi36] using Nat.totient_dvd_of_dvd h36
  exact dvd_trans (by norm_num : 4 ∣ 12) h12

/-- Pomerance's sufficient certificate cannot hold at a least hypothetical
counterexample: it forces five, while the descent excludes five there. -/
theorem minimal_unique_fails_criterion {n : ℕ} (h : UniqueTotient n)
    (hmin : ∀ c : ℕ, UniqueTotient c → n ≤ c) :
    ¬ SquareKernelCriterion.Criterion n := by
  intro hcriterion
  have h25 : 5 ^ 2 ∣ n := hcriterion 5 (by norm_num) (by
    simpa using four_dvd_totient_of_unique h)
  have h5not : ¬ 5 ∣ n := fermat_prime_not_dvd_of_minimal_unique h hmin
    (by norm_num : Nat.Prime 5) (by norm_num : 5 = 2 ^ 2 + 1) (by omega)
  exact h5not (dvd_trans (by norm_num : 5 ∣ 5 ^ 2) h25)

/-- If singleton fibers exist, some of them necessarily lie outside the
sufficient-certificate class. No existence of singleton fibers is asserted. -/
theorem exists_unique_outside_criterion (hex : ∃ n : ℕ, UniqueTotient n) :
    ∃ n : ℕ, UniqueTotient n ∧ ¬ SquareKernelCriterion.Criterion n := by
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  apply minimal_unique_fails_criterion (Nat.find_spec hex)
  intro c hc
  exact Nat.find_min' hex hc

/-- The exponent-one predecessor case explains why the same proof cannot
remove the prime three: its exceptional companion lifts to the original. -/
theorem three_boundary_totient (d : ℕ) (h3 : ¬ 3 ∣ d) :
    (6 * d).totient = (4 * d).totient := by
  have h3' : ¬ 3 ∣ 2 * d := by
    intro hd
    exact ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 3)).mp hd).elim
      (by norm_num) h3
  rw [show 6 * d = 3 * (2 * d) by ring,
    show 4 * d = 2 * (2 * d) by ring,
    Nat.totient_mul_of_prime_of_not_dvd (by norm_num : Nat.Prime 3) h3',
    Nat.totient_mul_of_prime_of_dvd Nat.prime_two (dvd_mul_right _ _)]

theorem three_boundary_lift (d a : ℕ) :
    2 * (3 ^ a * (6 * d)) = 3 ^ (a + 1) * (4 * d) := by ring

end Contribution.CarmichaelTotient.FermatDescent

namespace Contribution.CarmichaelTotient.InverseTotient

open Finset

/-- Every prime divisor occurs at least twice. Positivity is stated separately. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

private lemma predecessor_product_pos {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) : 0 < ∏ p ∈ s, (p - 1) := by
  apply Finset.prod_pos
  intro p hp
  have := (hs p hp).two_le
  omega

private lemma same_support {n m : ℕ} (hφ : n.totient = m.totient)
    (hs : n.primeFactors = m.primeFactors) : n = m := by
  have hn := Nat.totient_mul_prod_primeFactors n
  have hm := Nat.totient_mul_prod_primeFactors m
  rw [hφ, hs] at hn
  apply Nat.eq_of_mul_eq_mul_right
    (predecessor_product_pos fun p hp => Nat.prime_of_mem_primeFactors hp)
  exact hn.symm.trans hm

private lemma prime_dvd_prod_exists {s : Finset ℕ} {f : ℕ → ℕ}
    {p : ℕ} (hp : p.Prime) (hd : p ∣ ∏ q ∈ s, f q) :
    ∃ q ∈ s, p ∣ f q := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at hd
    exact (hp.not_dvd_one hd).elim
  | @insert q s hqs ih =>
    rw [Finset.prod_insert hqs] at hd
    rcases hp.dvd_mul.mp hd with hq | hs
    · exact ⟨q, Finset.mem_insert_self q s, hq⟩
    · obtain ⟨r, hrs, hpr⟩ := ih hs
      exact ⟨r, Finset.mem_insert_of_mem hrs, hpr⟩

private lemma prime_sq_not_dvd_prime_prod {s : Finset ℕ}
    (hs : ∀ q ∈ s, q.Prime) {p : ℕ} (hp : p.Prime) :
    ¬ p ^ 2 ∣ ∏ q ∈ s, q := by
  intro hsq
  have hd : p ∣ ∏ q ∈ s, q := Nat.dvd_of_pow_dvd (by decide) hsq
  obtain ⟨q, hqs, hpq⟩ := prime_dvd_prod_exists hp hd
  have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).mp hpq
  have hps : p ∈ s := hpqeq ▸ hqs
  have hprod : (∏ q ∈ s, q) = p * ∏ q ∈ s.erase p, q :=
    (Finset.mul_prod_erase s (fun q : ℕ => q) hps).symm
  rw [hprod, pow_two] at hsq
  have hd' : p ∣ ∏ q ∈ s.erase p, q := Nat.dvd_of_mul_dvd_mul_left hp.pos hsq
  obtain ⟨q, hqs, hpq⟩ := prime_dvd_prod_exists hp hd'
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (hs q (Finset.mem_of_mem_erase hqs))).mp hpq
  exact (Finset.ne_of_mem_erase hqs) heq.symm

/-- Euler's product after cancelling the common prime support. -/
theorem support_difference_identity {n m : ℕ} (hφ : n.totient = m.totient) :
    n * (∏ p ∈ n.primeFactors \ m.primeFactors, (p - 1)) *
        (∏ p ∈ m.primeFactors \ n.primeFactors, p) =
      m * (∏ p ∈ m.primeFactors \ n.primeFactors, (p - 1)) *
        (∏ p ∈ n.primeFactors \ m.primeFactors, p) := by
  let C := n.primeFactors ∩ m.primeFactors
  have hn := Nat.totient_mul_prod_primeFactors n
  have hm := Nat.totient_mul_prod_primeFactors m
  have hnl (f : ℕ → ℕ) :
      (∏ p ∈ n.primeFactors \ m.primeFactors, f p) * (∏ p ∈ C, f p) =
        ∏ p ∈ n.primeFactors, f p := by
    simpa only [C, Finset.sdiff_inter_self_left] using
      (Finset.prod_sdiff (f := f) (Finset.inter_subset_left
        (s₁ := n.primeFactors) (s₂ := m.primeFactors)))
  have hml (f : ℕ → ℕ) :
      (∏ p ∈ m.primeFactors \ n.primeFactors, f p) * (∏ p ∈ C, f p) =
        ∏ p ∈ m.primeFactors, f p := by
    simpa only [C, Finset.sdiff_inter_self_right] using
      (Finset.prod_sdiff (f := f) (Finset.inter_subset_right
        (s₁ := n.primeFactors) (s₂ := m.primeFactors)))
  rw [← hnl (fun p => p), ← hnl (fun p => p - 1)] at hn
  rw [← hml (fun p => p), ← hml (fun p => p - 1)] at hm
  apply Nat.eq_of_mul_eq_mul_right
    (predecessor_product_pos (s := C) fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hp).1)
  calc
    _ = (n * ((∏ p ∈ n.primeFactors \ m.primeFactors, (p - 1)) *
          (∏ p ∈ C, (p - 1)))) * (∏ p ∈ m.primeFactors \ n.primeFactors, p) := by ring
    _ = (n.totient * ((∏ p ∈ n.primeFactors \ m.primeFactors, p) *
          (∏ p ∈ C, p))) * (∏ p ∈ m.primeFactors \ n.primeFactors, p) := by rw [hn]
    _ = (m.totient * ((∏ p ∈ m.primeFactors \ n.primeFactors, p) *
          (∏ p ∈ C, p))) * (∏ p ∈ n.primeFactors \ m.primeFactors, p) := by rw [hφ]; ring
    _ = (m * ((∏ p ∈ m.primeFactors \ n.primeFactors, (p - 1)) *
          (∏ p ∈ C, (p - 1)))) * (∏ p ∈ n.primeFactors \ m.primeFactors, p) := by rw [hm]
    _ = _ := by ring

/-- A largest prime in the difference of two equal-totient supports
cannot occur squared on the side where it appears. -/
theorem largest_missing_prime_not_squared {n m r : ℕ} (hm : 0 < m)
    (hφ : n.totient = m.totient)
    (hr : r ∈ n.primeFactors \ m.primeFactors)
    (hmax : ∀ q ∈ m.primeFactors \ n.primeFactors, q ≤ r) : ¬ r ^ 2 ∣ n := by
  have hrn := (Finset.mem_sdiff.mp hr).1
  have hrm := (Finset.mem_sdiff.mp hr).2
  have hp : r.Prime := Nat.prime_of_mem_primeFactors hrn
  have hnotm : ¬ r ∣ m := by
    intro hd
    exact hrm (Nat.mem_primeFactors.mpr ⟨hp, hd, hm.ne'⟩)
  have hnotpred : ¬ r ∣ ∏ q ∈ m.primeFactors \ n.primeFactors, (q - 1) := by
    intro hd
    obtain ⟨q, hq, hrq⟩ := prime_dvd_prod_exists hp hd
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
    have hqpos : 0 < q - 1 := by have := hqp.two_le; omega
    have hle := hmax q hq
    have hdle := Nat.le_of_dvd hqpos hrq
    omega
  have hcop : (r ^ 2).Coprime
      (m * ∏ q ∈ m.primeFactors \ n.primeFactors, (q - 1)) := by
    apply Nat.Coprime.pow_left
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    rcases hp.dvd_mul.mp hd with h | h
    · exact hnotm h
    · exact hnotpred h
  intro hsq
  have hdiv : r ^ 2 ∣
      (m * ∏ q ∈ m.primeFactors \ n.primeFactors, (q - 1)) *
        (∏ q ∈ n.primeFactors \ m.primeFactors, q) := by
    rw [← support_difference_identity hφ]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hsq _) _
  exact prime_sq_not_dvd_prime_prod
    (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1) hp
    (hcop.dvd_of_dvd_mul_left hdiv)

/-- Euler's totient is injective on positive powerful (squarefull) integers. -/
theorem totient_injective_on_powerful {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hpn : Powerful n) (hpm : Powerful m) (hφ : n.totient = m.totient) : n = m := by
  by_contra hne
  have hns : n.primeFactors ≠ m.primeFactors := by
    intro hs
    exact hne (same_support hφ hs)
  let D := (n.primeFactors \ m.primeFactors) ∪ (m.primeFactors \ n.primeFactors)
  have hD : D.Nonempty := by
    by_contra he
    have he' : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    apply hns
    apply Finset.Subset.antisymm
    · intro p hp
      by_contra hpm
      have : p ∈ D := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp, hpm⟩)
      simp [he'] at this
    · intro p hp
      by_contra hpn
      have : p ∈ D := Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, hpn⟩)
      simp [he'] at this
  let r := D.max' hD
  have hr : r ∈ D := Finset.max'_mem D hD
  rcases Finset.mem_union.mp hr with hrn | hrm
  · have hmax : ∀ q ∈ m.primeFactors \ n.primeFactors, q ≤ r := by
      intro q hq
      exact Finset.le_max' D q (Finset.mem_union_right _ hq)
    exact largest_missing_prime_not_squared hm hφ hrn hmax
      (hpn r (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hrn).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hrn).1))
  · have hmax : ∀ q ∈ n.primeFactors \ m.primeFactors, q ≤ r := by
      intro q hq
      exact Finset.le_max' D q (Finset.mem_union_left _ hq)
    exact largest_missing_prime_not_squared hn hφ.symm hrm hmax
      (hpm r (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hrm).1)
        (Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hrm).1))

end Contribution.CarmichaelTotient.InverseTotient

namespace Contribution.CarmichaelTotient.OddDescent

/-- If a prime's predecessor accounts for the entire even part of a totient,
the remaining odd quotient must be a power of that prime whenever the prime
occurs in a preimage. This obstructs arbitrary fixed-totient normalization. -/
theorem odd_quotient_is_prime_power {p b t : ℕ} (hp : p.Prime)
    (hb : 0 < b) (hpb : p ∣ b) (ht : Odd t)
    (hphi : b.totient = (p - 1) * t) : ∃ a : ℕ, t = p ^ a := by
  obtain ⟨a, c, hpc, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' p hp.ne_one
  cases a with
  | zero =>
    simp only [pow_zero, one_mul] at heq
    exact (hpc (heq ▸ hpb)).elim
  | succ a =>
    have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
    have hprod : p ^ a * c.totient = t := by
      apply Nat.eq_of_mul_eq_mul_left hpredpos
      calc
        (p - 1) * (p ^ a * c.totient) =
            (p ^ (a + 1) * c).totient := by
          rw [Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpc).pow_left _),
            Nat.totient_prime_pow_succ hp]
          ring
        _ = (p - 1) * t := by rw [← heq, hphi]
    have hoddprod : Odd (p ^ a * c.totient) := by rw [hprod]; exact ht
    have hoddphi : Odd c.totient := (Nat.odd_mul.mp hoddprod).2
    have hone : c.totient = 1 := Nat.odd_totient_iff_eq_one.mp hoddphi
    exact ⟨a, by simpa [hone] using hprod.symm⟩

/-- An unbounded family of attained totients has no preimage containing five,
although the predecessor of five divides every value in the family. -/
theorem five_not_dvd_of_totient_four_times_three_power (k : ℕ) {b : ℕ}
    (hphi : b.totient = 4 * 3 ^ (k + 1)) : ¬ 5 ∣ b := by
  intro h5
  have hb : 0 < b := Nat.totient_pos.mp (by rw [hphi]; positivity)
  obtain ⟨a, ha⟩ := odd_quotient_is_prime_power (by norm_num : Nat.Prime 5)
    hb h5 ((show Odd 3 from ⟨1, rfl⟩).pow) (by simpa using hphi)
  have h3 : 3 ∣ 5 ^ a := by
    rw [← ha]
    exact dvd_pow_self 3 (by omega)
  have h35 := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3)) h3
  norm_num at h35

theorem attained_four_times_three_power (k : ℕ) :
    (4 * 3 ^ (k + 2)).totient = 4 * 3 ^ (k + 1) := by
  have h4 : Nat.totient 4 = 2 := by
    exact Nat.totient_prime_pow_succ Nat.prime_two 1
  rw [Nat.totient_mul ((by norm_num : Nat.Coprime 4 3).pow_right _), h4]
  rw [show k + 2 = (k + 1) + 1 by omega, Nat.totient_prime_pow_succ
    (by norm_num : Nat.Prime 3)]
  ring

/-- Removing a whole prime power preserves uniqueness if its predecessor
does not divide the cofactor's totient. No normalization hypothesis is used. -/
theorem unique_cofactor_of_predecessor_not_dvd {p a c : ℕ} (hp : p.Prime)
    (hpc : ¬ p ∣ c) (h : UniqueTotient (p ^ (a + 1) * c))
    (hpred : ¬ p - 1 ∣ c.totient) : UniqueTotient c := by
  have hc : 0 < c := Nat.pos_of_mul_pos_left h.1
  refine ⟨hc, ?_⟩
  intro b hb
  by_cases hpb : p ∣ b
  · have hdiv := Nat.totient_dvd_of_dvd hpb
    rw [Nat.totient_prime hp, hb] at hdiv
    exact (hpred hdiv).elim
  · have hphi : (p ^ (a + 1) * b).totient =
        (p ^ (a + 1) * c).totient := by
      rw [Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpb).pow_left _),
        Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpc).pow_left _), hb]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) (h.2 _ hphi)

/-- Consequently, a least singleton input must duplicate every prime's
predecessor in the totient of the complementary prime-power-free cofactor. -/
theorem predecessor_dvd_cofactor_totient_of_minimal_unique {p a c : ℕ}
    (hp : p.Prime) (hpc : ¬ p ∣ c) (h : UniqueTotient (p ^ (a + 1) * c))
    (hmin : ∀ b : ℕ, UniqueTotient b → p ^ (a + 1) * c ≤ b) :
    p - 1 ∣ c.totient := by
  by_contra hpred
  have hc := unique_cofactor_of_predecessor_not_dvd hp hpc h hpred
  have hle := hmin c hc
  have hppow : 1 < p ^ (a + 1) := one_lt_pow₀ hp.one_lt (by omega)
  nlinarith [hc.1]

/-- A least singleton has each predecessor square dividing its totient. -/
theorem predecessor_sq_dvd_totient_of_minimal_unique {n p : ℕ}
    (h : UniqueTotient n) (hmin : ∀ c : ℕ, UniqueTotient c → n ≤ c)
    (hp : p.Prime) (hpn : p ∣ n) : (p - 1) ^ 2 ∣ n.totient := by
  obtain ⟨a, c, hpc, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd h.1.ne' p hp.ne_one
  cases a with
  | zero =>
    simp only [pow_zero, one_mul] at heq
    exact (hpc (heq ▸ hpn)).elim
  | succ a =>
    subst n
    obtain ⟨t, ht⟩ := predecessor_dvd_cofactor_totient_of_minimal_unique hp hpc h hmin
    refine ⟨p ^ a * t, ?_⟩
    rw [Nat.totient_mul ((hp.coprime_iff_not_dvd.mpr hpc).pow_left _),
      Nat.totient_prime_pow_succ hp, ht]
    ring

/-- A symbolic boundary to odd-prime descent: the cofactor has an actual
different preimage already containing the complete predecessor support. -/
theorem canonical_boundary_collision {p u : ℕ} (hp : p.Prime) (hpu : ¬ p ∣ u) :
    p * ((p - 1) * u) ≠ (p - 1) ^ 2 * u ∧
      (p * ((p - 1) * u)).totient = ((p - 1) ^ 2 * u).totient := by
  have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
  have hpredlt : p - 1 < p := by omega
  have hu : 0 < u := Nat.pos_of_ne_zero (by
    intro hz
    exact hpu (hz ▸ dvd_zero p))
  have hpredu : p - 1 ∣ (p - 1) * u := dvd_mul_right _ _
  have hnotpred : ¬ p ∣ p - 1 := Nat.not_dvd_of_pos_of_lt hpredpos hpredlt
  have hnot : ¬ p ∣ (p - 1) * u := by
    intro hd
    exact (hp.dvd_mul.mp hd).elim hnotpred hpu
  constructor
  · have hlt := Nat.mul_lt_mul_of_pos_right hpredlt (Nat.mul_pos hpredpos hu)
    have hid : (p - 1) ^ 2 * u = (p - 1) * ((p - 1) * u) := by ring
    rw [hid]
    exact (Nat.ne_of_lt hlt).symm
  · have heq := totient_prime_mul_eq_pred_mul hp hnot hpredu
    simpa only [pow_two, mul_assoc] using heq

/-- The normalized lift of the boundary collision is precisely the original
input. Support normalization alone therefore cannot prove a contradiction. -/
theorem canonical_boundary_lift (p a u : ℕ) :
    (p - 1) * (p ^ a * (p * ((p - 1) * u))) =
      p ^ (a + 1) * ((p - 1) ^ 2 * u) := by ring

/-- For p congruent to three modulo four and odd u, the boundary cofactor
lies in the already reduced residue class four modulo eight. -/
theorem canonical_boundary_four_mod_eight (s t : ℕ) :
    ((4 * s + 2) ^ 2 * (2 * t + 1)) % 8 = 4 := by
  have heq : (4 * s + 2) ^ 2 * (2 * t + 1) =
      8 * ((2 * s * s + 2 * s) * (2 * t + 1) + t) + 4 := by ring
  rw [heq]
  omega

end Contribution.CarmichaelTotient.OddDescent

namespace Contribution.CarmichaelTotient.PrimeReplacement

/-- The prime 11 can be removed from the 44-block when 5 and 11 are absent
from the cofactor; its replacement introduces 5 with exponent two. -/
theorem eleven_block_collision {a : ℕ} (h5 : ¬ 5 ∣ a) (h11 : ¬ 11 ∣ a) :
    (50 * a).totient = (44 * a).totient := by
  have h5two : ¬ 5 ∣ 2 * a := by
    intro h
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp h with h | h
    · norm_num at h
    · exact h5 h
  have h11four : ¬ 11 ∣ 4 * a := by
    intro h
    rcases (show Nat.Prime 11 by norm_num).dvd_mul.mp h with h | h
    · norm_num at h
    · exact h11 h
  have hc : (25 : ℕ).Coprime (2 * a) := by
    have hc5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5two
    simpa using hc5.pow_left 2
  calc
    (50 * a).totient = (25 * (2 * a)).totient := by congr 1; ring
    _ = 20 * (2 * a).totient := by rw [Nat.totient_mul hc, show Nat.totient 25 = 20 by decide]
    _ = 10 * (4 * a).totient := by
      have hscale := Nat.totient_mul_of_prime_of_dvd (by norm_num : Nat.Prime 2)
        (dvd_mul_right 2 a)
      have heq : (4 * a).totient = 2 * (2 * a).totient := by
        simpa only [show 2 * (2 * a) = 4 * a by ring] using hscale
      rw [heq]
      ring
    _ = (11 * (4 * a)).totient := by
      rw [Nat.totient_mul_of_prime_of_not_dvd (by norm_num : Nat.Prime 11) h11four]
    _ = (44 * a).totient := by congr 1; ring

/-- In a singleton totient fiber, every factor 11 must occur at least twice.
Unlike predecessor-support forcing, this also covers the case 5 does not divide n. -/
theorem eleven_sq_dvd_of_unique {n : ℕ} (h : UniqueTotient n)
    (h11 : 11 ∣ n) : 11 ^ 2 ∣ n := by
  by_cases h5 : 5 ∣ n
  · apply Klee.prime_sq_dvd_of_prime_and_pred_support h.1 h.2
      (by norm_num : Nat.Prime 11) h11
    intro q hq hqd
    have hqd' : q ∣ 2 * 5 := by simpa using hqd
    rcases hq.dvd_mul.mp hqd' with hq2 | hq5
    · have heq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hq2
      subst q
      exact dvd_trans (by norm_num : 2 ∣ 4) (four_dvd_of_unique h.1 h.2)
    · have heq : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hq5
      simpa only [heq] using h5
  · by_contra hsq
    have h4 : 4 ∣ n := four_dvd_of_unique h.1 h.2
    have h44 : 44 ∣ n := by
      have hc : Nat.Coprime 4 11 := by norm_num
      simpa using hc.mul_dvd_of_dvd_of_dvd h4 h11
    obtain ⟨a, rfl⟩ := h44
    have h5a : ¬ 5 ∣ a := fun ha => h5 (dvd_mul_of_dvd_right ha 44)
    have h11a : ¬ 11 ∣ a := by
      intro ha
      obtain ⟨b, rfl⟩ := ha
      apply hsq
      use 4 * b
      ring
    have heq := h.2 (50 * a) (eleven_block_collision h5a h11a)
    have ha : 0 < a := Nat.pos_of_mul_pos_left h.1
    omega

end Contribution.CarmichaelTotient.PrimeReplacement


namespace Contribution.CarmichaelTotient.PrimeReplacement

/-- Replacing a prime whose predecessor uses only 2 and 5 by a power of 5,
while retaining a positive power of 2, preserves the totient of the block. -/
theorem two_five_block_collision {a p s k : ℕ} (hp : p.Prime)
    (hpred : p - 1 = 2 ^ (s + 1) * 5 ^ k)
    (h5 : ¬ 5 ∣ a) (hpa : ¬ p ∣ a) (hp2 : p ≠ 2) :
    ((2 ^ (s + 1) * 5 ^ (k + 1)) * a).totient = (4 * p * a).totient := by
  have h5pow : ¬ 5 ∣ 2 ^ (s + 1) * a := by
    intro h
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp h with h | h
    · have := (show Nat.Prime 5 by norm_num).dvd_of_dvd_pow h
      norm_num at this
    · exact h5 h
  have hpfour : ¬ p ∣ 4 * a := by
    intro h
    rcases hp.dvd_mul.mp h with h | h
    · have hp4 : p ∣ 2 ^ 2 := by simpa using h
      have hp2' := hp.dvd_of_dvd_pow hp4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2')
    · exact hpa h
  have hc : (5 ^ (k + 1)).Coprime (2 ^ (s + 1) * a) :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5pow).pow_left _
  have hscale : (2 ^ (s + 1) * a).totient = 2 ^ s * (2 * a).totient := by
    have hs := GlobalStrongerForcing.totient_mul_of_prime_support
      (a := 2 * a) (k := 2 ^ s) (by
        intro q hq hqd
        have hq2 := hq.dvd_of_dvd_pow hqd
        have heq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hq2
        simpa only [heq] using dvd_mul_right 2 a)
    simpa only [pow_succ, mul_assoc] using hs
  have hscale4 : (4 * a).totient = 2 * (2 * a).totient := by
    have hs := Nat.totient_mul_of_prime_of_dvd (by norm_num : Nat.Prime 2)
      (dvd_mul_right 2 a)
    simpa only [show 2 * (2 * a) = 4 * a by ring] using hs
  calc
    ((2 ^ (s + 1) * 5 ^ (k + 1)) * a).totient =
        (5 ^ (k + 1) * (2 ^ (s + 1) * a)).totient := by congr 1; ring
    _ = (5 ^ (k + 1)).totient * (2 ^ (s + 1) * a).totient := Nat.totient_mul hc
    _ = (5 ^ k * 4) * (2 ^ s * (2 * a).totient) := by
      rw [hscale, Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by omega : 0 < k + 1)]
      simp
    _ = (p - 1) * (4 * a).totient := by rw [hpred, hscale4, pow_succ]; ring
    _ = (p * (4 * a)).totient := by
      rw [Nat.totient_mul_of_prime_of_not_dvd hp hpfour]
    _ = (4 * p * a).totient := by congr 1; ring

/-- Every prime of the form 1 + 2^(s+1)*5^k that divides a singleton
preimage must divide it to at least the second power. -/
theorem two_five_prime_sq_dvd_of_unique {n p s k : ℕ} (h : UniqueTotient n)
    (hp : p.Prime) (hpred : p - 1 = 2 ^ (s + 1) * 5 ^ k)
    (hpn : p ∣ n) : p ^ 2 ∣ n := by
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have heven : 2 ∣ 2 ^ (s + 1) * 5 ^ k :=
      dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : s + 1 ≠ 0)) _
    rw [← hpred] at heven
    norm_num at heven
  by_cases h5 : 5 ∣ n
  · apply Klee.prime_sq_dvd_of_prime_and_pred_support h.1 h.2 hp hpn
    intro q hq hqd
    rw [hpred] at hqd
    rcases hq.dvd_mul.mp hqd with hq2 | hq5
    · have heq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp
        (hq.dvd_of_dvd_pow hq2)
      subst q
      exact dvd_trans (by norm_num : 2 ∣ 4) (four_dvd_of_unique h.1 h.2)
    · have heq : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp
        (hq.dvd_of_dvd_pow hq5)
      simpa only [heq] using h5
  · by_contra hsq
    have hp5 : p ≠ 5 := fun heq => h5 (heq ▸ hpn)
    have h4 : 4 ∣ n := four_dvd_of_unique h.1 h.2
    have h4p : 4 * p ∣ n := by
      have hc2 : (2 : ℕ).Coprime p :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by
          intro hd
          exact hp2 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hd).symm)
      have hc : (4 : ℕ).Coprime p := by simpa using hc2.pow_left 2
      exact hc.mul_dvd_of_dvd_of_dvd h4 hpn
    obtain ⟨a, rfl⟩ := h4p
    have h5a : ¬ 5 ∣ a := fun ha => h5 (dvd_mul_of_dvd_right ha (4 * p))
    have hpa : ¬ p ∣ a := by
      intro ha
      obtain ⟨b, rfl⟩ := ha
      apply hsq
      use 4 * b
      ring
    have heq := h.2 ((2 ^ (s + 1) * 5 ^ (k + 1)) * a)
      (two_five_block_collision hp hpred h5a hpa hp2)
    have hpdvd : p ∣ (2 ^ (s + 1) * 5 ^ (k + 1)) * a := heq ▸ hpn
    rcases hp.dvd_mul.mp hpdvd with hleft | hright
    · rcases hp.dvd_mul.mp hleft with h2 | h5'
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h2))
      · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h5'))
    · exact hpa hright

end Contribution.CarmichaelTotient.PrimeReplacement


namespace Contribution.CarmichaelTotient.PrimeReplacement

/-- A supported multiplier may accompany the missing-prime-5 replacement. -/
theorem missing_five_block_collision {a p k e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpred : p - 1 = 2 * 5 ^ k * e)
    (h5a : ¬ 5 ∣ a) (hpa : ¬ p ∣ a)
    (hse : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ 2 * a) :
    (5 ^ (k + 1) * (e * (2 * a))).totient = (4 * p * a).totient := by
  have h5two : ¬ 5 ∣ 2 * a := by
    intro hd
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp hd with hd | hd
    · norm_num at hd
    · exact h5a hd
  have h5e : ¬ 5 ∣ e := fun hd => h5two (hse 5 (by norm_num) hd)
  have h5part : ¬ 5 ∣ e * (2 * a) := by
    intro hd
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp hd with hd | hd
    · exact h5e hd
    · exact h5two hd
  have hc : (5 ^ (k + 1)).Coprime (e * (2 * a)) :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5part).pow_left _
  have hpfour : ¬ p ∣ 4 * a := by
    intro hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · have hp4 : p ∣ 2 ^ 2 := by simpa using hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow hp4))
    · exact hpa hd
  have hscale4 : (4 * a).totient = 2 * (2 * a).totient := by
    have hs := Nat.totient_mul_of_prime_of_dvd (by norm_num : Nat.Prime 2)
      (dvd_mul_right 2 a)
    simpa only [show 2 * (2 * a) = 4 * a by ring] using hs
  calc
    (5 ^ (k + 1) * (e * (2 * a))).totient =
        (5 ^ (k + 1)).totient * (e * (2 * a)).totient := Nat.totient_mul hc
    _ = (5 ^ k * 4) * (e * (2 * a).totient) := by
      rw [GlobalStrongerForcing.totient_mul_of_prime_support hse,
        Nat.totient_prime_pow (by norm_num : Nat.Prime 5) (by omega : 0 < k + 1)]
      simp
    _ = (p - 1) * (4 * a).totient := by rw [hpred, hscale4]; ring
    _ = (p * (4 * a)).totient := by
      rw [Nat.totient_mul_of_prime_of_not_dvd hp hpfour]
    _ = (4 * p * a).totient := by congr 1; ring

/-- Predecessor-support forcing remains valid when the prime 5 is allowed
as one missing predecessor prime. No assumption that 5 divides n is needed. -/
theorem prime_sq_dvd_of_pred_support_except_five {n p : ℕ} (h : UniqueTotient n)
    (hp : p.Prime) (hpn : p ∣ n)
    (hs : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q = 5 ∨ q ∣ n) : p ^ 2 ∣ n := by
  by_cases hp2 : p = 2
  · subst p
    simpa using four_dvd_of_unique h.1 h.2
  by_cases h5 : 5 ∣ n
  · apply Klee.prime_sq_dvd_of_prime_and_pred_support h.1 h.2 hp hpn
    intro q hq hqd
    rcases hs q hq hqd with hq5 | hqn
    · simpa only [hq5] using h5
    · exact hqn
  · by_contra hsq
    have hp5 : p ≠ 5 := fun heq => h5 (heq ▸ hpn)
    have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
    obtain ⟨d, hd⟩ := (hp.even_sub_one hp2).two_dvd
    have hd0 : d ≠ 0 := by intro heq; rw [heq, mul_zero] at hd; omega
    obtain ⟨k, e, he5, hde⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 5 (by decide)
    have hpred : p - 1 = 2 * 5 ^ k * e := by rw [hd, hde]; ring
    have h4 : 4 ∣ n := four_dvd_of_unique h.1 h.2
    have h4p : 4 * p ∣ n := by
      have hc2 : (2 : ℕ).Coprime p :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr (by
          intro hd'
          exact hp2 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp hd').symm)
      have hc : (4 : ℕ).Coprime p := by simpa using hc2.pow_left 2
      exact hc.mul_dvd_of_dvd_of_dvd h4 hpn
    obtain ⟨a, rfl⟩ := h4p
    have h5a : ¬ 5 ∣ a := fun ha => h5 (dvd_mul_of_dvd_right ha (4 * p))
    have hpa : ¬ p ∣ a := by
      intro ha
      obtain ⟨b, rfl⟩ := ha
      apply hsq
      use 4 * b
      ring
    have hpe : ¬ p ∣ e := by
      intro hd'
      have hppred : p ∣ p - 1 := by rw [hpred]; exact dvd_mul_of_dvd_right hd' _
      have := Nat.le_of_dvd hpredpos hppred
      omega
    have hse : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ 2 * a := by
      intro q hq hqe
      have hqpred : q ∣ p - 1 := by rw [hpred]; exact dvd_mul_of_dvd_right hqe _
      have hqnep : q ≠ p := by
        intro heq
        subst q
        exact hpe hqe
      have hqn : q ∣ 4 * p * a := by
        rcases hs q hq hqpred with hq5 | hqn
        · subst q
          exact False.elim (he5 hqe)
        · exact hqn
      rcases hq.dvd_mul.mp hqn with hq4p | hqa
      · rcases hq.dvd_mul.mp hq4p with hq4 | hqp
        · have hq4' : q ∣ 2 ^ 2 := by simpa using hq4
          have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp
            (hq.dvd_of_dvd_pow hq4')
          simpa only [hq2] using dvd_mul_right 2 a
        · exact False.elim (hqnep ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp))
      · exact dvd_mul_of_dvd_right hqa 2
    have heq := h.2 (5 ^ (k + 1) * (e * (2 * a)))
      (missing_five_block_collision hp hp2 hpred h5a hpa hse)
    have hpdvd : p ∣ 5 ^ (k + 1) * (e * (2 * a)) := heq ▸ hpn
    rcases hp.dvd_mul.mp hpdvd with hp5pow | hprest
    · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow hp5pow))
    · rcases hp.dvd_mul.mp hprest with hpe' | hp2a
      · exact hpe hpe'
      · rcases hp.dvd_mul.mp hp2a with hp2' | hpa'
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp2')
        · exact hpa hpa'

end Contribution.CarmichaelTotient.PrimeReplacement


namespace Contribution.CarmichaelTotient.PrimeReplacement

/-- Carmichael--Klee forcing with 5 permitted as a missing predecessor prime.
This allows a unitary block d whose totient introduces 5 to generate a new
prime square, even when 5 does not divide the singleton preimage. -/
theorem carmichael_klee_support_except_five {n d e a p : ℕ} (h : UniqueTotient n)
    (hdecomp : n = d * (e * a)) (hcop : d.Coprime (e * a))
    (hsupporte : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ a)
    (hsupportphi : ∀ q : ℕ, q.Prime → q ∣ d.totient → q = 5 ∨ q ∣ n)
    (hp : p.Prime) (hprime : p = 1 + e * d.totient) : p ^ 2 ∣ n := by
  have hpred : p - 1 = e * d.totient := by omega
  have hen : e ∣ n := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_right e a) d
  have hpredsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q = 5 ∨ q ∣ n := by
    intro q hq hqd
    rw [hpred] at hqd
    rcases hq.dvd_mul.mp hqd with hqe | hqphi
    · exact Or.inr (dvd_trans hqe hen)
    · exact hsupportphi q hq hqphi
  apply prime_sq_dvd_of_pred_support_except_five h hp _ hpredsupport
  by_contra hpn
  have han : a ∣ n := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_left a e) d
  have hpa : ¬ p ∣ a := fun ha => hpn (dvd_trans ha han)
  have hphi : (p * a).totient = n.totient := by
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa, hpred, hdecomp,
      Nat.totient_mul hcop, GlobalStrongerForcing.totient_mul_of_prime_support hsupporte]
    ring
  have heq := h.2 (p * a) hphi
  exact hpn (heq ▸ dvd_mul_right p a)

end Contribution.CarmichaelTotient.PrimeReplacement

namespace Contribution.CarmichaelTotient.InverseTotient.FiniteRatios

open Finset

private theorem totient_mul_of_dvd {a k : ℕ} (hk : 0 < k) (hka : k ∣ a) :
    (k * a).totient = k * a.totient := by
  have h := Nat.totient_gcd_mul_totient_mul k a
  rw [Nat.gcd_eq_left hka] at h
  have ht : 0 < k.totient := Nat.totient_pos.mpr hk
  nlinarith

/-- A fixed nonidentity rational multiplier cannot preserve totients on
any positive multiple of the square of a common multiple of its two entries. -/
theorem common_multiple_square_obstruction {M a b k : ℕ}
    (hM : 0 < M) (hk : 0 < k) (ha : 0 < a) (hb : 0 < b)
    (haM : a ∣ M) (hbM : b ∣ M) (hne : a ≠ b) :
    (a * (M ^ 2 * k / b)).totient ≠ (M ^ 2 * k).totient := by
  let c := (M / b) * M * k
  have hbc : b * c = M ^ 2 * k := by
    calc
      b * c = (b * (M / b)) * M * k := by dsimp [c]; ring
      _ = M * M * k := by rw [Nat.mul_div_cancel' hbM]
      _ = M ^ 2 * k := by ring
  have hc : 0 < c := by
    have hpos : 0 < M ^ 2 * k := Nat.mul_pos (Nat.pow_pos hM) hk
    rw [← hbc] at hpos
    exact Nat.pos_of_mul_pos_left hpos
  have hac : a ∣ c :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right haM (M / b)) k
  have hbcdiv : b ∣ c :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hbM (M / b)) k
  have hdiv : M ^ 2 * k / b = c := by
    rw [← hbc, Nat.mul_div_cancel_left c hb]
  intro h
  rw [hdiv, ← hbc, totient_mul_of_dvd ha hac,
    totient_mul_of_dvd hb hbcdiv] at h
  exact hne (Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hc) h)

/-- Every finite menu of distinct positive rational multipliers misses
every positive element of one fixed arithmetic progression. All displayed
quotients are integral, since the chosen common multiple includes every
denominator. No unproved collision-existence assumption is used. -/
theorem finite_menu_misses_progression (s : Finset (ℕ × ℕ))
    (hs : ∀ ab ∈ s, 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1 ≠ ab.2) :
    ∃ M : ℕ, 0 < M ∧ ∀ k : ℕ, 0 < k → ∀ ab ∈ s,
      ab.2 ∣ M ^ 2 * k ∧
      (ab.1 * (M ^ 2 * k / ab.2)).totient ≠ (M ^ 2 * k).totient := by
  let M := ∏ ab ∈ s, ab.1 * ab.2
  have hM : 0 < M := by
    apply Finset.prod_pos
    intro ab hab
    exact Nat.mul_pos (hs ab hab).1 (hs ab hab).2.1
  refine ⟨M, hM, ?_⟩
  intro k hk ab hab
  have habM : ab.1 * ab.2 ∣ M := Finset.dvd_prod_of_mem (fun ab => ab.1 * ab.2) hab
  have haM : ab.1 ∣ M := dvd_trans (dvd_mul_right ab.1 ab.2) habM
  have hbM : ab.2 ∣ M := dvd_trans (dvd_mul_left ab.2 ab.1) habM
  constructor
  · exact dvd_mul_of_dvd_left (dvd_trans hbM (dvd_pow_self M (by decide))) k
  · exact common_multiple_square_obstruction hM hk (hs ab hab).1
      (hs ab hab).2.1 haM hbM (hs ab hab).2.2

end Contribution.CarmichaelTotient.InverseTotient.FiniteRatios

namespace Contribution.CarmichaelTotient.InverseTotient.FiniteRatios

open Finset

private theorem equal_of_subset_and_missing_squares {n m : ℕ}
    (hm : 0 < m) (hφ : n.totient = m.totient)
    (hsub : m.primeFactors ⊆ n.primeFactors)
    (hsq : ∀ p ∈ n.primeFactors \ m.primeFactors, p ^ 2 ∣ n) : n = m := by
  have hrev : n.primeFactors ⊆ m.primeFactors := by
    intro p hp
    by_contra hpm
    have hd : p ∈ n.primeFactors \ m.primeFactors := Finset.mem_sdiff.mpr ⟨hp, hpm⟩
    apply Contribution.CarmichaelTotient.InverseTotient.largest_missing_prime_not_squared hm hφ hd
      (fun q hq => ((Finset.mem_sdiff.mp hq).2 (hsub (Finset.mem_sdiff.mp hq).1)).elim)
    exact hsq p hd
  have hs := Finset.Subset.antisymm hrev hsub
  have hn := Nat.totient_mul_prod_primeFactors n
  have hm' := Nat.totient_mul_prod_primeFactors m
  rw [hφ, hs] at hn
  have hpos : 0 < ∏ p ∈ m.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos (hn.symm.trans hm')

/-- Once every prime of a fixed numerator and denominator already occurs
squared in the input, their nonidentity ratio cannot preserve its totient. -/
theorem ratio_obstruction_of_prime_squares {n a b : ℕ}
    (hn : 0 < n) (ha : 0 < a) (hne : a ≠ b) (hbn : b ∣ n)
    (hsq : ∀ p : ℕ, p.Prime → p ∣ a * b → p ^ 2 ∣ n) :
    (a * (n / b)).totient ≠ n.totient := by
  let c := n / b
  have hbc : b * c = n := Nat.mul_div_cancel' hbn
  have hc : 0 < c := Nat.pos_of_mul_pos_left (hbc.symm ▸ hn)
  have hm : 0 < a * c := Nat.mul_pos ha hc
  have hsub : (a * c).primeFactors ⊆ n.primeFactors := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpn : p ∣ n := by
      rcases hpp.dvd_mul.mp hpd with hpa | hpc
      · exact Nat.dvd_of_pow_dvd (by decide)
          (hsq p hpp (dvd_mul_of_dvd_left hpa b))
      · rw [← hbc]
        exact dvd_mul_of_dvd_right hpc b
    exact Nat.mem_primeFactors.mpr ⟨hpp, hpn, hn.ne'⟩
  intro hφ
  have heq : n = a * c := equal_of_subset_and_missing_squares hm hφ.symm hsub (by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
    have hpd := Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
    rw [← hbc] at hpd
    rcases hpp.dvd_mul.mp hpd with hpb | hpc
    · exact hsq p hpp (dvd_mul_of_dvd_right hpb a)
    · exact ((Finset.mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr
        ⟨hpp, dvd_mul_of_dvd_right hpc a, hm.ne'⟩)).elim)
  exact hne (Nat.eq_of_mul_eq_mul_right hc (heq.symm.trans hbc.symm))

/-- Any finite fixed-ratio menu misses an arithmetic progression wholly
inside the reduced residue class `n ≡ 4 (mod 8)`. The conclusion explicitly
requires the denominator to divide the input. For ratios in lowest terms,
this is exactly the condition for the rational move to be an integer. -/
theorem finite_menu_misses_four_mod_eight (s : Finset (ℕ × ℕ))
    (hs : ∀ ab ∈ s, 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1 ≠ ab.2) :
    ∃ M : ℕ, 0 < M ∧ Odd M ∧ ∀ k : ℕ,
      (4 * M ^ 2 * (2 * k + 1)) % 8 = 4 ∧
      ∀ ab ∈ s, ab.2 ∣ 4 * M ^ 2 * (2 * k + 1) →
        (ab.1 * (4 * M ^ 2 * (2 * k + 1) / ab.2)).totient ≠
          (4 * M ^ 2 * (2 * k + 1)).totient := by
  let P := ∏ ab ∈ s, ab.1 * ab.2
  have hPpos : 0 < P := by
    apply Finset.prod_pos
    intro ab hab
    exact Nat.mul_pos (hs ab hab).1 (hs ab hab).2.1
  obtain ⟨e, M, hOdd, hP⟩ := Nat.exists_eq_two_pow_mul_odd hPpos.ne'
  have hM : 0 < M := by rcases hOdd with ⟨v, hv⟩; omega
  refine ⟨M, hM, hOdd, ?_⟩
  intro k
  constructor
  · have hOdd' : Odd (M ^ 2 * (2 * k + 1)) :=
      hOdd.pow.mul ⟨k, rfl⟩
    obtain ⟨v, hv⟩ := hOdd'
    rw [mul_assoc, hv]
    omega
  · intro ab hab hb
    have hn : 0 < 4 * M ^ 2 * (2 * k + 1) := by positivity
    apply ratio_obstruction_of_prime_squares hn (hs ab hab).1 (hs ab hab).2.2 hb
    intro p hp hpd
    have habP : ab.1 * ab.2 ∣ P :=
      Finset.dvd_prod_of_mem (fun ab => ab.1 * ab.2) hab
    have hpP : p ∣ 2 ^ e * M := hP ▸ dvd_trans hpd habP
    rcases hp.dvd_mul.mp hpP with hp2 | hpM
    · have hpeq : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp2)
      subst p
      exact dvd_mul_of_dvd_left (dvd_mul_right 4 (M ^ 2)) (2 * k + 1)
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpM 2) 4) (2 * k + 1)

end Contribution.CarmichaelTotient.InverseTotient.FiniteRatios

namespace Contribution.CarmichaelTotient.OddDoubling

/-- All eligible odd primes for the specific totient value `2^32`.
This is an exact divisor/primality certificate, not an integer input scan. -/
theorem eligible_prime_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p - 1 ∣ 2 ^ 32) :
    p = 3 ∨ p = 5 ∨ p = 17 ∨ p = 257 ∨ p = 65537 := by
  obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hform : p = 2 ^ k + 1 := by have := hp.two_le; omega
  subst p
  interval_cases k <;> (try norm_num at hp) <;> (try norm_num at hp2) <;> norm_num

/-- The product of the five eligible odd primes has totient `2^31`. -/
theorem totient_fermat_product : (4294967295 : ℕ).totient = 2 ^ 31 := by
  change (3 * (5 * (17 * (257 * 65537)))).totient = 2 ^ 31
  rw [Nat.totient_mul (by norm_num : Nat.Coprime 3 (5 * (17 * (257 * 65537)))),
    Nat.totient_mul (by norm_num : Nat.Coprime 5 (17 * (257 * 65537))),
    Nat.totient_mul (by norm_num : Nat.Coprime 17 (257 * 65537)),
    Nat.totient_mul (by norm_num : Nat.Coprime 257 65537)]
  rw [Nat.totient_prime (by norm_num : Nat.Prime 3),
    Nat.totient_prime (by norm_num : Nat.Prime 5),
    Nat.totient_prime (by norm_num : Nat.Prime 17),
    Nat.totient_prime (by norm_num : Nat.Prime 257),
    Nat.totient_prime (by norm_num : Nat.Prime 65537)]
  norm_num

/-- An odd preimage of `2^32` would divide the product of the five
eligible odd primes, each occurring at most once. -/
theorem odd_preimage_dvd_fermat_product {n : ℕ} (hn : Odd n)
    (hphi : n.totient = 2 ^ 32) : n ∣ 4294967295 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 4294967295 n).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · subst k
    simp
  have hpn : p ∣ n := Nat.dvd_of_pow_dvd (by omega) hpk
  have hp2 : p ≠ 2 := by
    intro heq
    exact hn.not_two_dvd_nat (heq ▸ hpn)
  have hk1 : k = 1 := by
    by_contra hne
    have h2k : 2 ≤ k := by omega
    have hsq : p ^ 2 ∣ n := dvd_trans (Nat.pow_dvd_pow p h2k) hpk
    have hphi2 : (p ^ 2).totient ∣ n.totient := Nat.totient_dvd_of_dvd hsq
    rw [Nat.totient_prime_pow hp (by norm_num), hphi] at hphi2
    have hpdiv : p ∣ 2 ^ 32 := dvd_trans (by simp) hphi2
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hpdiv)
  have hpred : p - 1 ∣ 2 ^ 32 := by
    simpa only [Nat.totient_prime hp, hphi] using Nat.totient_dvd_of_dvd hpn
  rcases eligible_prime_cases hp hp2 hpred with rfl | rfl | rfl | rfl | rfl <;>
    subst k <;> norm_num

/-- There is no odd integer with totient `2^32`. -/
theorem no_odd_preimage_two_pow_thirty_two {n : ℕ} (hn : Odd n) :
    n.totient ≠ 2 ^ 32 := by
  intro hphi
  have hd := Nat.totient_dvd_of_dvd (odd_preimage_dvd_fermat_product hn hphi)
  rw [hphi, totient_fermat_product] at hd
  norm_num at hd

/-- Totients of odd inputs are not closed under doubling, so that tempting
collision-construction principle cannot prove the global conjecture. -/
theorem odd_doubling_not_universal :
    ¬ (∀ n : ℕ, Odd n → ∃ m : ℕ, Odd m ∧ m.totient = 2 * n.totient) := by
  intro hall
  obtain ⟨m, hm, hphi⟩ := hall 4294967295 (by decide)
  apply no_odd_preimage_two_pow_thirty_two hm
  simpa only [totient_fermat_product, show 2 * 2 ^ 31 = (2 : ℕ) ^ 32 by norm_num]
    using hphi

end Contribution.CarmichaelTotient.OddDoubling
