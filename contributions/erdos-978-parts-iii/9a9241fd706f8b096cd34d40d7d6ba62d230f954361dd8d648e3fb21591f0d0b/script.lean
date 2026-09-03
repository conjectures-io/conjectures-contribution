import FormalConjectures.ErdosProblems.«978»

/-!
# Hensel correspondence and prime-square obstructions for `n ^ 4 + 2`

For every odd prime, reduction modulo `p` is a bijection between roots of
`X ^ 4 + 2` modulo `p ^ 2` and roots modulo `p`. Consequently there are at
most four bad residue classes modulo `p ^ 2`, and at least `p ^ 2 - 4` good
classes.

Every prime-square obstruction must moreover come from a prime congruent to
`1` or `3` modulo `8`. The file packages the periodic bad residue classes as
finite sets and rewrites the exact squarefree predicate using only those two
prime classes.

This is a global local-obstruction reduction, not a proof that squarefree
values occur infinitely often: square divisors from arbitrarily large primes
congruent to `1` or `3` modulo `8` remain uncontrolled.
-/

namespace Contribution.Erdos978PartIIIV2

/-- The square of a prime cannot divide the constant term `2`. -/
lemma prime_sq_not_dvd_two {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ 2 := by
  intro hpdvd
  have hle : p ^ 2 ≤ 2 := Nat.le_of_dvd (by norm_num) hpdvd
  nlinarith [hp.two_le]

/-- The prime `2` never causes a square obstruction. -/
lemma four_not_dvd_fourth_add_two (n : ℕ) : ¬ 4 ∣ n ^ 4 + 2 := by
  intro h
  have hzero : ((n ^ 4 + 2 : ℕ) : ZMod 4) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 4 + 2) 4).mpr h
  have hnever : ∀ x : ZMod 4, x ^ 4 + 2 ≠ 0 := by decide
  apply hnever (n : ZMod 4)
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hzero

/-- If `p ^ 2` divides `n ^ 4 + 2`, quadratic reciprocity forces the odd prime
`p` into one of the classes `1` and `3` modulo `8`. -/
lemma prime_mod_eight_of_sq_dvd_fourth_add_two {p n : ℕ}
    (hp : p.Prime) (hpdvd : p ^ 2 ∣ n ^ 4 + 2) :
    p % 8 = 1 ∨ p % 8 = 3 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact four_not_dvd_fourth_add_two n (by simpa using hpdvd)
  let _ : Fact p.Prime := ⟨hp⟩
  have hp_dvd : p ∣ n ^ 4 + 2 :=
    dvd_trans (dvd_pow_self p (by norm_num)) hpdvd
  have hzero : (n : ZMod p) ^ 4 + 2 = 0 := by
    have hcast : ((n ^ 4 + 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 4 + 2) p).mpr hp_dvd
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hcast
  have hpow : (n : ZMod p) ^ 4 = -2 := by
    exact eq_neg_of_add_eq_zero_left hzero
  have hsquare : IsSquare (-2 : ZMod p) := by
    refine ⟨(n : ZMod p) ^ 2, ?_⟩
    rw [← pow_add]
    norm_num
    exact hpow.symm
  exact (ZMod.exists_sq_eq_neg_two_iff hp2).mp hsquare

/-- Every prime-square divisor of `n ^ 4 + 2` is coprime to `n`. -/
lemma coprime_of_prime_sq_dvd_fourth_add_two {p n : ℕ}
    (hp : p.Prime) (hpdvd : p ^ 2 ∣ n ^ 4 + 2) : Nat.Coprime p n := by
  rw [hp.coprime_iff_not_dvd]
  intro hpn
  have hpow : p ^ 2 ∣ n ^ 4 := by
    rcases hpn with ⟨k, rfl⟩
    refine ⟨p ^ 2 * k ^ 4, ?_⟩
    ring
  have htwo : p ^ 2 ∣ (n ^ 4 + 2) - n ^ 4 := Nat.dvd_sub hpdvd hpow
  apply prime_sq_not_dvd_two hp
  simpa using htwo

/-- A root modulo `p` has at most one lift to a root modulo `p ^ 2`.

This is the simple-root (Hensel uniqueness) property for `X ^ 4 + 2`. -/
lemma primeSquareObstruction_lift_unique {p a b : ℕ} (hp : p.Prime)
    (ha : p ^ 2 ∣ a ^ 4 + 2) (hb : p ^ 2 ∣ b ^ 4 + 2)
    (hab : a ≡ b [MOD p]) : a ≡ b [MOD p ^ 2] := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp_two : p ≠ 2 := by
    intro h
    subst p
    exact four_not_dvd_fourth_add_two a (by simpa using ha)
  have hpa : ¬ p ∣ a :=
    (hp.coprime_iff_not_dvd.mp (coprime_of_prime_sq_dvd_fourth_add_two hp ha))
  have hcoeff : ¬ (p : ℤ) ∣
      ((b : ℤ) + (a : ℤ)) * ((b : ℤ) ^ 2 + (a : ℤ) ^ 2) := by
    intro hdiv
    have hz' : ((((b : ℤ) + (a : ℤ)) * ((b : ℤ) ^ 2 + (a : ℤ) ^ 2) : ℤ) :
        ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    have hz : ((b : ZMod p) + (a : ZMod p)) *
        ((b : ZMod p) ^ 2 + (a : ZMod p) ^ 2) = 0 := by
      exact_mod_cast hz'
    have habz : (b : ZMod p) = (a : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff b a p).mpr hab.symm
    have ha0 : (a : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hpa
    have htwo0 : (2 : ZMod p) ≠ 0 := by
      intro hzero
      have hpdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
      exact hp_two (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hpdvd) hp.two_le)
    have hfour0 : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]
      exact mul_ne_zero htwo0 htwo0
    have : (4 : ZMod p) * (a : ZMod p) ^ 3 = 0 := by
      rw [habz] at hz
      calc
        (4 : ZMod p) * (a : ZMod p) ^ 3 =
            ((a : ZMod p) + (a : ZMod p)) *
              ((a : ZMod p) ^ 2 + (a : ZMod p) ^ 2) := by ring
        _ = 0 := hz
    exact (mul_ne_zero hfour0 (pow_ne_zero 3 ha0)) this
  have hai : (p : ℤ) ^ 2 ∣ (a : ℤ) ^ 4 + 2 := by exact_mod_cast ha
  have hbi : (p : ℤ) ^ 2 ∣ (b : ℤ) ^ 4 + 2 := by exact_mod_cast hb
  have hdiff : (p : ℤ) ^ 2 ∣ (b : ℤ) ^ 4 - (a : ℤ) ^ 4 := by
    rw [show (b : ℤ) ^ 4 - (a : ℤ) ^ 4 =
      ((b : ℤ) ^ 4 + 2) - ((a : ℤ) ^ 4 + 2) by ring]
    exact Int.dvd_sub hbi hai
  have hprod : (p : ℤ) ^ 2 ∣
      ((b : ℤ) - (a : ℤ)) * (((b : ℤ) + (a : ℤ)) * ((b : ℤ) ^ 2 + (a : ℤ) ^ 2)) := by
    rw [show ((b : ℤ) - (a : ℤ)) *
      (((b : ℤ) + (a : ℤ)) * ((b : ℤ) ^ 2 + (a : ℤ) ^ 2)) =
      (b : ℤ) ^ 4 - (a : ℤ) ^ 4 by ring]
    exact hdiff
  have hp_int : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hp
  have hd : (p : ℤ) ^ 2 ∣ (b : ℤ) - (a : ℤ) :=
    hp_int.pow_dvd_of_dvd_mul_right 2 hcoeff hprod
  rw [Nat.modEq_iff_dvd]
  simpa using hd

/-- Every root of `X ^ 4 + 2` modulo an odd prime lifts to a root modulo the
prime square. Together with `primeSquareObstruction_lift_unique`, this is the
elementary Hensel correspondence for this polynomial. -/
lemma exists_primeSquareObstruction_lift {p a : ℕ} (hp : p.Prime) (hp_two : p ≠ 2)
    (ha : p ∣ a ^ 4 + 2) :
    ∃ b : ℕ, b ≡ a [MOD p] ∧ p ^ 2 ∣ b ^ 4 + 2 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hpa : ¬ p ∣ a := by
    intro hpa
    have hpow : p ∣ a ^ 4 := dvd_trans hpa (dvd_pow_self a (by norm_num))
    have htwo : p ∣ (a ^ 4 + 2) - a ^ 4 := Nat.dvd_sub ha hpow
    have hp_dvd_two : p ∣ 2 := by simpa using htwo
    exact hp_two (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hp_dvd_two) hp.two_le)
  obtain ⟨q, hq⟩ := ha
  let c : ZMod p := 4 * (a : ZMod p) ^ 3
  have htwo0 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hpdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    exact hp_two (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hpdvd) hp.two_le)
  have hfour0 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo0 htwo0
  have ha0 : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpa
  have hc0 : c ≠ 0 := mul_ne_zero hfour0 (pow_ne_zero 3 ha0)
  let t : ZMod p := -(q : ZMod p) * c⁻¹
  have ht : (q : ZMod p) + c * t = 0 := by
    dsimp [t]
    field_simp
    ring
  let T : ℕ := t.val
  have hinner : p ∣ q + 4 * a ^ 3 * T := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [show (T : ZMod p) = t by simp [T]]
    simpa [c, mul_assoc] using ht
  let b := a + p * T
  refine ⟨b, ?_, ?_⟩
  · have hzero : p * T ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right p T)
    simpa only [b, add_comm, add_zero] using hzero.add_left a
  · have hfirst : p ^ 2 ∣ p * (q + 4 * a ^ 3 * T) := by
      simpa [pow_two] using mul_dvd_mul_left p hinner
    have hrest : p ^ 2 ∣ p ^ 2 *
        (6 * a ^ 2 * T ^ 2 + 4 * a * p * T ^ 3 + p ^ 2 * T ^ 4) :=
      dvd_mul_right _ _
    have hid : b ^ 4 + 2 = p * (q + 4 * a ^ 3 * T) + p ^ 2 *
        (6 * a ^ 2 * T ^ 2 + 4 * a * p * T ^ 3 + p ^ 2 * T ^ 4) := by
      dsimp [b]
      calc
        (a + p * T) ^ 4 + 2 = (a ^ 4 + 2) + 4 * a ^ 3 * p * T +
            6 * a ^ 2 * p ^ 2 * T ^ 2 + 4 * a * p ^ 3 * T ^ 3 +
            p ^ 4 * T ^ 4 := by ring
        _ = p * (q + 4 * a ^ 3 * T) + p ^ 2 *
            (6 * a ^ 2 * T ^ 2 + 4 * a * p * T ^ 3 + p ^ 2 * T ^ 4) := by
          rw [hq]
          ring
    rw [hid]
    exact Nat.dvd_add hfirst hrest

/-- Prime-square obstruction is periodic modulo the prime square. -/
lemma prime_sq_dvd_fourth_add_two_iff_of_modEq {p n m : ℕ}
    (hnm : n ≡ m [MOD p ^ 2]) :
    p ^ 2 ∣ n ^ 4 + 2 ↔ p ^ 2 ∣ m ^ 4 + 2 := by
  have hpoly : n ^ 4 + 2 ≡ m ^ 4 + 2 [MOD p ^ 2] :=
    (hnm.pow 4).add_right 2
  constructor
  · intro hn
    exact Nat.modEq_zero_iff_dvd.mp
      (hpoly.symm.trans (Nat.modEq_zero_iff_dvd.mpr hn))
  · intro hm
    exact Nat.modEq_zero_iff_dvd.mp
      (hpoly.trans (Nat.modEq_zero_iff_dvd.mpr hm))

/-- The complete finite set of residues modulo `p ^ 2` which cause the local
prime-square obstruction. -/
def primeSquareObstructionResidues (p : ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun a => p ^ 2 ∣ a ^ 4 + 2

/-- The roots modulo `p` of the same polynomial. -/
def primeObstructionResidues (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun a => p ∣ a ^ 4 + 2

/-- Testing an arbitrary integer for the `p ^ 2` obstruction is equivalent to
testing its canonical residue in the finite obstruction set. -/
theorem prime_sq_dvd_fourth_add_two_iff_mod_mem {p n : ℕ} (hp : p.Prime) :
    p ^ 2 ∣ n ^ 4 + 2 ↔
      n % (p ^ 2) ∈ primeSquareObstructionResidues p := by
  have hmod : n ≡ n % (p ^ 2) [MOD p ^ 2] := (Nat.mod_modEq n (p ^ 2)).symm
  rw [primeSquareObstructionResidues, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hpdvd
    refine ⟨Nat.mod_lt n (pow_pos hp.pos 2), ?_⟩
    exact (prime_sq_dvd_fourth_add_two_iff_of_modEq hmod).mp hpdvd
  · rintro ⟨_, hpdvd⟩
    exact (prime_sq_dvd_fourth_add_two_iff_of_modEq hmod).mpr hpdvd

/-- For an odd prime, reduction modulo `p` is a bijection between roots
modulo `p ^ 2` and roots modulo `p`. -/
theorem primeSquareObstructionResidues_card_eq_primeObstructionResidues_card
    {p : ℕ} (hp : p.Prime) (hp_two : p ≠ 2) :
    (primeSquareObstructionResidues p).card =
      (primeObstructionResidues p).card := by
  apply Set.BijOn.finsetCard_eq (fun a : ℕ => a % p)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change a ∈ primeSquareObstructionResidues p at ha
    change a % p ∈ primeObstructionResidues p
    rw [primeObstructionResidues, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt a hp.pos, ?_⟩
    have hsq : p ^ 2 ∣ a ^ 4 + 2 := (Finset.mem_filter.mp ha).2
    have hpdiv : p ∣ a ^ 4 + 2 :=
      dvd_trans (dvd_pow_self p (by norm_num)) hsq
    have hmod : a ≡ a % p [MOD p] := (Nat.mod_modEq a p).symm
    have hpoly : a ^ 4 + 2 ≡ (a % p) ^ 4 + 2 [MOD p] :=
      (hmod.pow 4).add_right 2
    exact Nat.modEq_zero_iff_dvd.mp
      (hpoly.symm.trans (Nat.modEq_zero_iff_dvd.mpr hpdiv))
  · intro a ha b hb hab
    change a ∈ primeSquareObstructionResidues p at ha
    change b ∈ primeSquareObstructionResidues p at hb
    have hmodp : a ≡ b [MOD p] := by
      rw [Nat.ModEq]
      exact hab
    have hmodp2 := primeSquareObstruction_lift_unique hp
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hmodp
    exact hmodp2.eq_of_lt_of_lt
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
  · intro a ha
    change a ∈ primeObstructionResidues p at ha
    change ∃ b ∈ primeSquareObstructionResidues p, b % p = a
    obtain ⟨b, hba, hb⟩ := exists_primeSquareObstruction_lift hp hp_two
      (Finset.mem_filter.mp ha).2
    refine ⟨b % (p ^ 2), ?_, ?_⟩
    · rw [primeSquareObstructionResidues, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt b (pow_pos hp.pos 2), ?_⟩
      have hmod : b ≡ b % (p ^ 2) [MOD p ^ 2] :=
        (Nat.mod_modEq b (p ^ 2)).symm
      exact (prime_sq_dvd_fourth_add_two_iff_of_modEq hmod).mp hb
    · rw [Nat.mod_mod_of_dvd b (dvd_pow_self p (by norm_num))]
      rw [Nat.ModEq] at hba
      rw [hba]
      exact Nat.mod_eq_of_lt (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)

/-- There are at most four bad residue classes modulo the square of a prime. -/
theorem primeSquareObstructionResidues_card_le_four {p : ℕ} (hp : p.Prime) :
    (primeSquareObstructionResidues p).card ≤ 4 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let P : Polynomial (ZMod p) := Polynomial.X ^ 4 + Polynomial.C 2
  have hP_ne : P ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun Q : Polynomial (ZMod p) => Q.coeff 4) hzero
    dsimp only [P] at hcoeff
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
  calc
    (primeSquareObstructionResidues p).card ≤ P.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun a : ℕ => (a : ZMod p))
      · intro a ha
        change a ∈ primeSquareObstructionResidues p at ha
        change (a : ZMod p) ∈ P.roots.toFinset
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot]
        have hsq : p ^ 2 ∣ a ^ 4 + 2 := (Finset.mem_filter.mp ha).2
        have hpdiv : p ∣ a ^ 4 + 2 :=
          dvd_trans (dvd_pow_self p (by norm_num)) hsq
        have hcast : ((a ^ 4 + 2 : ℕ) : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr hpdiv
        simpa [P] using hcast
      · intro a ha b hb hab
        change a ∈ primeSquareObstructionResidues p at ha
        change b ∈ primeSquareObstructionResidues p at hb
        have hmodp : a ≡ b [MOD p] :=
          (ZMod.natCast_eq_natCast_iff a b p).mp hab
        have hmodp2 := primeSquareObstruction_lift_unique hp
          (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hmodp
        exact hmodp2.eq_of_lt_of_lt
          (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
          (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = 4 := by simp [P]

/-- The complementary good residue classes modulo `p ^ 2`. -/
def primeSquareGoodResidues (p : ℕ) : Finset ℕ :=
  (Finset.range (p ^ 2)).filter fun a => ¬ p ^ 2 ∣ a ^ 4 + 2

/-- Bad and good classes partition the complete residue system modulo `p ^ 2`. -/
theorem obstruction_card_add_good_card (p : ℕ) :
    (primeSquareObstructionResidues p).card +
      (primeSquareGoodResidues p).card = p ^ 2 := by
  simpa [primeSquareObstructionResidues, primeSquareGoodResidues] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range (p ^ 2)) (fun a => p ^ 2 ∣ a ^ 4 + 2))

/-- Every prime-square local factor retains at least `p ^ 2 - 4` of its
`p ^ 2` residue classes. -/
theorem primeSquareGoodResidues_card_lower_bound {p : ℕ} (hp : p.Prime) :
    p ^ 2 - 4 ≤ (primeSquareGoodResidues p).card := by
  have hbad := primeSquareObstructionResidues_card_le_four hp
  have hpartition := obstruction_card_add_good_card p
  omega

/-- Primes congruent to neither `1` nor `3` modulo `8` cannot cause a square
obstruction for any `n`. -/
lemma no_prime_square_obstruction_outside_one_or_three_mod_eight
    {p : ℕ} (hp : p.Prime) (hmod : ¬ (p % 8 = 1 ∨ p % 8 = 3)) (n : ℕ) :
    ¬ p ^ 2 ∣ n ^ 4 + 2 := by
  intro hpdvd
  exact hmod (prime_mod_eight_of_sq_dvd_fourth_add_two hp hpdvd)

/-- For primes outside the two admissible residue classes modulo `8`, the
finite obstruction set modulo `p ^ 2` is empty. -/
theorem primeSquareObstructionResidues_eq_empty {p : ℕ}
    (hp : p.Prime) (hmod : ¬ (p % 8 = 1 ∨ p % 8 = 3)) :
    primeSquareObstructionResidues p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact no_prime_square_obstruction_outside_one_or_three_mod_eight hp hmod a
    (Finset.mem_filter.mp ha).2

/-- For `n ^ 4 + 2`, squarefreeness only needs to be checked at primes
congruent to `1` or `3` modulo `8`. -/
theorem squarefree_fourth_add_two_iff_restricted_primes (n : ℕ) :
    Squarefree (n ^ 4 + 2) ↔
      ∀ p, p.Prime → (p % 8 = 1 ∨ p % 8 = 3) →
        ¬ p ^ 2 ∣ n ^ 4 + 2 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  simp only [pow_two]
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp hpdvd
    have hmod := prime_mod_eight_of_sq_dvd_fourth_add_two hp
      (by simpa only [pow_two] using hpdvd)
    exact h p hp hmod hpdvd

end Contribution.Erdos978PartIIIV2
