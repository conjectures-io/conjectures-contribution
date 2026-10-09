import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination

/-
Partial contribution concerning Erdos problem 686, multiplier 25.

This file preserves the earlier partial contribution and adds complete-factor
stencil results. The new dense bound retains unrestricted coefficients.
It proves the k=6 exclusion and the unbounded conditional k=5 exclusion when
any cross-block term ratio is a rational square, plus necessary conditions
and algebraic bridges. Neither the complete k=5 case nor all-k bounty is solved.
No numerical rank upper bound or class-group completeness is asserted.

The retained proofs are unchanged. The new stencil module reuses its dense
reduction for the unscaled special case. Attribution and exact scope are supplied
separately; no external computation is a Lean premise.
-/



/- Original module: work/session4/K6.lean -/

/-
Fixed-length k=6 exclusion for Erdős 686, multiplier 25.
This is a partial result, not the complete bounty target.
The mathematical argument is in work/session3/algebra/k6_elementary_audit.md.
Compiled with Lean 4.33.1 and the pinned Mathlib environment.
No unproved declarations are used.
-/

namespace Contribution.Erdos686TwentyFive

private def sixProduct (a : ℕ) : ℕ :=
  (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) * (a + 6)

private def centralProduct (x : ℤ) : ℤ :=
  (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25)

private def centralQ (x : ℤ) : ℤ := 2 * x ^ 3 - 35 * x

private lemma centralProduct_eq (n : ℕ) :
    centralProduct (2 * (n : ℤ) + 7) = 64 * (sixProduct n : ℤ) := by
  unfold centralProduct sixProduct
  push_cast
  ring

private lemma central_identity (x : ℤ) :
    centralQ x ^ 2 - 4 * centralProduct x = 189 * x ^ 2 + 900 := by
  unfold centralQ centralProduct
  ring

private lemma centralQ_pos {x : ℤ} (hx : 7 ≤ x) : 0 < centralQ x := by
  have hxpos : 0 < x := by omega
  have hi : 0 < 2 * x ^ 2 - 35 := by nlinarith [sq_nonneg (x - 7)]
  have hp := mul_pos hxpos hi
  unfold centralQ
  nlinarith [hp]

private lemma centralQ_mod (n : ℕ) :
    centralQ (2 * (n : ℤ) + 7) % 6 = 3 := by
  have hr : (n : ℤ) % 3 = 0 ∨ (n : ℤ) % 3 = 1 ∨ (n : ℤ) % 3 = 2 := by omega
  have hd : (n : ℤ) = 3 * ((n : ℤ) / 3) + (n : ℤ) % 3 := by omega
  rcases hr with h | h | h
  all_goals
    rw [h] at hd
    unfold centralQ
    rw [hd]
    ring_nf
    omega

private lemma sixProduct_pos (n : ℕ) : 0 < sixProduct n := by
  unfold sixProduct
  positivity

private lemma upper_bound (n m : ℕ)
    (heq : sixProduct m = 25 * sixProduct n) : m < 2 * n + 6 := by
  by_contra h
  have hm : 2 * n + 6 ≤ m := by omega
  have hp : 64 * sixProduct n ≤ sixProduct m := by
    calc
      64 * sixProduct n =
          (2 * (n + 1)) * (2 * (n + 2)) * (2 * (n + 3)) *
          (2 * (n + 4)) * (2 * (n + 5)) * (2 * (n + 6)) := by
        unfold sixProduct
        ring
      _ ≤ sixProduct m := by
        unfold sixProduct
        gcongr <;> omega
  have hpos := sixProduct_pos n
  omega

private theorem sixProduct_ne (n m : ℕ) (hmn : n + 6 ≤ m) :
    sixProduct m ≠ 25 * sixProduct n := by
  intro heq
  have hmu := upper_bound n m heq
  let x : ℤ := 2 * (n : ℤ) + 7
  let y : ℤ := 2 * (m : ℤ) + 7
  have hx : 7 ≤ x := by dsimp [x]; omega
  have hy : 7 ≤ y := by dsimp [y]; omega
  have hxy : x < y := by dsimp [x, y]; omega
  have hy5 : y < 5 * x := by dsimp [x, y]; omega
  have heqz : (sixProduct m : ℤ) = 25 * (sixProduct n : ℤ) := by
    exact_mod_cast heq
  have hP : centralProduct y = 25 * centralProduct x := by
    dsimp [x, y]
    rw [centralProduct_eq, centralProduct_eq]
    nlinarith [heqz]
  have hqx := centralQ_pos hx
  have hqy := centralQ_pos hy
  have hix := central_identity x
  have hiy := central_identity y
  have hysq : y ^ 2 < 25 * x ^ 2 := by
    have hp : 0 < (5 * x - y) * (5 * x + y) :=
      mul_pos (by omega) (by omega)
    nlinarith [hp]
  have hqsq : centralQ y ^ 2 < 25 * centralQ x ^ 2 := by
    nlinarith [hix, hiy, hP, hysq]
  have hq_lt : centralQ y < 5 * centralQ x := by
    nlinarith [hqsq]
  have hmx : centralQ x % 6 = 3 := centralQ_mod n
  have hmy : centralQ y % 6 = 3 := centralQ_mod m
  have hgap : 6 ≤ 5 * centralQ x - centralQ y := by omega
  have hsquare : centralQ y ^ 2 ≤ (5 * centralQ x - 6) ^ 2 := by
    have hp : 0 ≤ (5 * centralQ x - 6 - centralQ y) *
        (5 * centralQ x - 6 + centralQ y) := mul_nonneg (by omega) (by omega)
    nlinarith [hp]
  have h60 : 60 * centralQ x ≤ 4725 * x ^ 2 - 189 * y ^ 2 + 21636 := by
    nlinarith [hix, hiy, hP, hsquare]
  have hxy_sq : x ^ 2 < y ^ 2 := by
    have hp : 0 < (y - x) * (y + x) := mul_pos (by omega) (by omega)
    nlinarith [hp]
  have hF : 120 * x ^ 3 - 4536 * x ^ 2 - 2100 * x - 21636 < 0 := by
    unfold centralQ at h60
    nlinarith [h60, hxy_sq]
  have hn : n < 16 := by
    by_contra hn
    have ht : 0 ≤ x - 39 := by dsimp [x]; omega
    have ht2 : 0 ≤ (x - 39) ^ 2 := sq_nonneg _
    have ht3 : 0 ≤ (x - 39) ^ 3 := pow_nonneg ht _
    nlinarith [hF, ht, ht2, ht3]
  have hm : m < 36 := by omega
  have finite_check : ∀ a : Fin 16, ∀ b : Fin 36,
      a.val + 6 ≤ b.val → b.val ≤ 2 * a.val + 5 →
      sixProduct b.val ≠ 25 * sixProduct a.val := by decide
  exact finite_check ⟨n, hn⟩ ⟨m, hm⟩ hmn (by change m ≤ 2 * n + 5; omega) heq

/-- The multiplier 25 has no admissible representation with block length 6. -/
theorem k6_exclusion (n m : ℕ) (hmn : n + 6 ≤ m) :
    (∏ i ∈ Finset.Icc 1 6, (m + i)) ≠
      25 * (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  have hprod (a : ℕ) : (∏ i ∈ Finset.Icc 1 6, (a + i)) = sixProduct a := by
    norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, sixProduct]
  simpa only [hprod] using sixProduct_ne n m hmn

end Contribution.Erdos686TwentyFive

/- Original module: work/session6/PrimeTransport.lean -/

/-
Universal prime-divisor transport for the Erdős 686 multiplier-25 equation.
This is an unbounded necessary condition, not a solution of the bounty.
-/

namespace Contribution.Erdos686TwentyFive

private lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (f : ℕ → ℕ) (h : p ∣ ∏ i ∈ s, f i) :
    ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty] at h
      exact False.elim (hp.not_dvd_one h)
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at h
      rcases hp.dvd_mul.mp h with h | h
      · exact ⟨a, Finset.mem_insert_self a s, h⟩
      · obtain ⟨i, hi, hd⟩ := ih h
        exact ⟨i, Finset.mem_insert_of_mem hi, hd⟩

/-- A prime occurring in both disjoint blocks is bounded by their total width. -/
theorem common_prime_le_width (n m k p : ℕ) (hp : p.Prime)
    (hmn : n + k ≤ m)
    (hlower : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i))
    (hupper : p ∣ ∏ i ∈ Finset.Icc 1 k, (m + i)) :
    p ≤ m - n + k - 1 := by
  obtain ⟨i, hi, hpi⟩ := prime_dvd_finset_prod hp _ _ hlower
  obtain ⟨j, hj, hpj⟩ := prime_dvd_finset_prod hp _ _ hupper
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
  rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
  have hpos : 0 < (m + j) - (n + i) := by omega
  have hpd : p ∣ (m + j) - (n + i) := Nat.dvd_sub hpj hpi
  have hle := Nat.le_of_dvd hpos hpd
  omega

/-- Every prime divisor of the lower block is at most m-n+k-1. -/
theorem lower_prime_le_width (n m k p : ℕ) (hp : p.Prime)
    (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hlower : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i)) :
    p ≤ m - n + k - 1 := by
  apply common_prime_le_width n m k p hp hmn hlower
  rw [heq]
  exact dvd_mul_of_dvd_right hlower 25

/-- Every prime divisor of the upper block other than 5 has the same width bound. -/
theorem upper_prime_le_width (n m k p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hupper : p ∣ ∏ i ∈ Finset.Icc 1 k, (m + i)) :
    p ≤ m - n + k - 1 := by
  have hnot25 : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := h
    have hfive := hp.dvd_of_dvd_pow hpow
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hfive)
  have hlower : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    rw [heq] at hupper
    exact (hp.dvd_mul.mp hupper).resolve_left hnot25
  exact lower_prime_le_width n m k p hp hmn heq hlower

/-- If both blocks lie below 2n, every entry of the lower block is composite. -/
theorem lower_block_not_prime (n m k : ℕ) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hspan : m + k < 2 * n) (i : ℕ) (hi : i ∈ Finset.Icc 1 k) :
    ¬ (n + i).Prime := by
  intro hp
  have hd : n + i ∣ ∏ j ∈ Finset.Icc 1 k, (n + j) :=
    Finset.dvd_prod_of_mem (fun j => n + j) hi
  have hb := lower_prime_le_width n m k (n + i) hp hmn heq hd
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
  omega

/-- Under the same span bound and n≥5, every entry of the upper block is composite. -/
theorem upper_block_not_prime (n m k : ℕ) (hn : 5 ≤ n) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hspan : m + k < 2 * n) (i : ℕ) (hi : i ∈ Finset.Icc 1 k) :
    ¬ (m + i).Prime := by
  intro hp
  have hd : m + i ∣ ∏ j ∈ Finset.Icc 1 k, (m + j) :=
    Finset.dvd_prod_of_mem (fun j => m + j) hi
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
  have hp5 : m + i ≠ 5 := by omega
  have hb := upper_prime_le_width n m k (m + i) hp hp5 hmn heq hd
  omega

end Contribution.Erdos686TwentyFive

/- Original module: work/session6/GapSquareTransport.lean -/

/-
Squared divisibility transported through an exact finite-product ratio.
This is a reusable necessary condition, not the Erdős 686 bounty target.
-/

namespace Contribution.Erdos686TwentyFive

section CommRing

variable {R ι : Type*} [CommRing R]

/-- Shifting every factor by a multiple of q preserves the product modulo q. -/
theorem dvd_shifted_prod_sub_prod (s : Finset ι) (A : ι → R) (q d : R)
    (hd : q ∣ d) :
    q ∣ (∏ j ∈ s, (A j + d)) - ∏ j ∈ s, A j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hidentity :
          (A a + d) * (∏ j ∈ s, (A j + d)) - A a * (∏ j ∈ s, A j) =
          (A a + d) * ((∏ j ∈ s, (A j + d)) - ∏ j ∈ s, A j) +
            d * (∏ j ∈ s, A j) := by ring
      rw [hidentity]
      exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_of_dvd_left hd _)

/-- Algebraic square gain after separating the distinguished factor. -/
theorem square_dvd_of_coprime_product_complement
    (a C C' d q N : R) (ha : q ∣ a) (hd : q ∣ d)
    (hcop : IsCoprime q C) (hshift : q ∣ C' - C)
    (heq : (a + d) * C' = N * (a * C)) :
    q ^ 2 ∣ (N - 1) * a - d := by
  have hcop2 : IsCoprime (q ^ 2) C := by
    simpa only [pow_two] using hcop.mul_left hcop
  apply hcop2.dvd_of_dvd_mul_left
  have hprod : q * q ∣ (a + d) * (C' - C) :=
    mul_dvd_mul (dvd_add ha hd) hshift
  have hidentity : (a + d) * (C' - C) = C * ((N - 1) * a - d) := by
    calc
      (a + d) * (C' - C) = (a + d) * C' - (a + d) * C := by ring
      _ = N * (a * C) - (a + d) * C := by rw [heq]
      _ = C * ((N - 1) * a - d) := by ring
  simpa only [pow_two, hidentity] using hprod

/-- If q divides the distinguished term and the common shift, while being
coprime to the complementary product, the exact product ratio forces a square
divisibility. No primality, positivity or nonzero assumptions are needed. -/
theorem square_dvd_transport_of_coprime_complement [DecidableEq ι]
    (s : Finset ι) (A : ι → R) (i : ι) (hi : i ∈ s) (d q N : R)
    (hAi : q ∣ A i) (hd : q ∣ d)
    (hcop : IsCoprime q (∏ j ∈ s.erase i, A j))
    (heq : (∏ j ∈ s, (A j + d)) = N * (∏ j ∈ s, A j)) :
    q ^ 2 ∣ (N - 1) * A i - d := by
  apply square_dvd_of_coprime_product_complement
    (A i) (∏ j ∈ s.erase i, A j) (∏ j ∈ s.erase i, (A j + d)) d q N
    hAi hd hcop (dvd_shifted_prod_sub_prod (s.erase i) A q d hd)
  calc
    (A i + d) * (∏ j ∈ s.erase i, (A j + d)) =
        ∏ j ∈ s, (A j + d) := Finset.mul_prod_erase s (fun j => A j + d) hi
    _ = N * (∏ j ∈ s, A j) := heq
    _ = N * (A i * (∏ j ∈ s.erase i, A j)) := by
      rw [Finset.mul_prod_erase s A hi]

end CommRing

end Contribution.Erdos686TwentyFive

/- Original module: work/session7/HigherContactCertificate.lean -/

/-
Reusable algebraic core of the higher-contact certificates for Erdős 686.
This does not assert the prime-power normalization, any numerical certificate,
or the complete multiplier-25 bounty target.
-/

namespace Contribution.Erdos686TwentyFive

variable {A : Type*} [CommSemiring A]

/-- A monomial of total degree at least `order` is divisible by `q ^ order`
when both of its inputs are divisible by `q`. -/
theorem higherContact_monomial_dvd (q u v coefficient : A)
    (a b order : ℕ) (hu : q ∣ u) (hv : q ∣ v)
    (hdegree : order ≤ a + b) :
    q ^ order ∣ coefficient * u ^ a * v ^ b := by
  have hpowers : q ^ (a + b) ∣ u ^ a * v ^ b := by
    rw [pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hu a) (pow_dvd_pow_of_dvd hv b)
  have hmonomial : q ^ order ∣ u ^ a * v ^ b :=
    (pow_dvd_pow q hdegree).trans hpowers
  simpa only [mul_assoc] using dvd_mul_of_dvd_right hmonomial coefficient

/-- Every finite polynomial remainder whose monomials have total degree at
least `order` is divisible by `q ^ order` at inputs divisible by `q`. -/
theorem higherContact_remainder_dvd (s : Finset (ℕ × ℕ))
    (coefficient : ℕ × ℕ → A) (q u v : A) (order : ℕ)
    (hu : q ∣ u) (hv : q ∣ v)
    (hdegree : ∀ ab ∈ s, order ≤ ab.1 + ab.2) :
    q ^ order ∣ ∑ ab ∈ s, coefficient ab * u ^ ab.1 * v ^ ab.2 := by
  classical
  revert hdegree
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨0, by rw [mul_zero]⟩
  | @insert ab s hab ih =>
      intro hdegree
      rw [Finset.sum_insert hab]
      obtain ⟨w, hw⟩ := higherContact_monomial_dvd q u v (coefficient ab)
        ab.1 ab.2 order hu hv (hdegree ab (Finset.mem_insert_self ab s))
      obtain ⟨z, hz⟩ := ih (fun cd hcd => hdegree cd (Finset.mem_insert_of_mem hcd))
      exact ⟨w + z, by rw [mul_add, ← hw, ← hz]⟩

/-- An exact identity `G = F * H + remainder` gives higher divisibility of `G`
on `F = 0`, when the remainder has the required total degree. -/
theorem higherContact_certificate_dvd (s : Finset (ℕ × ℕ))
    (coefficient : ℕ × ℕ → A) (q u v G F H : A) (order : ℕ)
    (hu : q ∣ u) (hv : q ∣ v)
    (hdegree : ∀ ab ∈ s, order ≤ ab.1 + ab.2)
    (hidentity : G = F * H + ∑ ab ∈ s, coefficient ab * u ^ ab.1 * v ^ ab.2)
    (hcurve : F = 0) : q ^ order ∣ G := by
  rw [hidentity, hcurve, zero_mul, zero_add]
  exact higherContact_remainder_dvd s coefficient q u v order hu hv hdegree

end Contribution.Erdos686TwentyFive

/- Original module: work/session9/QuotientBridge.lean -/

/-
Exact algebraic bridge for the length-five quotient used in session 9.
This file does NOT prove existence, nonexistence, or squareclass completeness.
-/

namespace Contribution.Erdos686TwentyFive

def centeredFive (t : ℚ) : ℚ := t ^ 5 - 5 * t ^ 3 + 4 * t

def quotientSextic (r : ℚ) : ℚ :=
  9 * r ^ 6 + 400 * r ^ 5 - 1250 * r ^ 3 + 400 * r + 5625

theorem centeredFive_product (a : ℚ) :
    centeredFive (a + 3) =
      (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) := by
  unfold centeredFive
  ring

theorem quotient_discriminant (r X : ℚ)
    (h : (r ^ 5 - 25) * X ^ 2 - 5 * (r ^ 3 - 25) * X +
      4 * (r - 25) = 0) :
    (2 * (r ^ 5 - 25) * X - 5 * (r ^ 3 - 25)) ^ 2 =
      quotientSextic r := by
  unfold quotientSextic
  have hid :
      (2 * (r ^ 5 - 25) * X - 5 * (r ^ 3 - 25)) ^ 2 -
        (9 * r ^ 6 + 400 * r ^ 5 - 1250 * r ^ 3 + 400 * r + 5625) =
      4 * (r ^ 5 - 25) * ((r ^ 5 - 25) * X ^ 2 -
        5 * (r ^ 3 - 25) * X + 4 * (r - 25)) := by ring
  rw [h, mul_zero] at hid
  exact sub_eq_zero.mp hid

theorem centeredFive_to_quotient (x y : ℚ) (hx : x ≠ 0)
    (h : centeredFive y = 25 * centeredFive x) :
    (2 * ((y / x) ^ 5 - 25) * x ^ 2 -
      5 * ((y / x) ^ 3 - 25)) ^ 2 = quotientSextic (y / x) := by
  apply quotient_discriminant (y / x) (x ^ 2)
  have hxy : y / x * x = y := div_mul_cancel₀ y hx
  have hmul : x * (((y / x) ^ 5 - 25) * (x ^ 2) ^ 2 -
      5 * ((y / x) ^ 3 - 25) * x ^ 2 + 4 * (y / x - 25)) = 0 := by
    calc
      _ = centeredFive (y / x * x) - 25 * centeredFive x := by
        unfold centeredFive
        ring
      _ = 0 := by rw [hxy, h]; ring
  exact (mul_eq_zero.mp hmul).resolve_left hx


end Contribution.Erdos686TwentyFive

/- Original module: work/session13/NormRelationBridge.lean -/

/-
Abstract linear-algebra bridge for the session-13 norm relation.

This file proves only that a coefficient-five identity between linear maps
over F_2 gives an injection into a product and the corresponding dimension
bound.  It does not construct class groups or arithmetic correspondences,
instantiate the maps with number fields, certify any class-group bound, or
prove the k=5 case or the full Erdős 686 multiplier-25 problem.
-/

namespace Contribution.Erdos686TwentyFive.NormRelationBridge

variable {V A B C : Type*}
variable [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup A] [Module (ZMod 2) A]
variable [AddCommGroup B] [Module (ZMod 2) B]
variable [AddCommGroup C] [Module (ZMod 2) C]

/-- Additive multiplication by five is the identity on an F_2-vector space. -/
theorem five_nsmul (x : V) : (5 : ℕ) • x = x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  change (5 : ZMod 2) • x = x
  have h5 : (5 : ZMod 2) = 1 := by decide
  rw [h5, one_smul]

/-- The three forward maps jointly separate points if the reverse maps
recover additive multiplication by five. -/
theorem relation_injective
    (a : V →ₗ[ZMod 2] A) (b : V →ₗ[ZMod 2] B) (c : V →ₗ[ZMod 2] C)
    (u : A →ₗ[ZMod 2] V) (v : B →ₗ[ZMod 2] V) (w : C →ₗ[ZMod 2] V)
    (h : ∀ x : V, u (a x) + v (b x) + w (c x) = (5 : ℕ) • x) :
    Function.Injective (a.prod (b.prod c)) := by
  intro x y hxy
  have ha : a x = a y := congrArg Prod.fst hxy
  have hb : b x = b y := congrArg (fun t : A × B × C => t.2.1) hxy
  have hc : c x = c y := congrArg (fun t : A × B × C => t.2.2) hxy
  calc
    x = u (a x) + v (b x) + w (c x) := by
      simpa only [five_nsmul] using (h x).symm
    _ = u (a y) + v (b y) + w (c y) := by rw [ha, hb, hc]
    _ = y := by simpa only [five_nsmul] using h y

/-- Consequently the source dimension is at most the sum of the three
target dimensions. -/
theorem relation_finrank_le
    [Module.Finite (ZMod 2) V]
    [Module.Finite (ZMod 2) A]
    [Module.Finite (ZMod 2) B]
    [Module.Finite (ZMod 2) C]
    (a : V →ₗ[ZMod 2] A) (b : V →ₗ[ZMod 2] B) (c : V →ₗ[ZMod 2] C)
    (u : A →ₗ[ZMod 2] V) (v : B →ₗ[ZMod 2] V) (w : C →ₗ[ZMod 2] V)
    (h : ∀ x : V, u (a x) + v (b x) + w (c x) = (5 : ℕ) • x) :
    Module.finrank (ZMod 2) V ≤
      Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B +
        Module.finrank (ZMod 2) C := by
  have hi := LinearMap.finrank_le_finrank_of_injective
    (relation_injective a b c u v w h)
  simpa only [Module.finrank_prod, Nat.add_assoc] using hi


end Contribution.Erdos686TwentyFive.NormRelationBridge

/- Original module: work/publication686/K6RatioBridge.lean -/

/- Direct use of the fixed-length exclusion in the original rational-ratio form. -/
namespace Contribution.Erdos686TwentyFive

/-- The rational ratio occurring in the original question cannot equal 25
when the block length is six.  Its denominator is proved positive. -/
theorem k6_ratio_exclusion (n m : ℕ) (hmn : n + 6 ≤ m) :
    (25 : ℚ) ≠
      ((∏ i ∈ Finset.Icc 1 6, (m + i) : ℕ) : ℚ) /
        ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) := by
  intro h
  have hnpos : 0 < (∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) := by
    apply Finset.prod_pos
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    omega
  have hnzero : ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hq : ((∏ i ∈ Finset.Icc 1 6, (m + i) : ℕ) : ℚ) =
      25 * ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) :=
    ((eq_div_iff hnzero).mp h).symm
  have hn : (∏ i ∈ Finset.Icc 1 6, (m + i) : ℕ) =
      25 * (∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) := by
    exact_mod_cast hq
  exact k6_exclusion n m hmn hn

end Contribution.Erdos686TwentyFive

/- Original module: work/session14/SquareCenterExclusion.lean -/

/- An unbounded conditional exclusion for length five, not the full bounty. -/

namespace Contribution.Erdos686TwentyFive.SquareCenter

def product (x : ℤ) : ℤ := x * (x ^ 2 - 1) * (x ^ 2 - 4)

def nearSquare (x : ℤ) : ℤ := 2 * x ^ 2 - 5

lemma square_identity (x : ℤ) :
    x * (nearSquare x ^ 2 - 9) = 4 * product x := by
  unfold nearSquare product
  ring

lemma product_positive {x : ℤ} (hx : 3 ≤ x) : 0 < product x := by
  unfold product
  have h1 : 0 < x ^ 2 - 1 := by nlinarith
  have h4 : 0 < x ^ 2 - 4 := by nlinarith
  exact mul_pos (mul_pos (by omega) h1) h4

lemma less_than_double {x y : ℤ} (hx : 3 ≤ x)
    (h : product y = 25 * product x) : y < 2 * x := by
  by_contra hlt
  have hy : 2 * x ≤ y := by omega
  have hxx : 0 ≤ x := by omega
  have hyy : 0 ≤ y := by omega
  have hsq : (2 * x) ^ 2 ≤ y ^ 2 := by nlinarith
  have hmono : product (2 * x) ≤ product y := by
    unfold product
    gcongr <;> nlinarith
  have hpos : 0 < x * (x ^ 2 - 1) * (7 * x ^ 2 + 92) := by
    apply mul_pos
    · apply mul_pos <;> nlinarith
    · positivity
  have hid : product (2 * x) - 25 * product x =
      x * (x ^ 2 - 1) * (7 * x ^ 2 + 92) := by unfold product; ring
  omega

/-- No multiplier-25 length-five identity has positive centers with a common
integer factor times squares. This has no height bound on any variable. -/
theorem common_square_factor_exclusion (d a b : ℤ)
    (hd : 1 ≤ d) (ha : 1 ≤ a) (hab : a < b)
    (hx : 3 ≤ d * a ^ 2) :
    product (d * b ^ 2) ≠ 25 * product (d * a ^ 2) := by
  intro heq
  let x := d * a ^ 2
  let y := d * b ^ 2
  have hb : 1 ≤ b := by omega
  have hxy : y < 2 * x := less_than_double hx heq
  have hratio : b ^ 2 < 2 * a ^ 2 := by
    dsimp [x, y] at hxy
    nlinarith
  have ha3 : 3 ≤ a := by
    by_contra hh
    have hsmall : a ≤ 2 := by omega
    have haux := mul_nonneg (show 0 ≤ a by omega) (show 0 ≤ 2 - a by omega)
    have hdiff := mul_nonneg (show 0 ≤ b - a - 1 by omega)
      (show 0 ≤ b + a + 1 by omega)
    nlinarith
  have hxlow : a ^ 2 ≤ x := by
    dsimp [x]
    nlinarith [mul_nonneg (show 0 ≤ d - 1 by omega) (sq_nonneg a)]
  have hylow : 3 ≤ y := by
    dsimp [y]
    nlinarith [mul_nonneg (show 0 ≤ d - 1 by omega) (sq_nonneg b)]
  let U := b * nearSquare y
  let V := 5 * a * nearSquare x
  have hU : 0 < U := by
    dsimp [U, nearSquare]
    apply mul_pos (by omega)
    nlinarith
  have hV : 0 < V := by
    dsimp [V, nearSquare]
    apply mul_pos (by nlinarith)
    nlinarith [hx]
  have hrel : U ^ 2 - V ^ 2 = 9 * (b ^ 2 - 25 * a ^ 2) := by
    have hix := square_identity x
    have hiy := square_identity y
    have hbase : d * (b ^ 2 * (nearSquare y ^ 2 - 9) -
        25 * a ^ 2 * (nearSquare x ^ 2 - 9)) = 0 := by
      calc
        _ = y * (nearSquare y ^ 2 - 9) -
            25 * (x * (nearSquare x ^ 2 - 9)) := by dsimp [x, y]; ring
        _ = 0 := by rw [hix, hiy]; change 4 * product (d * b ^ 2) - 25 * (4 * product (d * a ^ 2)) = 0; rw [heq]; ring
    have hzero : b ^ 2 * (nearSquare y ^ 2 - 9) -
        25 * a ^ 2 * (nearSquare x ^ 2 - 9) = 0 :=
      (mul_eq_zero.mp hbase).resolve_left (by omega)
    dsimp [U, V]
    nlinarith only [hzero]
  have hUV : U < V := by nlinarith [sq_nonneg a]
  have hgap : 1 ≤ V - U := by omega
  have hsum : V + U ≤ 9 * (25 * a ^ 2 - b ^ 2) := by
    have hp := mul_nonneg (show 0 ≤ V - U - 1 by omega)
      (show 0 ≤ V + U by omega)
    nlinarith [hrel]
  have ha2 : 9 ≤ a ^ 2 := by nlinarith
  have h27 : 27 * a ≤ a ^ 4 := by
    have h1 : 3 * a ≤ a ^ 2 := by nlinarith
    have h2 := mul_nonneg (show 0 ≤ a ^ 2 - 9 by omega) (sq_nonneg a)
    nlinarith
  have hxsq : a ^ 4 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - a ^ 2)]
  have hq : 45 * a < nearSquare x := by
    dsimp [nearSquare]
    nlinarith
  have hbig : 225 * a ^ 2 < V := by
    dsimp [V]
    nlinarith [mul_pos (show 0 < 5 * a by omega) (show 0 < nearSquare x - 45 * a by omega)]
  nlinarith [sq_nonneg b]

end Contribution.Erdos686TwentyFive.SquareCenter

/- Original module: work/session14/SquarePairExclusion.lean -/

namespace Contribution.Erdos686TwentyFive.SquarePair

def block (n : ℕ) : ℕ := (n+1)*(n+2)*(n+3)*(n+4)*(n+5)

def bracket (n : ℕ) : ℕ := (1903654 * (n + 3)) / 1000000 - 3

def row (n : ℕ) : Prop :=
    (block (bracket n) < 25 * block n ∧ 25 * block n < block (bracket n + 1)) ∨
    (block (bracket n - 1) < 25 * block n ∧ 25 * block n < block (bracket n))

instance (n : ℕ) : Decidable (row n) := inferInstanceAs (Decidable (_ ∨ _))

def check (s k : ℕ) : Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool)
    (fun s => decide (row s))
    (fun k ih s => ih s && ih (s + 2 ^ k)) k s

theorem check_sound (k s : ℕ) (h : check s k = true) :
    ∀ n, s ≤ n → n < s + 2 ^ k → row n := by
  induction k generalizing s with
  | zero =>
    intro n hn hn'
    have he : n = s := by norm_num at hn'; omega
    subst n
    simpa [check] using h
  | succ k ih =>
    have hs : check s k = true ∧ check (s + 2 ^ k) k = true := by
      simpa only [check, Bool.and_eq_true_iff] using h
    intro n hn hn'
    by_cases hm : n < s + 2 ^ k
    · exact ih s hs.1 n hn hm
    · apply ih (s + 2 ^ k) hs.2 n (by omega)
      rw [pow_succ] at hn'
      omega

lemma checked_16384 : check 0 14 = true := by decide +kernel

theorem block_mono : Monotone block := by
  intro n m h
  unfold block
  gcongr

/-- A compact, kernel-checked bracketing certificate for a previously searched box. -/
theorem finite_five_exclusion (n m : ℕ) (hn : n < 16384) :
    block m ≠ 25 * block n := by
  intro heq
  have hr := check_sound 14 0 checked_16384 n (Nat.zero_le _) (by norm_num; exact hn)
  rcases hr with ⟨hl, hu⟩ | ⟨hl, hu⟩
  · by_cases hm : m ≤ bracket n
    · have hb := block_mono hm
      omega
    · have hb := block_mono (show bracket n + 1 ≤ m by omega)
      omega
  · by_cases hm : m ≤ bracket n - 1
    · have hb := block_mono hm
      omega
    · have hb := block_mono (show bracket n ≤ m by omega)
      omega



def q (i : ℕ) (t : ℤ) : ℤ :=
  match i with
  | 1 => 8*t^2 + 40*t + 40
  | 2 => 8*t^2 + 20*t - 5
  | 3 => 8*t^2 - 20
  | 4 => 8*t^2 - 20*t - 5
  | _ => 8*t^2 - 40*t + 40

def r (i : ℕ) (t : ℤ) : ℤ :=
  match i with
  | 2 => 120*t + 409
  | 3 => 144
  | 4 => -120*t + 409
  | _ => 64

lemma q_lower (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5)
    (t : ℤ) (ht : 10000 ≤ t) : 7*t^2 ≤ q i t := by
  have h := mul_nonneg (show 0 ≤ t - 40 by omega) (show 0 ≤ t by omega)
  interval_cases i <;> norm_num [q] <;> nlinarith

lemma r_bound (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5)
    (t : ℤ) (ht : 0 ≤ t) : -(120*t+409) ≤ r i t ∧ r i t ≤ 120*t+409 := by
  interval_cases i <;> norm_num [r] <;> omega

lemma near_identity (n i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5) :
    ((n : ℤ) + i) * (q i ((n : ℤ)+i)^2-r i ((n : ℤ)+i)) =
      64 * (block n : ℤ) := by
  interval_cases i <;> norm_num [q,r,block] <;> ring

lemma residual_separation (i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5)
    (hj : 1 ≤ j) (hj' : j ≤ 5) (u v : ℤ)
    (hu : 10000 ≤ u) (hv : u ≤ v) (hv' : v ≤ 3*u) :
    v*r j v ≠ 25*u*r i u := by
  have hsq : v^2 ≤ 9*u^2 := by nlinarith [mul_nonneg (show 0 ≤ 3*u-v by omega) (show 0 ≤ 3*u+v by omega)]
  have hsq' : u^2 ≤ v^2 := by nlinarith [mul_nonneg (show 0 ≤ v-u by omega) (show 0 ≤ v+u by omega)]
  have hu2 : 10000*u ≤ u^2 := by nlinarith [mul_nonneg (show 0 ≤ u-10000 by omega) (show 0 ≤ u by omega)]
  interval_cases i <;> interval_cases j <;> norm_num [r] <;> intro h <;> nlinarith

lemma square_gap (d a b u v A B R S : ℤ)
    (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : a ≤ b)
    (hu : 10000 ≤ u) (hv : u ≤ v) (hv' : v ≤ 3*u)
    (hua : u = d*a^2) (hvb : v = d*b^2)
    (hA : 7*u^2 ≤ A) (hB : 7*v^2 ≤ B)
    (hR : -(120*u+409) ≤ R ∧ R ≤ 120*u+409)
    (hS : -(120*v+409) ≤ S ∧ S ≤ 120*v+409)
    (heq : b^2*(B^2-S) = 25*a^2*(A^2-R)) :
    b*B = 5*a*A := by
  have hb1 : 1 ≤ b := by omega
  have hapos : 0 < a := by omega
  have hu0 : 0 < u := by omega
  have hv0 : 0 < v := by omega
  have hau : a^2 ≤ u := by nlinarith [mul_nonneg (show 0 ≤ d-1 by omega) (sq_nonneg a)]
  have hab2 : b^2 ≤ 3*a^2 := by nlinarith
  have hv2 : u^2 ≤ v^2 := by nlinarith [mul_nonneg (show 0 ≤ v-u by omega) (show 0 ≤ v+u by omega)]
  have hAu : 0 < A := by nlinarith
  have hBu : 7*u^2 ≤ B := by nlinarith
  have hB0 : 0 < B := by nlinarith
  have hua100 : 100*a ≤ u := by
    have hh : 10000*u ≤ u^2 := by nlinarith [mul_nonneg (show 0 ≤ u-10000 by omega) (show 0 ≤ u by omega)]
    nlinarith
  let U := b*B
  let V := 5*a*A
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hsum : 42*a*u^2 ≤ U+V := by
    have h1 := mul_nonneg (show 0 ≤ b-a by omega) (show 0 ≤ B by omega)
    have h2 := mul_nonneg (show 0 ≤ a by omega) (show 0 ≤ B-7*u^2 by omega)
    have h3 := mul_nonneg (show 0 ≤ 5*a by omega) (show 0 ≤ A-7*u^2 by omega)
    dsimp [U,V]
    nlinarith only [h1,h2,h3]
  have hq : U^2-V^2 = b^2*S-25*a^2*R := by
    dsimp [U,V]
    nlinarith only [heq]
  let T := a^2*(4080*u+11452)
  have hS' : -(360*u+409) ≤ S ∧ S ≤ 360*u+409 := by constructor <;> linarith [hS.1,hS.2]
  have hbS : -(3*a^2*(360*u+409)) ≤ b^2*S ∧
      b^2*S ≤ 3*a^2*(360*u+409) := by
    have h1 := mul_nonneg (sq_nonneg b) (show 0 ≤ S+(360*u+409) by omega)
    have h2 := mul_nonneg (sq_nonneg b) (show 0 ≤ (360*u+409)-S by omega)
    have h3 := mul_nonneg (show 0 ≤ 3*a^2-b^2 by omega) (show 0 ≤ 360*u+409 by omega)
    constructor <;> nlinarith only [h1,h2,h3]
  have haR : -(25*a^2*(120*u+409)) ≤ 25*a^2*R ∧
      25*a^2*R ≤ 25*a^2*(120*u+409) := by
    have h1 := mul_nonneg (show 0 ≤ 25*a^2 by positivity) (show 0 ≤ R+(120*u+409) by omega)
    have h2 := mul_nonneg (show 0 ≤ 25*a^2 by positivity) (show 0 ≤ (120*u+409)-R by omega)
    constructor <;> nlinarith only [h1,h2]
  have hbound : -T ≤ U^2-V^2 ∧ U^2-V^2 ≤ T := by
    dsimp [T]
    constructor <;> nlinarith only [hbS.1,hbS.2,haR.1,haR.2,hq]
  have hT : T < U+V := by
    have h1 := mul_nonneg (show 0 ≤ u-100*a by omega) (show 0 ≤ 42*a*u by positivity)
    have h2 := mul_pos (show 0 < a^2 by positivity)
      (show 0 < 120*u-11452 by omega)
    dsimp [T]
    nlinarith only [h1,h2,hsum]
  by_contra hne
  change U ≠ V at hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := mul_nonneg (show 0 ≤ V-U-1 by omega) (show 0 ≤ V+U by omega)
    nlinarith [hbound.1]
  · have hh := mul_nonneg (show 0 ≤ U-V-1 by omega) (show 0 ≤ U+V by omega)
    nlinarith [hbound.2]


lemma block_upper (n m : ℕ) (heq : block m = 25*block n) : m ≤ 2*n+4 := by
  by_contra h
  have hm : 2*n+5 ≤ m := by omega
  have hp : 32*block n ≤ block m := by
    calc
      32*block n = (2*(n+1))*(2*(n+2))*(2*(n+3))*(2*(n+4))*(2*(n+5)) := by unfold block; ring
      _ ≤ block m := by unfold block; gcongr <;> omega
  have hpos : 0 < block n := by unfold block; positivity
  omega

/-- If any one term from each of two disjoint length-five blocks is a common
positive integer times squares, the product ratio cannot be 25. No height limit. -/
theorem common_square_pair_exclusion (n m i j d a b : ℕ)
    (hi : 1 ≤ i) (hi' : i ≤ 5) (hj : 1 ≤ j) (hj' : j ≤ 5)
    (hmn : n+5 ≤ m) (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hl : n+i = d*a^2) (hh : m+j = d*b^2) :
    block m ≠ 25*block n := by
  intro heq
  by_cases hn : n < 16384
  · exact finite_five_exclusion n m hn heq
  have hn' : 16384 ≤ n := by omega
  have hm := block_upper n m heq
  let u : ℤ := (n : ℤ)+i
  let v : ℤ := (m : ℤ)+j
  have hu : 10000 ≤ u := by dsimp [u]; omega
  have hv : u ≤ v := by dsimp [u,v]; omega
  have hv' : v ≤ 3*u := by dsimp [u,v]; omega
  have hua : u = (d : ℤ)*(a : ℤ)^2 := by dsimp [u]; exact_mod_cast hl
  have hvb : v = (d : ℤ)*(b : ℤ)^2 := by dsimp [v]; exact_mod_cast hh
  have hdi : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hai : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hbi : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hab : (a : ℤ) ≤ b := by
    by_contra hn
    have hsq : (b : ℤ)^2 ≤ (a : ℤ)^2 := by nlinarith
    have hmul := mul_nonneg (show 0 ≤ (d : ℤ) by omega)
      (show 0 ≤ (a : ℤ)^2-(b : ℤ)^2 by omega)
    have huv : u < v := by dsimp [u,v]; omega
    nlinarith
  have hei : (block m : ℤ) = 25*(block n : ℤ) := by exact_mod_cast heq
  have he1 := near_identity n i hi hi'
  have he2 := near_identity m j hj hj'
  have hcancel : (b : ℤ)^2*(q j v^2-r j v) =
      25*(a : ℤ)^2*(q i u^2-r i u) := by
    have hzero : (d : ℤ) * ((b : ℤ)^2*(q j v^2-r j v) -
        25*(a : ℤ)^2*(q i u^2-r i u)) = 0 := by
      calc
        _ = v*(q j v^2-r j v)-25*(u*(q i u^2-r i u)) := by rw [hvb,hua]; ring
        _ = 0 := by change ((m : ℤ)+j)*(q j ((m : ℤ)+j)^2-r j ((m : ℤ)+j))-25*(((n : ℤ)+i)*(q i ((n : ℤ)+i)^2-r i ((n : ℤ)+i))) = 0; rw [he1,he2,hei]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (by omega))
  have hgap := square_gap (d : ℤ) a b u v (q i u) (q j v) (r i u) (r j v)
    hdi hai hab hu hv hv' hua hvb
    (q_lower i hi hi' u hu) (q_lower j hj hj' v (by omega))
    (r_bound i hi hi' u (by omega)) (r_bound j hj hj' v (by omega)) hcancel
  have hres : (b : ℤ)^2*r j v = 25*(a : ℤ)^2*r i u := by
    have hs := congrArg (fun t : ℤ => t^2) hgap
    nlinarith only [hs,hcancel]
  apply residual_separation i j hi hi' hj hj' u v hu hv hv'
  calc
    v*r j v = (d : ℤ)*((b : ℤ)^2*r j v) := by rw [hvb]; ring
    _ = (d : ℤ)*(25*(a : ℤ)^2*r i u) := by rw [hres]
    _ = 25*u*r i u := by rw [hua]; ring

/-- The same unbounded exclusion in the finite-product notation of the bounty. -/
theorem k5_square_pair_exclusion (n m i j d a b : ℕ)
    (hi : 1 ≤ i) (hi' : i ≤ 5) (hj : 1 ≤ j) (hj' : j ≤ 5)
    (hmn : n+5 ≤ m) (hd : 1 ≤ d) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hl : n+i = d*a^2) (hh : m+j = d*b^2) :
    (∏ t ∈ Finset.Icc 1 5, (m+t)) ≠ 25*(∏ t ∈ Finset.Icc 1 5, (n+t)) := by
  have hprod (z : ℕ) : (∏ t ∈ Finset.Icc 1 5, (z+t)) = block z := by
    norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, block]
  simpa only [hprod] using common_square_pair_exclusion n m i j d a b
    hi hi' hj hj' hmn hd ha hb hl hh



lemma square_ratio_representation (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hs : IsSquare ((v : ℚ)/(u : ℚ))) :
    ∃ d a b : ℕ, 1 ≤ d ∧ 1 ≤ a ∧ 1 ≤ b ∧ u=d*a^2 ∧ v=d*b^2 := by
  obtain ⟨⟨b,hb⟩,⟨a,ha⟩⟩ := Rat.isSquare_iff.mp hs
  obtain ⟨c,hcv,hcu⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den
    (v : ℤ) (show (u : ℤ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hu))
  have hl : u = c.natAbs*a^2 := by
    have h := congrArg Int.natAbs hcu
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Int.cast_natCast,
      ha, pow_two] using h
  have hh : v = c.natAbs*b.natAbs^2 := by
    have h := congrArg Int.natAbs hcv
    simpa only [Int.natAbs_mul, Int.natAbs_natCast, Int.cast_natCast,
      hb, Int.natAbs_mul, pow_two] using h
  have hd : 1 ≤ c.natAbs := by
    by_contra h
    have hc : c.natAbs = 0 := by omega
    simp [hc] at hl
    omega
  have ha' : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    simp [ha0] at hl
    omega
  have hb' : 1 ≤ b.natAbs := by
    by_contra h
    have hb0 : b.natAbs = 0 := by omega
    simp [hb0] at hh
    omega
  exact ⟨c.natAbs,a,b.natAbs,hd,ha',hb',hl,hh⟩

/-- In every hypothetical admissible length-five witness, all 25 cross-block
term ratios are nonsquares in Q. This does not assert the existence of a witness. -/
theorem cross_ratios_nonsquare (n m : ℕ) (hmn : n+5 ≤ m)
    (heq : (∏ t ∈ Finset.Icc 1 5, (m+t)) = 25*(∏ t ∈ Finset.Icc 1 5, (n+t)))
    (i j : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5) (hj : 1 ≤ j) (hj' : j ≤ 5) :
    ¬IsSquare (((m+j : ℕ) : ℚ)/((n+i : ℕ) : ℚ)) := by
  intro hs
  obtain ⟨d,a,b,hd,ha,hb,hl,hh⟩ := square_ratio_representation
    (n+i) (m+j) (by omega) (by omega) hs
  exact k5_square_pair_exclusion n m i j d a b hi hi' hj hj' hmn hd ha hb hl hh heq

end Contribution.Erdos686TwentyFive.SquarePair

/- Complete-factor stencil API; sessions20-21. -/

set_option maxHeartbeats 1000000
namespace Contribution.Erdos686TwentyFive.FactorStencil

/-- Reduce four exact consecutive differences with all omitted factors retained.
For the intended use, the lower terms are `a*z*t*u`, `b*v*w`, `c*r*x`,
and the upper terms are `d*v*u`, `e*z*r*w`, `f*x*y`. The six coefficients
are arbitrary positive integers; none is assumed to divide the multiplier25. -/
theorem dense_stencil_reduction (a b c d e f z t u v w r x y : ℤ)
    (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c) (hd : 0 < d) (_he : 0 < e) (_hf : 0 < f)
    (hz : 0 < z) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hr : 0 < r) (hx : 0 < x) (_hy : 0 < y)
    (huw : b * w < d * u)
    (h1 : b * v * w = a * z * t * u + 1) (h2 : e * z * r * w = d * v * u + 1)
    (h3 : c * r * x = b * v * w + 1) (h4 : f * x * y = e * z * r * w + 1) :
    ∃ q h j : ℤ, 0 < q ∧ 0 < h ∧ 0 < j ∧
      2 * q = j * x ∧ q * h < d * e * z ∧ IsCoprime x z ∧
      b * d * c ^ 2 * q * x ^ 2 = a ^ 2 * b * e * z ^ 3 * h * t ^ 2 + (d * e * z - q * h) ^ 2 ∧
      (d * e * z - q * h) * r = a * b * z * t + 2 * b * q * w ∧
      d * c * x = (d * e * z - q * h) * w - a * h * z * t ∧ d * u = b * w + r * h ∧
      q * u * w = d * v * u - b * v * w + 1 := by
  let q := d * b * v ^ 2 - e * a * z ^ 2 * t * r
  have hqw : w * q = d * v - a * z * t := by
    dsimp [q]
    linear_combination d * v * h1 - a * z * t * h2
  have hqu : q * u = e * z * r - b * v := by
    dsimp [q]
    linear_combination e * z * r * h1 - b * v * h2
  let l := d * u - b * w
  have hl : 0 < l := by dsimp [l]; omega
  have hquwl : q * u * w = v * l + 1 := by
    dsimp [l]
    linear_combination w * hqu + h2
  have hq : 0 < q := by
    by_contra hn
    have hn' : q ≤ 0 := by omega
    have hnp := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hn' hu.le) hw.le
    nlinarith [mul_pos hv hl]
  have hqw2 : b * q * w ^ 2 - a * z * t * l = d := by
    dsimp [l]
    linear_combination b * w * hqw + d * h1
  have hqu2 : d * q * u ^ 2 - e * z * r * l = b := by
    dsimp [l]
    linear_combination d * u * hqu + b * h2
  have hquw : q * u * w = r * (e * z * w - c * x) + 1 := by
    linear_combination w * hqu + h3
  have hdivl : r ∣ q * u * l := by
    refine ⟨e * z * l - b * e * z * w + b * c * x, ?_⟩
    dsimp [l] at hqu2 ⊢
    linear_combination hqu2 - b * hquw
  have hrcp : IsCoprime r (q * u) := by
    refine ⟨-e * z * w + c * x, w, ?_⟩
    linear_combination hquw
  obtain ⟨h, heqh⟩ := hrcp.dvd_of_dvd_mul_left hdivl
  have hh : 0 < h := by
    by_contra hn
    have hn' : h ≤ 0 := by omega
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hr.le hn']
  have hau : d * u = b * w + r * h := by dsimp [l] at heqh; linarith
  let A := d * e * z - q * h
  have hAr : A * r = a * b * z * t + 2 * b * q * w := by
    dsimp [A]
    linear_combination -d * hqu - b * hqw + q * hau
  have hA : 0 < A := by
    by_contra hn
    have hn' : A ≤ 0 := by omega
    have hp : 0 < a * b * z * t + 2 * b * q * w := by positivity
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hn' hr.le]
  have hgap : q * h < d * e * z := by dsimp [A] at hA; omega
  have hqw3 : b * q * w ^ 2 - a * z * t * r * h = d := by
    rw [heqh] at hqw2
    simpa only [mul_assoc] using hqw2
  have hbot : c * r * x = a * z * t * u + 2 := by linarith
  have hax : d * c * x = A * w - a * h * z * t := by
    have heq : r * (d * c * x - A * w + a * h * z * t) = 0 := by
      linear_combination d * hbot + a * z * t * hau - w * hAr - 2 * hqw3
    have heq' := (mul_eq_zero.mp heq).resolve_left (ne_of_gt hr)
    linarith
  have hK : b * A * q * w ^ 2 - 2 * a * b * z * q * h * t * w - a ^ 2 * b * z ^ 2 * h * t ^ 2 = d * A := by
    linear_combination A * hqw3 + a * z * t * h * hAr
  have hnorm : b * d * c ^ 2 * q * x ^ 2 = a ^ 2 * b * e * z ^ 3 * h * t ^ 2 + (d * e * z - q * h) ^ 2 := by
    have heq : d * (b * d * c ^ 2 * q * x ^ 2 - a ^ 2 * b * e * z ^ 3 * h * t ^ 2-(d * e * z - q * h) ^ 2) = 0 := by
      dsimp [A] at hax hK
      linear_combination b * q * (d * c * x + (d * e * z - q * h) * w - a * z * h * t) * hax + (d * e * z - q * h) * hK
    have heq' := (mul_eq_zero.mp heq).resolve_left (ne_of_gt hd)
    linarith
  have hxw : IsCoprime x w := by
    refine ⟨c * r, -b * v, ?_⟩
    linear_combination h3
  have hdx : x ∣ q * u * w := by
    refine ⟨f * y - c * r, ?_⟩
    linear_combination w * hqu - h4 + h3
  have hdqu : x ∣ q * u := hxw.dvd_of_dvd_mul_right hdx
  have hd2q : x ∣ 2 * q := by
    obtain ⟨s, hs⟩ := hdqu
    refine ⟨q * c * r - a * z * t * s, ?_⟩
    linear_combination -q * hbot - a * z * t * hs
  have hxz : IsCoprime x z := by
    refine ⟨f * y, -e * r * w, ?_⟩
    linear_combination h4
  obtain ⟨j, hj⟩ := hd2q
  have hjpos : 0 < j := by
    by_contra hn
    have hn' : j ≤ 0 := by omega
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hx.le hn']
  refine ⟨q, h, j, hq, hh, hjpos, ?_, hgap, hxz, hnorm, hAr, hax, hau, ?_⟩
  · linarith
  · dsimp [l] at hquwl
    linear_combination hquwl

/-- Exact cubic identity with the formerly omitted coefficients explicit. -/
private theorem dense_stencil_cubic_identity (a b c d e z h t x j L : ℤ)
    (hL : L = 2 * d * e * z - j * h * x)
    (he : 2 * b * d * c ^ 2 * j * x ^ 3 = 4 * a ^ 2 * b * e * h * t ^ 2 * z ^ 3 + L ^ 2) :
    4 * b * e * j * ((2 * d ^ 2 * e * c) ^ 2-(a * j * h ^ 2 * t) ^ 2) * x ^ 3 =
      12 * a ^ 2 * b * e * j ^ 2 * h ^ 3 * t ^ 2 * x ^ 2 * L +
      12 * a ^ 2 * b * e * j * h ^ 2 * t ^ 2 * x * L ^ 2 +
      4 * a ^ 2 * b * e * h * t ^ 2 * L ^ 3 + (2 * d * e) ^ 3 * L ^ 2 := by
  subst L
  linear_combination (2 * d * e) ^ 3 * he

/-- Positivity bounds parameters relative to the omitted cofactors, not uniformly. -/
private theorem dense_stencil_parameter_bound (a b c d e z h t x j L : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hepos : 0 < e)
    (hh : 0 < h) (ht : 0 < t) (hx : 0 < x) (hj : 0 < j) (hLp : 0 < L)
    (hL : L = 2 * d * e * z - j * h * x)
    (he : 2 * b * d * c ^ 2 * j * x ^ 3 = 4 * a ^ 2 * b * e * h * t ^ 2 * z ^ 3 + L ^ 2) :
    a * j * h ^ 2 * t < 2 * d ^ 2 * e * c := by
  have hid := dense_stencil_cubic_identity a b c d e z h t x j L hL he
  have hp : 0 < 12 * a ^ 2 * b * e * j ^ 2 * h ^ 3 * t ^ 2 * x ^ 2 * L +
      12 * a ^ 2 * b * e * j * h ^ 2 * t ^ 2 * x * L ^ 2 +
      4 * a ^ 2 * b * e * h * t ^ 2 * L ^ 3 + (2 * d * e) ^ 3 * L ^ 2 := by positivity
  have hprod : 0 < 4 * b * e * j * ((2 * d ^ 2 * e * c) ^ 2-(a * j * h ^ 2 * t) ^ 2) * x ^ 3 := by linarith
  have hdiff : 0 < (2 * d ^ 2 * e * c) ^ 2-(a * j * h ^ 2 * t) ^ 2 := by
    by_contra hn
    have hn' : (2 * d ^ 2 * e * c) ^ 2-(a * j * h ^ 2 * t) ^ 2 ≤ 0 := by omega
    have hp' := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 4 * b * e * j) hn'
    have hp'' := mul_nonpos_of_nonpos_of_nonneg hp' (by positivity : 0 ≤ x ^ 3)
    linarith
  have hT : 0 < 2 * d ^ 2 * e * c := by positivity
  have hS : 0 < a * j * h ^ 2 * t := by positivity
  nlinarith

/-- Primitivity gives a positive integer complementary divisor.
With `L = 2*d*e*z - j*h*x`, `T = 2*d^2*e*c`, and `S = a*j*h^2*t`,
the final identity is `K*L = 2*(T+S)`. No absolute bound on `T` is asserted. -/
theorem dense_stencil_complementary_divisor (a c d e z h t x j w q L : ℤ)
    (hc : 0 < c) (hd : 0 < d) (hz : 0 < z) (hh : 0 < h) (hj : 0 < j) (hw : 0 < w)
    (hcp : IsCoprime x z) (hq : 2 * q = j * x)
    (hax : d * c * x = (d * e * z - q * h) * w - a * h * z * t)
    (hL : L = 2 * d * e * z - j * h * x) :
    ∃ K : ℤ, 0 < K ∧ z * K = 2 * d * c + j * h * w ∧
      x * K = 2 * (d * e * w - a * h * t) ∧ K * L = 2 * (2 * d ^ 2 * e * c + a * j * h ^ 2 * t) := by
  have hid : x * (2 * d * c + j * h * w) = 2 * z * (d * e * w - a * h * t) := by
    linear_combination 2 * hax - h * w * hq
  have hdiv : z ∣ x * (2 * d * c + j * h * w) := by
    refine ⟨2 * (d * e * w - a * h * t), ?_⟩
    linear_combination hid
  obtain ⟨K, hK⟩ := hcp.symm.dvd_of_dvd_mul_left hdiv
  have hKpos : 0 < K := by
    by_contra hn
    have hn' : K ≤ 0 := by omega
    have hp : 0 < 2 * d * c + j * h * w := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz.le hn']
  have hxK : x * K = 2 * (d * e * w - a * h * t) := by
    have hz0 : z * (x * K - 2 * (d * e * w - a * h * t)) = 0 := by
      linear_combination hid - x * hK
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz0).resolve_left (ne_of_gt hz))
  refine ⟨K, hKpos, by linarith, hxK, ?_⟩
  linear_combination K * hL - 2 * d * e * hK - j * h * hxK

/-- This is effective only when T itself has an independent bound. -/
private theorem linear_divisor_bound (K L S T : ℤ)
    (hK : 0 < K) (hL : 0 < L) (hST : S < T)
    (he : K * L = 2 * (T + S)) : L < 4 * T := by
  have hK1 : 1 ≤ K := by omega
  nlinarith [mul_nonneg (by omega : 0 ≤ K - 1) hL.le]

/-- Assembled bound from the complete six-term equations. The coefficients
    a,b,c,d,e,f are unrestricted, so this is not an absolute height bound. -/
theorem dense_stencil_linear_bound (a b c d e f z t u v w r x y : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hz : 0 < z) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y)
    (huw : b * w < d * u)
    (h1 : b * v * w = a * z * t * u + 1) (h2 : e * z * r * w = d * v * u + 1)
    (h3 : c * r * x = b * v * w + 1) (h4 : f * x * y = e * z * r * w + 1) :
    ∃ q h j K L : ℤ, 0 < q ∧ 0 < h ∧ 0 < j ∧ 0 < K ∧ 0 < L ∧
      2 * q = j * x ∧ L = 2 * (d * e * z - q * h) ∧ a * j * h ^ 2 * t < 2 * d ^ 2 * e * c ∧
      K * L = 2 * (2 * d ^ 2 * e * c + a * j * h ^ 2 * t) ∧ L < 8 * d ^ 2 * e * c := by
  obtain ⟨q, h, j, hq, hh, hj, hqx, hgap, hcp, hnorm, _hAr, hax, _hau, _hquw⟩ :=
    dense_stencil_reduction a b c d e f z t u v w r x y
      ha hb hc hd he hf hz ht hu hv hw hr hx hy huw h1 h2 h3 h4
  let L := 2 * (d * e * z - q * h)
  have hLp : 0 < L := by dsimp [L]; omega
  have hL : L = 2 * d * e * z - j * h * x := by
    dsimp [L]
    linear_combination -h * hqx
  have hcubic : 2 * b * d * c ^ 2 * j * x ^ 3 = 4 * a ^ 2 * b * e * h * t ^ 2 * z ^ 3 + L ^ 2 := by
    dsimp [L]
    linear_combination 4 * hnorm - 2 * b * d * c ^ 2 * x ^ 2 * hqx
  have hST := dense_stencil_parameter_bound a b c d e z h t x j L
    ha hb hc hd he hh ht hx hj hLp hL hcubic
  obtain ⟨K, hK, _hzK, _hxK, hKL⟩ := dense_stencil_complementary_divisor a c d e z h t x j w q L
    hc hd hz hh hj hw hcp hqx hax hL
  have hbound := linear_divisor_bound K L (a * j * h ^ 2 * t) (2 * d ^ 2 * e * c) hK hLp hST hKL
  exact ⟨q, h, j, K, L, hq, hh, hj, hK, hLp, hqx, rfl, hST, hKL, by nlinarith⟩


/-- The arithmetic obstruction obtained from the consecutive six-term stencil. -/
private theorem reduced_system_impossible (q z h t x : ℤ)
    (hq : 0 < q) (hz : 0 < z) (hh : 0 < h) (ht : 0 < t) (hx : 0 < x)
    (hgap : q * h < z) (hdiv : x ∣ 2 * q) (hcp : IsCoprime x z)
    (hnorm : q * x ^ 2 = z ^ 3 * h * t ^ 2 + (z - q * h) ^ 2) : False := by
  have hxl : x ≤ 2 * q := Int.le_of_dvd (by positivity) hdiv
  have hs : x ^ 2 ≤ 4 * q ^ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * q - x) (by positivity : 0 ≤ 2 * q + x)]
  have hqs := mul_le_mul_of_nonneg_left hs hq.le
  have hbound : z ^ 3 * h * t ^ 2 < 4 * q ^ 3 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hgap)]
  have hh1 : 1 ≤ h := by omega
  have ht1 : 1 ≤ t := by omega
  have htt : 1 ≤ h * t ^ 2 := by nlinarith [mul_nonneg (by omega : 0 ≤ h - 1) (sq_nonneg t)]
  have hz3 : 0 < z ^ 3 := by positivity
  have hcoarse : z ^ 3 < 4 * q ^ 3 := by
    nlinarith [mul_nonneg hz3.le (by linarith : 0 ≤ h * t ^ 2 - 1)]
  have hzlt : z < 2 * q := by
    by_contra h
    have hp : (2 * q) ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    nlinarith [pow_pos hq 3]
  have hhone : h = 1 := by
    by_contra hne
    have htwo : 2 ≤ h := by omega
    nlinarith [mul_nonneg hq.le (by omega : 0 ≤ h - 2)]
  subst h
  have hqz : q < z := by simpa using hgap
  have hqz3 : q ^ 3 ≤ z ^ 3 := pow_le_pow_left₀ hq.le hqz.le 3
  have htone : t = 1 := by
    by_contra hne
    have htwo : 2 ≤ t := by omega
    have hp : 0 ≤ t ^ 2 - 4 := by nlinarith
    nlinarith [mul_nonneg hz3.le hp]
  subst t
  norm_num only [mul_one, one_pow] at hnorm
  have hxq : q < x := by
    by_contra h
    have hs2 : x ^ 2 ≤ q ^ 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ q - x) (by positivity : 0 ≤ q + x)]
    have hqhs := mul_le_mul_of_nonneg_left hs2 hq.le
    nlinarith [sq_pos_of_pos (sub_pos.mpr hqz)]
  have hxeq : x = 2 * q := by
    obtain ⟨b, hb⟩ := hdiv
    have hbpos : 0 < b := by
      by_contra hne
      have hle : b ≤ 0 := by omega
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hx.le hle]
    have hb1 : b = 1 := by
      by_contra hne
      have hb2 : 2 ≤ b := by omega
      nlinarith [mul_nonneg hx.le (by omega : 0 ≤ b - 2)]
    rw [hb1] at hb
    linarith
  have hqcp : IsCoprime q z := hcp.of_isCoprime_of_dvd_left ⟨2, by linarith⟩
  let a := z - q
  have ha : 0 < a := by dsimp [a]; linarith
  have haq : a < q := by dsimp [a]; linarith
  have hca : IsCoprime q a := by
    obtain ⟨f, g, hfg⟩ := hqcp
    refine ⟨f + g, g, ?_⟩
    dsimp [a]
    linear_combination hfg
  have hd : q ∣ a ^ 2 * (a + 1) := by
    refine ⟨3 * q ^ 2 - 3 * q * a - 3 * a ^ 2, ?_⟩
    dsimp [a]
    rw [hxeq] at hnorm
    linear_combination -hnorm
  have hcap : IsCoprime q (a ^ 2) := by simpa [pow_two] using hca.mul_right hca
  have had : q ∣ a + 1 := hcap.dvd_of_dvd_mul_left hd
  have hale : q ≤ a + 1 := Int.le_of_dvd (by omega) had
  have heqa : a + 1 = q := by omega
  have heqz : z = 2 * q - 1 := by dsimp [a] at heqa; omega
  have hquadratic : 4 * q ^ 2 - 11 * q + 4 = 0 := by
    rw [hxeq, heqz] at hnorm
    have hhq : q * (4 * q ^ 2 - 11 * q + 4) = 0 := by linear_combination -hnorm
    exact (mul_eq_zero.mp hhq).resolve_left (ne_of_gt hq)
  have hq2 : 2 ≤ q := by omega
  by_cases hqeq : q = 2
  · norm_num [hqeq] at hquadratic
  · have hq3 : 3 ≤ q := by omega
    nlinarith [mul_nonneg hq.le (by omega : 0 ≤ q - 3)]


/-- The unscaled complete six-term stencil has no positive integer solution.
This excludes the stated factorization, without a height bound. -/
theorem consecutive_stencil_impossible (z t u v w r x y : ℤ)
    (hz : 0 < z) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y)
    (huw : w < u)
    (h1 : v * w = z * t * u + 1) (h2 : z * r * w = v * u + 1)
    (h3 : r * x = v * w + 1) (h4 : x * y = z * r * w + 1) : False := by
  obtain ⟨q, h, j, hq, hh, _hj, hjx, hgap, hcp, hnorm, _hAr, _hax, _hau, _hquw⟩ :=
    dense_stencil_reduction 1 1 1 1 1 1 z t u v w r x y
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hz ht hu hv hw hr hx hy (by simpa using huw)
      (by simpa using h1) (by simpa using h2) (by simpa using h3) (by simpa using h4)
  apply reduced_system_impossible q z h t x hq hz hh ht hx
    (by simpa using hgap) ⟨j, by linarith⟩ hcp
  simpa using hnorm

/-- Explicit position-preserving specialization to the selected k=5 matrix template. -/
theorem labeled_pattern_impossible (n m z t u v w r x y : ℤ)
    (hz : 0 < z) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y)
    (hnm : n < m)
    (hA1 : z * t * u = n + 1) (hA2 : v * w = n + 2) (hA3 : r * x = n + 3)
    (hB2 : v * u = m + 2) (hB3 : z * r * w = m + 3) (hB4 : x * y = m + 4) : False := by
  have huw : w < u := by
    by_contra h
    have hh : 0 ≤ w - u := by omega
    nlinarith [mul_nonneg hv.le hh]
  exact consecutive_stencil_impossible z t u v w r x y hz ht hu hv hw hr hx hy huw
    (by linarith) (by linarith) (by linarith) (by linarith)


/-- Use the dense bound at the actual lower positions1,2,3 and upper positions2,3,4.
All displayed factorizations are complete. This bound depends on the unrestricted
coefficients and does not exclude the dense length-five case. -/
theorem labeled_dense_pattern_bound (n m a b c d e f z t u v w r x y : ℤ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hz : 0 < z) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (hr : 0 < r) (hx : 0 < x) (hy : 0 < y)
    (hnm : n < m)
    (hA1 : a * z * t * u = n + 1) (hA2 : b * v * w = n + 2) (hA3 : c * r * x = n + 3)
    (hB2 : d * v * u = m + 2) (hB3 : e * z * r * w = m + 3) (hB4 : f * x * y = m + 4) :
    ∃ q h j K L : ℤ, 0 < q ∧ 0 < h ∧ 0 < j ∧ 0 < K ∧ 0 < L ∧
      2 * q = j * x ∧ L = 2 * (d * e * z - q * h) ∧ a * j * h ^ 2 * t < 2 * d ^ 2 * e * c ∧
      K * L = 2 * (2 * d ^ 2 * e * c + a * j * h ^ 2 * t) ∧ L < 8 * d ^ 2 * e * c := by
  have huw : b * w < d * u := by
    by_contra hn
    have hle : d * u ≤ b * w := by omega
    nlinarith [mul_nonneg hv.le (sub_nonneg.mpr hle)]
  exact dense_stencil_linear_bound a b c d e f z t u v w r x y
    ha hb hc hd he hf hz ht hu hv hw hr hx hy huw
    (by linarith) (by linarith) (by linarith) (by linarith)

end Contribution.Erdos686TwentyFive.FactorStencil
