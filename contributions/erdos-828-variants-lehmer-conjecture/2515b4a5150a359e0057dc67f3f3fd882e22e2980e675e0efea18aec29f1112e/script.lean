import FormalConjectures.ErdosProblems.«828»

/-!
Elementary structural consequences for a hypothetical composite solution of
Lehmer's totient divisibility condition in Erdős problem 828.

These are classical necessary conditions assembled from Mathlib's totient,
squarefree, Carmichael, and modular-congruence APIs. In addition, the script
rules out every product of at most four primes, derives a five-distinct-prime-
factor lower bound, and exposes the normal-prime-support and 2-adic sieves. It
does not prove that a composite solution is impossible.
-/

namespace Contribution.Erdos828Lehmer

open scoped Nat

/-- A composite counterexample to the forward direction of Lehmer's target. -/
def IsCompositeCandidate (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ φ n ∣ n - 1

/-- A composite `n > 1` satisfying `φ n ∣ n - 1` is odd. -/
theorem odd_of_composite_of_totient_dvd_sub_one {n : ℕ}
    (hn : 1 < n) (hcomp : ¬ n.Prime) (hφ : φ n ∣ n - 1) : Odd n := by
  have hn2 : 2 < n := by
    have hne : n ≠ 2 := by
      intro h
      exact hcomp (h ▸ Nat.prime_two)
    omega
  have h2φ : 2 ∣ φ n := even_iff_two_dvd.mp (Nat.totient_even hn2)
  have h2sub : 2 ∣ n - 1 := dvd_trans h2φ hφ
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2n : 2 ∣ n := even_iff_two_dvd.mp heven
  have h21 : 2 ∣ n - (n - 1) := Nat.dvd_sub h2n h2sub
  have hdiff : n - (n - 1) = 1 := by omega
  have : 2 ∣ 1 := by simpa only [hdiff] using h21
  norm_num at this

/-- For every prime divisor `p` of `n`, Lehmer's divisibility condition forces
`p - 1 ∣ n - 1`. -/
theorem prime_sub_one_dvd_sub_one_of_totient_dvd {n p : ℕ}
    (hp : p.Prime) (hpn : p ∣ n) (hφ : φ n ∣ n - 1) : p - 1 ∣ n - 1 := by
  have htot : φ p ∣ φ n := Nat.totient_dvd_of_dvd hpn
  have := dvd_trans htot hφ
  simpa [Nat.totient_prime hp] using this

/-- Every `n > 1` satisfying `φ n ∣ n - 1` is squarefree. -/
theorem squarefree_of_totient_dvd_sub_one {n : ℕ}
    (hn : 1 < n) (hφ : φ n ∣ n - 1) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hppn
  have hp_tot_pp : p ∣ φ (p * p) := by
    rw [show p * p = p ^ 2 by simp [pow_two], Nat.totient_prime_pow hp (by norm_num)]
    simp
  have hp_tot_n : p ∣ φ n :=
    dvd_trans hp_tot_pp (Nat.totient_dvd_of_dvd hppn)
  have hp_sub : p ∣ n - 1 := dvd_trans hp_tot_n hφ
  have hp_n : p ∣ n := dvd_trans (dvd_mul_right p p) hppn
  have hp_one : p ∣ n - (n - 1) := Nat.dvd_sub hp_n hp_sub
  apply hp.not_dvd_one
  have hdiff : n - (n - 1) = 1 := by omega
  simpa only [hdiff] using hp_one

/-- Euler's totient of a product of two distinct primes. This target-local
interface keeps the semiprime obstruction below independent of simplifier
details. -/
theorem totient_mul_distinct_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : φ (p * q) = (p - 1) * (q - 1) := by
  have hcop : p.Coprime q := (hp.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  rw [Nat.totient_mul hcop, Nat.totient_prime hp, Nat.totient_prime hq]

/-- For distinct integers at least three, the product of their predecessors
strictly exceeds their sum minus two. -/
theorem predecessor_product_exceeds_sum {p q : ℕ}
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p ≠ q) :
    p + q - 2 < (p - 1) * (q - 1) := by
  have hp1 : 2 ≤ p - 1 := by omega
  have hq1 : 2 ≤ q - 1 := by omega
  have hne : p - 1 ≠ q - 1 := by omega
  have hor : 3 ≤ p - 1 ∨ 3 ≤ q - 1 := by omega
  have hsum : p + q - 2 = (p - 1) + (q - 1) := by omega
  rw [hsum]
  rcases hor with hp4 | hq4 <;> nlinarith

/-- The product of two distinct odd primes cannot satisfy Lehmer's totient
divisibility. -/
theorem not_totient_dvd_sub_one_of_distinct_odd_primes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p ≠ q) :
    ¬ φ (p * q) ∣ p * q - 1 := by
  intro hφ
  rw [totient_mul_distinct_primes hp hq hpq] at hφ
  have hpq9 : 9 ≤ p * q := Nat.mul_le_mul hp3 hq3
  have hprodpos : 0 < p * q - 1 := by omega
  have hle : (p - 1) * (q - 1) ≤ p * q - 1 := Nat.le_of_dvd hprodpos hφ
  have hdiv : (p - 1) * (q - 1) ∣
      (p * q - 1) - (p - 1) * (q - 1) :=
    Nat.dvd_sub hφ (dvd_refl _)
  have hdiff : (p * q - 1) - (p - 1) * (q - 1) = p + q - 2 := by
    have hp_eq : p = (p - 1) + 1 := by omega
    have hq_eq : q = (q - 1) + 1 := by omega
    nth_rewrite 1 [hp_eq]
    nth_rewrite 1 [hq_eq]
    simp [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_comm]
    rw [show p - 1 + (q - 1 + (p - 1) * (q - 1)) =
        (p - 1) * (q - 1) + ((p - 1) + (q - 1)) by ac_rfl]
    simp
    omega
  rw [hdiff] at hdiv
  have hlinpos : 0 < p + q - 2 := by omega
  have hlinle : (p - 1) * (q - 1) ≤ p + q - 2 := Nat.le_of_dvd hlinpos hdiv
  exact (Nat.not_le_of_lt (predecessor_product_exceeds_sum hp3 hq3 hpq)) hlinle

/-- No product of two primes, equal or distinct, satisfies Lehmer's totient
divisibility. The equal-prime case is excluded by squarefreeness; in the
distinct case oddness reduces to the preceding arithmetic obstruction. -/
theorem no_product_of_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ¬ φ (p * q) ∣ p * q - 1 := by
  intro hφ
  have hn : 1 < p * q := by nlinarith [hp.two_le, hq.two_le]
  by_cases hpq : p = q
  · have hsf := squarefree_of_totient_dvd_sub_one hn hφ
    have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp
    apply hnot
    simp [hpq]
  · have hcomp : ¬ (p * q).Prime := Nat.not_prime_mul hp.ne_one hq.ne_one
    have hodd := odd_of_composite_of_totient_dvd_sub_one hn hcomp hφ
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      rcases hodd with ⟨k, hk⟩
      omega
    have hq2 : q ≠ 2 := by
      intro heq
      subst q
      rcases hodd with ⟨k, hk⟩
      omega
    have hp3 : 3 ≤ p := by
      have hp_lower := hp.two_le
      omega
    have hq3 : 3 ≤ q := by
      have hq_lower := hq.two_le
      omega
    exact not_totient_dvd_sub_one_of_distinct_odd_primes hp hq hp3 hq3 hpq hφ

/-- Euler's totient of a product of three pairwise distinct primes. -/
theorem totient_mul_three_distinct_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    φ (p * q * r) = (p - 1) * (q - 1) * (r - 1) := by
  have hpqcop : p.Coprime q := (hp.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  have hprcop : p.Coprime r := (hp.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hd)
  have hqrcop : q.Coprime r := (hq.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hd)
  rw [Nat.totient_mul (hprcop.mul_left hqrcop), Nat.totient_mul hpqcop,
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_prime hr]

/-- Three increasing primes cannot satisfy Lehmer's totient divisibility. -/
theorem no_product_of_three_increasing_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p < q) (hqr : q < r) :
    ¬ φ (p * q * r) ∣ p * q * r - 1 := by
  intro hφ
  have hφorig := hφ
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hpr_ne : p ≠ r := ne_of_lt (lt_trans hpq hqr)
  have hqr_ne : q ≠ r := ne_of_lt hqr
  rw [totient_mul_three_distinct_primes hp hq hr hpq_ne hpr_ne hqr_ne] at hφ
  let D := (p - 1) * (q - 1) * (r - 1)
  have hpq4 : 4 ≤ p * q := Nat.mul_le_mul hp.two_le hq.two_le
  have hpqr8 : 8 ≤ p * q * r := Nat.mul_le_mul hpq4 hr.two_le
  have hn : 1 < p * q * r := by omega
  have hpq_not_one : p * q ≠ 1 := by nlinarith [hp.two_le, hq.two_le]
  have hcomp : ¬ (p * q * r).Prime := Nat.not_prime_mul hpq_not_one hr.ne_one
  have hodd := odd_of_composite_of_totient_dvd_sub_one hn hcomp hφorig
  have hpodd : Odd p := Nat.Odd.of_mul_left (Nat.Odd.of_mul_left hodd)
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    rcases hpodd with ⟨k, hk⟩
    omega
  have hp3 : 3 ≤ p := by
    have hp_lower := hp.two_le
    omega
  have hq4 : 4 ≤ q := by omega
  have hq_ne_four : q ≠ 4 := by
    intro heq
    subst q
    norm_num at hq
  have hq5 : 5 ≤ q := by
    omega
  have hr6 : 6 ≤ r := by omega
  have hr_ne_six : r ≠ 6 := by
    intro heq
    subst r
    norm_num at hr
  have hr7 : 7 ≤ r := by
    omega
  have hDpos : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hp_ratio : 2 * p ≤ 3 * (p - 1) := by omega
  have hq_ratio : 4 * q ≤ 5 * (q - 1) := by omega
  have hr_ratio : 6 * r ≤ 7 * (r - 1) := by omega
  have hratio := Nat.mul_le_mul (Nat.mul_le_mul hp_ratio hq_ratio) hr_ratio
  have hratio_clean : 48 * (p * q * r) ≤ 105 * D := by
    calc
      48 * (p * q * r) = (2 * p) * (4 * q) * (6 * r) := by ring
      _ ≤ (3 * (p - 1)) * (5 * (q - 1)) * (7 * (r - 1)) := hratio
      _ = 105 * D := by simp only [D]; ring
  have hbound : p * q * r - 1 < D * 3 := by
    omega
  rcases hφ with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkzero, mul_zero] at hk
    omega
  have hklt : k < 3 := by
    rw [hk] at hbound
    exact (Nat.mul_lt_mul_left hDpos).mp hbound
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    have hD_eq : D = p * q * r - 1 := by simpa [hk1] using hk.symm
    have htot_eq : φ (p * q * r) = p * q * r - 1 :=
      (totient_mul_three_distinct_primes hp hq hr hpq_ne hpr_ne hqr_ne).trans hD_eq
    exact hcomp ((Nat.totient_eq_iff_prime (by positivity)).mp htot_eq)
  have hk2 : k = 2 := by omega
  have hp_eq_three : p = 3 := by
    by_contra hp3ne
    have hp5 : 5 ≤ p := by
      rcases hpodd with ⟨t, ht⟩
      omega
    have hp_ratio' : 4 * p ≤ 5 * (p - 1) := by omega
    have hq_ratio' : 4 * q ≤ 5 * (q - 1) := by omega
    have hr_ratio' : 4 * r ≤ 5 * (r - 1) := by omega
    have hratio' := Nat.mul_le_mul (Nat.mul_le_mul hp_ratio' hq_ratio') hr_ratio'
    have hratio_clean' : 64 * (p * q * r) ≤ 125 * D := by
      calc
        64 * (p * q * r) = (4 * p) * (4 * q) * (4 * r) := by ring
        _ ≤ (5 * (p - 1)) * (5 * (q - 1)) * (5 * (r - 1)) := hratio'
        _ = 125 * D := by simp only [D]; ring
    have hbound' : p * q * r - 1 < D * 2 := by
      omega
    rw [hk, hk2] at hbound'
    omega
  subst p
  have hfactor : (q - 4) * (r - 4) = 11 := by
    dsimp [D] at hk
    norm_num [hk2] at hk
    have hkZ := congrArg (fun t : ℕ => (t : ℤ)) hk
    norm_num [Nat.cast_sub (by omega : 1 ≤ 3 * q * r),
      Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub (by omega : 1 ≤ r)] at hkZ
    have hfactorZ : (((q - 4) * (r - 4) : ℕ) : ℤ) = 11 := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 4 ≤ q),
        Nat.cast_sub (by omega : 4 ≤ r)]
      ring_nf at hkZ ⊢
      linarith
    exact_mod_cast hfactorZ
  have hdiv11 : q - 4 ∣ 11 := ⟨r - 4, hfactor.symm⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp hdiv11 with hq4 | hq4
  · have hq5eq : q = 5 := by omega
    subst q
    norm_num at hfactor
    have hr15 : r = 15 := by omega
    subst r
    norm_num at hr
  · have hq15 : q = 15 := by omega
    subst q
    norm_num at hq

/-- No product of three pairwise distinct primes satisfies Lehmer's totient
divisibility, independently of the order in which the factors are supplied. -/
theorem no_product_of_three_distinct_primes {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ φ (p * q * r) ∣ p * q * r - 1 := by
  intro hφ
  by_cases hpq_lt : p < q
  · by_cases hqr_lt : q < r
    · exact no_product_of_three_increasing_primes hp hq hr hpq_lt hqr_lt hφ
    · have hrq_lt : r < q := by omega
      by_cases hpr_lt : p < r
      · apply no_product_of_three_increasing_primes hp hr hq hpr_lt hrq_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
      · have hrp_lt : r < p := by omega
        apply no_product_of_three_increasing_primes hr hp hq hrp_lt hpq_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
  · have hqp_lt : q < p := by omega
    by_cases hpr_lt : p < r
    · apply no_product_of_three_increasing_primes hq hp hr hqp_lt hpr_lt
      simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
    · have hrp_lt : r < p := by omega
      by_cases hqr_lt : q < r
      · apply no_product_of_three_increasing_primes hq hr hp hqr_lt hrp_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
      · have hrq_lt : r < q := by omega
        apply no_product_of_three_increasing_primes hr hq hp hrq_lt hqp_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ

/-- Euler's totient of a product of four pairwise distinct primes. -/
theorem totient_mul_four_distinct_primes {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    φ (p * q * r * s) = (p - 1) * (q - 1) * (r - 1) * (s - 1) := by
  have hpqcop : p.Coprime q := (hp.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  have hprcop : p.Coprime r := (hp.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hd)
  have hpscop : p.Coprime s := (hp.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hps ((Nat.prime_dvd_prime_iff_eq hp hs).mp hd)
  have hqrcop : q.Coprime r := (hq.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hd)
  have hqscop : q.Coprime s := (hq.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hqs ((Nat.prime_dvd_prime_iff_eq hq hs).mp hd)
  have hrscop : r.Coprime s := (hr.coprime_iff_not_dvd).2 <| by
    intro hd
    exact hrs ((Nat.prime_dvd_prime_iff_eq hr hs).mp hd)
  rw [Nat.totient_mul ((hpscop.mul_left hqscop).mul_left hrscop),
    Nat.totient_mul (hprcop.mul_left hqrcop), Nat.totient_mul hpqcop,
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_prime hr,
    Nat.totient_prime hs]

/-- Four strictly increasing primes cannot satisfy Lehmer's totient
divisibility. -/
theorem no_product_of_four_increasing_primes {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    ¬ φ (p * q * r * s) ∣ p * q * r * s - 1 := by
  intro hφ
  have hφorig := hφ
  have hpq_ne : p ≠ q := ne_of_lt hpq
  have hpr_ne : p ≠ r := ne_of_lt (lt_trans hpq hqr)
  have hps_ne : p ≠ s := ne_of_lt (lt_trans (lt_trans hpq hqr) hrs)
  have hqr_ne : q ≠ r := ne_of_lt hqr
  have hqs_ne : q ≠ s := ne_of_lt (lt_trans hqr hrs)
  have hrs_ne : r ≠ s := ne_of_lt hrs
  rw [totient_mul_four_distinct_primes hp hq hr hs hpq_ne hpr_ne hps_ne
    hqr_ne hqs_ne hrs_ne] at hφ
  let D := (p - 1) * (q - 1) * (r - 1) * (s - 1)
  have hpq4 : 4 ≤ p * q := Nat.mul_le_mul hp.two_le hq.two_le
  have hpqr8 : 8 ≤ p * q * r := Nat.mul_le_mul hpq4 hr.two_le
  have hpqrs16 : 16 ≤ p * q * r * s := Nat.mul_le_mul hpqr8 hs.two_le
  have hn : 1 < p * q * r * s := by omega
  have hpqr_ne_one : p * q * r ≠ 1 := by
    omega
  have hcomp : ¬ (p * q * r * s).Prime := Nat.not_prime_mul hpqr_ne_one hs.ne_one
  have hodd := odd_of_composite_of_totient_dvd_sub_one
    hn hcomp hφorig
  have hpodd : Odd p :=
    Nat.Odd.of_mul_left (Nat.Odd.of_mul_left (Nat.Odd.of_mul_left hodd))
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    rcases hpodd with ⟨k, hk⟩
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq4 : 4 ≤ q := by omega
  have hq_ne_four : q ≠ 4 := by
    intro heq
    subst q
    norm_num at hq
  have hq5 : 5 ≤ q := by omega
  have hr6 : 6 ≤ r := by omega
  have hr_ne_six : r ≠ 6 := by
    intro heq
    subst r
    norm_num at hr
  have hr7 : 7 ≤ r := by omega
  have hs8 : 8 ≤ s := by omega
  have hs_ne_eight : s ≠ 8 := by
    intro heq
    subst s
    norm_num at hs
  have hs9 : 9 ≤ s := by omega
  have hs_ne_nine : s ≠ 9 := by
    intro heq
    subst s
    norm_num at hs
  have hs10 : 10 ≤ s := by omega
  have hs_ne_ten : s ≠ 10 := by
    intro heq
    subst s
    norm_num at hs
  have hs11 : 11 ≤ s := by omega
  have hDpos : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  have hp_ratio : 2 * p ≤ 3 * (p - 1) := by omega
  have hq_ratio : 4 * q ≤ 5 * (q - 1) := by omega
  have hr_ratio : 6 * r ≤ 7 * (r - 1) := by omega
  have hs_ratio : 10 * s ≤ 11 * (s - 1) := by omega
  have hratio := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul hp_ratio hq_ratio) hr_ratio) hs_ratio
  have hratio_clean : 480 * (p * q * r * s) ≤ 1155 * D := by
    calc
      480 * (p * q * r * s) =
          (2 * p) * (4 * q) * (6 * r) * (10 * s) := by ring
      _ ≤ (3 * (p - 1)) * (5 * (q - 1)) * (7 * (r - 1)) *
          (11 * (s - 1)) := hratio
      _ = 1155 * D := by simp only [D]; ring
  have hbound : p * q * r * s - 1 < D * 3 := by omega
  rcases hφ with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hk0
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
    rw [hkzero, mul_zero] at hk
    omega
  have hklt : k < 3 := by
    rw [hk] at hbound
    exact (Nat.mul_lt_mul_left hDpos).mp hbound
  have hk_ne_one : k ≠ 1 := by
    intro hk1
    have hD_eq : D = p * q * r * s - 1 := by simpa [hk1] using hk.symm
    have htot_eq : φ (p * q * r * s) = p * q * r * s - 1 :=
      (totient_mul_four_distinct_primes hp hq hr hs hpq_ne hpr_ne hps_ne
        hqr_ne hqs_ne hrs_ne).trans hD_eq
    exact hcomp ((Nat.totient_eq_iff_prime (by positivity)).mp htot_eq)
  have hk2 : k = 2 := by omega
  have hp_eq_three : p = 3 := by
    by_contra hp3ne
    have hp5 : 5 ≤ p := by
      rcases hpodd with ⟨t, ht⟩
      omega
    have hq6 : 6 ≤ q := by omega
    have hr7' : 7 ≤ r := by omega
    have hs8' : 8 ≤ s := by omega
    have hp_ratio' : 4 * p ≤ 5 * (p - 1) := by omega
    have hq_ratio' : 5 * q ≤ 6 * (q - 1) := by omega
    have hr_ratio' : 6 * r ≤ 7 * (r - 1) := by omega
    have hs_ratio' : 7 * s ≤ 8 * (s - 1) := by omega
    have hratio' := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul hp_ratio' hq_ratio') hr_ratio') hs_ratio'
    have hratio_clean' : 840 * (p * q * r * s) ≤ 1680 * D := by
      calc
        840 * (p * q * r * s) =
            (4 * p) * (5 * q) * (6 * r) * (7 * s) := by ring
        _ ≤ (5 * (p - 1)) * (6 * (q - 1)) * (7 * (r - 1)) *
            (8 * (s - 1)) := hratio'
        _ = 1680 * D := by simp only [D]; ring
    have hbound' : p * q * r * s - 1 < D * 2 := by
      -- The displayed coefficient bound is actually non-strict at ratio two;
      -- strictness comes from subtracting one from the numerator.
      omega
    rw [hk, hk2] at hbound'
    omega
  subst p
  have hq_lt_eleven : q < 11 := by
    by_contra hnot
    have hq11 : 11 ≤ q := by omega
    have hr12 : 12 ≤ r := by omega
    have hs13 : 13 ≤ s := by omega
    have hp_ratio' : 2 * 3 ≤ 3 * (3 - 1) := by norm_num
    have hq_ratio' : 10 * q ≤ 11 * (q - 1) := by omega
    have hr_ratio' : 11 * r ≤ 12 * (r - 1) := by omega
    have hs_ratio' : 12 * s ≤ 13 * (s - 1) := by omega
    have hratio' := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul hp_ratio' hq_ratio') hr_ratio') hs_ratio'
    have hratio_clean' : 2640 * (3 * q * r * s) ≤ 5148 * D := by
      calc
        2640 * (3 * q * r * s) =
            (2 * 3) * (10 * q) * (11 * r) * (12 * s) := by ring
        _ ≤ (3 * (3 - 1)) * (11 * (q - 1)) * (12 * (r - 1)) *
            (13 * (s - 1)) := hratio'
        _ = 5148 * D := by simp only [D]; ring
    have hbound' : 3 * q * r * s - 1 < D * 2 := by omega
    rw [hk, hk2] at hbound'
    omega
  have hq_cases : q = 5 ∨ q = 7 := by
    interval_cases q <;> norm_num at hq <;> omega
  rcases hq_cases with rfl | rfl
  · by_cases hr16 : r < 16
    · interval_cases r <;> norm_num at hr <;>
        norm_num [D, hk2] at hk <;> omega
    · have hr16le : 16 ≤ r := by omega
      have hs16le : 16 ≤ s := by omega
      have hfactor : (r - 16) * (s - 16) = 239 := by
        dsimp [D] at hk
        norm_num [hk2] at hk
        have hkZ := congrArg (fun t : ℕ => (t : ℤ)) hk
        norm_num [Nat.cast_sub (by omega : 1 ≤ 3 * 5 * r * s),
          Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_sub (by omega : 1 ≤ s)] at hkZ
        have hfactorZ : (((r - 16) * (s - 16) : ℕ) : ℤ) = 239 := by
          rw [Nat.cast_mul, Nat.cast_sub hr16le, Nat.cast_sub hs16le]
          ring_nf at hkZ ⊢
          linarith
        exact_mod_cast hfactorZ
      have hdiv239 : r - 16 ∣ 239 := ⟨s - 16, hfactor.symm⟩
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 239)).mp hdiv239 with hr16eq | hr16eq
      · have hr17 : r = 17 := by omega
        subst r
        norm_num at hfactor
        have hs255 : s = 255 := by omega
        subst s
        norm_num at hs
      · have hr255 : r = 255 := by omega
        subst r
        norm_num at hr
  · have h3sub : 3 ∣ 3 * 7 * r * s - 1 := by
      rw [hk, hk2]
      dsimp [D]
      refine ⟨4 * (r - 1) * (s - 1) * 2, ?_⟩
      ring
    have h3n : 3 ∣ 3 * 7 * r * s := by
      refine ⟨7 * r * s, ?_⟩
      ring
    have h31 : 3 ∣ 3 * 7 * r * s - (3 * 7 * r * s - 1) :=
      Nat.dvd_sub h3n h3sub
    have hdiff : 3 * 7 * r * s - (3 * 7 * r * s - 1) = 1 := by
      have : 0 < 3 * 7 * r * s := by positivity
      omega
    rw [hdiff] at h31
    norm_num at h31

/-- If the first prime is smaller than the other three, sorting those three
reduces the claim to the increasing-prime theorem. -/
theorem no_product_of_four_with_least_first {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hpr : p < r) (hps : p < s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    ¬ φ (p * q * r * s) ∣ p * q * r * s - 1 := by
  intro hφ
  by_cases hqr_lt : q < r
  · by_cases hrs_lt : r < s
    · exact no_product_of_four_increasing_primes hp hq hr hs hpq hqr_lt hrs_lt hφ
    · have hsr_lt : s < r := by omega
      by_cases hqs_lt : q < s
      · apply no_product_of_four_increasing_primes hp hq hs hr hpq hqs_lt hsr_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
      · have hsq_lt : s < q := by omega
        apply no_product_of_four_increasing_primes hp hs hq hr hps hsq_lt hqr_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
  · have hrq_lt : r < q := by omega
    by_cases hqs_lt : q < s
    · apply no_product_of_four_increasing_primes hp hr hq hs hpr hrq_lt hqs_lt
      simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
    · have hsq_lt : s < q := by omega
      by_cases hrs_lt : r < s
      · apply no_product_of_four_increasing_primes hp hr hs hq hpr hrs_lt hsq_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
      · have hsr_lt : s < r := by omega
        apply no_product_of_four_increasing_primes hp hs hr hq hps hsr_lt hrq_lt
        simpa [mul_assoc, mul_comm, mul_left_comm] using hφ

/-- No product of four pairwise distinct primes satisfies Lehmer's totient
divisibility, independently of the order in which the factors are supplied. -/
theorem no_product_of_four_distinct_primes {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    ¬ φ (p * q * r * s) ∣ p * q * r * s - 1 := by
  intro hφ
  have hmin :
      (p < q ∧ p < r ∧ p < s) ∨
      (q < p ∧ q < r ∧ q < s) ∨
      (r < p ∧ r < q ∧ r < s) ∨
      (s < p ∧ s < q ∧ s < r) := by
    omega
  rcases hmin with h | h | h | h
  · exact no_product_of_four_with_least_first hp hq hr hs h.1 h.2.1 h.2.2
      hqr hqs hrs hφ
  · apply no_product_of_four_with_least_first hq hp hr hs h.1 h.2.1 h.2.2
      hpr hps hrs
    simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
  · apply no_product_of_four_with_least_first hr hp hq hs h.1 h.2.1 h.2.2
      hpq hps hqs
    simpa [mul_assoc, mul_comm, mul_left_comm] using hφ
  · apply no_product_of_four_with_least_first hs hp hq hr h.1 h.2.1 h.2.2
      hpq hpr hqr
    simpa [mul_assoc, mul_comm, mul_left_comm] using hφ

/-- Euler's theorem plus `φ n ∣ n - 1`: every base coprime to `n` satisfies
the Carmichael-style congruence `a^(n-1) ≡ 1 (mod n)`. -/
theorem pow_sub_one_modeq_one_of_totient_dvd {n a : ℕ}
    (ha : a.Coprime n) (hφ : φ n ∣ n - 1) : a ^ (n - 1) ≡ 1 [MOD n] := by
  rcases hφ with ⟨k, hk⟩
  have hpow := Nat.ModEq.pow k (Nat.ModEq.pow_totient ha)
  simpa [← pow_mul, hk] using hpow

/-- The elementary structural bundle for a hypothetical composite Lehmer
number. This is a consequence package, not a proof that no such `n` exists. -/
theorem composite_lehmer_candidate_structure {n : ℕ}
    (hn : 1 < n) (hcomp : ¬ n.Prime) (hφ : φ n ∣ n - 1) :
    Odd n ∧
      Squarefree n ∧
      (∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
      (∀ a, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) := by
  exact ⟨odd_of_composite_of_totient_dvd_sub_one hn hcomp hφ,
    squarefree_of_totient_dvd_sub_one hn hφ,
    fun _ hp hpn => prime_sub_one_dvd_sub_one_of_totient_dvd hp hpn hφ,
    fun _ ha => pow_sub_one_modeq_one_of_totient_dvd ha hφ⟩

/-- The structure bundle exposed directly from the counterexample predicate. -/
theorem structure_of_composite_candidate {n : ℕ} (h : IsCompositeCandidate n) :
    Odd n ∧
      Squarefree n ∧
      (∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
      (∀ a, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) :=
  composite_lehmer_candidate_structure h.1 h.2.1 h.2.2

/-- A hypothetical composite Lehmer candidate is not a semiprime. This
statement rules out both products of distinct primes and prime squares. -/
theorem composite_candidate_not_product_of_two_primes {n : ℕ}
    (h : IsCompositeCandidate n) :
    ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q := by
  rintro ⟨p, q, hp, hq, rfl⟩
  exact no_product_of_two_primes hp hq h.2.2

/-- Every hypothetical composite candidate has at least three distinct prime
factors. This packages squarefreeness and the semiprime obstruction in the
standard cardinality form used by stronger Lehmer bounds. -/
theorem three_le_primeFactors_card_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : 3 ≤ n.primeFactors.card := by
  by_contra hnot
  have hcard : n.primeFactors.card ≤ 2 := by omega
  have hn : 1 < n := h.1
  have hsf := squarefree_of_totient_dvd_sub_one h.1 h.2.2
  interval_cases hc : n.primeFactors.card
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hc
    rcases Nat.primeFactors_eq_empty.mp hempty with rfl | rfl <;> omega
  · obtain ⟨p, hpfs⟩ := Finset.card_eq_one.mp hc
    have hp_mem : p ∈ n.primeFactors := by simp [hpfs]
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hprod := Nat.prod_primeFactors_of_squarefree hsf
    have hpn : p = n := by simpa [hpfs] using hprod
    exact h.2.1 (hpn ▸ hp)
  · obtain ⟨p, q, hpq, hpfs⟩ := Finset.card_eq_two.mp hc
    have hp_mem : p ∈ n.primeFactors := by simp [hpfs]
    have hq_mem : q ∈ n.primeFactors := by simp [hpfs]
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hprod := Nat.prod_primeFactors_of_squarefree hsf
    have hnprod : n = p * q := by
      simpa [hpfs, hpq, mul_comm] using hprod.symm
    exact composite_candidate_not_product_of_two_primes h ⟨p, q, hp, hq, hnprod⟩

/-- Every hypothetical composite candidate has at least four distinct prime
factors. The new case beyond the semiprime bound is the elementary exclusion of
products of three distinct primes proved above. -/
theorem four_le_primeFactors_card_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : 4 ≤ n.primeFactors.card := by
  have hthree := three_le_primeFactors_card_of_composite_candidate h
  by_contra hnot
  have hcard : n.primeFactors.card = 3 := by omega
  obtain ⟨p, q, r, hpq, hpr, hqr, hpfs⟩ := Finset.card_eq_three.mp hcard
  have hp_mem : p ∈ n.primeFactors := by simp [hpfs]
  have hq_mem : q ∈ n.primeFactors := by simp [hpfs]
  have hr_mem : r ∈ n.primeFactors := by simp [hpfs]
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  have hsf := squarefree_of_totient_dvd_sub_one h.1 h.2.2
  have hprod := Nat.prod_primeFactors_of_squarefree hsf
  have hnprod : n = p * q * r := by
    simpa [hpfs, hpq, hpr, hqr, mul_assoc, mul_comm, mul_left_comm] using hprod.symm
  apply no_product_of_three_distinct_primes hp hq hr hpq hpr hqr
  simpa [hnprod] using h.2.2

/-- Every hypothetical composite candidate has at least five distinct prime
factors. -/
theorem five_le_primeFactors_card_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : 5 ≤ n.primeFactors.card := by
  have hfour := four_le_primeFactors_card_of_composite_candidate h
  by_contra hnot
  have hcard : n.primeFactors.card = 4 := by omega
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, hpfs⟩ :=
    Finset.card_eq_four.mp hcard
  have hp_mem : p ∈ n.primeFactors := by simp [hpfs]
  have hq_mem : q ∈ n.primeFactors := by simp [hpfs]
  have hr_mem : r ∈ n.primeFactors := by simp [hpfs]
  have hs_mem : s ∈ n.primeFactors := by simp [hpfs]
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hr : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  have hs : s.Prime := Nat.prime_of_mem_primeFactors hs_mem
  have hsf := squarefree_of_totient_dvd_sub_one h.1 h.2.2
  have hprod := Nat.prod_primeFactors_of_squarefree hsf
  have hnprod : n = p * q * r * s := by
    simpa [hpfs, hpq, hpr, hps, hqr, hqs, hrs, mul_assoc, mul_comm,
      mul_left_comm] using hprod.symm
  apply no_product_of_four_distinct_primes
    hp hq hr hs hpq hpr hps hqr hqs hrs
  simpa [hnprod] using h.2.2

/-- The structural handoff augmented with the checked exclusions through four
prime factors. -/
theorem strengthened_structure_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) :
    Odd n ∧
      Squarefree n ∧
      (∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
      (∀ a, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]) ∧
      (¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∧
      5 ≤ n.primeFactors.card := by
  rcases structure_of_composite_candidate h with ⟨hodd, hsf, hk, hc⟩
  exact ⟨hodd, hsf, hk, hc, composite_candidate_not_product_of_two_primes h,
    five_le_primeFactors_card_of_composite_candidate h⟩

/-- The divisibility premise makes `n` coprime to its own totient. -/
theorem coprime_totient_of_totient_dvd_sub_one {n : ℕ} (hn : 1 ≤ n)
    (hφ : φ n ∣ n - 1) : n.Coprime (φ n) := by
  exact Nat.Coprime.of_dvd_right hφ
    ((Nat.coprime_self_sub_right hn).2 (Nat.coprime_one_right n))

/-- The composite obstruction is a composite number in Mathlib's standard
predicate. -/
theorem composite_of_composite_candidate {n : ℕ} (h : IsCompositeCandidate n) :
    n.Composite := by
  exact ⟨h.1, h.2.1⟩

/-- Every Lehmer candidate is coprime to its totient. -/
theorem coprime_totient_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : n.Coprime (φ n) :=
  coprime_totient_of_totient_dvd_sub_one (Nat.le_of_lt h.1) h.2.2

/-- Every composite Lehmer candidate is a Carmichael number, exposed through
the `IsCarmichael` predicate used elsewhere in Formal Conjectures. -/
theorem isCarmichael_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : IsCarmichael n := by
  intro a ha hna
  refine ⟨(Nat.probablePrime_iff_modEq n ha).2 ?_, h.2.1, h.1⟩
  exact pow_sub_one_modeq_one_of_totient_dvd hna.symm h.2.2

/-- Exact bridge: a natural is a composite Lehmer candidate iff it is a
Carmichael number that also satisfies Lehmer's totient divisibility. -/
theorem isCompositeCandidate_iff_isCarmichael_and_totient_dvd {n : ℕ} :
    IsCompositeCandidate n ↔ IsCarmichael n ∧ φ n ∣ n - 1 := by
  constructor
  · intro h
    exact ⟨isCarmichael_of_composite_candidate h, h.2.2⟩
  · rintro ⟨hc, hφ⟩
    have hbase := hc 1 (by omega) (Nat.coprime_one_right n)
    exact ⟨hbase.2.2, hbase.2.1, hφ⟩

/-- The predecessor of every prime divisor is coprime to a Lehmer candidate.
This is the target-facing form of Lehmer's normal-prime-support restriction. -/
theorem coprime_prime_sub_one_of_prime_dvd_candidate {n q : ℕ}
    (h : IsCompositeCandidate n) (hq : q.Prime) (hqn : q ∣ n) :
    n.Coprime (q - 1) := by
  have hqφ : q - 1 ∣ φ n := by
    have ht := Nat.totient_dvd_of_dvd hqn
    simpa [Nat.totient_prime hq] using ht
  exact Nat.Coprime.of_dvd_right hqφ
    (coprime_totient_of_composite_candidate h)

/-- If `p` and `q` are prime divisors of a Lehmer candidate, then `p` cannot
divide `q - 1`. In particular, two supported primes cannot satisfy
`q = p*x + 1`. -/
theorem prime_not_dvd_other_sub_one_of_prime_divisors {n p q : ℕ}
    (h : IsCompositeCandidate n) (hp : p.Prime) (hpn : p ∣ n)
    (hq : q.Prime) (hqn : q ∣ n) : ¬ p ∣ q - 1 := by
  intro hpq
  have hcop : p.Coprime (q - 1) :=
    (coprime_prime_sub_one_of_prime_dvd_candidate h hq hqn).of_dvd_left hpn
  exact hp.ne_one (hcop.eq_one_of_dvd hpq)

/-- Lehmer's original forbidden-shift condition, as an explicit equality
interface convenient for finite prime-support searches. -/
theorem no_prime_factor_mul_add_one_of_prime_divisors {n p q x : ℕ}
    (h : IsCompositeCandidate n) (hp : p.Prime) (hpn : p ∣ n)
    (hq : q.Prime) (hqn : q ∣ n) : q ≠ p * x + 1 := by
  intro hqeq
  apply prime_not_dvd_other_sub_one_of_prime_divisors h hp hpn hq hqn
  refine ⟨x, ?_⟩
  omega

/-- For an odd `n`, every prime-factor predecessor contributes a factor two
to the totient. -/
theorem two_pow_primeFactors_card_dvd_totient_of_odd {n : ℕ} (hn : Odd n) :
    2 ^ n.primeFactors.card ∣ φ n := by
  have htwo : (∏ _p ∈ n.primeFactors, 2) ∣
      ∏ p ∈ n.primeFactors, (p - 1) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpodd : Odd p := Odd.of_dvd_nat hn hpn
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hpodd odd_one)
  have hprod : (∏ p ∈ n.primeFactors, (p - 1)) ∣ φ n := by
    rw [Nat.totient_eq_div_primeFactors_mul]
    exact dvd_mul_left _ _
  simpa using dvd_trans htwo hprod

/-- The existing five-factor bound forces a concrete 2-adic sieve:
`32 ∣ φ(n)` for every composite Lehmer candidate. -/
theorem thirty_two_dvd_totient_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : 32 ∣ φ n := by
  have hpow := two_pow_primeFactors_card_dvd_totient_of_odd
    (odd_of_composite_of_totient_dvd_sub_one h.1 h.2.1 h.2.2)
  have hdiv : 2 ^ 5 ∣ 2 ^ n.primeFactors.card :=
    pow_dvd_pow 2 (five_le_primeFactors_card_of_composite_candidate h)
  norm_num at hdiv
  exact dvd_trans hdiv hpow

/-- Consequently every composite Lehmer candidate is `1 mod 32`. -/
theorem thirty_two_dvd_sub_one_of_composite_candidate {n : ℕ}
    (h : IsCompositeCandidate n) : 32 ∣ n - 1 :=
  dvd_trans (thirty_two_dvd_totient_of_composite_candidate h) h.2.2

/-- Exact target-body reduction: Lehmer's equivalence is true precisely when
there is no composite candidate satisfying the totient divisibility. -/
theorem target_body_iff_no_composite_candidate :
    (∀ n > 1, φ n ∣ n - 1 ↔ Prime n) ↔
      ∀ n, ¬ IsCompositeCandidate n := by
  constructor
  · intro h n hn
    exact hn.2.1 (Nat.prime_iff.mpr ((h n hn.1).mp hn.2.2))
  · intro h n hn
    constructor
    · intro hφ
      apply Nat.prime_iff.mp
      by_contra hprime
      exact h n ⟨hn, hprime, hφ⟩
    · intro hprime
      simp [Nat.totient_prime (Nat.prime_iff.mpr hprime)]

end Contribution.Erdos828Lehmer
