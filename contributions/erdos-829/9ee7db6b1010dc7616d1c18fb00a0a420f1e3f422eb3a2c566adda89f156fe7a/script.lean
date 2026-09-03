import FormalConjectures.ErdosProblems.«829»

/-!
# Primitive-factor and divisor-discriminant reductions for sums of two cubes

For positive `n`, this file gives an exact arithmetic characterization of the
possible root sums `d = x + y` in representations `x ^ 3 + y ^ 3 = n`.
It also isolates the nearly-unitary factorization forced by coprime roots and
bounds the ordered representation count by twice the number of divisors which
pass the characterization or, more simply, lie in the forced cubic window.
These results do not prove the fixed-polylogarithmic bound asked for in Erdős
829.
-/

namespace Contribution.Erdos829CubeDiscriminant

/-- The complementary factor in the classical factorization of a sum of two
cubes. -/
def cubeCofactor (x y : ℕ) : ℕ :=
  x ^ 2 + y ^ 2 - x * y

lemma mul_cubeCofactor (x y : ℕ) :
    (x + y) * cubeCofactor x y = x ^ 3 + y ^ 3 := by
  have hxy : x * y ≤ x ^ 2 + y ^ 2 := by nlinarith
  have hmul : (x + y) * (x * y) ≤ (x + y) * (x ^ 2 + y ^ 2) :=
    Nat.mul_le_mul_left (x + y) hxy
  simp only [cubeCofactor]
  rw [Nat.mul_sub_left_distrib]
  rw [Nat.sub_eq_iff_eq_add hmul]
  ring

lemma cubeCofactor_add_three_mul (x y : ℕ) :
    cubeCofactor x y + 3 * (x * y) = (x + y) ^ 2 := by
  have hxy : x * y ≤ x ^ 2 + y ^ 2 := by nlinarith
  simp only [cubeCofactor]
  calc
    x ^ 2 + y ^ 2 - x * y + 3 * (x * y) =
        x ^ 2 + y ^ 2 + 2 * (x * y) := by omega
    _ = (x + y) ^ 2 := by ring

/-- For coprime roots, the root sum and complementary cubic factor have gcd
dividing `3`. -/
lemma gcd_rootSum_cubeCofactor_dvd_three {x y : ℕ}
    (hcop : x.Coprime y) :
    Nat.gcd (x + y) (cubeCofactor x y) ∣ 3 := by
  let g := Nat.gcd (x + y) (cubeCofactor x y)
  have hgd : g ∣ x + y := Nat.gcd_dvd_left _ _
  have hgq : g ∣ cubeCofactor x y := Nat.gcd_dvd_right _ _
  have hgd2 : g ∣ (x + y) ^ 2 := dvd_pow hgd (by norm_num)
  have hg3xy : g ∣ 3 * (x * y) := by
    have hsub := Nat.dvd_sub hgd2 hgq
    have hdiff : (x + y) ^ 2 - cubeCofactor x y = 3 * (x * y) := by
      rw [← cubeCofactor_add_three_mul x y]
      omega
    simpa only [hdiff] using hsub
  have hg3xsum : g ∣ 3 * x * (x + y) := by
    exact dvd_mul_of_dvd_right hgd (3 * x)
  have hg3ysum : g ∣ 3 * y * (x + y) := by
    exact dvd_mul_of_dvd_right hgd (3 * y)
  have hg3x2 : g ∣ 3 * x ^ 2 := by
    have hsub := Nat.dvd_sub hg3xsum hg3xy
    have hsum : 3 * x * (x + y) = 3 * x ^ 2 + 3 * (x * y) := by ring
    rw [hsum, Nat.add_sub_cancel_right] at hsub
    exact hsub
  have hg3y2 : g ∣ 3 * y ^ 2 := by
    have hsub := Nat.dvd_sub hg3ysum hg3xy
    have hsum : 3 * y * (x + y) = 3 * y ^ 2 + 3 * (x * y) := by ring
    rw [hsum, Nat.add_sub_cancel_right] at hsub
    exact hsub
  have hggcd : g ∣ Nat.gcd (3 * x ^ 2) (3 * y ^ 2) :=
    Nat.dvd_gcd hg3x2 hg3y2
  have hpows : Nat.gcd (x ^ 2) (y ^ 2) = 1 :=
    (hcop.pow 2 2).gcd_eq_one
  simpa [Nat.gcd_mul_left, hpows] using hggcd

/-- A primitive two-cube representation forces its root-sum divisor to be
unitary apart from a possible common factor `3`. -/
theorem coprime_cubeSum_rootSum_nearlyUnitary {x y n : ℕ}
    (hcop : x.Coprime y) (hsum : x ^ 3 + y ^ 3 = n) :
    x + y ∣ n ∧ Nat.gcd (x + y) (n / (x + y)) ∣ 3 := by
  have hfac : (x + y) * cubeCofactor x y = n :=
    (mul_cubeCofactor x y).trans hsum
  have hpos : 0 < x + y := by
    by_contra h
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp at hcop
  constructor
  · exact ⟨cubeCofactor x y, hfac.symm⟩
  · have hdiv : n / (x + y) = cubeCofactor x y :=
      Nat.div_eq_of_eq_mul_right hpos hfac.symm
    rw [hdiv]
    exact gcd_rootSum_cubeCofactor_dvd_three hcop

/-- Away from the exceptional factor `3`, a primitive representation gives a
unitary root-sum divisor. -/
theorem coprime_cubeSum_rootSum_unitary_of_three_not_dvd {x y n : ℕ}
    (hcop : x.Coprime y) (hthree : ¬3 ∣ x + y)
    (hsum : x ^ 3 + y ^ 3 = n) :
    x + y ∣ n ∧ (x + y).Coprime (n / (x + y)) := by
  have hnear := coprime_cubeSum_rootSum_nearlyUnitary hcop hsum
  refine ⟨hnear.1, ?_⟩
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp hnear.2 with h | h
  · exact h
  · exfalso
    apply hthree
    rw [← h]
    exact Nat.gcd_dvd_left _ _

def rootDifference (x y : ℕ) : ℕ :=
  if x ≤ y then y - x else x - y

lemma rootDifference_le_add (x y : ℕ) :
    rootDifference x y ≤ x + y := by
  simp only [rootDifference]
  split_ifs <;> omega

lemma rootDifference_parity (x y : ℕ) :
    2 ∣ x + y + rootDifference x y := by
  simp only [rootDifference]
  split_ifs with h
  · use y
    omega
  · use x
    omega

lemma cubeSum_discriminant_identity (x y : ℕ) :
    4 * (x ^ 3 + y ^ 3) =
      (x + y) * ((x + y) ^ 2 + 3 * rootDifference x y ^ 2) := by
  simp only [rootDifference]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [Nat.add_sub_cancel_left]
    ring
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge h)
    simp only [Nat.add_sub_cancel_left]
    ring

lemma cubeSum_rootSum_cube_bounds (x y : ℕ) :
    x ^ 3 + y ^ 3 ≤ (x + y) ^ 3 ∧
      (x + y) ^ 3 ≤ 4 * (x ^ 3 + y ^ 3) := by
  constructor
  · calc
      x ^ 3 + y ^ 3 ≤ x ^ 3 + y ^ 3 + 3 * (x * y) * (x + y) :=
        Nat.le_add_right _ _
      _ = (x + y) ^ 3 := by ring
  · calc
      (x + y) ^ 3 = (x + y) * (x + y) ^ 2 := by ring
      _ ≤ (x + y) * ((x + y) ^ 2 + 3 * rootDifference x y ^ 2) := by
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ = 4 * (x ^ 3 + y ^ 3) := (cubeSum_discriminant_identity x y).symm

lemma cube_sum_of_discriminant {n d k : ℕ}
    (hk : k ≤ d) (heven : 2 ∣ d + k)
    (hdisc : 4 * n = d * (d ^ 2 + 3 * k ^ 2)) :
    ∃ x y : ℕ, x + y = d ∧ x ^ 3 + y ^ 3 = n := by
  rcases heven with ⟨x, hx⟩
  have hxd : x ≤ d := by omega
  let y := d - x
  have hsum : x + y = d := by
    exact Nat.add_sub_of_le hxd
  have hrootDifference : rootDifference x y = k := by
    simp only [rootDifference]
    split_ifs <;> omega
  refine ⟨x, y, hsum, ?_⟩
  have hid := cubeSum_discriminant_identity x y
  rw [hsum, hrootDifference] at hid
  omega

/-- Divisors which pass the complete nonnegative two-cube discriminant test. -/
def admissibleRootSums (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d =>
    ∃ k ∈ Finset.range (d + 1),
      2 ∣ d + k ∧ 4 * n = d * (d ^ 2 + 3 * k ^ 2)

lemma rootSum_mem_admissibleRootSums {n x y : ℕ} (hn : n ≠ 0)
    (hsum : x ^ 3 + y ^ 3 = n) :
    x + y ∈ admissibleRootSums n := by
  apply Finset.mem_filter.mpr
  constructor
  · apply Nat.mem_divisors.mpr
    constructor
    · have hdiv :=
        (show Odd 3 by decide).nat_add_dvd_pow_add_pow x y
      simpa only [hsum] using hdiv
    · exact hn
  · refine ⟨rootDifference x y, Finset.mem_range.mpr ?_,
      rootDifference_parity x y, ?_⟩
    · exact Nat.lt_succ_of_le (rootDifference_le_add x y)
    · simpa only [hsum] using cubeSum_discriminant_identity x y

lemma cube_sum_of_mem_admissibleRootSums {n d : ℕ}
    (hd : d ∈ admissibleRootSums n) :
    ∃ x y : ℕ, x + y = d ∧ x ^ 3 + y ^ 3 = n := by
  rcases (Finset.mem_filter.mp hd).2 with ⟨k, hk, heven, hdisc⟩
  exact cube_sum_of_discriminant (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    heven hdisc

/-- A divisor passes the test exactly when it is the sum of the roots in a
nonnegative representation of `n` as two cubes. -/
theorem mem_admissibleRootSums_iff {n d : ℕ} (hn : n ≠ 0) :
    d ∈ admissibleRootSums n ↔
      ∃ x y : ℕ, x + y = d ∧ x ^ 3 + y ^ 3 = n := by
  constructor
  · exact cube_sum_of_mem_admissibleRootSums
  · rintro ⟨x, y, rfl, hsum⟩
    exact rootSum_mem_admissibleRootSums hn hsum

/-- Every admissible root sum lies in the classical short cubic interval. -/
theorem admissibleRootSum_cube_bounds {n d : ℕ}
    (hd : d ∈ admissibleRootSums n) :
    n ≤ d ^ 3 ∧ d ^ 3 ≤ 4 * n := by
  rcases cube_sum_of_mem_admissibleRootSums hd with ⟨x, y, rfl, rfl⟩
  exact cubeSum_rootSum_cube_bounds x y

/-- The simpler outer sieve consisting of all divisors in the forced cubic
window. -/
def cubicWindowDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => n ≤ d ^ 3 ∧ d ^ 3 ≤ 4 * n

lemma mem_cubicWindowDivisors_iff {n d : ℕ} (hn : n ≠ 0) :
    d ∈ cubicWindowDivisors n ↔
      d ∣ n ∧ n ≤ d ^ 3 ∧ d ^ 3 ≤ 4 * n := by
  simp [cubicWindowDivisors, Nat.mem_divisors, hn]

lemma admissibleRootSums_subset_cubicWindowDivisors (n : ℕ) :
    admissibleRootSums n ⊆ cubicWindowDivisors n := by
  intro d hd
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
    admissibleRootSum_cube_bounds hd⟩

open AdditiveCombinatorics Asymptotics Erdos829 Filter

noncomputable section

noncomputable def cubeRoot (m : ℕ) : ℕ := by
  classical
  exact if h : m ∈ cubes then Classical.choose h else 0

lemma cubeRoot_pow_three {m : ℕ} (hm : m ∈ cubes) :
    cubeRoot m ^ 3 = m := by
  rw [cubeRoot, dif_pos hm]
  exact Classical.choose_spec hm

noncomputable def cubeRepresentations (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.HasAntidiagonal.antidiagonal n).filter fun e =>
    e.1 ∈ cubes ∧ e.2 ∈ cubes

lemma sumRep_cubes_eq_card_cubeRepresentations (n : ℕ) :
    sumRep cubes n = (cubeRepresentations n).card := by
  simpa only [cubeRepresentations] using sumRep_def cubes n

noncomputable def leftRoot {n : ℕ} (e : cubeRepresentations n) : ℕ :=
  cubeRoot e.1.1

noncomputable def rightRoot {n : ℕ} (e : cubeRepresentations n) : ℕ :=
  cubeRoot e.1.2

lemma leftRoot_pow_three {n : ℕ} (e : cubeRepresentations n) :
    leftRoot e ^ 3 = e.1.1 := by
  classical
  apply cubeRoot_pow_three
  exact (Finset.mem_filter.mp e.property).2.1

lemma rightRoot_pow_three {n : ℕ} (e : cubeRepresentations n) :
    rightRoot e ^ 3 = e.1.2 := by
  classical
  apply cubeRoot_pow_three
  exact (Finset.mem_filter.mp e.property).2.2

lemma roots_cube_sum {n : ℕ} (e : cubeRepresentations n) :
    leftRoot e ^ 3 + rightRoot e ^ 3 = n := by
  classical
  rw [leftRoot_pow_three, rightRoot_pow_three]
  exact Finset.HasAntidiagonal.mem_antidiagonal.mp
    (Finset.mem_filter.mp e.property).1

noncomputable def admissibleRootSum {n : ℕ} (hn : n ≠ 0)
    (e : cubeRepresentations n) : admissibleRootSums n :=
  ⟨leftRoot e + rightRoot e,
    rootSum_mem_admissibleRootSums hn (roots_cube_sum e)⟩

noncomputable def representationCode {n : ℕ} (hn : n ≠ 0)
    (e : cubeRepresentations n) : admissibleRootSums n × Bool :=
  (admissibleRootSum hn e, decide (leftRoot e ≤ rightRoot e))

lemma pair_eq_of_add_eq_add_of_cube_add_cube_eq
    {x y u v : ℕ} (hpos : 0 < x + y)
    (hsum : x + y = u + v)
    (hcube : x ^ 3 + y ^ 3 = u ^ 3 + v ^ 3)
    (horient : decide (x ≤ y) = decide (u ≤ v)) :
    (x, y) = (u, v) := by
  have hident :
      x ^ 3 + y ^ 3 + 3 * (x * y) * (x + y) =
        u ^ 3 + v ^ 3 + 3 * (u * v) * (u + v) := by
    calc
      x ^ 3 + y ^ 3 + 3 * (x * y) * (x + y) = (x + y) ^ 3 := by ring
      _ = (u + v) ^ 3 := by rw [hsum]
      _ = u ^ 3 + v ^ 3 + 3 * (u * v) * (u + v) := by ring
  rw [hcube, ← hsum] at hident
  have hscaled : 3 * (x * y) = 3 * (u * v) := by
    exact mul_right_cancel₀ hpos.ne' (Nat.add_left_cancel hident)
  have hprod : x * y = u * v := mul_left_cancel₀ (by norm_num) hscaled
  have hsumZ : (x : ℤ) + y = u + v := by exact_mod_cast hsum
  have hprodZ : (x : ℤ) * y = u * v := by exact_mod_cast hprod
  have hfactor : ((x : ℤ) - u) * ((x : ℤ) - v) = 0 := by
    nlinarith
  have hcases : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
    rcases mul_eq_zero.mp hfactor with hxu | hxv
    · left
      have hxu' : x = u := by exact_mod_cast sub_eq_zero.mp hxu
      exact ⟨hxu', by omega⟩
    · right
      have hxv' : x = v := by exact_mod_cast sub_eq_zero.mp hxv
      exact ⟨hxv', by omega⟩
  rcases hcases with h | h
  · exact Prod.ext h.1 h.2
  · by_cases hxy : x ≤ y
    · have huv : u ≤ v := by
        by_contra huv
        simp [hxy, huv] at horient
      have : x = y := by omega
      exact Prod.ext (by omega) (by omega)
    · have huv : ¬u ≤ v := by
        intro huv
        simp [hxy, huv] at horient
      exfalso
      omega

lemma representationCode_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (representationCode hn) := by
  intro e f hef
  have hsum : leftRoot e + rightRoot e = leftRoot f + rightRoot f := by
    simpa only [representationCode, admissibleRootSum] using
      congrArg (fun z : admissibleRootSums n × Bool => (z.1 : ℕ)) hef
  have horient :
      decide (leftRoot e ≤ rightRoot e) =
        decide (leftRoot f ≤ rightRoot f) := by
    simpa only [representationCode] using congrArg Prod.snd hef
  have hcube :
      leftRoot e ^ 3 + rightRoot e ^ 3 =
        leftRoot f ^ 3 + rightRoot f ^ 3 :=
    (roots_cube_sum e).trans (roots_cube_sum f).symm
  have hroots := pair_eq_of_add_eq_add_of_cube_add_cube_eq
    (by
      by_contra h
      have hzero : leftRoot e + rightRoot e = 0 := Nat.eq_zero_of_not_pos h
      have hcubes := roots_cube_sum e
      have hz := Nat.add_eq_zero_iff.mp hzero
      rw [hz.1, hz.2] at hcubes
      exact hn hcubes.symm)
    hsum hcube horient
  have hleft : leftRoot e = leftRoot f := congrArg Prod.fst hroots
  have hright : rightRoot e = rightRoot f := congrArg Prod.snd hroots
  apply Subtype.ext
  apply Prod.ext
  · calc
      e.1.1 = leftRoot e ^ 3 := (leftRoot_pow_three e).symm
      _ = leftRoot f ^ 3 := by rw [hleft]
      _ = f.1.1 := leftRoot_pow_three f
  · calc
      e.1.2 = rightRoot e ^ 3 := (rightRoot_pow_three e).symm
      _ = rightRoot f ^ 3 := by rw [hright]
      _ = f.1.2 := rightRoot_pow_three f

/-- Every positive integer has at most twice as many ordered two-cube
representations as it has admissible root-sum divisors. -/
theorem sumRep_cubes_le_two_mul_admissibleRootSums_card (n : ℕ) (hn : n ≠ 0) :
    sumRep cubes n ≤ 2 * (admissibleRootSums n).card := by
  rw [sumRep_cubes_eq_card_cubeRepresentations]
  have hcard :
      Fintype.card (cubeRepresentations n) ≤
        Fintype.card (admissibleRootSums n × Bool) :=
    Fintype.card_le_of_injective
      (representationCode hn) (representationCode_injective hn)
  simpa [Nat.mul_comm] using hcard

/-- Every positive `n` has at most twice as many ordered two-cube
representations as divisors in the forced window `n ≤ d^3 ≤ 4n`. -/
theorem sumRep_cubes_le_two_mul_cubicWindowDivisors_card (n : ℕ)
    (hn : n ≠ 0) :
    sumRep cubes n ≤ 2 * (cubicWindowDivisors n).card := by
  exact (sumRep_cubes_le_two_mul_admissibleRootSums_card n hn).trans
    (Nat.mul_le_mul_left 2
      (Finset.card_le_card (admissibleRootSums_subset_cubicWindowDivisors n)))

/-- The discriminant-filtered bound is always at least as strong as the
classical twice-the-divisor-count bound. -/
theorem two_mul_admissibleRootSums_card_le_two_mul_divisors_card (n : ℕ) :
    2 * (admissibleRootSums n).card ≤ 2 * n.divisors.card := by
  exact Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.filter_subset _ _))

/-- Target-facing form: it suffices to bound the number of divisors which pass
the exact discriminant test. -/
theorem sumRep_cubes_isBigO_admissibleRootSums :
    (fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => ((admissibleRootSums n).card : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : n ≠ 0 := by omega
  simpa only [Real.norm_natCast] using
    (show (sumRep cubes n : ℝ) ≤
        2 * ((admissibleRootSums n).card : ℝ) by
      exact_mod_cast sumRep_cubes_le_two_mul_admissibleRootSums_card n hn0)

/-- A fixed-polylogarithmic estimate for admissible root sums would settle the
upper-bound side of Erdős 829. -/
theorem polylog_bound_of_admissibleRootSums_polylog_bound
    (h : ∃ C : ℕ,
      (fun n : ℕ => ((admissibleRootSums n).card : ℝ)) =O[atTop]
        (fun n : ℕ => (Real.log n) ^ C)) :
    ∃ C : ℕ, (fun n : ℕ => (sumRep cubes n : ℝ)) =O[atTop]
      (fun n : ℕ => (Real.log n) ^ C) := by
  rcases h with ⟨C, hC⟩
  exact ⟨C, sumRep_cubes_isBigO_admissibleRootSums.trans hC⟩

/-- The filter is genuinely sharper already at `n = 8`: it retains only root
sum `2`, while `8` has four positive divisors. -/
theorem admissibleRootSums_eight :
    admissibleRootSums 8 = {2} := by
  decide

theorem sumRep_cubes_eight_le_two :
    sumRep cubes 8 ≤ 2 := by
  simpa [admissibleRootSums_eight] using
    sumRep_cubes_le_two_mul_admissibleRootSums_card 8 (by norm_num)

end

end Contribution.Erdos829CubeDiscriminant
