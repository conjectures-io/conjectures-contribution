import Mathlib
import FormalConjectures.ErdosProblems.«242»

/-!
# Erdős Problem 242 (Erdős–Straus): a checked reduction to primes `p ≡ 1 (mod 12)`

`Erdos242.erdos_242` asks, for every `n > 2`, for **strictly increasing** naturals
`1 ≤ x < y < z` with `(4 / n : ℚ) = 1 / x + 1 / y + 1 / z`.

## The obstacle

Every classical attack on Erdős–Straus proceeds one residue class (or one prime) at a time, and
the two glue steps are left informal in the literature:

* *"a solution for a divisor gives a solution for the multiple"* — scaling all three denominators
  by `n / d`;
* *"now split the last unit fraction"* — passing from a **two**-term representation
  `q = 1/x + 1/m` to a **three**-term one.

Both are traps in Lean, because the strict chain `x < y < z` is what the target demands and it is
exactly what naive manipulations destroy (the Sylvester split `1/m = 1/(m+1) + 1/(m(m+1))` only
keeps the chain for `m ≥ 2`, and the two classical identity families produce their three
denominators in *different* orders). Mathlib has no Egyptian-fraction material to build on —
grepping the pinned Mathlib source for `egyptian`, `unitFrac` and `unit fraction` returns nothing,
and `straus` returns only an unrelated Goodman–Strauss tiling citation — so a solver currently
redoes this bookkeeping inside every case of every case split. (The
formal-conjectures repository does define unrelated Egyptian-fraction notions elsewhere,
`Erdos206.egyptianSum` and `Erdos304.unitFractionExpressible`; the latter is a `Finset`-indexed,
*unordered* predicate that also forbids the denominator `1`, so neither one states this target's
ordered conclusion.)

## What is proved here

`IsSumOfThreeUnitFractions` packages the target's conclusion (`target_iff_isSumOfThreeUnitFractions`
below checks this is `Iff.rfl`, i.e. no statement drift), and around it:

* `unitFrac_split`, `of_two_term` — the Sylvester split, and the two-term → three-term interface,
  which discharges the strict chain once for the whole `a ∣ n + 1` family;
* `div_eq_of_mul_eq_succ` — one identity `a / n = c / n + 1 / d + 1 / (n * d)` (valid whenever
  `b * d = n + 1` and `c + b = a`) that specialises to *both* classical families, and is stated
  for a general numerator `a`, so it also covers the single residue class `n ≡ a - 1 (mod a)` of
  `Erdos242.erdos_242.variants.schinzel_generalization` — not that variant's
  eventually-every-`n` statement;
* `of_dvd_succ` — the `a ∣ n + 1` family in ready-to-apply form, general numerator;
* `four_div_of_even`, `four_div_of_three_mod_four`, `four_div_of_two_mod_three` — the three
  covered classes, each an unconditional theorem;
* `IsSumOfThreeUnitFractions.div_nat`, `four_div_of_dvd` — the divisor-to-multiple step;
* `four_div_of_prime_factor_ne_one_mod_twelve` — the unconditional core: any `n > 2` with a prime
  factor outside `1 mod 12` is already solved;
* `prime_factor_one_mod_twelve_of_not` and `mod_twelve_of_not` — the contrapositive packaging: a
  counterexample has *all* prime factors `≡ 1 (mod 12)`, hence is itself `≡ 1 (mod 12)`;
* `reduce_to_primes_one_mod_twelve` and `erdos_242_of_primes_one_mod_twelve` — the reduction, and
  the same statement written in the *literal* syntax of `Erdos242.erdos_242`;
* `erdos_242_iff_primes_one_mod_twelve` — the reduction is an *equivalence*, so the residual
  prime obligation is no stronger than the target it replaces;
* `mul_denom_bounds`, `four_div_denom_bounds` — the bracket `n < 4x < 3n` on the *smallest*
  denominator, which confines that one denominator to an explicit finite range for each `n`. Only
  `x` is bounded here: nothing in this file bounds `y` or `z`, so this alone does not turn the
  remaining prime case into a finite search.

## Handoff (G1)

A later solver can use declaration
`Contribution.Erdos242Reduction.reduce_to_primes_one_mod_twelve` to discharge the obligation
`∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z`
in target `Erdos242.erdos_242`, replacing it by the single obligation for primes `p ≡ 1 (mod 12)`.
The worked use site `erdos_242_of_primes_one_mod_twelve` at the end of this file writes that
replacement out in the literal syntax of the target's conclusion;
`target_iff_isSumOfThreeUnitFractions` certifies by `Iff.rfl` that the two are the same statement,
and `erdos_242_iff_primes_one_mod_twelve` certifies that the replacement gives away nothing.

*References:*
- [erdosproblems.com/242](https://www.erdosproblems.com/242)
-/

namespace Contribution.Erdos242Reduction

/-- `q` is a sum of three unit fractions with strictly increasing positive denominators.
This is *definitionally* the conclusion of `Erdos242.erdos_242` at `q = 4 / n`, and, at
`q = a / n`, the body of the `∀ᶠ` in `Erdos242.erdos_242.variants.schinzel_generalization`. -/
def IsSumOfThreeUnitFractions (q : ℚ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ q = 1 / x + 1 / y + 1 / z

/-- The Sylvester (greedy) split of a unit fraction, with both new denominators kept in `ℕ`. -/
theorem unitFrac_split {m : ℕ} (hm : 1 ≤ m) :
    (1 / m : ℚ) = 1 / ((m + 1 : ℕ) : ℚ) + 1 / ((m * (m + 1) : ℕ) : ℚ) := by
  have h0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Two-term to three-term.** A representation `q = 1/x + 1/m` with `x ≤ m` and `2 ≤ m` upgrades
to a genuine three-term representation with *strictly increasing* denominators. It checks the
strict chain once for the whole `a ∣ n + 1` family (`of_dvd_succ`, hence
`four_div_of_three_mod_four`) and is applied directly, with `x = m`, by `four_div_of_even`. The
`3 ∣ n + 1` family cannot be routed through it — there the middle denominator is `n` itself — so
`four_div_of_two_mod_three` checks its own chain. -/
theorem of_two_term {q : ℚ} {x m : ℕ} (hx : 1 ≤ x) (hxm : x ≤ m) (hm : 2 ≤ m)
    (h : q = 1 / x + 1 / m) : IsSumOfThreeUnitFractions q := by
  refine ⟨x, m + 1, m * (m + 1), hx, by omega, ?_, ?_⟩
  · calc m + 1 < 2 * (m + 1) := by omega
      _ ≤ m * (m + 1) := Nat.mul_le_mul hm (le_refl _)
  · rw [h, unitFrac_split (show 1 ≤ m by omega)]
    ring

/-- **The master identity.** If `b * d = n + 1` and `c + b = a`, then
`a / n = c / n + 1 / d + 1 / (n * d)`.

Taking `c = 0, b = a` gives the classical two-term family (`a ∣ n + 1`), and taking `c = 1,
b = a - 1` gives the classical three-term family (`(a - 1) ∣ n + 1`). Both families for `a = 4`
are used below; the general `a` is what the Schinzel variant needs. -/
theorem div_eq_of_mul_eq_succ {a b c d n : ℕ} (hn : 1 ≤ n) (hbd : b * d = n + 1)
    (habc : c + b = a) :
    ((a : ℚ) / n) = (c : ℚ) / n + 1 / d + 1 / ((n * d : ℕ) : ℚ) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbd' : (b : ℚ) * d = (n : ℚ) + 1 := by exact_mod_cast hbd
  have habc' : (c : ℚ) + b = a := by exact_mod_cast habc
  have hna : (n : ℚ) = (b : ℚ) * d - 1 := by linarith
  have haa : (a : ℚ) = (c : ℚ) + b := by linarith
  have hne : (b : ℚ) * d - 1 ≠ 0 := by rw [← hna]; exact hn0
  push_cast
  rw [hna, haa]
  field_simp
  ring

/-- **The two-term family, for a general numerator.** If `a ∣ n + 1` (and `n ≥ 2`) then
`a / n = 1/d + 1/(n d)` with `d = (n+1)/a`, hence `a / n` is a sum of three unit fractions with
increasing denominators. Stated for general `a`, it is one tool for one residue class of
`Erdos242.erdos_242.variants.schinzel_generalization` — it fires exactly on `n ≡ a - 1 (mod a)`,
density `1 / a`, whereas that variant asks for all sufficiently large `n` — as well as for
`a = 4`. -/
theorem of_dvd_succ {a n : ℕ} (hn : 2 ≤ n) (h : a ∣ n + 1) :
    IsSumOfThreeUnitFractions ((a : ℚ) / n) := by
  obtain ⟨d, hd⟩ := h
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have key := div_eq_of_mul_eq_succ (a := a) (b := a) (c := 0) (d := d) (n := n)
    (by omega) hd.symm (by omega)
  refine of_two_term (x := d) (m := n * d) hd1 (Nat.le_mul_of_pos_left d (by omega)) ?_ ?_
  · calc 2 ≤ n := hn
      _ = n * 1 := (mul_one n).symm
      _ ≤ n * d := Nat.mul_le_mul (le_refl n) hd1
  · push_cast at key ⊢
    linear_combination key

/-- Every even `n ≥ 4` is covered: `4 / (2m) = 1/m + 1/(m+1) + 1/(m(m+1))`. -/
theorem four_div_of_even {n : ℕ} (hn : 4 ≤ n) (h2 : 2 ∣ n) :
    IsSumOfThreeUnitFractions ((4 : ℚ) / n) := by
  obtain ⟨m, rfl⟩ := h2
  have hm : 2 ≤ m := by omega
  have hm0 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine of_two_term (x := m) (m := m) (by omega) (le_refl _) hm ?_
  push_cast
  field_simp
  ring

/-- Every `n ≡ 3 (mod 4)` is covered: `4 ∣ n + 1`, so `of_dvd_succ` applies. -/
theorem four_div_of_three_mod_four {n : ℕ} (hn : 2 ≤ n) (h : n % 4 = 3) :
    IsSumOfThreeUnitFractions ((4 : ℚ) / n) := by
  have key := of_dvd_succ (a := 4) (n := n) hn (by omega)
  push_cast at key
  exact key

/-- Every `n ≡ 2 (mod 3)` with `n ≥ 3` is covered, via `3 ∣ n + 1` and the three-term family:
`4 / n = 1/d + 1/n + 1/(n d)` with `d = (n+1)/3`, and here the *middle* denominator is `n`. -/
theorem four_div_of_two_mod_three {n : ℕ} (hn : 3 ≤ n) (h : n % 3 = 2) :
    IsSumOfThreeUnitFractions ((4 : ℚ) / n) := by
  obtain ⟨d, hd⟩ : ∃ d, 3 * d = n + 1 := ⟨(n + 1) / 3, by omega⟩
  have hd2 : 2 ≤ d := by omega
  have key := div_eq_of_mul_eq_succ (a := 4) (b := 3) (c := 1) (d := d) (n := n)
    (by omega) hd (by omega)
  refine ⟨d, n, n * d, by omega, by omega, ?_, ?_⟩
  · calc n = n * 1 := (mul_one n).symm
      _ < n * d := by
          have : n * 2 ≤ n * d := Nat.mul_le_mul (le_refl n) hd2
          linarith
  · push_cast at key ⊢
    linear_combination key

/-- **Scaling.** Dividing a three-unit-fraction rational by a positive natural again gives one:
scale every denominator by `k`, which preserves the strict chain. -/
theorem IsSumOfThreeUnitFractions.div_nat {q : ℚ} (h : IsSumOfThreeUnitFractions q)
    {k : ℕ} (hk : 1 ≤ k) : IsSumOfThreeUnitFractions (q / k) := by
  obtain ⟨x, y, z, hx, hxy, hyz, rfl⟩ := h
  have hx0 : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hy0 : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz0 : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨k * x, k * y, k * z, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    mul_lt_mul_of_pos_left hxy (by omega), mul_lt_mul_of_pos_left hyz (by omega), ?_⟩
  push_cast
  field_simp

/-- **Divisor to multiple.** A representation for `4 / d` with `d ∣ n` yields one for `4 / n`.
This is the step that lets a solver work with the prime factors of `n` only. -/
theorem four_div_of_dvd {d n : ℕ} (hn : 0 < n) (hdn : d ∣ n)
    (h : IsSumOfThreeUnitFractions ((4 : ℚ) / d)) : IsSumOfThreeUnitFractions ((4 : ℚ) / n) := by
  obtain ⟨k, rfl⟩ := hdn
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have heq : ((4 : ℚ) / ((d * k : ℕ) : ℚ)) = ((4 : ℚ) / (d : ℚ)) / (k : ℚ) := by
    push_cast
    rw [div_div]
  rw [heq]
  exact h.div_nat hk0

/-- **The unconditional core of the reduction.** If `n > 2` has *any* prime factor `p` with
`p % 12 ≠ 1`, then `4 / n` is already a sum of three unit fractions with increasing denominators.
Indeed such a `p` is `2`, or satisfies `p % 4 = 3`, or satisfies `p % 3 = 2`, and each of those
three cases is an unconditional theorem above; `four_div_of_dvd` lifts the solution from `p`
to `n`. -/
theorem four_div_of_prime_factor_ne_one_mod_twelve {n p : ℕ} (hn : 2 < n) (hp : p.Prime)
    (hpn : p ∣ n) (h12 : p % 12 ≠ 1) : IsSumOfThreeUnitFractions ((4 : ℚ) / n) := by
  have hp2 : 2 ≤ p := hp.two_le
  by_cases hp2' : p = 2
  · subst hp2'
    exact four_div_of_even (by omega) hpn
  · have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2')
    by_cases h4 : p % 4 = 3
    · exact four_div_of_dvd (by omega) hpn (four_div_of_three_mod_four (by omega) h4)
    by_cases h3 : p % 3 = 2
    · exact four_div_of_dvd (by omega) hpn (four_div_of_two_mod_three (by omega) h3)
    have hp3 : p % 3 ≠ 0 := by
      intro hcon
      have hdd : (3 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero hcon
      have : (3 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdd
      omega
    exact absurd (by omega : p % 12 = 1) h12

/-- **Structure of a counterexample.** If `n > 2` has no such representation then *every*
prime factor of `n` is `≡ 1 (mod 12)`; `mod_twelve_of_not` below upgrades this to
`n ≡ 1 (mod 12)` for `n` itself. -/
theorem prime_factor_one_mod_twelve_of_not {n : ℕ} (hn : 2 < n)
    (h : ¬ IsSumOfThreeUnitFractions ((4 : ℚ) / n)) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    p % 12 = 1 := by
  by_contra h12
  exact h (four_div_of_prime_factor_ne_one_mod_twelve hn hp hpn h12)

/-- **Any counterexample is `≡ 1 (mod 12)`.** Combining
`prime_factor_one_mod_twelve_of_not` with `four_div_of_dvd` along the prime factorisation:
if `n > 2` has no representation then `n % 12 = 1`. -/
theorem mod_twelve_of_not :
    ∀ n : ℕ, 2 < n → ¬ IsSumOfThreeUnitFractions ((4 : ℚ) / n) → n % 12 = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    obtain ⟨p, hpp, hpdvd⟩ : ∃ p, p.Prime ∧ p ∣ n :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    have hp2 : 2 ≤ p := hpp.two_le
    have hp12 : p % 12 = 1 := prime_factor_one_mod_twelve_of_not hn h hpp hpdvd
    obtain ⟨m, hm⟩ := hpdvd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · rw [Nat.mul_zero] at hm; omega
      · exact hpos
    rcases eq_or_lt_of_le hm1 with hone | hgt
    · rw [← hone, Nat.mul_one] at hm
      omega
    · have hmn : m ∣ n := ⟨p, by rw [hm, Nat.mul_comm]⟩
      have hmlt : m < n := by
        have hmul : 2 * m ≤ p * m := Nat.mul_le_mul hp2 (le_refl m)
        linarith
      have hmnot : ¬ IsSumOfThreeUnitFractions ((4 : ℚ) / m) := fun hc =>
        h (four_div_of_dvd (by omega) hmn hc)
      have hm2 : 2 < m := by
        rcases (show m = 2 ∨ 2 < m by omega) with rfl | h2
        · have hdd : (2 : ℕ) ∣ n := ⟨p, by rw [hm, Nat.mul_comm]⟩
          have h2' := prime_factor_one_mod_twelve_of_not hn h Nat.prime_two hdd
          omega
        · exact h2
      have hmm := ih m hmlt hm2 hmnot
      simp [hm, Nat.mul_mod, hp12, hmm]

/-- **The reduction.** If the Erdős–Straus conjecture holds for every prime `p ≡ 1 (mod 12)`,
then it holds for every `n > 2`. -/
theorem reduce_to_primes_one_mod_twelve
    (H : ∀ p : ℕ, p.Prime → p % 12 = 1 → IsSumOfThreeUnitFractions ((4 : ℚ) / p)) :
    ∀ n : ℕ, 2 < n → IsSumOfThreeUnitFractions ((4 : ℚ) / n) := by
  intro n hn
  have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  by_cases h12 : n.minFac % 12 = 1
  · exact four_div_of_dvd (by omega) hdvd (H _ hp h12)
  · exact four_div_of_prime_factor_ne_one_mod_twelve hn hp hdvd h12

/-- **The reduction is an equivalence.** Conversely, the hypothesis of
`reduce_to_primes_one_mod_twelve` is itself a special case of its conclusion: a prime `p` with
`p % 12 = 1` satisfies `p ≥ 13 > 2`. So the handoff replaces the target by an obligation that is
neither stronger nor weaker than the target restricted to those primes. -/
theorem erdos_242_iff_primes_one_mod_twelve :
    (∀ n : ℕ, 2 < n → IsSumOfThreeUnitFractions ((4 : ℚ) / n)) ↔
      (∀ p : ℕ, p.Prime → p % 12 = 1 → IsSumOfThreeUnitFractions ((4 : ℚ) / p)) := by
  constructor
  · intro T p hp hp12
    have hp2 : 2 ≤ p := hp.two_le
    exact T p (by omega)
  · exact reduce_to_primes_one_mod_twelve

/-- **Search bound (rational form).** In any representation `q = 1/x + 1/y + 1/z` with
`1 ≤ x < y < z`, the smallest denominator is bracketed by `1 < x * q < 3`. -/
theorem mul_denom_bounds {q : ℚ} {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (h : q = 1 / x + 1 / y + 1 / z) : 1 < (x : ℚ) * q ∧ (x : ℚ) * q < 3 := by
  have hx0 : (0 : ℚ) < x := by exact_mod_cast hx
  have hy0 : (0 : ℚ) < y := by exact_mod_cast (by omega : 0 < y)
  have hz0 : (0 : ℚ) < z := by exact_mod_cast (by omega : 0 < z)
  have hxy' : (x : ℚ) < y := by exact_mod_cast hxy
  have hxz' : (x : ℚ) < z := by exact_mod_cast (by omega : x < z)
  have hexp : (x : ℚ) * q = 1 + (x : ℚ) / y + (x : ℚ) / z := by
    rw [h]
    field_simp
  rw [hexp]
  have hpy : (0 : ℚ) < (x : ℚ) / y := div_pos hx0 hy0
  have hpz : (0 : ℚ) < (x : ℚ) / z := div_pos hx0 hz0
  have hly : (x : ℚ) / y < 1 := (div_lt_one hy0).mpr hxy'
  have hlz : (x : ℚ) / z < 1 := (div_lt_one hz0).mpr hxz'
  exact ⟨by linarith, by linarith⟩

/-- **Search bound for the target.** For `4 / n`, the *smallest* denominator of any representation
satisfies `n < 4 * x` and `4 * x < 3 * n`, i.e. it lies strictly between `n / 4` and `3n / 4`.
This confines `x` to an explicit finite range for each fixed `n`; `y` and `z` are not bounded
here. -/
theorem four_div_denom_bounds {n x y z : ℕ} (hn : 0 < n) (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (h : ((4 : ℚ) / n) = 1 / x + 1 / y + 1 / z) : n < 4 * x ∧ 4 * x < 3 * n := by
  obtain ⟨h1, h2⟩ := mul_denom_bounds hx hxy hyz h
  have hn0 : (0 : ℚ) < n := by exact_mod_cast hn
  have hne : (n : ℚ) ≠ 0 := ne_of_gt hn0
  have ex : (n : ℚ) * ((x : ℚ) * (4 / n)) = 4 * x := by field_simp
  have e1 : (n : ℚ) < 4 * x := by
    have h1' := mul_lt_mul_of_pos_left h1 hn0
    rw [mul_one, ex] at h1'
    exact h1'
  have e2 : (4 : ℚ) * x < 3 * n := by
    have h2' := mul_lt_mul_of_pos_left h2 hn0
    rw [ex] at h2'
    linarith
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩

/- ## Worked use sites against the target statement -/

/-- No statement drift: `IsSumOfThreeUnitFractions (4 / n)` **is**, definitionally, the
conclusion of `Erdos242.erdos_242`. -/
theorem target_iff_isSumOfThreeUnitFractions (n : ℕ) :
    IsSumOfThreeUnitFractions ((4 : ℚ) / n) ↔
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z :=
  Iff.rfl

/-- **The handoff, spelled out.** The literal statement of `Erdos242.erdos_242` follows from its
own special case at primes `p ≡ 1 (mod 12)`. A solver attacking the target may now `apply` this
and is left with exactly one obligation, for such primes only. -/
theorem erdos_242_of_primes_one_mod_twelve
    (H : ∀ p : ℕ, p.Prime → p % 12 = 1 →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / p : ℚ) = 1 / x + 1 / y + 1 / z)
    (n : ℕ) (hn : 2 < n) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z :=
  reduce_to_primes_one_mod_twelve
    (fun p hp hp12 => (target_iff_isSumOfThreeUnitFractions p).mpr (H p hp hp12)) n hn

/-- The API really produces witnesses (it is not vacuous): `4/5 = 1/2 + 1/5 + 1/10`, obtained
from `four_div_of_two_mod_three` with `d = 2`. -/
example : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / (5 : ℕ) : ℚ) = 1 / x + 1 / y + 1 / z :=
  (target_iff_isSumOfThreeUnitFractions 5).mp
    (four_div_of_two_mod_three (by norm_num) (by norm_num))

/-- Likewise for the two other covered classes, `4/6` (even) and `4/7` (`7 ≡ 3 mod 4`). -/
example : IsSumOfThreeUnitFractions ((4 : ℚ) / (6 : ℕ)) ∧
    IsSumOfThreeUnitFractions ((4 : ℚ) / (7 : ℕ)) :=
  ⟨four_div_of_even (by norm_num) (by norm_num),
    four_div_of_three_mod_four (by norm_num) (by norm_num)⟩

/-- **Use site for the search bound.** When a solver is left with a prime `p ≡ 1 (mod 12)` and
hunts for the smallest denominator `x`, the range to scan is explicit and finite: `p / 4 < x`
(natural-number division) together with `4 * x < 3 * p`. -/
example (p x y z : ℕ) (hp : 0 < p) (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z)
    (h : (4 / p : ℚ) = 1 / x + 1 / y + 1 / z) : p / 4 < x ∧ 4 * x < 3 * p := by
  obtain ⟨h1, h2⟩ := four_div_denom_bounds hp hx hxy hyz h
  exact ⟨by omega, h2⟩

end Contribution.Erdos242Reduction
