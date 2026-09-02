import Mathlib
import FormalConjectures.ErdosProblems.«406»

/-!
# Erdős 406, the `1,2` variant: a positional-digit API and a checked congruence sieve

Target: `Erdos406.erdos_406.variants.one_two`, i.e.
`IsGreatest { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] } (2 ^ 15)`.

## The obstacle

The membership predicate `Nat.digits 3 n ⊆ [1, 2]` is a *list* statement: `List.Subset` quantifies
over the elements of `Nat.digits 3 n`, a list produced by well-founded recursion. Nothing in
Mathlib lets one attack it for *symbolic* `n`.

* For a concrete numeral the predicate is not an obstacle: plain `decide` does stall at the
  `Decidable` instance `List.decidableBAll`, but Mathlib's simp set (`Nat.digits_of_two_le_of_pos`
  with the `Nat.reduceDiv` / `Nat.reduceMod` simprocs) evaluates `Nat.digits` on numerals, so the
  membership half of the target, `2 ^ 15 ∈ { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] }`, is
  closed by `⟨⟨15, rfl⟩, by norm_num⟩` with no help from this file. The gap is for a *variable*
  `n` (here `2 ^ k` with `k` symbolic), where no simp lemma applies.
* The interesting half, `2 ^ 15 ∈ upperBounds { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] }`,
  is a statement about a *set of naturals*, whereas every actual argument is about the *exponent*
  `k` of a power `2 ^ k`.
* The only realistic elementary attack is a congruence sieve: the low base-`3` digits of `2 ^ k`
  depend only on `2 ^ k mod 3 ^ m`, which is periodic in `k`. Running it requires passing between
  "the list `Nat.digits 3 n` contains a `0`" and the arithmetic predicate `n / 3 ^ i % 3 = 0`, and
  Mathlib has only the two halves of that bridge -- `Nat.getD_digits` (the `i`-th digit is
  `n / b ^ i % b`) and `Nat.lt_digits_length_iff` (when `i` is a genuine position) -- with no
  lemma joining them.

## The contribution

`mem_digits_iff` is the missing bridge, in both directions and with the range side condition
built in: `d ∈ Nat.digits b n ↔ ∃ i, b ^ i ≤ n ∧ n / b ^ i % b = d` (the guard `b ^ i ≤ n` says
exactly that position `i` is a genuine digit position). From it,
`digits_subset_one_two_iff` turns the target's own predicate into positional arithmetic, and
`digits_subset_one_two_iff_forall_lt` makes it a *finite, decidable* check;
`digits_subset_zero_one_iff` does the same for the sibling statement `Erdos406.erdos_406`.
`digits_subset_one_two_succ_iff` is the `rcases`-friendly recursive form, with the hereditary
lemma `digits_div_pow_subset` (closure under deleting trailing digits) and the constructor
`digits_three_mul_add_subset` (closure under appending a digit `1` or `2`) as its two halves.

For the sieve: `digit_eq_of_mod_pow_eq` says low digits depend only on a residue,
`zero_mem_digits_of_residue` converts a residue computation into a genuine `0` digit, and
`zero_mem_digits_two_pow_of_check` assembles them into a sieve engine usable at any modulus
`3 ^ m`. The Euler periodicity it needs is taken straight from Mathlib
(`Nat.pow_totient_mod` together with `Nat.totient_prime_pow`); nothing is re-derived here.

`isGreatest_iff` discharges the membership half of the target once and for all and reduces the
rest to a statement about exponents. `isGreatest_iff_sieved` additionally lets a solver assume
that `k` survives the sieve at `3 ^ 5`.

## What the sieve does *not* do

`card_sieve_survivors` is a checked search: for each `1 ≤ m ≤ 5`, exactly `2 ^ m` of the
`3 ^ (m - 1) * 2` residue classes of the exponent survive the sieve at modulus `3 ^ m`. At
`m = 5` that is the count used by `isGreatest_iff_sieved`: `32` of the `162` classes mod `162`
survive, so `130 / 162 ≈ 80.2%` of the exponents are settled outright. In the checked range the
surviving *count* is `2 ^ m` while the surviving *density* is `(2 / 3) ^ (m - 1)`; the same
pattern is expected for every `m` (it follows from `2` being a primitive root modulo `3 ^ m`),
but that general statement is *not* proved here, only checked for `m ≤ 5`. To be plain about it:
the sieve reduces density, not difficulty. The `32` classes left at `3 ^ 5` still contain the
entire open problem, and no finite instance of this method can close the target. What is offered here is the
bookkeeping, the decidable reformulation and the sieve engine, with the mathematical core left
open in one clearly stated hypothesis.

A later solver can use declaration `isGreatest_iff_sieved` to discharge or simplify obligation
`2 ^ 15 ∈ upperBounds { n | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] }` in target
`Erdos406.erdos_406.variants.one_two`. (`digits_subset_one_two_iff_forall_lt` also closes the
membership half by `decide`, but so does `by norm_num` without this file; that lemma earns its
place for symbolic `n`, not for the numeral `2 ^ 15`.)

The closing section `UseSite` demonstrates both, and ends with a theorem whose statement is
literally the target's, modulo the one hypothesis that is left open.
-/

namespace Contribution.Erdos406OneTwo

/- ### From lists of digits to positional arithmetic -/

/-- `d` is a base-`b` digit of `n` exactly when some genuine position `i` (that is, a position
with `b ^ i ≤ n`) carries the digit `d`. The guard `b ^ i ≤ n` cannot be dropped: for `i` beyond
the length of the expansion of `n` one always has `n / b ^ i % b = 0`. -/
theorem mem_digits_iff {b : ℕ} (hb : 2 ≤ b) (d n : ℕ) :
    d ∈ Nat.digits b n ↔ ∃ i, b ^ i ≤ n ∧ n / b ^ i % b = d := by
  have hb' : 1 < b := hb
  constructor
  · intro h
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem h
    refine ⟨i, (Nat.lt_digits_length_iff hb' n).mp hi, ?_⟩
    rw [← Nat.getD_digits n i hb, List.getD_eq_getElem _ _ hi, hget]
  · rintro ⟨i, hle, heq⟩
    have hi : i < (Nat.digits b n).length := (Nat.lt_digits_length_iff hb' n).mpr hle
    have hget : (Nat.digits b n).getD i 0 = d := by rw [Nat.getD_digits n i hb, heq]
    rw [List.getD_eq_getElem _ _ hi] at hget
    exact hget ▸ List.getElem_mem hi

/-- Having all base-`3` digits in `[1, 2]` is the same as having no `0` digit: the only other
possibilities for a base-`3` digit are `1` and `2`. -/
theorem digits_subset_one_two_iff_zero_notMem (n : ℕ) :
    Nat.digits 3 n ⊆ [1, 2] ↔ 0 ∉ Nat.digits 3 n := by
  constructor
  · intro h h0
    simpa using h h0
  · intro h d hd
    have h3 : d < 3 := Nat.digits_lt_base (by norm_num) hd
    have hd0 : d ≠ 0 := fun e => h (e ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- The target's membership predicate, positionally: every genuine base-`3` position of `n`
carries a nonzero digit. -/
theorem digits_subset_one_two_iff (n : ℕ) :
    Nat.digits 3 n ⊆ [1, 2] ↔ ∀ i, 3 ^ i ≤ n → n / 3 ^ i % 3 ≠ 0 := by
  rw [digits_subset_one_two_iff_zero_notMem, mem_digits_iff (by norm_num)]
  simp only [not_exists, not_and]

/-- A *finite, decidable* form of the target's membership predicate: if `n < 3 ^ m` then only the
positions `i < m` have to be inspected. For explicit `n` and `m` the right-hand side is closed by
`decide`. -/
theorem digits_subset_one_two_iff_forall_lt {n m : ℕ} (hn : n < 3 ^ m) :
    Nat.digits 3 n ⊆ [1, 2] ↔ ∀ i < m, 3 ^ i ≤ n → n / 3 ^ i % 3 ≠ 0 := by
  rw [digits_subset_one_two_iff]
  refine ⟨fun h i _ hi => h i hi, fun h i hi => ?_⟩
  by_cases him : i < m
  · exact h i him hi
  · exact absurd (le_trans (Nat.pow_le_pow_right (by norm_num) (not_lt.mp him)) hi) (by omega)

/-- The same reformulation for the digit pair `[0, 1]`, i.e. for the sibling statement
`Erdos406.erdos_406` in the same source file: having all base-`3` digits in `[0, 1]` means no
position carries the digit `2`. -/
theorem digits_subset_zero_one_iff (n : ℕ) :
    Nat.digits 3 n ⊆ [0, 1] ↔ ∀ i, 3 ^ i ≤ n → n / 3 ^ i % 3 ≠ 2 := by
  rw [show (∀ i, 3 ^ i ≤ n → n / 3 ^ i % 3 ≠ 2) ↔ 2 ∉ Nat.digits 3 n by
    rw [mem_digits_iff (by norm_num)]; simp only [not_exists, not_and]]
  constructor
  · intro h h2
    simpa using h h2
  · intro h d hd
    have h3 : d < 3 := Nat.digits_lt_base (by norm_num) hd
    have hd2 : d ≠ 2 := fun e => h (e ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/- ### Recursive structure of the `1,2` family -/

/-- The `rcases`-friendly recursive form of the target's predicate, peeling off the last base-`3`
digit. Its `mp` direction is the hereditary step, its `mpr` direction the constructor step. -/
theorem digits_subset_one_two_succ_iff {n : ℕ} (hn : n ≠ 0) :
    Nat.digits 3 n ⊆ [1, 2] ↔ n % 3 ≠ 0 ∧ Nat.digits 3 (n / 3) ⊆ [1, 2] := by
  have h3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 3) (Nat.pos_of_ne_zero hn), List.cons_subset]
  refine and_congr_left' ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- Hereditary property: the family is closed under deleting any number of trailing base-`3`
digits. This is what lets a search over the members proceed prefix by prefix. -/
theorem digits_div_pow_subset {n : ℕ} (j : ℕ) (h : Nat.digits 3 n ⊆ [1, 2]) :
    Nat.digits 3 (n / 3 ^ j) ⊆ [1, 2] := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rcases eq_or_ne (n / 3 ^ j) 0 with h0 | h0
    · rw [pow_succ, ← Nat.div_div_eq_div_mul, h0]
      simp
    · rw [pow_succ, ← Nat.div_div_eq_div_mul]
      exact ((digits_subset_one_two_succ_iff h0).mp ih).2

/-- Constructor: appending a digit `1` or `2` stays inside the family. Together with
`digits_div_pow_subset` this says that the members of the family are exactly the nonempty
`{1, 2}`-strings read in base `3`. -/
theorem digits_three_mul_add_subset {n d : ℕ} (hd : d = 1 ∨ d = 2)
    (h : Nat.digits 3 n ⊆ [1, 2]) : Nat.digits 3 (3 * n + d) ⊆ [1, 2] := by
  have hne : 3 * n + d ≠ 0 := by omega
  rw [digits_subset_one_two_succ_iff hne, Nat.mul_add_mod, Nat.mul_add_div (by norm_num)]
  refine ⟨by omega, ?_⟩
  rwa [Nat.div_eq_of_lt (by omega), Nat.add_zero]

/- ### The congruence sieve -/

/-- Low digits depend only on a residue: if `n` and `r` agree modulo `b ^ m`, then they have the
same `i`-th base-`b` digit for every `i < m`. -/
theorem digit_eq_of_mod_pow_eq {b n r m i : ℕ} (hi : i < m) (h : n % b ^ m = r % b ^ m) :
    n / b ^ i % b = r / b ^ i % b := by
  have hdvd : b ^ (i + 1) ∣ b ^ m := pow_dvd_pow b hi
  have key : ∀ x : ℕ, x / b ^ i % b = x % b ^ (i + 1) / b ^ i := by
    intro x
    rw [pow_succ, Nat.mod_mul_right_div_self]
  rw [key n, key r, ← Nat.mod_mod_of_dvd n hdvd, ← Nat.mod_mod_of_dvd r hdvd, h]

/-- Certificate turning a residue computation into a genuine `0` digit: if `3 ^ m ≤ n` and the
residue `n % 3 ^ m` carries a `0` in one of its lowest `m` base-`3` digits, then `n` itself has a
`0` digit, hence is not of the shape the target asks for. -/
theorem zero_mem_digits_of_residue {n m i : ℕ} (hn : 3 ^ m ≤ n) (hi : i < m)
    (h : n % 3 ^ m / 3 ^ i % 3 = 0) : 0 ∈ Nat.digits 3 n := by
  refine (mem_digits_iff (b := 3) (by norm_num) 0 n).mpr ⟨i, ?_, ?_⟩
  · exact le_trans (Nat.pow_le_pow_right (by norm_num) hi.le) hn
  · rw [digit_eq_of_mod_pow_eq hi (Nat.mod_mod_of_dvd n dvd_rfl).symm]
    exact h

/-- The sieve engine, at an arbitrary modulus `3 ^ m`. Hypothesis `h` is a decidable check run on
the single number `k % (3 ^ (m - 1) * 2)`; when it fires, `2 ^ k` has a base-`3` digit equal to
`0`, so `2 ^ k` is not a member of the target's set. The reduction of the exponent `k` to
`k % (3 ^ (m - 1) * 2)` is Euler periodicity, imported from Mathlib as `Nat.pow_totient_mod`
plus `Nat.totient_prime_pow`. -/
theorem zero_mem_digits_two_pow_of_check {k m : ℕ} (hm : 0 < m) (hk : 3 ^ m ≤ 2 ^ k)
    (h : ∃ i < m, 2 ^ (k % (3 ^ (m - 1) * 2)) % 3 ^ m / 3 ^ i % 3 = 0) :
    0 ∈ Nat.digits 3 (2 ^ k) := by
  obtain ⟨i, hi, hzero⟩ := h
  refine zero_mem_digits_of_residue hk hi ?_
  rw [Nat.pow_totient_mod (Nat.one_lt_pow (by omega) (by norm_num))
      (Nat.Coprime.pow_right _ (by norm_num)),
    Nat.totient_prime_pow Nat.prime_three hm]
  exact hzero

/-- The sieve at `m = 5`, spelled out with numerals so that its hypothesis is `decide`-able. -/
theorem zero_mem_digits_two_pow_of_check_five {k : ℕ} (hk : 8 ≤ k)
    (h : ∃ i < 5, 2 ^ (k % 162) % 243 / 3 ^ i % 3 = 0) : 0 ∈ Nat.digits 3 (2 ^ k) := by
  refine zero_mem_digits_two_pow_of_check (m := 5) (by norm_num) ?_ ?_
  · calc (3 : ℕ) ^ 5 ≤ 2 ^ 8 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  · norm_num
    exact h

/-- A checked search bound, and a checked *limit* of the method: for each `1 ≤ m ≤ 5` exactly `2 ^ m`
of the `3 ^ (m - 1) * 2` residue classes of the exponent survive the sieve at modulus `3 ^ m`.

At `m = 5` this is the count consumed by `isGreatest_iff_sieved`: `32` of the `162` classes mod
`162` survive (`162 = 3 ^ 4 * 2`, `243 = 3 ^ 5`), so `130` classes, about `80.2%` of all
exponents, are settled outright. The doubling is the honest caveat: the number of surviving
classes is `2 ^ m` in the checked range `m ≤ 5` even as their density `(2 / 3) ^ (m - 1)`
shrinks (the general `2 ^ m` pattern is expected, since `2` is a primitive root mod `3 ^ m`,
but is only checked here, not proved). Refining the modulus therefore reduces density but not
difficulty -- the survivors still contain the entire open problem, and no finite instance of
this sieve can close the target. -/
theorem card_sieve_survivors :
    ∀ m ∈ [1, 2, 3, 4, 5],
      ((List.range (3 ^ (m - 1) * 2)).countP fun r =>
        ∀ i < m, 2 ^ r % 3 ^ m / 3 ^ i % 3 ≠ 0) = 2 ^ m := by
  decide

/- ### Reduction of the target, and the use site -/

/-- **Reduction to exponents.** The membership half of the target is discharged here (it is also
a one-line `norm_num` fact), and the upper-bound half is shown to be
exactly the statement that `2 ^ k` has a `0` among its base-`3` digits for every `k ≥ 16`. -/
theorem isGreatest_iff :
    IsGreatest { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] } (2 ^ 15) ↔
      ∀ k, 16 ≤ k → 0 ∈ Nat.digits 3 (2 ^ k) := by
  have hmem : Nat.digits 3 (2 ^ 15) ⊆ [1, 2] := by
    rw [digits_subset_one_two_iff_forall_lt (m := 10) (by norm_num)]
    decide
  constructor
  · rintro ⟨-, hub⟩ k hk
    by_contra h0
    have hle : (2 : ℕ) ^ k ≤ 2 ^ 15 :=
      hub ⟨⟨k, rfl⟩, (digits_subset_one_two_iff_zero_notMem _).mpr h0⟩
    have h1 : (2 : ℕ) ^ 16 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    exact absurd (h1.trans hle) (by norm_num)
  · intro h
    refine ⟨⟨⟨15, rfl⟩, hmem⟩, ?_⟩
    rintro n ⟨⟨k, rfl⟩, hn⟩
    by_contra hlt
    push_neg at hlt
    have hk : 16 ≤ k := by
      by_contra hk
      push_neg at hk
      exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (by omega)))
    exact (digits_subset_one_two_iff_zero_notMem _).mp hn (h k hk)

/-- **Reduction to the exponents that survive the sieve.** As `isGreatest_iff`, except that the
solver may additionally assume that `k` passes the test modulo `3 ^ 5`; by
`card_sieve_survivors` this leaves `32` of the `162` residue classes mod `162` -- which is a
smaller set of exponents to worry about, not an easier one. -/
theorem isGreatest_iff_sieved :
    IsGreatest { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] } (2 ^ 15) ↔
      ∀ k, 16 ≤ k → (∀ i < 5, 2 ^ (k % 162) % 243 / 3 ^ i % 3 ≠ 0) →
        0 ∈ Nat.digits 3 (2 ^ k) := by
  rw [isGreatest_iff]
  refine ⟨fun h k hk _ => h k hk, fun h k hk => ?_⟩
  by_cases hc : ∃ i < 5, 2 ^ (k % 162) % 243 / 3 ^ i % 3 = 0
  · exact zero_mem_digits_two_pow_of_check_five (by omega) hc
  · push_neg at hc
    exact h k hk hc

namespace UseSite

/-- Worked example 1: the easy half of the target via the positional route. (`by norm_num` also
closes it; this only demonstrates `digits_subset_one_two_iff_forall_lt` on a numeral.) -/
example : (2 : ℕ) ^ 15 ∈ { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] } :=
  ⟨⟨15, rfl⟩, (digits_subset_one_two_iff_forall_lt (m := 10) (by norm_num)).mpr (by decide)⟩

/-- Worked example 2: the sieve in action. Every exponent `k ≥ 8` with `k ≡ 0 [MOD 162]` is killed
outright, and so are the exponents in `129` further residue classes. -/
example {k : ℕ} (hk : 8 ≤ k) (hmod : k % 162 = 0) : 0 ∈ Nat.digits 3 (2 ^ k) :=
  zero_mem_digits_two_pow_of_check_five hk (by rw [hmod]; decide)

/-- Worked example 3: building members of the family with the constructor lemma, the way a
prefix search would. -/
example : Nat.digits 3 (3 * (3 * 1 + 2) + 1) ⊆ [1, 2] :=
  digits_three_mul_add_subset (by norm_num)
    (digits_three_mul_add_subset (by norm_num) (by norm_num))

/-- Worked example 4, the handoff itself: the target now follows from a sieved statement about
exponents. A solver finishing the `1, 2` variant of Erdős 406 only has to supply `h`; the
`IsGreatest` bookkeeping, the membership half, and `130` of the `162` residue classes of the
exponent are done. The remaining `32` classes are where the mathematics still is. -/
theorem erdos_406_variants_one_two_of_sieved
    (h : ∀ k, 16 ≤ k → (∀ i < 5, 2 ^ (k % 162) % 243 / 3 ^ i % 3 ≠ 0) →
      0 ∈ Nat.digits 3 (2 ^ k)) :
    IsGreatest { n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [1, 2] } (2 ^ 15) :=
  isGreatest_iff_sieved.mpr h

end UseSite

end Contribution.Erdos406OneTwo
