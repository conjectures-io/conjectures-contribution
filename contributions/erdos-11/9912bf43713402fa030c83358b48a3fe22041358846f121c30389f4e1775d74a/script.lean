import Mathlib
import FormalConjectures.ErdosProblems.«11»

/-!
# Erdős Problem 11: eliminating `k`, and reducing the `¬ 4 ∣ n` variant to the odd case

Target: `Erdos11.erdos_11` — every odd `n > 1` is of the form `k + 2 ^ l` with `k` squarefree.

## The obstacles this file removes

1. **The witness `k` is a spurious existential.** In `∃ k l, Squarefree k ∧ n = k + 2 ^ l` the
   number `k` is completely determined by `l` (it is `n - 2 ^ l`), and `l` is then forced to
   satisfy `2 ^ l < n`. Every argument about the statement — and every finite verification of
   it — begins by redoing that bookkeeping with truncated `ℕ`-subtraction.
   `exists_squarefree_add_two_pow_iff` does it once and for all, with no hypothesis on `n`.
2. **The relation between `erdos_11` and `erdos_11.variants.not_four_dvd` is left informal.**
   The file records that Erdős "often asked this under the weaker assumption that `n > 1` is
   not divisible by `4`", but nothing connects the two statements. The even numbers added by
   that variant are exactly the `n ≡ 2 [MOD 4]`, i.e. `n = 2 * m` with `m` odd, and the evident
   transfer of a representation of `m` to one of `2 * m` works **only if the squarefree part is
   odd** (`Squarefree (2 * k)` needs `k` odd). So that route does not derive the variant from
   the main problem; it derives it from an odd-squarefree-part strengthening. (No
   non-implication is asserted anywhere in this file: both statements are open, and nothing
   here shows that the variant fails to follow from `erdos_11` — only that this argument for it
   needs the extra parity.)
3. **Nobody has said how much of a strengthening that is.** Here it is bounded from above: on
   `n ≡ 1 [MOD 4]` the strengthening is free, so the whole gap between `erdos_11` and
   `erdos_11.variants.not_four_dvd` is *contained in* the single residue class `n ≡ 3 [MOD 4]`
   — and in fact in the sparser subclass of those `m ≡ 3 [MOD 4]` for which `2 * m - 1` is not
   squarefree, since otherwise `2 * m = (2 * m - 1) + 2 ^ 0` already does the job. Only
   containment is proved; no lower bound on the residual obligation is claimed.

## Note on computation (what actually works in this environment)

Mathlib's `DecidablePred (Squarefree : ℕ → Prop)` is built from `Nat.minSqFac`, which is
defined by well-founded recursion, so **plain `decide` is stuck**: `example : Squarefree 15 :=
by decide` fails here with "reduction got stuck at the `Decidable` instance
`match Nat.minSqFac 15 with ...`". It does **not** follow that there is no computational entry
point: `decide +kernel` reduces the very same instance without difficulty and is fully
kernel-checked (`example : Squarefree 15 := by decide +kernel` succeeds). This file therefore
carries **no squarefreeness test of its own** — it uses stock Mathlib's instance with
`decide +kernel`. (An earlier draft worked around the plain-`decide` failure with a hand-rolled
bounded trial-division test; measured against `decide +kernel` on Mathlib's own instance that
test was the *slower* of the two, so it has been removed rather than shipped.)

Measured in this environment (`leanprover/lean4:v4.27.0`, warm cache). Absolute wall times are
machine-dependent, so the figure that matters is the delta over an `import Mathlib` baseline,
which was ≈ 25s on the box used: this whole file elaborates in ≈ 50s, i.e. the search over odd
`m < 1024` below costs ≈ 25s; widened to odd `m < 4096` (exponents `l < 12`) the same search
costs ≈ 145s on top of the baseline — a 4-fold range for a nearly 6-fold cost, so the cost is
superlinear in the range. That is nowhere near
`erdos_11.variants.finite_bound1` (`n < 10 ^ 7`), let alone `finite_bound2` (`n < 2 ^ 50`):
kernel decision stops more than three orders of magnitude short of `finite_bound1` (`4096`
against `10 ^ 7` is a factor of about `2400`), and **this file makes no attempt on those two
variants**. Do not expect to widen the range below by editing the numerals.

## The contribution

* `exists_squarefree_add_two_pow_iff` — the unconditional `k`-elimination. It is stated in the
  target's own syntactic shape, so `rw` fires on the goal of `Erdos11.erdos_11` directly.
* `IsSumOdd` — the odd-squarefree-part strengthening, with `isSumOdd_iff_of_odd` as its
  `rcases`-friendly single-variable form (for odd `n` it says exactly that the exponent may be
  taken `≥ 1`).
* `IsSumOdd.two_mul` — the doubling bridge, the real content of obstacle 2: an odd squarefree
  part survives multiplication by `2`, via `Nat.squarefree_mul` and coprimality.
* `exists_squarefree_add_two_pow_of_not_four_dvd` — the pointwise reduction, and its two global
  corollaries `not_four_dvd_of_isSumOdd` (the odd strengthening implies the variant outright)
  and `not_four_dvd_of_erdos_11_of_three_mod_four` (given the main problem, the strengthening is
  needed only at those `n ≡ 3 [MOD 4]` with `2 * n - 1` not squarefree — this is obstacle 3,
  made precise).
* `isSumOdd_iff_of_one_mod_four` — the fact that makes the previous line work.
* `two_pow_two_of_erdos_11` — the two-powers variant is an outright consequence of the target.
* `not_four_dvd_lt_1024` — the worked use site, see below.

## Handoff

A later solver can use declaration `Contribution.Erdos11SquarefreeSum.exists_squarefree_add_two_pow_iff`
to simplify obligation `∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l` in target `Erdos11.erdos_11`
to the single-variable search `∃ l : ℕ, 2 ^ l < n ∧ Squarefree (n - 2 ^ l)`.

A later solver can use declaration `Contribution.Erdos11SquarefreeSum.not_four_dvd_of_isSumOdd`
to discharge obligation `∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l` in target
`Erdos11.erdos_11.variants.not_four_dvd`, from a proof of the odd case alone.

`not_four_dvd_lt_1024` is the worked use site: a complete, kernel-checked instance of
`Erdos11.erdos_11.variants.not_four_dvd` for all `1 < n < 1024` with `¬ 4 ∣ n`. Its only
arithmetic input is one stock-Mathlib `decide +kernel` search **over the odd numbers only**;
the even case `n ≡ 2 [MOD 4]` is supplied by the reduction API. It is there to show how the
API composes, not as a record: a direct search over the whole range would also settle this
particular bound, but it would not survive the removal of the bound, whereas the three
reduction lemmas carry any future proof of the odd case to the variant unchanged.
-/

namespace Contribution.Erdos11SquarefreeSum

/- ### Eliminating the witness `k` -/

/-- **The `k`-elimination.** The conclusion of `Erdos11.erdos_11` is equivalent to a search
over the exponent alone. Both hypotheses of the target are unnecessary: a squarefree number is
nonzero, so `2 ^ l < n` comes for free, and the degenerate values `n = 0, 1` are correctly
handled (both sides are false).

The statement is deliberately written in the target's own shape, so a solver can literally
`rw [exists_squarefree_add_two_pow_iff]` on the goal of `Erdos11.erdos_11`, and is left in
terms of truncated subtraction because that is the form in which the resulting predicate is
decidable. -/
theorem exists_squarefree_add_two_pow_iff {n : ℕ} :
    (∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) ↔ ∃ l : ℕ, 2 ^ l < n ∧ Squarefree (n - 2 ^ l) := by
  constructor
  · rintro ⟨k, l, hk, rfl⟩
    have hk0 : k ≠ 0 := hk.ne_zero
    exact ⟨l, by omega, by simpa using hk⟩
  · rintro ⟨l, hlt, hk⟩
    exact ⟨n - 2 ^ l, l, hk, by omega⟩

/- ### The odd-squarefree-part strengthening -/

/-- `IsSumOdd n` is the strengthening of the target's conclusion in which the squarefree part
is required to be **odd**. This is the property that actually propagates to the even numbers
covered by `Erdos11.erdos_11.variants.not_four_dvd`. -/
def IsSumOdd (n : ℕ) : Prop := ∃ k l : ℕ, Squarefree k ∧ Odd k ∧ n = k + 2 ^ l

/-- For odd `n`, requiring the squarefree part to be odd is exactly requiring the exponent to
be positive. This is the `rcases`-friendly single-variable form of `IsSumOdd`, and the shape in
which a finite search produces it. -/
theorem isSumOdd_iff_of_odd {n : ℕ} (hn : Odd n) :
    IsSumOdd n ↔ ∃ l : ℕ, 1 ≤ l ∧ 2 ^ l < n ∧ Squarefree (n - 2 ^ l) := by
  constructor
  · rintro ⟨k, l, hk, hko, rfl⟩
    have hk0 : k ≠ 0 := hk.ne_zero
    have hl : 1 ≤ l := by
      rcases Nat.eq_zero_or_pos l with rfl | h
      · rw [Nat.odd_iff] at hn hko; simp at hn; omega
      · exact h
    exact ⟨l, hl, by omega, by simpa using hk⟩
  · rintro ⟨l, hl, hlt, hk⟩
    refine ⟨n - 2 ^ l, l, hk, ?_, by omega⟩
    have h2 : 2 ∣ 2 ^ l := dvd_pow_self 2 (by omega)
    rw [Nat.odd_iff] at hn ⊢
    omega

/-- **The doubling bridge.** An odd squarefree part survives multiplication by `2`, so a
representation of `n` with odd squarefree part yields one of `2 * n`. This is the step that
takes the odd numbers to the numbers `≡ 2 [MOD 4]`, and it is the reason the evident transfer
of a representation from `m` to `2 * m` does *not* derive
`Erdos11.erdos_11.variants.not_four_dvd` from `Erdos11.erdos_11`: without the parity of `k`,
`2 * k` need not be squarefree. This is a statement about that argument only — the variant is
open, and nothing here proves it does not follow from `Erdos11.erdos_11` by some other route
(see `not_four_dvd_of_erdos_11_of_three_mod_four`, which exploits one). -/
theorem IsSumOdd.two_mul {n : ℕ} (h : IsSumOdd n) :
    ∃ k l : ℕ, Squarefree k ∧ 2 * n = k + 2 ^ l := by
  obtain ⟨k, l, hk, hko, rfl⟩ := h
  refine ⟨2 * k, l + 1, ?_, by ring⟩
  rw [Nat.squarefree_mul (Nat.coprime_two_left.mpr hko)]
  exact ⟨Nat.squarefree_two, hk⟩

/-- **The strengthening is free on `n ≡ 1 [MOD 4]`.** If `n % 4 = 1` then the exponent `l = 0`
is impossible, since it would force `4 ∣ n - 1` to be squarefree; so *every* representation of
such an `n` already has an odd squarefree part. Together with
`not_four_dvd_of_erdos_11_of_three_mod_four` this confines the whole gap between the target
and its `¬ 4 ∣ n` variant to (a subclass of) the class `n ≡ 3 [MOD 4]`. -/
theorem isSumOdd_iff_of_one_mod_four {n : ℕ} (hn : n % 4 = 1) :
    IsSumOdd n ↔ ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  have hodd : Odd n := by rw [Nat.odd_iff]; omega
  constructor
  · rintro ⟨k, l, hk, -, hkl⟩
    exact ⟨k, l, hk, hkl⟩
  · intro h
    obtain ⟨l, hlt, hsq⟩ := exists_squarefree_add_two_pow_iff.mp h
    refine (isSumOdd_iff_of_odd hodd).mpr ⟨l, ?_, hlt, hsq⟩
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · exact absurd (Nat.isUnit_iff.mp (hsq 2 (by simp only [pow_zero]; omega))) (by norm_num)
    · omega

/- ### Reducing the `¬ 4 ∣ n` variant to the odd numbers -/

/-- **The pointwise reduction.** To represent a single `n` with `¬ 4 ∣ n`, it is enough to have
the odd strengthening `IsSumOdd` for the odd numbers `≤ n`: either `n` is odd and one drops the
parity of `k`, or `n = 2 * m` with `m` odd and `IsSumOdd.two_mul` applies. The case `n = 2` is
the base case `2 = 1 + 2 ^ 0`. -/
theorem exists_squarefree_add_two_pow_of_not_four_dvd {n : ℕ} (hn : ¬ 4 ∣ n) (hn' : 1 < n)
    (H : ∀ m : ℕ, Odd m → 1 < m → m ≤ n → IsSumOdd m) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ := he
    have hmo : Odd m := by rw [Nat.odd_iff]; omega
    rcases eq_or_lt_of_le (show 1 ≤ m by omega) with h1 | h1
    · exact ⟨1, 0, squarefree_one, by omega⟩
    · have := (H m hmo h1 (by omega)).two_mul
      rw [two_mul] at this
      exact this
  · obtain ⟨k, l, hk, -, hkl⟩ := H n ho hn' le_rfl
    exact ⟨k, l, hk, hkl⟩

/-- **The odd strengthening implies the variant.** If every odd `n > 1` has a representation
with an *odd* squarefree part, then Erdős' more general question
`Erdos11.erdos_11.variants.not_four_dvd` — every `n > 1` with `¬ 4 ∣ n` — follows. So the only
extra strength needed beyond `Erdos11.erdos_11` is the parity of the squarefree part. -/
theorem not_four_dvd_of_isSumOdd (H : ∀ n : ℕ, Odd n → 1 < n → IsSumOdd n) :
    type_of% Erdos11.erdos_11.variants.not_four_dvd := fun _n hn hn' =>
  exists_squarefree_add_two_pow_of_not_four_dvd hn hn' fun m hm hm1 _ => H m hm hm1

/-- **The gap is contained in the class `n ≡ 3 [MOD 4]`.** Assuming the target
`Erdos11.erdos_11` itself, the `¬ 4 ∣ n` variant follows from the odd strengthening `IsSumOdd`
imposed on *part* of the single residue class `n ≡ 3 [MOD 4]`. Three routes cover everything
else: an odd `n` is handled by `Erdos11.erdos_11` directly; an even `n = 2 * m` is settled
outright by `n = (2 * m - 1) + 2 ^ 0` whenever `2 * m - 1` happens to be squarefree, with no
appeal to `IsSumOdd m` at all; and among the even `n = 2 * m` that remain, those with
`m ≡ 1 [MOD 4]` get `IsSumOdd m` for free from the target (`isSumOdd_iff_of_one_mod_four`). So
`H3` is invoked only at those `m ≡ 3 [MOD 4]` for which `2 * m - 1` is not squarefree — for
instance `n = 14` (`m = 7 ≡ 3 [MOD 4]`) needs nothing from `H3`, since `14 = 13 + 2 ^ 0`. That
subclass is sparse: a sieve run outside Lean over the 250000 values `m ≡ 3 [MOD 4]` below
`10 ^ 6` finds `2 * m - 1` squarefree for 202645 of them, leaving about 19% of the class.

This is strictly sharper than `not_four_dvd_of_isSumOdd`, and it is the statement a solver of
`Erdos11.erdos_11` should aim at next if they want the variant too. Only containment is proved:
nothing here shows that the residual obligation is *needed*, and no lower bound on it is
claimed. -/
theorem not_four_dvd_of_erdos_11_of_three_mod_four (H : type_of% Erdos11.erdos_11)
    (H3 : ∀ n : ℕ, n % 4 = 3 → 1 < n → ¬ Squarefree (2 * n - 1) → IsSumOdd n) :
    type_of% Erdos11.erdos_11.variants.not_four_dvd := by
  intro n hn hn'
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨m, rfl⟩ := he
    have hmo : Odd m := by rw [Nat.odd_iff]; omega
    rcases eq_or_lt_of_le (show 1 ≤ m by omega) with h1 | h1
    · exact ⟨1, 0, squarefree_one, by omega⟩
    · by_cases hsq : Squarefree (2 * m - 1)
      · exact ⟨2 * m - 1, 0, hsq, by omega⟩
      · have hodd : IsSumOdd m := by
          have h14 : m % 4 = 1 ∨ m % 4 = 3 := by have := Nat.odd_iff.mp hmo; omega
          rcases h14 with h1' | h3'
          · exact (isSumOdd_iff_of_one_mod_four h1').mpr (H m hmo h1)
          · exact H3 m h3' h1 hsq
        have hd := hodd.two_mul
        rw [two_mul] at hd
        exact hd
  · exact H n ho hn'

/-- **The two-powers variant is an outright consequence of the target.** Given
`Erdos11.erdos_11`, apply it to `n - 2` (still odd, and `> 1` once `n > 3`) and add back
`2 ^ 1`; the single small case `n = 3` is `1 + 2 ^ 0 + 2 ^ 0`. -/
theorem two_pow_two_of_erdos_11 (H : type_of% Erdos11.erdos_11) :
    type_of% Erdos11.erdos_11.variants.two_pow_two := by
  intro n hn hn'
  rw [Nat.odd_iff] at hn
  rcases eq_or_lt_of_le (show 3 ≤ n by omega) with h3 | h3
  · exact ⟨1, 0, 0, squarefree_one, by omega⟩
  · obtain ⟨k, l, hk, hkl⟩ := H (n - 2) (by rw [Nat.odd_iff]; omega) (by omega)
    exact ⟨k, l, 1, hk, by rw [pow_one]; omega⟩

/- ### Worked use site

A complete, kernel-checked instance of `Erdos11.erdos_11.variants.not_four_dvd` below `1024`.
The whole arithmetic input is the single `decide +kernel` search `key`, which runs over the
**odd** numbers only and uses Mathlib's own `DecidablePred Squarefree` instance (no test of our
own); everything else — in particular every even `n ≡ 2 [MOD 4]` — is supplied by the reduction
lemmas above. -/

/-- Every `1 < n < 1024` with `¬ 4 ∣ n` is the sum of a squarefree number and a power of two:
the bounded instance of `Erdos11.erdos_11.variants.not_four_dvd`. -/
theorem not_four_dvd_lt_1024 (n : ℕ) (hn : ¬ 4 ∣ n) (h : n < 1024) (hn' : 1 < n) :
    ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  have key : ∀ m < 1024, Odd m → 1 < m →
      ∃ l ∈ Finset.range 10, 1 ≤ l ∧ Squarefree (m - 2 ^ l) := by decide +kernel
  refine exists_squarefree_add_two_pow_of_not_four_dvd hn hn' fun m hm hm1 hmn => ?_
  obtain ⟨l, -, hl1, hsq⟩ := key m (by omega) hm hm1
  have hne := hsq.ne_zero
  exact (isSumOdd_iff_of_odd hm).mpr ⟨l, hl1, by omega, hsq⟩

end Contribution.Erdos11SquarefreeSum
