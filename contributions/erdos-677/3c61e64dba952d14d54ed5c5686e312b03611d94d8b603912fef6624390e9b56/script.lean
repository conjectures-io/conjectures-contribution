import Mathlib
import FormalConjectures.ErdosProblems.«677»

/-!
# A prime-witness API for Erdős 677 (`M(n, k) = lcm{n+1, …, n+k}`)

Target: `Erdos677.erdos_677` :
`∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k`,
where `Finset.lcmInterval n k = (Finset.Ioc n (n + k)).lcm id` is `M(n, k)`.

## The obstacle

`lcmInterval` is a `Finset.lcm` over an `Ioc`, and a solver who tries to compute with it
immediately hits two problems.

1. It has *no* unfolding lemma. `simp [Finset.lcmInterval]` does not stop at
   `(Finset.Ioc n (n + k)).lcm id`: on `ℕ` it keeps going through the
   `LocallyFiniteOrder` instance and leaves a goal about
   `List.foldr GCDMonoid.lcm 1 (List.map id (List.range' (n+1) (n+k-n)))`, on which none of
   the `Finset.lcm` API applies. `lcmInterval_eq_lcm_Ioc` is the missing entry point.
2. Beyond the small cases that size alone settles (`erdos_677_of_k_le_two` separates two lcms
   by an inequality, with no prime), the general way to *separate* two lcms is to exhibit a
   prime power dividing one and not the other, and Mathlib has no "prime power divides an lcm"
   lemma: `Nat.Prime.dvd_lcm` covers
   `p ∣ lcm a b` only, and there is no `Finset`-indexed version at all
   (`Finset.lcm_dvd_iff` goes the wrong way — it characterises what the lcm *divides*).
   So the natural argument "the interval `(m, m+k]` contains a prime `p > n+k`, hence
   `p ∣ M(m,k)` but `p ∤ M(n,k)`" cannot even be started.

## What is proved here

`primePow_dvd_lcm_iff` (two arguments), `primePow_dvd_finset_lcm_iff` (any `Finset ℕ`) and
`primePow_dvd_lcmInterval_iff` (the target's definition) supply the missing direction:
for `p` prime and `e > 0`, `p ^ e ∣ M(n,k)` **iff** some element of `(n, n+k]` is divisible by
`p ^ e`. On top of that sits the separation criterion `lcmInterval_ne_of_primePow`, its prime
special case `lcmInterval_ne_of_prime_mem_Ioc`, and the headline reduction.

**A later solver can use declaration `Contribution.Erdos677LcmInterval.erdos_677_of_primeFree`
to discharge or simplify the obligation
`∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k`
in target `Erdos677.erdos_677`**: it reduces that goal to the case where the interval
`(m, m + k]` contains **no prime at all**, which is exactly the hard core of the problem
(whenever `m ≥ n + k`, any prime `p ∈ (m, m+k]` already exceeds `n + k`, so it divides
`M(m,k)` and cannot divide `M(n,k)`).

Two further use sites show the API in action against the real statement:
`erdos_677_of_k_le_two` proves the target outright for all `k ≤ 2`, and
`erdos_677_zero_left` proves the first case `M(k, k) ≠ M(0, k)` of every `k` from Bertrand's
postulate. `not_forall_lcmInterval_ne` checks that the hypothesis `k > 0` cannot be dropped.
-/

namespace Contribution.Erdos677LcmInterval

open Finset

variable {m n k p e a : ℕ}

/- ### Unfolding and basic API -/

/-- The missing unfolding lemma for `Finset.lcmInterval`. Rewriting with this (rather than
`simp [Finset.lcmInterval]`, which unfolds the `ℕ` `LocallyFiniteOrder` instance into
`List.range'`) puts a goal into the shape where the `Finset.lcm` API applies. -/
theorem lcmInterval_eq_lcm_Ioc (n k : ℕ) : lcmInterval n k = (Finset.Ioc n (n + k)).lcm id :=
  rfl

/-- Every member of the interval `(n, n+k]` divides `M(n, k)`. -/
theorem dvd_lcmInterval (h₁ : n < a) (h₂ : a ≤ n + k) : a ∣ lcmInterval n k :=
  Finset.dvd_lcm (f := id) (Finset.mem_Ioc.mpr ⟨h₁, h₂⟩)

/-- `M(n, k)` is positive (for `k = 0` it is the empty lcm `1`). This is the side condition of
every `Nat.le_of_dvd` step in arguments about `lcmInterval`. -/
theorem lcmInterval_pos : 0 < lcmInterval n k := by
  refine Nat.pos_of_ne_zero ?_
  rw [lcmInterval_eq_lcm_Ioc, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, hx0⟩
  rw [Finset.mem_Ioc] at hx
  simp only [id_eq] at hx0
  omega

/-- The basic size bound `n + k ≤ M(n, k)` for `k > 0`. -/
theorem le_lcmInterval (hk : 0 < k) : n + k ≤ lcmInterval n k :=
  Nat.le_of_dvd lcmInterval_pos (dvd_lcmInterval (by omega) le_rfl)

/-- Monotonicity in the interval: if `(n, n+k] ⊆ (n', n'+k']` then `M(n,k) ∣ M(n',k')`.
In particular `M(n, k) ∣ M(n, k')` for `k ≤ k'`. -/
theorem lcmInterval_dvd_lcmInterval {n' k' : ℕ} (h₁ : n' ≤ n) (h₂ : n + k ≤ n' + k') :
    lcmInterval n k ∣ lcmInterval n' k' :=
  Finset.lcm_mono (Finset.Ioc_subset_Ioc h₁ h₂)

/- ### Degenerate and base cases -/

/-- `M(n, 0) = 1`: the empty lcm. -/
theorem lcmInterval_zero_eq_one (n : ℕ) : lcmInterval n 0 = 1 := by
  rw [lcmInterval_eq_lcm_Ioc, Nat.add_zero, Finset.Ioc_self, Finset.lcm_empty]

/-- The hypothesis `k > 0` in `Erdos677.erdos_677` is **necessary**: dropping it makes the
statement false, since `M(m, 0) = M(n, 0) = 1` for all `m, n`. -/
theorem not_forall_lcmInterval_ne :
    ¬ ∀ (m n k : ℕ), m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := fun h =>
  h 1 0 0 (by omega) (by rw [lcmInterval_zero_eq_one, lcmInterval_zero_eq_one])

/-- `M(n, 1) = n + 1`. -/
theorem lcmInterval_one_eq (n : ℕ) : lcmInterval n 1 = n + 1 := by
  rw [lcmInterval_eq_lcm_Ioc, Nat.Ioc_succ_singleton, Finset.lcm_singleton]
  simp

/-- `M(n, 2) = (n + 1)(n + 2)`, because consecutive integers are coprime. -/
theorem lcmInterval_two_eq (n : ℕ) : lcmInterval n 2 = (n + 1) * (n + 2) := by
  have hs : Finset.Ioc n (n + 2) = {n + 1, n + 2} := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcop : Nat.Coprime (n + 1) (n + 2) := by
    have hrw : n + 2 = (n + 1) + 1 := by omega
    rw [hrw, Nat.coprime_self_add_right]
    exact Nat.coprime_one_right _
  rw [lcmInterval_eq_lcm_Ioc, hs, Finset.lcm_insert, Finset.lcm_singleton]
  simp only [id_eq, normalize_eq, lcm_eq_nat_lcm]
  exact hcop.lcm_eq_mul

/- ### Prime powers dividing an lcm -/

/-- A prime power divides `Nat.lcm b c` iff it divides one of `b`, `c`.
This is the prime-power strengthening of `Nat.Prime.dvd_lcm` (which only covers `e = 1`);
it is what makes the exponent of `p` in an lcm computable as a maximum. -/
theorem primePow_dvd_lcm_iff (hp : p.Prime) (b c : ℕ) :
    p ^ e ∣ Nat.lcm b c ↔ p ^ e ∣ b ∨ p ^ e ∣ c := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hbc : Nat.lcm b c ≠ 0 := Nat.lcm_ne_zero hb hc
  rw [hp.pow_dvd_iff_le_factorization hbc, hp.pow_dvd_iff_le_factorization hb,
    hp.pow_dvd_iff_le_factorization hc, Nat.factorization_lcm hb hc]
  simp only [Finsupp.sup_apply, le_sup_iff]

/-- A positive prime power divides the lcm of a finite set of naturals iff it divides one of
its members. (`Finset.lcm_dvd_iff` characterises what the lcm divides; this is the missing
converse direction, valid for prime powers.) -/
theorem primePow_dvd_finset_lcm_iff (hp : p.Prime) (he : 0 < e) (s : Finset ℕ) :
    p ^ e ∣ s.lcm id ↔ ∃ a ∈ s, p ^ e ∣ a := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h1 : 1 < p ^ e := Nat.one_lt_pow (by omega) hp.one_lt
      rw [Finset.lcm_empty]
      constructor
      · intro h
        exact absurd (Nat.le_of_dvd one_pos h) (by omega)
      · rintro ⟨x, hx, -⟩
        simp at hx
  | insert b s _ ih =>
      rw [Finset.lcm_insert, lcm_eq_nat_lcm, primePow_dvd_lcm_iff hp, ih]
      simp

/-- **Prime-power description of `M(n, k)`.** For `p` prime and `e > 0`,
`p ^ e ∣ M(n, k)` iff some element of the interval `(n, n + k]` is divisible by `p ^ e`.
This converts a statement about the bespoke `lcmInterval` into a statement about a single
integer of the interval, which is the form all elementary arguments about `M(n, k)` use. -/
theorem primePow_dvd_lcmInterval_iff (hp : p.Prime) (he : 0 < e) :
    p ^ e ∣ lcmInterval n k ↔ ∃ a, n < a ∧ a ≤ n + k ∧ p ^ e ∣ a := by
  rw [lcmInterval_eq_lcm_Ioc, primePow_dvd_finset_lcm_iff hp he]
  simp only [Finset.mem_Ioc, and_assoc]

/- ### Separation criteria for the target -/

/-- **Separation criterion.** To prove `M(m, k) ≠ M(n, k)` it suffices to exhibit a prime power
`p ^ e` (`e > 0`) that divides some element of `(m, m + k]` and no element of `(n, n + k]`. -/
theorem lcmInterval_ne_of_primePow (hp : p.Prime) (he : 0 < e)
    (ha₁ : m < a) (ha₂ : a ≤ m + k) (hdvd : p ^ e ∣ a)
    (hsep : ∀ b, n < b → b ≤ n + k → ¬ p ^ e ∣ b) :
    lcmInterval m k ≠ lcmInterval n k := by
  intro hEq
  have h1 : p ^ e ∣ lcmInterval m k :=
    (primePow_dvd_lcmInterval_iff hp he).mpr ⟨a, ha₁, ha₂, hdvd⟩
  rw [hEq] at h1
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := (primePow_dvd_lcmInterval_iff hp he).mp h1
  exact hsep b hb₁ hb₂ hb₃

/-- **Prime witness.** A prime `p` lying in `(m, m + k]` and exceeding `n + k` separates the two
lcms: it divides `M(m, k)` and is too large to divide any element of `(n, n + k]`. -/
theorem lcmInterval_ne_of_prime_mem_Ioc (hp : p.Prime) (h₁ : m < p) (h₂ : p ≤ m + k)
    (h₃ : n + k < p) : lcmInterval m k ≠ lcmInterval n k := by
  refine lcmInterval_ne_of_primePow (e := 1) hp one_pos h₁ h₂ (by simp) ?_
  intro b hb₁ hb₂ hd
  rw [pow_one] at hd
  have := Nat.le_of_dvd (by omega) hd
  omega

/- ### The reduction, and worked use sites against `Erdos677.erdos_677` -/

/-- **Reduction of the target to prime-free intervals.** If the statement of
`Erdos677.erdos_677` holds whenever the interval `(m, m + k]` contains no prime, then it holds
in general. Indeed under `m ≥ n + k` a prime `p ∈ (m, m + k]` automatically satisfies
`p > m ≥ n + k`, so `lcmInterval_ne_of_prime_mem_Ioc` applies.

Consequently a solver only has to handle `m, k` for which `(m, m + k]` is a prime gap; any
input of the form "every interval `(x, x + k]` with `x ≥ f k` contains a prime" removes the
remaining cases through `lcmInterval_ne_of_prime_mem_Ioc`. -/
theorem erdos_677_of_primeFree
    (H : ∀ m n k : ℕ, 0 < k → n + k ≤ m → (∀ p ∈ Finset.Ioc m (m + k), ¬ p.Prime) →
      lcmInterval m k ≠ lcmInterval n k) :
    ∀ (m n k : ℕ), k > 0 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := by
  intro m n k hk hm
  by_cases hpf : ∀ p ∈ Finset.Ioc m (m + k), ¬ p.Prime
  · exact H m n k hk hm hpf
  · push_neg at hpf
    obtain ⟨p, hpmem, hp⟩ := hpf
    rw [Finset.mem_Ioc] at hpmem
    exact lcmInterval_ne_of_prime_mem_Ioc hp hpmem.1 hpmem.2 (by omega)

/-- **Worked use site 1.** The statement of `Erdos677.erdos_677` is *proved* for all `k ≤ 2`,
using only the base-case computations above. -/
theorem erdos_677_of_k_le_two :
    ∀ (m n k : ℕ), k > 0 → k ≤ 2 → m ≥ n + k → lcmInterval m k ≠ lcmInterval n k := by
  intro m n k hk hk2 hm
  interval_cases k
  · rw [lcmInterval_one_eq, lcmInterval_one_eq]
    omega
  · rw [lcmInterval_two_eq, lcmInterval_two_eq]
    have : (n + 1) * (n + 2) < (m + 1) * (m + 2) := by nlinarith
    omega

/-- **Worked use site 2.** The first case `n = 0`, `m = k` of the target, for every `k > 0`:
`M(k, k) ≠ M(0, k)`. The prime witness is supplied by Bertrand's postulate, which gives a prime
in `(k, 2k] = (m, m + k]`. -/
theorem erdos_677_zero_left (hk : 0 < k) : lcmInterval k k ≠ lcmInterval 0 k := by
  obtain ⟨p, hp, h₁, h₂⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega)
  exact lcmInterval_ne_of_prime_mem_Ioc hp h₁ (by omega) (by omega)

end Contribution.Erdos677LcmInterval
