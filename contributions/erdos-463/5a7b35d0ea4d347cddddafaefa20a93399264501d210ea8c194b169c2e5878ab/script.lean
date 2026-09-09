import FormalConjectures.ErdosProblems.«463»

/-!
# Erdős 463 is equivalent to the growth of one explicit function

Erdős 463 asks for `f → ∞` such that every large `n` has a composite `m` with
`n + f n < m < n + minFac m`. Define the **reach** of `n` as the largest `d` for which
`n + d` is such a composite. Then the problem is *exactly* the statement `reach → ∞`.
-/

namespace Contribution.Erdos463Reach

open Filter Nat

/-- The admissible offsets at `n`: `d` with `n + d` composite and `d < minFac (n + d)`. -/
def offsets (n : ℕ) : Set ℕ := {d | 0 < d ∧ (n + d).Composite ∧ d < (n + d).minFac}

/-- Admissible offsets are bounded: `d < minFac (n+d) ≤ √(n+d)` forces `d ≤ n`. -/
theorem offsets_le {n d : ℕ} (hd : d ∈ offsets n) : d ≤ n := by
  obtain ⟨_, hc, hlt⟩ := hd
  have hsq : (n + d).minFac ^ 2 ≤ n + d :=
    Nat.minFac_sq_le_self (by omega) hc.2
  nlinarith

theorem offsets_bddAbove (n : ℕ) : BddAbove (offsets n) := ⟨n, fun _ hd => offsets_le hd⟩

/-- The reach of `n`: the largest admissible offset (`0` if there is none). -/
noncomputable def reach (n : ℕ) : ℕ := sSup (offsets n)

theorem le_reach {n d : ℕ} (hd : d ∈ offsets n) : d ≤ reach n :=
  le_csSup (offsets_bddAbove n) hd

theorem reach_mem {n : ℕ} (h : (offsets n).Nonempty) : reach n ∈ offsets n :=
  Nat.sSup_mem h (offsets_bddAbove n)

/-- **Erdős 463 ⟺ `reach → ∞`.** The right-hand side is the exact body of the pinned
statement `Erdos463.erdos_463`. -/
theorem erdos_463_iff_tendsto_reach :
    (∃ (f : ℕ → ℕ) (_ : Tendsto f atTop atTop), ∀ᶠ n in atTop,
        ∃ m, m.Composite ∧ n + f n < m ∧ m < n + m.minFac)
      ↔ Tendsto reach atTop atTop := by
  constructor
  · rintro ⟨f, hf, hev⟩
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N₁, hN₁⟩ := (tendsto_atTop_atTop.mp hf) b
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hev
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    obtain ⟨m, hc, h1, h2⟩ := hN₂ n (le_of_max_le_right hn)
    have hd : m - n ∈ offsets n := by
      refine ⟨by omega, ?_, ?_⟩
      · rw [Nat.add_sub_cancel' (by omega)]; exact hc
      · rw [Nat.add_sub_cancel' (by omega)]; omega
    have := le_reach hd
    have := hN₁ n (le_of_max_le_left hn)
    omega
  · intro hr
    refine ⟨fun n => reach n - 1, ?_, ?_⟩
    · rw [tendsto_atTop_atTop]
      intro b
      obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp hr) (b + 1)
      exact ⟨N, fun n hn => by have := hN n hn; omega⟩
    · obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp hr) 1
      refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
      have hpos : 1 ≤ reach n := hN n hn
      have hne : (offsets n).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        have : reach n = 0 := by simp [reach, hempty]
        omega
      obtain ⟨_, hc, hlt⟩ := reach_mem hne
      exact ⟨n + reach n, hc, by dsimp only; omega, by omega⟩

/-- A certified *hole*: `n = 16` has no admissible offset at all, so `reach 16 = 0`.
(Every `n + d` with `d ≤ 16` is prime or has a prime factor `≤ d`.) -/
theorem reach_sixteen : reach 16 = 0 := by
  have h : offsets 16 = ∅ := by
    ext d
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hd
    have hle : d ≤ 16 := offsets_le hd
    obtain ⟨h0, hc, hlt⟩ := hd
    interval_cases d <;> revert h0 hc hlt <;> norm_num [Nat.Composite]
  simp [reach, h]


/-- Sharper bound: an admissible offset satisfies `d² < n + d`. -/
theorem offsets_sq_lt {n d : ℕ} (hd : d ∈ offsets n) : d * d < n + d := by
  obtain ⟨_, hc, hlt⟩ := hd
  have hsq : (n + d).minFac ^ 2 ≤ n + d := Nat.minFac_sq_le_self (by omega) hc.2
  nlinarith

/-- **`reach` is unbounded** (so `limsup reach = ∞` unconditionally): just below a prime
square `q²` the offset `q − 1` is admissible, since `minFac (q²) = q`. Erdős 463 asks for
the far stronger `liminf reach = ∞`. -/
theorem reach_unbounded (B : ℕ) : ∃ n, B ≤ reach n := by
  obtain ⟨q, hqB, hq⟩ := Nat.exists_infinite_primes (B + 2)
  have h2 : 2 ≤ q := hq.two_le
  have hqq : q ^ 2 - (q - 1) + (q - 1) = q ^ 2 := by
    have hq2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    have : q - 1 ≤ q ^ 2 := le_trans (Nat.sub_le q 1) hq2
    omega
  have hd : q - 1 ∈ offsets (q ^ 2 - (q - 1)) := by
    refine ⟨by omega, ?_, ?_⟩
    · rw [hqq]
      refine ⟨by nlinarith, fun hp => ?_⟩
      have := (Nat.prime_dvd_prime_iff_eq hq hp).mp (dvd_pow_self q two_ne_zero)
      nlinarith
    · rw [hqq, hq.pow_minFac (by norm_num)]
      omega
  exact ⟨q ^ 2 - (q - 1), le_trans (by omega) (le_reach hd)⟩

/-- **The deepest computed hole, certified:** `reach 267380 = 3`. The offset `3` works because
`267383 = 47 · 5689`; and no `d ∈ [4, 517]` works (larger `d` is excluded by `offsets_sq_lt`),
since each `267380 + d` is prime or has a prime factor `≤ d`. -/
theorem reach_267380 : reach 267380 = 3 := by
  have h3 : 3 ∈ offsets 267380 := by
    refine ⟨by norm_num, ?_, ?_⟩
    · norm_num [Nat.Composite]
    · norm_num
  have hle : ∀ d ∈ offsets 267380, d ≤ 3 := by
    intro d hd
    have hsq := offsets_sq_lt hd
    have hB : d ≤ 517 := by nlinarith
    by_contra hgt
    push Not at hgt
    obtain ⟨h0, hc, hlt⟩ := hd
    interval_cases d <;> revert hc hlt <;> norm_num [Nat.Composite]
  exact le_antisymm (csSup_le ⟨3, h3⟩ hle) (le_reach h3)

end Contribution.Erdos463Reach
