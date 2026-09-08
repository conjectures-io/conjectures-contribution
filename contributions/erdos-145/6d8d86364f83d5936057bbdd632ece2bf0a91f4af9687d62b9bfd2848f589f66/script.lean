import Mathlib
import FormalConjectures.ErdosProblems.«145»

/-!
# Erdős Problem 145: squarefree gaps, the squarefree density, and the cases `α = 0`, `α = 1`

Target: `Erdos145.erdos_145` — with `s 0 < s 1 < ⋯` the squarefree numbers
(`Erdos145.s n = Nat.nth Squarefree n`) and `Erdos145.A x` the set of indices `n` with
`s n ≤ x`, does `(1 / x) * ∑ n ∈ A x, (s (n + 1) - s n) ^ α` converge as `x → ∞` for every
`α ≥ 0`?

## The obstacle

The pool file states three companions — `erdos_145.variants.le_two` (`α ∈ [0, 2]`, Erdős 1951),
`erdos_145.variants.le_three` (`α ∈ [0, 3]`, Hooley 1973) and
`erdos_145.variants.le_eleven_thirds` (`α ∈ [0, 11/3]`, Greaves–Harman–Huxley 1997) — all with
the *same* unproved conclusion
`∃ β, Tendsto (fun x ↦ 1 / x * ∑ n ∈ A x, (s (n + 1) - s n : ℝ) ^ α) atTop (𝓝 β)`.
Each needs two ingredients that are absent from the pool file and from Mathlib:

* a *gap bound* for consecutive squarefree numbers — grepping the pinned Mathlib for
  `Squarefree` turns up no statement locating a squarefree number in a short interval;
* *counting* information for `{n ≤ x | Squarefree n}` — the pinned Mathlib has `Squarefree`,
  the Möbius function and a sieve file, but no bound on, and no asymptotic for, the squarefree
  counting function; in particular the squarefree density is not available anywhere in
  Mathlib or in `FormalConjecturesForMathlib`.

The density is exactly the `α = 0` case, since `(s (n + 1) - s n) ^ (0 : ℝ) = 1` makes the
sum the number of squarefree integers `≤ x`; and the gap bound is exactly what the `α = 1`
case needs, since that sum telescopes.  This file supplies both, fully checked, and settles
those two exponents outright.

## What is proved

**A uniform periodic-counting bound.**  Mathlib already counts a periodic predicate over one
full period: `Nat.filter_Ico_card_eq_of_periodic` (`Mathlib/Data/Nat/Periodic.lean`) gives
`#{n ∈ Ico k (k + P) | p n} = P.count p`, and that lemma is what proves `card_filter_Ioc_mul`
here.  What Mathlib does not have, and what this file adds, is the *uniform-in-`N`* error
bound `abs_card_filter_Ioc_sub_le`: if `p : ℕ → Prop` is `Function.Periodic` with period `P`,
`0 < P`, then for every `N`
`|#{n ∈ Ioc 0 N | p n} - N * #{n ∈ Ioc 0 P | p n} / P| ≤ P`,
an error that does not grow with `N`.  `card_filter_Ioc_split` cuts a filtered count at an
interior point.  `sum_inv_sq_Icc_le` is the tail bound `∑_{d = a+1}^{M} 1/d² ≤ 1/a`, deduced
here from Mathlib's sharper `sum_Ioc_inv_sq_le_sub` (`Mathlib/Analysis/PSeries.lean`) in the
`1/(d*d)`-over-`Icc` shape that the sieve arguments below consume.

**An elementary sieve, giving squarefree gaps.**  `exists_squarefree_mem_Ioc`: if `0 < t` and
`16 * (m + t) < (t + 4) ^ 2` then `(m, m + t]` contains a squarefree number — a non-squarefree
`n` is divisible by `d * d` for some prime `d ≤ √(m + t)`, such multiples number at most
`t / d² + 1` (`card_filter_dvd_Ioc`, `card_filter_dvd_Ioc_le`), and `∑_{d ≥ 2} 1/d² ≤ 3/4`
leaves a quarter of the interval uncovered.  `nextSquarefree` is the least squarefree number
above `m`, characterised as such by `isLeast_nextSquarefree` (an `IsLeast` bridge to standard
Mathlib vocabulary, and the only order fact about the definition used below); the sieve then
gives
`nextSquarefree_le`: `nextSquarefree m ≤ m + 4 * Nat.sqrt m + 8`, and `s_succ_le` in the
target's own sequence.

**Two-sided counting bounds, valid for every `N`.**  Run over `(0, N]` the same sieve gives
`card_squarefree_Ioc_ge`: `N / 4 ≤ #{n ∈ Ioc 0 N | Squarefree n}`, with no error term; and
`card_squarefree_Ioc_le`: `#{n ∈ Ioc 0 N | Squarefree n} ≤ 3 N / 4 + 1`, because every
multiple of `4` is non-squarefree.

**The squarefree density exists** (`exists_tendsto_squarefree_density`):
`∃ L, Tendsto (fun x : ℝ ↦ #{n ∈ Ioc 0 ⌊x⌋₊ | Squarefree n} / x) atTop (𝓝 L)`.
The proof is self-contained and avoids Möbius inversion.  For each `D`, `SieveFree D` (no
`d² ∣ n` for `2 ≤ d ≤ D`) is periodic with period `sieveModulus D = (D !)²`
(`sieveFree_periodic`), so `abs_card_filter_Ioc_sub_le` counts it with error `≤ (D !)²`
uniformly in `N`; and it overshoots the squarefree count by at most `N / D`
(`card_sieveFree_le`, from `sum_inv_sq_Icc_le`).  Together
(`abs_squarefree_count_div_sub_le`) the ratio `#{n ≤ N | Squarefree n} / N` sits within
`1 / D + (D !)² / N` of a constant depending only on `D`, so it is Cauchy
(`exists_tendsto_squarefree_count`) and the limit transfers to a real variable through
Mathlib's `tendsto_nat_floor_div_atTop`.  The classical value is `6 / π² = 0.6079…`,
which this argument does not identify; `squarefree_density_exists_mem_Icc` does pin it to
`[1/4, 3/4]`, so the squarefree numbers are proved to have positive density and *not* to have
full density.

**Two exponents of the solved companions, proved.**  `A_eq_range` and `card_A_eq` identify the
target's index set (`#(A x) = #{n ∈ Ioc 0 ⌊x⌋₊ | Squarefree n}`); `s_zero` and `sum_sub_eq`
telescope the `α = 1` sum to `nextSquarefree ⌊x⌋₊ - 1`.
* `erdos_145_variants_le_two_at_one` proves the `α = 1` case, with the limit *computed*:
  `tendsto_sum_rpow_one` shows the average tends to `1`.
* `erdos_145_variants_le_two_at_zero` proves the `α = 0` case from the density.
Both are verbatim the conclusion of `Erdos145.erdos_145.variants.le_two` at a legal `α` (and
of `variants.le_three` and `variants.le_eleven_thirds`, whose conclusions are the same
formula).  The match is definitional, not approximate: with `h : (1 : ℝ) ∈ Set.Icc 0 2` and
`h' : (0 : ℝ) ∈ Set.Icc 0 2`, both
`example : erdos_145_variants_le_two_at_one = Erdos145.erdos_145.variants.le_two h := rfl` and
`example : erdos_145_variants_le_two_at_zero = Erdos145.erdos_145.variants.le_two h' := rfl`
typecheck; all six such checks (two exponents against each of the three companions) were run
in a scratch file and deliberately not kept here, so that no declaration in this file depends
on an unproved one.

**Two-sided bounds for `0 ≤ α ≤ 1`.**  Each summand lies between `1` and the gap itself, so
`bounds_of_le_one` traps the target's quantity between `1/4 - 1/x` and `1 + 4/√x + 7/x`, and
`mem_Icc_of_tendsto` forces *any* limit claimed by the companions for `0 ≤ α ≤ 1` into
`[1/4, 1]`.

## Handoff

A later solver can use declaration `Contribution.Erdos145Squarefree.avg_rpow_zero` to
discharge or simplify obligation `Erdos145.erdos_145.variants.le_two` in target
`Erdos145.erdos_145`: it rewrites that obligation's average into the squarefree counting
ratio `#{n ∈ Ioc 0 ⌊x⌋₊ | Squarefree n} / x` at `α = 0`.  Precisely, and no more than this:
composed with `exists_tendsto_squarefree_density` it discharges the **`α = 0` instance** of
that obligation, which is `erdos_145_variants_le_two_at_zero` below; the companion quantifies
over all `α ∈ Set.Icc 0 2`, so the companion itself is *not* closed by this file.  Likewise
`sum_sub_eq` rewrites the same obligation's sum at `α = 1` into the closed form
`nextSquarefree ⌊x⌋₊ - 1`, which with `nextSquarefree_le` settles the `α = 1` instance
(`erdos_145_variants_le_two_at_one`).  The open target `Erdos145.erdos_145` itself is
untouched.
-/

namespace Contribution.Erdos145Squarefree

open Filter Finset
open scoped Topology

/- ### Tail sums of `1 / d²` -/

/-- The tail bound `∑_{d = a+1}^{M} 1/d² ≤ 1/a`.  This is Mathlib's strictly sharper
`sum_Ioc_inv_sq_le_sub` (`Mathlib/Analysis/PSeries.lean`, which gives
`(k : α)⁻¹ - (n : α)⁻¹`) transported to the `1/(d*d)`-over-`Finset.Icc` shape, and extended to
the degenerate range `M < a` where the sum is empty.  It is the numerical input both to the
gap sieve and to the density argument: it is what makes the sieve's error term `O(1/D)`. -/
theorem sum_inv_sq_Icc_le {a : ℕ} (ha : 1 ≤ a) (M : ℕ) :
    ∑ d ∈ Finset.Icc (a + 1) M, (1 : ℝ) / (d * d) ≤ 1 / a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  rcases Nat.lt_or_ge M a with h | h
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hIcc : Finset.Icc (a + 1) M = Finset.Ioc a M := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have hterm : ∀ d ∈ Finset.Ioc a M, (1 : ℝ) / (d * d) = ((d : ℝ) ^ 2)⁻¹ := by
      intro d _; rw [sq, one_div]
    rw [hIcc, Finset.sum_congr rfl hterm]
    have hmain := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := a) (n := M) (by omega) h
    have hM : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
    rw [one_div]
    linarith

/-- `∑_{d = 2}^{D} 1/d² ≤ 3/4`: the *strict* deficit `1 - 3/4` is what leaves room for a
squarefree number in `exists_squarefree_mem_Ioc` and in `card_squarefree_Ioc_ge`. -/
theorem sum_inv_sq_Icc_two_le (D : ℕ) : ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / (d * d) ≤ 3 / 4 := by
  rcases Nat.lt_or_ge D 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; norm_num
  · have hins : Finset.Icc 2 D = insert 2 (Finset.Icc 3 D) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hins, Finset.sum_insert (by simp)]
    have h2 := sum_inv_sq_Icc_le (a := 2) (by norm_num) D
    norm_num at h2 ⊢
    linarith

/- ### Counting a predicate in an interval -/

/-- Cutting a filtered count at an interior point. -/
theorem card_filter_Ioc_split {p : ℕ → Prop} [DecidablePred p] {a b : ℕ} (h : a ≤ b) :
    #{n ∈ Finset.Ioc 0 a | p n} + #{n ∈ Finset.Ioc a b | p n} = #{n ∈ Finset.Ioc 0 b | p n} := by
  rw [← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) h, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl))]

/-- Exact count of the multiples of `k` in `(m, m + t]`, in the form
`m / k + #multiples = (m + t) / k` (no truncated subtraction). -/
theorem card_filter_dvd_Ioc (m t k : ℕ) :
    m / k + #{n ∈ Finset.Ioc m (m + t) | k ∣ n} = (m + t) / k := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div (m + t) k, ← Nat.Ioc_filter_dvd_card_eq_div m k]
  exact card_filter_Ioc_split (p := fun n => k ∣ n) (Nat.le_add_right m t)

/-- There are at most `t / k + 1` multiples of `k` in an interval `(m, m + t]`. -/
theorem card_filter_dvd_Ioc_le (m t : ℕ) {k : ℕ} (hk : 0 < k) :
    (#{n ∈ Finset.Ioc m (m + t) | k ∣ n} : ℝ) ≤ t / k + 1 := by
  have h := card_filter_dvd_Ioc m t k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (((m + t) / k : ℕ) : ℝ) ≤ ((m : ℝ) + t) / k := by
    have h' := Nat.cast_div_le (α := ℝ) (m := m + t) (n := k)
    push_cast at h'
    exact h'
  have h2 : ((m : ℝ)) / k - 1 < ((m / k : ℕ) : ℝ) := by
    have hm := Nat.div_add_mod m k
    have hlt := Nat.mod_lt m hk
    have hcast : (m : ℝ) < k * ((m / k : ℕ) : ℝ) + k := by
      have h' : (m : ℝ) = k * ((m / k : ℕ) : ℝ) + ((m % k : ℕ) : ℝ) := by exact_mod_cast hm.symm
      have h3 : ((m % k : ℕ) : ℝ) < k := by exact_mod_cast hlt
      linarith
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hk0]
    linarith [hcast]
  have h3 : (((m + t) / k : ℕ) : ℝ)
      = ((m / k : ℕ) : ℝ) + (#{n ∈ Finset.Ioc m (m + t) | k ∣ n} : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h.symm
  have h4 : ((m : ℝ) + t) / k = (m : ℝ) / k + (t : ℝ) / k := by ring
  linarith

/- ### Counting a periodic predicate

The per-block count is Mathlib's `Nat.filter_Ico_card_eq_of_periodic`; it is used verbatim in
`card_filter_Ioc_mul` below.  What is built here is the *uniform-in-`N`* error bound
`abs_card_filter_Ioc_sub_le`, which Mathlib does not have. -/

/-- Over a whole number of periods the count is exact.  The per-block equality is Mathlib's
`Nat.filter_Ico_card_eq_of_periodic`, up to the `Ioc`/`Ico` index shift. -/
theorem card_filter_Ioc_mul {p : ℕ → Prop} [DecidablePred p] {P : ℕ}
    (hper : Function.Periodic p P) (k : ℕ) :
    #{n ∈ Finset.Ioc 0 (k * P) | p n} = k * #{n ∈ Finset.Ioc 0 P | p n} := by
  have hblock : ∀ j : ℕ,
      #{n ∈ Finset.Ioc (j * P) (j * P + P) | p n} = #{n ∈ Finset.Ioc 0 P | p n} := by
    intro j
    have e1 : Finset.Ioc (j * P) (j * P + P) = Finset.Ico (j * P + 1) (j * P + 1 + P) := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    have e2 : Finset.Ioc 0 P = Finset.Ico 1 (1 + P) := by
      ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [e1, e2, Nat.filter_Ico_card_eq_of_periodic _ _ _ hper,
      Nat.filter_Ico_card_eq_of_periodic _ _ _ hper]
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit := card_filter_Ioc_split (p := p) (a := k * P) (b := k * P + P) (by omega)
    have he : (k + 1) * P = k * P + P := by ring
    rw [he, ← hsplit, ih, hblock k]
    ring

/-- **Periodic counting, uniformly in `N`.**  A predicate on `ℕ` invariant under `· + P`
(`0 < P`) has an exact density `#{n ∈ Ioc 0 P | p n} / P`, with an error bounded by the period
`P` *for every `N` at once*.  This is the engine of the density argument below: the error does
not grow with `N`, so dividing by `N` sends it to `0`.  Mathlib's
`Nat.filter_Ico_card_eq_of_periodic` supplies only the exact count over one period, which is
the `card_filter_Ioc_mul` half of the argument. -/
theorem abs_card_filter_Ioc_sub_le {p : ℕ → Prop} [DecidablePred p] {P : ℕ} (hP : 0 < P)
    (hper : Function.Periodic p P) (N : ℕ) :
    |(#{n ∈ Finset.Ioc 0 N | p n} : ℝ)
      - (N : ℝ) * (#{n ∈ Finset.Ioc 0 P | p n} : ℝ) / P| ≤ P := by
  set c := #{n ∈ Finset.Ioc 0 P | p n} with hc
  have hcP : c ≤ P := by
    calc c ≤ #(Finset.Ioc 0 P) := Finset.card_filter_le _ _
      _ = P := by simp
  set k := N / P with hk
  have hkP : k * P ≤ N := Nat.div_mul_le_self N P
  have hlt : N < k * P + P := by
    have h1 := (Nat.div_lt_iff_lt_mul hP).1 (Nat.lt_succ_self k)
    rw [Nat.succ_mul] at h1
    omega
  have hsplit := card_filter_Ioc_split (p := p) (a := k * P) (b := N) hkP
  rw [card_filter_Ioc_mul hper k, ← hc] at hsplit
  have hmid : #{n ∈ Finset.Ioc (k * P) N | p n} ≤ N - k * P := by
    calc #{n ∈ Finset.Ioc (k * P) N | p n} ≤ #(Finset.Ioc (k * P) N) := Finset.card_filter_le _ _
      _ = N - k * P := by rw [Nat.card_Ioc]
  have hlow : k * c ≤ #{n ∈ Finset.Ioc 0 N | p n} := by omega
  have hupp : #{n ∈ Finset.Ioc 0 N | p n} ≤ k * c + (N - k * P) := by omega
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hNr : (N : ℝ) = (k : ℝ) * P + ((N - k * P : ℕ) : ℝ) := by
    have hn : k * P + (N - k * P) = N := by omega
    exact_mod_cast hn.symm
  have hlowR : ((k : ℝ)) * c ≤ (#{n ∈ Finset.Ioc 0 N | p n} : ℝ) := by exact_mod_cast hlow
  have huppR : (#{n ∈ Finset.Ioc 0 N | p n} : ℝ) ≤ (k : ℝ) * c + ((N - k * P : ℕ) : ℝ) := by
    exact_mod_cast hupp
  have hrP : ((N - k * P : ℕ) : ℝ) ≤ P := by
    have h1 : N - k * P ≤ P := by omega
    exact_mod_cast h1
  have hr0 : (0 : ℝ) ≤ ((N - k * P : ℕ) : ℝ) := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hcPR : (c : ℝ) ≤ P := by exact_mod_cast hcP
  have hexp : (N : ℝ) * (c : ℝ) / P = (k : ℝ) * c + ((N - k * P : ℕ) : ℝ) * c / P := by
    rw [hNr]; field_simp
  have hfrac : 0 ≤ ((N - k * P : ℕ) : ℝ) * c / P := by positivity
  have hfrac2 : ((N - k * P : ℕ) : ℝ) * c / P ≤ P := by
    rw [div_le_iff₀ hP0]
    nlinarith
  rw [abs_le]
  constructor
  · rw [hexp]; linarith
  · rw [hexp]; linarith

/- ### An elementary sieve: squarefree numbers in short intervals -/

/-- **Squarefree numbers in short intervals.**  If `0 < t` and `16 * (m + t) < (t + 4) ^ 2`,
then `(m, m + t]` contains a squarefree number.  Since the hypothesis holds for `t` slightly
larger than `4 √m`, this is an elementary `O(√m)` bound on squarefree gaps. -/
theorem exists_squarefree_mem_Ioc {m t : ℕ} (ht : 0 < t) (h : 16 * (m + t) < (t + 4) ^ 2) :
    ∃ n ∈ Finset.Ioc m (m + t), Squarefree n := by
  by_contra hcon
  push_neg at hcon
  have hD1 : 1 ≤ Nat.sqrt (m + t) := by
    rw [Nat.le_sqrt]
    omega
  set D := Nat.sqrt (m + t) with hDdef
  have hsub : Finset.Ioc m (m + t) ⊆
      (Finset.Icc 2 D).biUnion (fun d => {n ∈ Finset.Ioc m (m + t) | d * d ∣ n}) := by
    intro n hn
    have hns := hcon n hn
    simp only [Finset.mem_Ioc] at hn
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push_neg at hns
    obtain ⟨p, hp, hpd⟩ := hns
    have hp2 : 2 ≤ p := hp.two_le
    have hple : p * p ≤ n := Nat.le_of_dvd (by omega) hpd
    refine Finset.mem_biUnion.2 ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      refine ⟨hp2, ?_⟩
      rw [hDdef, Nat.le_sqrt]
      omega
    · simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hn.1, hn.2⟩, hpd⟩
  have hcard : t ≤ ∑ d ∈ Finset.Icc 2 D, #{n ∈ Finset.Ioc m (m + t) | d * d ∣ n} := by
    calc t = #(Finset.Ioc m (m + t)) := by rw [Nat.card_Ioc]; omega
      _ ≤ _ := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h1 : (t : ℝ) ≤ ∑ d ∈ Finset.Icc 2 D,
      ((#{n ∈ Finset.Ioc m (m + t) | d * d ∣ n} : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have h2 : ∀ d ∈ Finset.Icc 2 D,
      ((#{n ∈ Finset.Ioc m (m + t) | d * d ∣ n} : ℕ) : ℝ) ≤ (t : ℝ) * (1 / ((d : ℝ) * d)) + 1 := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    have hdd : 0 < d * d := by nlinarith [hd.1]
    have hle := card_filter_dvd_Ioc_le m t hdd
    have hrw : (t : ℝ) / ((d * d : ℕ) : ℝ) = (t : ℝ) * (1 / ((d : ℝ) * d)) := by
      push_cast
      ring
    rw [hrw] at hle
    exact hle
  have h3 : (t : ℝ) ≤ (t : ℝ) * (3 / 4) + ((D : ℝ) - 1) := by
    have h4 := h1.trans (Finset.sum_le_sum h2)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h4
    have h5 : (∑ _d ∈ Finset.Icc 2 D, (1 : ℝ)) = ((D : ℝ) - 1) := by
      rw [Finset.sum_const, Nat.card_Icc]
      have hc : (D + 1 - 2 : ℕ) = D - 1 := by omega
      rw [hc, nsmul_eq_mul, Nat.cast_sub hD1]
      push_cast
      ring
    rw [h5] at h4
    have h6 := sum_inv_sq_Icc_two_le D
    nlinarith [Nat.cast_nonneg (α := ℝ) t]
  have h7 : (t : ℝ) + 4 ≤ 4 * (D : ℝ) := by linarith
  have h8 : t + 4 ≤ 4 * D := by exact_mod_cast h7
  have h9 : D ^ 2 ≤ m + t := Nat.sqrt_le' (m + t)
  nlinarith

/-- Every `m` is followed by a squarefree number within `4 √m + 8`. -/
theorem exists_squarefree_Ioc_sqrt (m : ℕ) :
    ∃ n, m < n ∧ n ≤ m + 4 * Nat.sqrt m + 8 ∧ Squarefree n := by
  have hlt := Nat.lt_succ_sqrt' m
  obtain ⟨n, hn, hsf⟩ :=
    exists_squarefree_mem_Ioc (m := m) (t := 4 * Nat.sqrt m + 8) (by omega) (by nlinarith)
  simp only [Finset.mem_Ioc] at hn
  exact ⟨n, hn.1, by omega, hsf⟩

/- ### The next squarefree number -/

/-- The least squarefree number strictly larger than `m`. -/
noncomputable def nextSquarefree (m : ℕ) : ℕ := Nat.nth Squarefree (Nat.count Squarefree (m + 1))

/-- **The specification of `nextSquarefree`**, as a bridge to Mathlib's `IsLeast`:
`nextSquarefree m` is the least element of `{n | m < n ∧ Squarefree n}`.  Membership gives
`m < nextSquarefree m` and `Squarefree (nextSquarefree m)`; minimality gives
`nextSquarefree m ≤ n` for every squarefree `n > m`.  This is the complete order API of the
definition: `nextSquarefree_le` and `tendsto_nextSquarefree_floor` use nothing else about it
(`s_succ` and `sum_sub_eq` additionally unfold it, to tie it to the target's `Erdos145.s`). -/
theorem isLeast_nextSquarefree (m : ℕ) :
    IsLeast {n : ℕ | m < n ∧ Squarefree n} (nextSquarefree m) := by
  refine ⟨⟨Nat.le_nth_count Nat.squarefree_infinite (m + 1),
    Nat.nth_mem_of_infinite Nat.squarefree_infinite _⟩, ?_⟩
  rintro n ⟨hmn, hn⟩
  have hc := Nat.nth_count (p := Squarefree) hn
  rw [nextSquarefree, ← hc]
  exact (Nat.nth_le_nth Nat.squarefree_infinite).2 (Nat.count_monotone _ hmn)

/-- **Squarefree gaps are `O(√m)`**: `nextSquarefree m ≤ m + 4 √m + 8`. -/
theorem nextSquarefree_le (m : ℕ) : nextSquarefree m ≤ m + 4 * Nat.sqrt m + 8 := by
  obtain ⟨n, h1, h2, h3⟩ := exists_squarefree_Ioc_sqrt m
  exact ((isLeast_nextSquarefree m).2 ⟨h1, h3⟩).trans h2

/- ### Two-sided counting bounds for the squarefree numbers -/

/-- **At least a quarter of `(0, N]` is squarefree**, for every `N` and with no error term.
This is the sieve of `exists_squarefree_mem_Ioc` run over a whole initial segment: the
multiples of `d * d` in `(0, N]` number exactly `N / (d * d)`, and `sum_inv_sq_Icc_two_le`
bounds the total by `3 N / 4`.  (The true density is `6 / π² = 0.6079…`.) -/
theorem card_squarefree_Ioc_ge (N : ℕ) :
    (N : ℝ) / 4 ≤ (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ) := by
  set D := Nat.sqrt N with hD
  have hsub : {n ∈ Finset.Ioc 0 N | ¬ Squarefree n} ⊆
      (Finset.Icc 2 D).biUnion (fun d => {n ∈ Finset.Ioc 0 N | d * d ∣ n}) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, hnN⟩, hns⟩ := hn
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push_neg at hns
    obtain ⟨p, hp, hpd⟩ := hns
    have hple : p * p ≤ n := Nat.le_of_dvd hn0 hpd
    refine Finset.mem_biUnion.2 ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      refine ⟨hp.two_le, ?_⟩
      rw [hD, Nat.le_sqrt]
      omega
    · simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hn0, hnN⟩, hpd⟩
  have hne : (#{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} : ℝ) ≤ (N : ℝ) * (3 / 4) := by
    have hc : (#{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} : ℝ)
        ≤ ∑ d ∈ Finset.Icc 2 D, ((#{n ∈ Finset.Ioc 0 N | d * d ∣ n} : ℕ) : ℝ) := by
      have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      exact_mod_cast h
    have h2 : ∀ d ∈ Finset.Icc 2 D,
        ((#{n ∈ Finset.Ioc 0 N | d * d ∣ n} : ℕ) : ℝ) ≤ (N : ℝ) * (1 / ((d : ℝ) * d)) := by
      intro d _
      rw [Nat.Ioc_filter_dvd_card_eq_div, mul_one_div]
      have h0 := Nat.cast_div_le (α := ℝ) (m := N) (n := d * d)
      rwa [Nat.cast_mul] at h0
    have h3 := hc.trans (Finset.sum_le_sum h2)
    rw [← Finset.mul_sum] at h3
    have h4 := sum_inv_sq_Icc_two_le D
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hsplit : #{n ∈ Finset.Ioc 0 N | Squarefree n}
      + #{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} = N := by
    rw [Finset.card_filter_add_card_filter_not, Nat.card_Ioc, Nat.sub_zero]
  have hsplitR : (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ)
      + (#{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} : ℝ) = (N : ℝ) := by
    exact_mod_cast hsplit
  linarith

/-- **At most three quarters of `(0, N]` is squarefree**, for every `N`.  Every multiple of
`4` is non-squarefree, and `Nat.Ioc_filter_dvd_card_eq_div` counts those exactly.  Together
with `card_squarefree_Ioc_ge` this shows the squarefree numbers *and* their complement each
occupy a positive proportion of `(0, N]`. -/
theorem card_squarefree_Ioc_le (N : ℕ) :
    (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ) ≤ 3 * N / 4 + 1 := by
  have hsub : {n ∈ Finset.Ioc 0 N | 4 ∣ n} ⊆ {n ∈ Finset.Ioc 0 N | ¬ Squarefree n} := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, fun hsf => ?_⟩
    have h2 : (2 : ℕ) * 2 ∣ n := by simpa using hn.2
    have hu := hsf 2 h2
    rw [Nat.isUnit_iff] at hu
    omega
  have hcard : N / 4 ≤ #{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div N 4]
    exact Finset.card_le_card hsub
  have hsplit : #{n ∈ Finset.Ioc 0 N | Squarefree n}
      + #{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} = N := by
    rw [Finset.card_filter_add_card_filter_not, Nat.card_Ioc, Nat.sub_zero]
  have hdiv : (N : ℝ) / 4 - 1 ≤ ((N / 4 : ℕ) : ℝ) := by
    have h1 : (N : ℝ) < 4 * ((N / 4 : ℕ) : ℝ) + 4 := by
      have h2 : N < 4 * (N / 4) + 4 := by omega
      exact_mod_cast h2
    linarith
  have hcardR : ((N / 4 : ℕ) : ℝ) ≤ (#{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} : ℝ) := by
    exact_mod_cast hcard
  have hsplitR : (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ)
      + (#{n ∈ Finset.Ioc 0 N | ¬ Squarefree n} : ℝ) = (N : ℝ) := by exact_mod_cast hsplit
  linarith

/- ### The squarefree density exists

For a fixed cutoff `D` the sieved set `SieveFree D` is *periodic*, hence has an exact
density; and it differs from the squarefree numbers by at most a `1/D` fraction.  Letting
`D → ∞` shows the squarefree ratio is Cauchy.  No Möbius inversion is needed. -/

/-- `SieveFree D n` : no square `d * d` with `2 ≤ d ≤ D` divides `n`.  A finite,
periodic approximation to `Squarefree`. -/
def SieveFree (D n : ℕ) : Prop := ∀ d ∈ Finset.Icc 2 D, ¬ (d * d ∣ n)

instance (D n : ℕ) : Decidable (SieveFree D n) := by unfold SieveFree; infer_instance

/-- The period of `SieveFree D`: `(D !)²` is divisible by `d * d` for every `d ≤ D`. -/
def sieveModulus (D : ℕ) : ℕ := D.factorial * D.factorial

theorem sq_dvd_sieveModulus {D d : ℕ} (hd : d ∈ Finset.Icc 2 D) : d * d ∣ sieveModulus D := by
  simp only [Finset.mem_Icc] at hd
  exact mul_dvd_mul (Nat.dvd_factorial (by omega) hd.2) (Nat.dvd_factorial (by omega) hd.2)

/-- **`SieveFree D` is periodic** with period `sieveModulus D`, in Mathlib's
`Function.Periodic` vocabulary. -/
theorem sieveFree_periodic (D : ℕ) : Function.Periodic (SieveFree D) (sieveModulus D) := by
  intro n
  refine propext ⟨?_, ?_⟩
  · intro h d hd hdvd
    exact h d hd (Nat.dvd_add hdvd (sq_dvd_sieveModulus hd))
  · intro h d hd hdvd
    refine h d hd ?_
    have hs := Nat.dvd_sub hdvd (sq_dvd_sieveModulus hd)
    rwa [Nat.add_sub_cancel] at hs

theorem sieveFree_of_squarefree {D n : ℕ} (h : Squarefree n) : SieveFree D n := by
  intro d hd hdvd
  simp only [Finset.mem_Icc] at hd
  have hu := h d hdvd
  rw [Nat.isUnit_iff] at hu
  omega

/-- **The sieve overshoots by at most `N / D`.**  Anything counted by `SieveFree D` but not
squarefree is divisible by `p * p` for a prime `D < p ≤ √N`, and `sum_inv_sq_Icc_le` bounds
the number of such `n ≤ N` by `N / D`. -/
theorem card_sieveFree_le (D N : ℕ) (hD : 1 ≤ D) :
    (#{n ∈ Finset.Ioc 0 N | SieveFree D n} : ℝ)
      ≤ (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ) + N / D := by
  classical
  set s := {n ∈ Finset.Ioc 0 N | SieveFree D n} with hs
  have hsplit : #{n ∈ s | Squarefree n} + #{n ∈ s | ¬ Squarefree n} = #s :=
    Finset.card_filter_add_card_filter_not _
  have he1 : {n ∈ s | Squarefree n} = {n ∈ Finset.Ioc 0 N | Squarefree n} := by
    rw [hs, Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    simp only [and_iff_right_iff_imp]
    exact fun h => sieveFree_of_squarefree h
  have hsub : {n ∈ s | ¬ Squarefree n} ⊆
      (Finset.Icc (D + 1) (Nat.sqrt N)).biUnion
        (fun d => {n ∈ Finset.Ioc 0 N | d * d ∣ n}) := by
    intro n hn
    simp only [hs, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨⟨hn0, hnN⟩, hsf⟩, hns⟩ := hn
    rw [Nat.squarefree_iff_prime_squarefree] at hns
    push_neg at hns
    obtain ⟨p, hp, hpd⟩ := hns
    have hple : p * p ≤ n := Nat.le_of_dvd hn0 hpd
    have hpD : D < p := by
      by_contra hcon
      exact hsf p (by simp only [Finset.mem_Icc]; exact ⟨hp.two_le, by omega⟩) hpd
    refine Finset.mem_biUnion.2 ⟨p, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      refine ⟨by omega, ?_⟩
      rw [Nat.le_sqrt]
      omega
    · simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hn0, hnN⟩, hpd⟩
  have hcard : (#{n ∈ s | ¬ Squarefree n} : ℝ) ≤ (N : ℝ) / D := by
    have h1 : #{n ∈ s | ¬ Squarefree n}
        ≤ ∑ d ∈ Finset.Icc (D + 1) (Nat.sqrt N), #{n ∈ Finset.Ioc 0 N | d * d ∣ n} :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : (#{n ∈ s | ¬ Squarefree n} : ℝ)
        ≤ ∑ d ∈ Finset.Icc (D + 1) (Nat.sqrt N),
            ((#{n ∈ Finset.Ioc 0 N | d * d ∣ n} : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ∀ d ∈ Finset.Icc (D + 1) (Nat.sqrt N),
        ((#{n ∈ Finset.Ioc 0 N | d * d ∣ n} : ℕ) : ℝ) ≤ (N : ℝ) * (1 / ((d : ℝ) * d)) := by
      intro d _
      rw [Nat.Ioc_filter_dvd_card_eq_div, mul_one_div]
      have h0 := Nat.cast_div_le (α := ℝ) (m := N) (n := d * d)
      rwa [Nat.cast_mul] at h0
    have h4 := h2.trans (Finset.sum_le_sum h3)
    rw [← Finset.mul_sum] at h4
    have h5 := sum_inv_sq_Icc_le (a := D) hD (Nat.sqrt N)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
    calc (#{n ∈ s | ¬ Squarefree n} : ℝ) ≤ (N : ℝ) * ∑ d ∈ Finset.Icc (D + 1) (Nat.sqrt N),
            (1 : ℝ) / ((d : ℝ) * d) := h4
      _ ≤ (N : ℝ) * (1 / D) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          exact_mod_cast h5
      _ = (N : ℝ) / D := by ring
  have hsplitR : (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ) + (#{n ∈ s | ¬ Squarefree n} : ℝ)
      = (#s : ℝ) := by
    rw [← he1]; exact_mod_cast hsplit
  linarith

/-- Bookkeeping for the two error terms: an additive approximation `|G - N * y| ≤ Pd`
together with a one-sided comparison `Q ≤ G ≤ Q + N / Dd` gives `|Q / N - y| ≤ 1/Dd + Pd/N`. -/
theorem abs_div_sub_le_of_abs_sub_le {Q G y N Pd Dd : ℝ} (hN : 0 < N) (hD : 0 < Dd)
    (hP : 0 < Pd) (h1 : |G - N * y| ≤ Pd) (h2 : Q ≤ G) (h3 : G ≤ Q + N / Dd) :
    |Q / N - y| ≤ 1 / Dd + Pd / N := by
  have hND : (0 : ℝ) ≤ N / Dd := by positivity
  rw [abs_le] at h1
  have hA : |Q - N * y| ≤ N / Dd + Pd := by
    rw [abs_le]
    constructor
    · linarith [h1.1]
    · linarith [h1.2]
  have he : Q / N - y = (Q - N * y) / N := by field_simp
  rw [he, abs_div, abs_of_pos hN, div_le_iff₀ hN]
  have he2 : (1 / Dd + Pd / N) * N = N / Dd + Pd := by field_simp
  rw [he2]
  exact hA

/-- **The squarefree ratio is within `1/D + (D !)²/N` of a constant depending only on `D`.**
The two error sources are the sieve's overshoot (`card_sieveFree_le`) and the periodic
counting error (`abs_card_filter_Ioc_sub_le`). -/
theorem abs_squarefree_count_div_sub_le {D N : ℕ} (hD : 1 ≤ D) (hN : 1 ≤ N) :
    |(#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ) / N
        - (#{n ∈ Finset.Ioc 0 (sieveModulus D) | SieveFree D n} : ℝ) / (sieveModulus D : ℝ)|
      ≤ 1 / D + (sieveModulus D : ℝ) / N := by
  have hPn : 0 < sieveModulus D := Nat.mul_pos (Nat.factorial_pos D) (Nat.factorial_pos D)
  have hP0 : (0 : ℝ) < (sieveModulus D : ℝ) := by exact_mod_cast hPn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 := abs_card_filter_Ioc_sub_le (p := SieveFree D) hPn (sieveFree_periodic D) N
  rw [mul_div_assoc] at h1
  have h2 : (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ)
      ≤ (#{n ∈ Finset.Ioc 0 N | SieveFree D n} : ℝ) := by
    have hsub : {n ∈ Finset.Ioc 0 N | Squarefree n} ⊆ {n ∈ Finset.Ioc 0 N | SieveFree D n} := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, sieveFree_of_squarefree hn.2⟩
    exact_mod_cast Finset.card_le_card hsub
  exact abs_div_sub_le_of_abs_sub_le hN0 hD0 hP0 h1 h2 (card_sieveFree_le D N hD)

/-- **The squarefree numbers have a density** (integer version): `#{n ≤ N | Squarefree n} / N`
converges.  The value is not identified here; it is classically `6 / π²`. -/
theorem exists_tendsto_squarefree_count :
    ∃ L : ℝ, Tendsto (fun N : ℕ => (#{n ∈ Finset.Ioc 0 N | Squarefree n} : ℝ) / N)
      atTop (𝓝 L) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨D, hD⟩ := exists_nat_gt (4 / ε)
  have h4e : (0 : ℝ) < 4 / ε := by positivity
  have hD1 : 1 ≤ D := by
    by_contra hcon
    have hD0 : D = 0 := by omega
    rw [hD0] at hD
    simp only [Nat.cast_zero] at hD
    linarith
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD1
  have hinvD : 1 / (D : ℝ) < ε / 4 := by
    rw [div_lt_iff₀ hD0]
    have h4 : 4 < (D : ℝ) * ε := (div_lt_iff₀ hε).1 hD
    linarith
  have hPn : 0 < sieveModulus D := Nat.mul_pos (Nat.factorial_pos D) (Nat.factorial_pos D)
  have hP0 : (0 : ℝ) < (sieveModulus D : ℝ) := by exact_mod_cast hPn
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * (sieveModulus D : ℝ) / ε)
  have hPm : ∀ m : ℕ, M ≤ m → (sieveModulus D : ℝ) / m < ε / 4 := by
    intro m hm
    have hmR : (M : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) hM) hmR
    rw [div_lt_iff₀ hm0]
    have h4 : 4 * (sieveModulus D : ℝ) < (M : ℝ) * ε := (div_lt_iff₀ hε).1 hM
    nlinarith
  refine ⟨max M 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right M 1) hn
  have hnM : M ≤ n := le_trans (le_max_left M 1) hn
  have hN1 : 1 ≤ max M 1 := le_max_right M 1
  have hNM : M ≤ max M 1 := le_max_left M 1
  rw [Real.dist_eq]
  have e1 := abs_squarefree_count_div_sub_le hD1 hn1
  have e2 := abs_squarefree_count_div_sub_le hD1 hN1
  have hsplit :
      (#{n ∈ Finset.Ioc 0 n | Squarefree n} : ℝ) / n
          - (#{k ∈ Finset.Ioc 0 (max M 1) | Squarefree k} : ℝ) / (max M 1)
        = ((#{n ∈ Finset.Ioc 0 n | Squarefree n} : ℝ) / n
            - (#{k ∈ Finset.Ioc 0 (sieveModulus D) | SieveFree D k} : ℝ) / (sieveModulus D : ℝ))
          - ((#{k ∈ Finset.Ioc 0 (max M 1) | Squarefree k} : ℝ) / (max M 1)
            - (#{k ∈ Finset.Ioc 0 (sieveModulus D) | SieveFree D k} : ℝ)
              / (sieveModulus D : ℝ)) := by ring
  rw [hsplit]
  calc |_| ≤ _ := abs_sub _ _
    _ < ε := by
        have h1 := hPm n hnM
        have h2 := hPm (max M 1) hNM
        linarith [e1, e2]

/-- **The squarefree numbers have a density** (real version):
`#{n ≤ x | Squarefree n} / x` converges as `x → ∞`.  This is the `α = 0` case of the target's
solved companions; see `erdos_145_variants_le_two_at_zero`. -/
theorem exists_tendsto_squarefree_density :
    ∃ L : ℝ, Tendsto (fun x : ℝ => (#{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} : ℝ) / x)
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_squarefree_count
  refine ⟨L, ?_⟩
  have h1 : Tendsto (fun x : ℝ => (#{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} : ℝ) / (⌊x⌋₊ : ℝ))
      atTop (𝓝 L) := hL.comp tendsto_nat_floor_atTop
  have h2 := h1.mul tendsto_nat_floor_div_atTop
  rw [mul_one] at h2
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hfl : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hfl0 : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hfl
  field_simp

/- ### The interface to the target's `s` and `A` -/

/-- The target's sequence starts at `1`: `s 0 = 1`.  (This is the constant that the telescoped
`α = 1` sum subtracts, so it is needed for `sum_sub_eq`.) -/
theorem s_zero : Erdos145.s 0 = 1 := by
  have hc : Nat.count Squarefree 1 = 0 := by simp [Nat.count_succ]
  have h := Nat.nth_count (p := Squarefree) squarefree_one
  rwa [hc] at h

/-- Consecutive terms of the target's sequence: `s (n + 1)` is the next squarefree number
after `s n`. -/
theorem s_succ (n : ℕ) : Erdos145.s (n + 1) = nextSquarefree (Erdos145.s n) := by
  rw [nextSquarefree, Nat.count_nth_succ_of_infinite Nat.squarefree_infinite]

/-- The gap bound transported to the target's sequence: `s (n + 1) ≤ s n + 4 √(s n) + 8`. -/
theorem s_succ_le (n : ℕ) :
    Erdos145.s (n + 1) ≤ Erdos145.s n + 4 * Nat.sqrt (Erdos145.s n) + 8 := by
  rw [s_succ]
  exact nextSquarefree_le _

/-- Consecutive terms of the target's sequence differ by at least `1`. -/
theorem one_le_s_sub (n : ℕ) : (1 : ℝ) ≤ (Erdos145.s (n + 1) : ℝ) - Erdos145.s n := by
  have h : Erdos145.s n < Erdos145.s (n + 1) :=
    (Nat.nth_lt_nth Nat.squarefree_infinite).2 (Nat.lt_succ_self n)
  have h' : (Erdos145.s n : ℝ) + 1 ≤ (Erdos145.s (n + 1) : ℝ) := by exact_mod_cast h
  linarith

/-- The target's index set `A x` is an initial segment: the indices below the number of
squarefree integers `≤ x`. -/
theorem A_eq_range (x : ℝ) : Erdos145.A x = Finset.range (Nat.count Squarefree (⌊x⌋₊ + 1)) := by
  ext n
  have h : n < Nat.count Squarefree (⌊x⌋₊ + 1) ↔ Nat.nth Squarefree n < ⌊x⌋₊ + 1 :=
    Nat.lt_nth_iff_count_lt Nat.squarefree_infinite
  simp only [Erdos145.A, Erdos145.s, Finset.mem_preimage, Finset.mem_Icc, Finset.mem_range, h]
  omega

/-- **The target's index set is the squarefree counting function**:
`#(A x) = #{n ∈ Ioc 0 ⌊x⌋₊ | Squarefree n}`.  This is the identification that turns the
`α = 0` case into the density of the squarefree numbers. -/
theorem card_A_eq (x : ℝ) :
    #(Erdos145.A x) = #{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} := by
  have hset : {n ∈ Finset.range (⌊x⌋₊ + 1) | Squarefree n}
      = {n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
    constructor
    · rintro ⟨hn, hsf⟩
      refine ⟨⟨?_, hn⟩, hsf⟩
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact absurd hsf not_squarefree_zero
      · exact hpos
    · rintro ⟨⟨_, hn⟩, hsf⟩
      exact ⟨hn, hsf⟩
  rw [A_eq_range, Finset.card_range, Nat.count_eq_card_filter_range, hset]

/-- **Telescoping.**  The `α = 1` sum of the target has the closed form
`nextSquarefree ⌊x⌋₊ - 1`. -/
theorem sum_sub_eq (x : ℝ) :
    ∑ n ∈ Erdos145.A x, ((Erdos145.s (n + 1) : ℝ) - Erdos145.s n)
      = (nextSquarefree ⌊x⌋₊ : ℝ) - 1 := by
  rw [A_eq_range, Finset.sum_range_sub (fun n => (Erdos145.s n : ℝ)), s_zero]
  norm_num [nextSquarefree]

/-- **The `α = 0` average of the target is the squarefree counting ratio.** -/
theorem avg_rpow_zero (x : ℝ) :
    1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (0 : ℝ)
      = (#{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} : ℝ) / x := by
  simp only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, card_A_eq]
  ring

/-- The `α = 1` sum bounded in terms of `x` alone: `∑ (s (n + 1) - s n) ≤ x + 4 √x + 7`. -/
theorem sum_sub_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Erdos145.A x, ((Erdos145.s (n + 1) : ℝ) - Erdos145.s n) ≤ x + 4 * Real.sqrt x + 7 := by
  rw [sum_sub_eq]
  have hb : (nextSquarefree ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) + 4 * (Nat.sqrt ⌊x⌋₊ : ℝ) + 8 := by
    exact_mod_cast nextSquarefree_le ⌊x⌋₊
  have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have h4 : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le (by linarith)))
  linarith

/- ### The limit at `α = 1` -/

/-- The closed form of the `α = 1` average tends to `1`; this is where the gap bound
`nextSquarefree_le` is used. -/
theorem tendsto_nextSquarefree_floor :
    Tendsto (fun x : ℝ => 1 / x * ((nextSquarefree ⌊x⌋₊ : ℝ) - 1)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun y : ℝ => (4 : ℝ) / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (4 : ℝ)
  have hsq : Tendsto (fun x : ℝ => (4 : ℝ) / Real.sqrt x) atTop (𝓝 0) :=
    hinv.comp Real.tendsto_sqrt_atTop
  have h7 : Tendsto (fun y : ℝ => (7 : ℝ) / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (7 : ℝ)
  have h1 : Tendsto (fun y : ℝ => (1 : ℝ) / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (1 : ℝ)
  have hlow : Tendsto (fun x : ℝ => 1 - 1 / x) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h1
  have hup : Tendsto (fun x : ℝ => 1 + (4 / Real.sqrt x + 7 / x)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hsq.add h7)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hnext : (x : ℝ) - 1 ≤ (nextSquarefree ⌊x⌋₊ : ℝ) - 1 := by
      have h4 : ((⌊x⌋₊ : ℝ)) + 1 ≤ (nextSquarefree ⌊x⌋₊ : ℝ) := by
        exact_mod_cast (isLeast_nextSquarefree ⌊x⌋₊).1.1
      have h5 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hx0]
    have hmul : (1 - 1 / x) * x = x - 1 := by field_simp
    rw [hmul]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hsqrt : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x :=
      Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le (by linarith)))
    have hb : (nextSquarefree ⌊x⌋₊ : ℝ) ≤ (⌊x⌋₊ : ℝ) + 4 * (Nat.sqrt ⌊x⌋₊ : ℝ) + 8 := by
      exact_mod_cast nextSquarefree_le ⌊x⌋₊
    have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hsqx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hx0]
    have hexp : (1 + (4 / Real.sqrt x + 7 / x)) * x = x + 4 * (x / Real.sqrt x) + 7 := by
      field_simp
      ring
    rw [hexp, Real.div_sqrt]
    linarith

/- ### Two-sided bounds for `0 ≤ α ≤ 1` -/

/-- **A two-sided a priori bound for `0 ≤ α ≤ 1`.**  For `x ≥ 1` the quantity whose limit the
target asks about lies between `1/4 - 1/x` and `1 + 4/√x + 7/x`.  Both gap directions are
used: each summand is at least `1` because consecutive squarefree numbers are distinct
(`one_le_s_sub`), and at most the gap itself because `α ≤ 1`; the lower bound then comes from
`card_squarefree_Ioc_ge` (through `card_A_eq`) and the upper bound from `sum_sub_le`. -/
theorem bounds_of_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    1 / 4 - 1 / x ≤ 1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α ∧
      1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α
        ≤ 1 + 4 / Real.sqrt x + 7 / x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsqx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hlow : (#(Erdos145.A x) : ℝ)
      ≤ ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α := by
    calc (#(Erdos145.A x) : ℝ) = ∑ _n ∈ Erdos145.A x, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun n _ => Real.one_le_rpow (one_le_s_sub n) hα0
  have hupp : ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α
      ≤ ∑ n ∈ Erdos145.A x, ((Erdos145.s (n + 1) : ℝ) - Erdos145.s n) := by
    refine Finset.sum_le_sum fun n _ => ?_
    calc (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α
        ≤ (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_s_sub n) hα1
      _ = _ := Real.rpow_one _
  have hfloor : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
    have h5 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith
  constructor
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hx0]
    have hmul : (1 / 4 - 1 / x) * x = x / 4 - 1 := by field_simp
    rw [hmul]
    have hA : (⌊x⌋₊ : ℝ) / 4 ≤ (#(Erdos145.A x) : ℝ) := by
      rw [card_A_eq]
      exact card_squarefree_Ioc_ge _
    linarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hx0]
    have hexp : (1 + 4 / Real.sqrt x + 7 / x) * x = x + 4 * (x / Real.sqrt x) + 7 := by
      field_simp
    rw [hexp, Real.div_sqrt]
    exact hupp.trans (sum_sub_le hx)

/-- **Any limit asserted by the companions for `0 ≤ α ≤ 1` lies in `[1/4, 1]`.**  Applied to
the exact conclusion of `Erdos145.erdos_145.variants.le_two` (and of the other two
companions), this rules out every value outside `[1/4, 1]`; in particular any such limit is
positive. -/
theorem mem_Icc_of_tendsto {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h : atTop.Tendsto (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x,
      (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ α) (𝓝 β)) :
    β ∈ Set.Icc (1 / 4 : ℝ) 1 := by
  have h1 : Tendsto (fun y : ℝ => (1 : ℝ) / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (1 : ℝ)
  have hinv : Tendsto (fun y : ℝ => (4 : ℝ) / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (4 : ℝ)
  have hsq : Tendsto (fun x : ℝ => (4 : ℝ) / Real.sqrt x) atTop (𝓝 0) :=
    hinv.comp Real.tendsto_sqrt_atTop
  have h7 : Tendsto (fun y : ℝ => (7 : ℝ) / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (7 : ℝ)
  have hlow : Tendsto (fun x : ℝ => 1 / 4 - 1 / x) atTop (𝓝 (1 / 4)) := by
    simpa using tendsto_const_nhds.sub h1
  have hupp : Tendsto (fun x : ℝ => 1 + 4 / Real.sqrt x + 7 / x) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add hsq).add h7
  constructor
  · refine le_of_tendsto_of_tendsto hlow h ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx using (bounds_of_le_one hα0 hα1 hx).1
  · refine le_of_tendsto_of_tendsto h hupp ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx using (bounds_of_le_one hα0 hα1 hx).2

/- ### Use sites against the target statements -/

/-- **The `α = 1` average of the target converges, with limit `1`.**  This is the sharp form
of the `α = 1` case: the limit is not merely asserted to exist, it is computed. -/
theorem tendsto_sum_rpow_one :
    atTop.Tendsto
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (1 : ℝ))
      (𝓝 1) := by
  have hfun :
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x,
          (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (1 : ℝ))
        = fun x : ℝ ↦ 1 / x * ((nextSquarefree ⌊x⌋₊ : ℝ) - 1) := by
    funext x
    rw [← sum_sub_eq x]
    exact congrArg _ (Finset.sum_congr rfl fun n _ => Real.rpow_one _)
  rw [hfun]
  exact tendsto_nextSquarefree_floor

/-- **The `α = 1` instance of `Erdos145.erdos_145.variants.le_two`, proved.**  This is verbatim
the conclusion of that companion (and of `variants.le_three` and of
`variants.le_eleven_thirds`, whose conclusions are the same formula) with `α := 1`, a legal
instance since `1 ∈ Set.Icc 0 2`; the type identity is definitional, so
`Erdos145.erdos_145.variants.le_two h` for `h : (1 : ℝ) ∈ Set.Icc 0 2` can be replaced by
this theorem.  The companion's own `∀ α ∈ Set.Icc 0 2` remains open. -/
theorem erdos_145_variants_le_two_at_one :
    ∃ β : ℝ, atTop.Tendsto
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (1 : ℝ))
      (𝓝 β) :=
  ⟨1, tendsto_sum_rpow_one⟩

/-- **The `α = 0` instance of `Erdos145.erdos_145.variants.le_two`, proved.**  Verbatim the
conclusion of that companion with `α := 0` (a legal instance, `0 ∈ Set.Icc 0 2`), obtained
from `exists_tendsto_squarefree_density` through the interface lemma `avg_rpow_zero`.  The
limit is the density of the squarefree numbers, classically `6 / π²`.  The companion's own
`∀ α ∈ Set.Icc 0 2` remains open. -/
theorem erdos_145_variants_le_two_at_zero :
    ∃ β : ℝ, atTop.Tendsto
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x, (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (0 : ℝ))
      (𝓝 β) := by
  obtain ⟨L, hL⟩ := exists_tendsto_squarefree_density
  refine ⟨L, ?_⟩
  have hfun :
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x,
          (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (0 : ℝ))
        = fun x : ℝ ↦ (#{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} : ℝ) / x := by
    funext x
    exact avg_rpow_zero x
  rw [hfun]
  exact hL

/-- **The density of the squarefree numbers exists and lies strictly inside `[0, 1]`**,
namely in `[1/4, 3/4]`: a positive proportion of the integers is squarefree, and a positive
proportion is not.  Existence is `exists_tendsto_squarefree_density`; the lower bound is
`mem_Icc_of_tendsto` at `α = 0` read through `avg_rpow_zero`, the upper bound is
`card_squarefree_Ioc_le`.  (The classical value `6 / π² = 0.6079…` is indeed in this
range.) -/
theorem squarefree_density_exists_mem_Icc :
    ∃ L ∈ Set.Icc (1 / 4 : ℝ) (3 / 4),
      Tendsto (fun x : ℝ => (#{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} : ℝ) / x) atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_squarefree_density
  have hzero :
      (fun x : ℝ ↦ 1 / x * ∑ n ∈ Erdos145.A x,
          (Erdos145.s (n + 1) - Erdos145.s n : ℝ) ^ (0 : ℝ))
        = fun x : ℝ ↦ (#{n ∈ Finset.Ioc 0 ⌊x⌋₊ | Squarefree n} : ℝ) / x := funext avg_rpow_zero
  refine ⟨L, ⟨?_, ?_⟩, hL⟩
  · exact (mem_Icc_of_tendsto (α := 0) le_rfl zero_le_one (by rw [hzero]; exact hL)).1
  · have h1 : Tendsto (fun y : ℝ => (1 : ℝ) / y) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (1 : ℝ)
    have hupp : Tendsto (fun x : ℝ => 3 / 4 + 1 / x) atTop (𝓝 (3 / 4)) := by
      simpa using tendsto_const_nhds.add h1
    refine le_of_tendsto_of_tendsto hL hupp ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hb := card_squarefree_Ioc_le ⌊x⌋₊
    rw [div_le_iff₀ hx0]
    have hexp : (3 / 4 + 1 / x) * x = 3 * x / 4 + 1 := by field_simp
    rw [hexp]
    linarith

end Contribution.Erdos145Squarefree
