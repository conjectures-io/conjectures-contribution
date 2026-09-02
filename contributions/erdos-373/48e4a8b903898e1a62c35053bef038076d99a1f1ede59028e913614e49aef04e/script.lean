import Mathlib
import FormalConjectures.ErdosProblems.«373»

/-!
# Erdős Problem 373: structural API for the solution set `Erdos373.S`

Erdős Problem 373 asks for the finiteness of
`S = {(n, l) | n ! = ∏ aᵢ! , l = [a₁ ≥ … ≥ a_k] descending, a₁ < n - 1, every aᵢ > 1}`.

## The obstacle

`Erdos373.S` lives in `Set (ℕ × List ℕ)`, but every known mathematical approach to the
problem produces a bound on the *first* coordinate only (Erdős' argument bounds `n`; Hickerson
conjectures `n ≤ 16`). Turning such a bound into `S.Finite` is not a formality in Lean:

* the second coordinate ranges over lists of unbounded length over the *infinite* alphabet `ℕ`,
  and `Mathlib`'s list-finiteness lemma `List.finite_length_le` is stated for a `Finite`
  alphabet (`Mathlib/Data/Set/Finite/List.lean` opens with `variable (α : Type*) [Finite α]`),
  so it does not apply to `List ℕ`;
* nothing in the statement of `S` bounds the *length* of `l` — that has to be extracted from
  the equation `n ! = ∏ aᵢ !` itself.

So a solver arriving with "n is bounded" still has to redo, by hand, the bookkeeping that
bounds the entries of `l` and the length of `l`. This file does that bookkeeping once, and
adds the elementary structural facts about `S` that the classical approach actually uses.

## The delta

* `finite_bounded_lists` is the missing `Mathlib`-shaped lemma: sets of lists over `ℕ` with
  bounded entries *and* bounded length are finite (proved by transporting along `Fin (N+1)`).
* `length_le_fst` supplies the missing length bound `k ≤ n` for every solution, and
  `length_lt_fst` sharpens it to the strict `k < n` (Legendre: `2 ^ k ∣ n !` forces
  `k ≤ n - s₂(n) < n`);
  obtained from `2 ^ k ∣ n !` and Legendre's bound `(n !).factorization 2 ≤ n`.
* `finite_of_forall_fst_le` combines these into the main reduction, and
  `finite_iff_exists_fst_bound` shows the reduction loses nothing (it is an `Iff`).
* `not_prime_of_headI_lt_of_le_fst` is the classical prime obstruction — no prime lies in
  `(a₁, n]` — and `fst_lt_two_mul_headI` combines it with Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`) to give `n < 2 * a₁`. Feeding both back into the
  obstruction gives the checked bound `nine_le_fst : 9 ≤ n`, which is sharp: the worked
  example after it exhibits `(9, [7, 3, 3, 2]) ∈ S`.
* `suranyi_mem` embeds Surányi's two-factorial equation into `S`, so the same machinery serves
  `Erdos373.erdos_373.variants.suranyi`.

## G1

A later solver can use declaration `Contribution.Erdos373Finiteness.finite_of_forall_fst_le`
to discharge or simplify obligation `Erdos373.erdos_373 : Erdos373.S.Finite` in target
erdos-373: it reduces that open goal to producing a single `N` with `n ≤ N` for every solution
`(n, l)`, which is the form in which the number-theoretic argument is actually stated.

The use sites are `hickerson_mem` (which *is* the first conjunct of
`Erdos373.erdos_373.variants.maximal_solution`, so that variant is reduced to its second
conjunct), `suranyi_finite`, and the worked `example`s throughout the file — including the one
deriving `Erdos373.erdos_373` from the second conjunct of `maximal_solution`.
-/

open scoped Nat

namespace Contribution.Erdos373Finiteness

open Erdos373

/- ### Degenerate cases

Membership `(n, l) ∈ Erdos373.S` unfolds definitionally to the four-fold conjunction
`n ! = (l.map Nat.factorial).prod ∧ l.Pairwise (· ≥ ·) ∧ l.headI < n - 1 ∧ ∀ a ∈ l, 1 < a`,
so `h.1`, `h.2.1`, `h.2.2.1`, `h.2.2.2` are used below to name its components. -/

/-- A solution never has an empty list of factorials: `n ! = 1` forces `n ≤ 1`, which is
incompatible with `0 = [].headI < n - 1`. -/
theorem ne_nil {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : l ≠ [] := by
  rintro rfl
  have h1 : n ! = 1 := by simpa using h.1
  have h2 : (0 : ℕ) < n - 1 := by simpa using h.2.2.1
  have h3 : 1 < n ! := Nat.one_lt_factorial.mpr (by omega)
  omega

/-- The largest entry of a solution is at least `2`. This is the hypothesis needed to feed
`l.headI` to Bertrand's postulate, which requires a nonzero input. -/
theorem two_le_headI {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : 2 ≤ l.headI := by
  rcases l with _ | ⟨a, t⟩
  · exact absurd rfl (ne_nil h)
  · simpa using h.2.2.2 a (by simp)

/-- Every entry of a solution is `< n - 1`, not just the largest one. The statement of `S`
only constrains `l.headI`; this propagates the constraint to all of `l` via the sortedness
hypothesis (`List.Pairwise.head!_le`). -/
theorem mem_lt_sub_one {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) {a : ℕ} (ha : a ∈ l) :
    a < n - 1 := by
  have hmax : a ≤ l.headI := h.2.1.head!_le ha
  exact lt_of_le_of_lt hmax h.2.2.1

/-- A solution has at least two factorials on the right-hand side: a single one would give
`a ! = n !` with `a < n`. -/
theorem two_le_length {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : 2 ≤ l.length := by
  rcases l with _ | ⟨a, _ | ⟨b, t⟩⟩
  · exact absurd rfl (ne_nil h)
  · exfalso
    have hprod : n ! = a ! := by simpa using h.1
    have ha : 1 < a := h.2.2.2 a (by simp)
    have han : a < n - 1 := mem_lt_sub_one h (by simp)
    have : a = n := (Nat.factorial_inj ha).mp hprod.symm
    omega
  · simp

/-- **Worked example (degenerate case).** The equation `n ! = a !` has no non-trivial
solution, in the precise sense of `Erdos373.S`. A solver doing case analysis on `l` can
discharge the one-element branch with this. -/
example {n a : ℕ} : (n, [a]) ∉ S := fun h => by simpa using two_le_length h

/- ### The prime obstruction and Bertrand's postulate -/

/-- **The classical obstruction.** If `(n, l)` is a solution then no prime lies in the
interval `(a₁, n]`: such a prime would divide `n !` but none of the `aᵢ !`. -/
theorem not_prime_of_headI_lt_of_le_fst {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) {p : ℕ}
    (hlt : l.headI < p) (hle : p ≤ n) : ¬ p.Prime := by
  intro hp
  have hdvd : p ∣ n ! := (Nat.Prime.dvd_factorial hp).mpr hle
  rw [h.1] at hdvd
  obtain ⟨x, hx, hpx⟩ := (Prime.dvd_prod_iff hp.prime).mp hdvd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have hpa : p ≤ a := (Nat.Prime.dvd_factorial hp).mp hpx
  have hmax : a ≤ l.headI := h.2.1.head!_le ha
  omega

/-- **Bertrand's postulate applied to Erdős 373.** Every solution satisfies `n < 2 * a₁`,
i.e. the largest factorial on the right-hand side already uses more than half of `n`. -/
theorem fst_lt_two_mul_headI {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : n < 2 * l.headI := by
  by_contra hcon
  push_neg at hcon
  have hne : l.headI ≠ 0 := by have := two_le_headI h; omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul l.headI hne
  exact not_prime_of_headI_lt_of_le_fst h hlt (hle.trans hcon) hp

/-- **A checked lower bound for the first coordinate:** every solution has `9 ≤ n`.

`fst_lt_two_mul_headI` together with `a₁ < n - 1` already forces `5 ≤ n`; the remaining
cases `n ∈ {5, 6, 7, 8}` are killed by exhibiting the prime that `S` forbids in `(a₁, n]`
(namely `5` for `n ∈ {5, 6}` and `7` for `n ∈ {7, 8}`). The bound is sharp — see the example
immediately below. -/
theorem nine_le_fst {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : 9 ≤ n := by
  by_contra hcon
  push_neg at hcon
  have h1 : n < 2 * l.headI := fst_lt_two_mul_headI h
  have h2 : 2 ≤ l.headI := two_le_headI h
  have h3 : l.headI < n - 1 := h.2.2.1
  have h5 : 5 ≤ n := by omega
  interval_cases n
  · exact not_prime_of_headI_lt_of_le_fst h (p := 5) (by omega) (by norm_num) (by norm_num)
  · exact not_prime_of_headI_lt_of_le_fst h (p := 5) (by omega) (by norm_num) (by norm_num)
  · exact not_prime_of_headI_lt_of_le_fst h (p := 7) (by omega) (by norm_num) (by norm_num)
  · exact not_prime_of_headI_lt_of_le_fst h (p := 7) (by omega) (by norm_num) (by norm_num)

/-- **Worked example (sharpness of `nine_le_fst`).** The smallest solution is
`9 ! = 7 ! 3 ! 3 ! 2 !`, so the bound `9 ≤ n` cannot be improved. -/
example : (9, [7, 3, 3, 2]) ∈ S := by decide

/- ### Bounding the length of the list -/

/-- A list of naturals all `> 1` has `2 ^ length` dividing the product of the factorials of
its entries, since each `aᵢ !` is even. -/
theorem two_pow_length_dvd_prod {l : List ℕ} (h : ∀ a ∈ l, 1 < a) :
    2 ^ l.length ∣ (l.map Nat.factorial).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 2 ∣ a ! := Nat.dvd_factorial (by norm_num) (h a (by simp))
    have ht := ih fun x hx => h x (by simp [hx])
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    exact mul_comm (2 ^ t.length) 2 ▸ mul_dvd_mul ha ht

/-- **The missing length bound.** A solution `n ! = a₁ ! ⋯ a_k !` has `k ≤ n`
(see `length_lt_fst` for the strict form `k < n`).

Proof: `2 ^ k ∣ n !` by `two_pow_length_dvd_prod`, hence `k ≤ (n !).factorization 2`, and
Legendre's estimate `Nat.factorization_factorial_le_div_pred` bounds that by `n / (2 - 1) = n`.
Nothing in the definition of `Erdos373.S` bounds `l.length`, so without this the pair
`(n, l)` cannot be confined to a finite set even when `n` is known. -/
theorem length_le_fst {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : l.length ≤ n := by
  have hdvd : 2 ^ l.length ∣ n ! := h.1 ▸ two_pow_length_dvd_prod h.2.2.2
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (Nat.factorial_ne_zero n)).mp hdvd
  have h2 := Nat.factorization_factorial_le_div_pred Nat.prime_two n
  simpa using h1.trans h2

/-- **The strict length bound.** Legendre's exact formula `(2 - 1) * v₂(n !) = n - s₂(n)` with
`s₂(n) ≥ 1` for `n ≠ 0` gives `k ≤ v₂(n !) < n`; the weak bound `length_le_fst` is never
attained. -/
theorem length_lt_fst {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) : l.length < n := by
  have hn : n ≠ 0 := by
    rintro rfl
    simpa using h.2.2.1
  have hdvd : 2 ^ l.length ∣ n ! := h.1 ▸ two_pow_length_dvd_prod h.2.2.2
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
    (Nat.factorial_ne_zero n)).mp hdvd
  have h2 := Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
  have h3 : (Nat.digits 2 n).sum ≠ 0 := fun h0 =>
    Nat.getLast_digit_ne_zero 2 hn ((List.sum_eq_zero_iff.mp h0) _ (List.getLast_mem _))
  norm_num at h2
  omega

/- ### Finiteness -/

/-- Lists over `ℕ` with bounded entries and bounded length form a finite set.
`Mathlib`'s `List.finite_length_le` is stated for a `Finite` alphabet, so it does not apply
to `List ℕ`; the proof here transports the bounded lists along `Fin (N + 1) → ℕ`. -/
theorem finite_bounded_lists (N M : ℕ) :
    {l : List ℕ | (∀ a ∈ l, a ≤ N) ∧ l.length ≤ M}.Finite := by
  refine Set.Finite.subset
    ((List.finite_length_le (Fin (N + 1)) M).image (List.map Fin.val)) ?_
  rintro l ⟨hb, hl⟩
  refine ⟨l.map fun a => (⟨min a N, by omega⟩ : Fin (N + 1)), by simpa using hl, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun a ha => by
    simp [Function.comp_apply, Nat.min_eq_left (hb a ha)]

/-- **Main reduction.** To prove `Erdos373.S.Finite` it suffices to bound the first
coordinate: all the list bookkeeping (entries `< n - 1` by `mem_lt_sub_one`, length `≤ n` by
`length_le_fst`, finiteness of the resulting box by `finite_bounded_lists`) is done here. -/
theorem finite_of_forall_fst_le {N : ℕ} (h : ∀ p ∈ S, p.1 ≤ N) : S.Finite := by
  refine Set.Finite.subset ((Set.finite_Iic N).prod (finite_bounded_lists N N)) ?_
  rintro ⟨n, l⟩ hp
  have hn : n ≤ N := h _ hp
  refine ⟨Set.mem_Iic.mpr hn, fun a ha => ?_, (length_le_fst hp).trans hn⟩
  have := mem_lt_sub_one hp ha
  omega

/-- **Reformulation.** Erdős 373 is *equivalent* to a bound on `n`; no information is lost
by passing to `finite_of_forall_fst_le`. -/
theorem finite_iff_exists_fst_bound : S.Finite ↔ ∃ N, ∀ p ∈ S, p.1 ≤ N := by
  constructor
  · intro hS
    obtain ⟨N, hN⟩ := (hS.image Prod.fst).bddAbove
    exact ⟨N, fun p hp => hN ⟨p, hp, rfl⟩⟩
  · rintro ⟨N, hN⟩
    exact finite_of_forall_fst_le hN

/- ### Use sites -/

/-- Hickerson's solution really is a solution: this is literally the first conjunct of
`Erdos373.erdos_373.variants.maximal_solution`, discharged. -/
theorem hickerson_mem : (16, [14, 5, 2]) ∈ S := by decide

/-- **Worked use site 1.** Together with `hickerson_mem`, this shows that
`Erdos373.erdos_373.variants.maximal_solution` reduces to its second conjunct, and that that
conjunct implies `Erdos373.erdos_373`. -/
example (h : ∀ s ∈ S, s.fst ≤ 16) : (16, [14, 5, 2]) ∈ S ∧ S.Finite :=
  ⟨hickerson_mem, finite_of_forall_fst_le h⟩

/-- Surányi's two-factorial equation embeds into `Erdos373.S`. -/
theorem suranyi_mem {n a b : ℕ} (heq : n ! = a ! * b !) (ha : 1 < a) (hb : 1 < b)
    (hba : b ≤ a) (hne : a + 1 ≠ n) : (n, [a, b]) ∈ S := by
  have hpos := Nat.factorial_pos a
  have hb2 : 1 < b ! := Nat.one_lt_factorial.mpr hb
  have hlt : a ! < n ! := by rw [heq]; nlinarith
  have han : a < n := (Nat.factorial_lt (by omega)).mp hlt
  refine ⟨by simpa using heq, by simpa using hba, ?_, ?_⟩
  · simp only [List.headI]
    omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · simp at hx

/-- **Worked example.** Surányi's solution `10 ! = 7 ! 6 !` viewed inside `Erdos373.S`
through the bridge. -/
example : (10, [7, 6]) ∈ S :=
  suranyi_mem (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Worked use site 2.** `Erdos373.erdos_373.variants.suranyi` asserts a set *equality*
(the Surányi set is exactly `{(10, 7, 6)}`); this lemma supplies the finiteness consequence
of that statement, i.e. the necessary condition that the Surányi set is finite, and derives it
from `Erdos373.erdos_373`. -/
theorem suranyi_finite (h : S.Finite) :
    {(n, a, b) : ℕ × ℕ × ℕ |
      n ! = a ! * b ! ∧ 1 < n ∧ 1 < a ∧ 1 < b ∧ b ≤ a ∧ a + 1 ≠ n}.Finite := by
  refine Set.Finite.of_finite_image (f := fun p : ℕ × ℕ × ℕ => (p.1, [p.2.1, p.2.2]))
    (h.subset ?_) ?_
  · rintro _ ⟨⟨n, a, b⟩, hp, rfl⟩
    obtain ⟨h1, _, h3, h4, h5, h6⟩ := hp
    exact suranyi_mem h1 h3 h4 h5 h6
  · rintro ⟨n, a, b⟩ - ⟨n', a', b'⟩ - hEq
    simp only [Prod.mk.injEq, List.cons.injEq, and_true] at hEq
    obtain ⟨rfl, rfl, rfl⟩ := hEq
    rfl

/-- **Worked example.** This is exactly how the last step of a solution of erdos-373 would
read once the number-theoretic work has produced a bound on `n`. -/
example (H : ∀ n l, (n, l) ∈ S → n ≤ 16) : S.Finite := by
  refine finite_of_forall_fst_le (N := 16) ?_
  rintro ⟨n, l⟩ hp
  exact H n l hp

/-- **Worked example.** The prime obstruction in the form a search would use it: every prime
`p ≤ n` is already `≤ a₁`. Applied to Hickerson's `16 ! = 14 ! 5 ! 2 !` it says that `15` and
`16` are composite, which they are. -/
example {n : ℕ} {l : List ℕ} (h : (n, l) ∈ S) (p : ℕ) (hp : p.Prime) (hle : p ≤ n) :
    p ≤ l.headI := by
  by_contra hcon
  exact not_prime_of_headI_lt_of_le_fst h (by omega) hle hp

end Contribution.Erdos373Finiteness
