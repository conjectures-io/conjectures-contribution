import Mathlib
import FormalConjectures.ErdosProblems.«1135»

/-!
# Erdős 1135 (the $3x+1$ problem): a Terras descent API for `CollatzConjecture.collatzStep`

Target: `Erdos1135.erdos_1135`, whose statement is `type_of% CollatzConjecture.collatz_conjecture`,
i.e. `∀ (n : ℕ), n > 0 → ∃ m, CollatzConjecture.collatzStep^[m] n = 1`.

## The obstacle

The reward statement is an unbounded existential over the *number of iterations* of
`collatzStep`, a function whose two branches are hidden behind `if Even n then n / 2 else 3 * n + 1`.
Three walls stand in front of any attempt, before any mathematics happens.

* There is no way to *shorten* the goal. A solver who has shown that the orbit of `n` reaches
  some smaller `k` still has to re-assemble a witness `m` for `n` out of a witness for `k`, by
  hand, through `Function.iterate_add_apply`, every single time. The classical approach — strong
  induction on `n` via a *descent* (the orbit of `n` dips below `n`) — is unavailable until that
  plumbing exists, and it also needs the (unstated) fact that the orbit of a positive number
  stays positive, otherwise the induction has nothing to descend on. (Only the one-step fact
  `collatzStep_pos` is new; the orbit version is Mathlib's `Set.MapsTo.iterate`, which
  `reaches1_of_descent_above` calls.)
* The `if Even n then …` guard is not in a shape `rcases` can consume. Case analysis on the
  residue of `n` — the standard tool in this area, and the one Terras and Lagarias use — has to
  re-derive `Even (2 * k)`, `¬ Even (2 * k + 1)`, `2 * k / 2 = k` at each of the many steps, and
  a residue class mod `2 ^ k` costs a hand-written chain of `k` such rewrites.
* The literature this file follows (Terras 1976, and the shortcut-map half of Lagarias' 1985
  survey) works with the *shortcut* map `n ↦ (3n+1)/2` on odd numbers rather than with
  `collatzStep`, and nothing in Mathlib or in this repository connects the two maps.

Mathlib contains nothing about the Collatz map: `grep -ri collatz` over `Mathlib/` returns
no hits, so none of this can be imported.

## The contribution

The centre of the file is `iterate_collatzShortcut_add_two_pow_mul`, the **affine structure
theorem** of Terras: for the shortcut map `T = collatzShortcut`,
`T^[k] (n + 2 ^ k * c) = T^[k] n + 3 ^ oddCount k n * c`, where `oddCount k n` counts the odd
steps among the first `k`. In words: `T^[k]` is affine on every residue class mod `2 ^ k`, with
slope `3 ^ (number of odd steps)`, so *the entire class is determined by its representative*.

That converts an infinite family of hand-written rewrite chains into two numeric checks.
`iterate_collatzShortcut_lt_self` and its user-facing form `exists_descent_of_mod` say: if the
representative `r = n % 2 ^ k` satisfies `3 ^ oddCount k r < 2 ^ k` and `T^[k] r < r + n / 2 ^ k`,
then `n` has a strict `collatzStep` descent. For concrete `k` and `r` the first hypothesis is a
closed numeric statement, so `decide` settles it outright. The second is *not* closed — it still
mentions the variable `n`, through `n / 2 ^ k` — so `decide` cannot be applied to it directly;
it is settled instead by a `decide` for the value `collatzShortcut^[k] r` followed by `omega`.
Every use site below follows exactly that pattern, and the classes `0 mod 2`, `1 mod 4`,
`3 mod 16` and (in a use site below) `7 mod 128` are discharged this way.

Around it sits the plumbing the obstacle asks for. `Reaches1` names the target's conclusion;
`reaches1_step_iff` moves it one step along the orbit in **both** directions (the backwards
direction is not formal — it needs the `1 → 4 → 2 → 1` cycle), `reaches1_iterate_iff` moves it
any number of steps, and `reaches1_of_descent_above` is the strong-induction engine: *a checked
finite initial segment plus a descent above it proves the conjecture*. The engine is stated for
an arbitrary map `f` that preserves `Reaches1` and positivity, so it applies verbatim to
`collatzStep` and to `collatzShortcut` (both instantiations appear as use sites).
`forall_reaches1_iff_descent` records that the reduction is lossless — the target is
**equivalent** to the descent statement.

`reaches1_iff_exists_iterate_collatzShortcut` proves the equivalence of the two formulations of
the conjecture — an equivalence that is routinely taken for granted, and that appears neither in
Mathlib nor elsewhere in this repository; the delicate direction is
`exists_iterate_collatzShortcut_eq_one`, which has to know that the value a shortcut step jumps
over is never `1`. `reachesOneIn` / `reaches1_of_reachesOneIn` turn "we checked it by computer"
into a kernel-checked interface for the initial segment that the engine consumes.

The headline `erdos_1135_of_descent_mod_sixteen` puts it together: thirteen of the sixteen
residue classes mod `16` are settled here, so the whole target follows from a descent for
`n ≡ 7, 11, 15 (mod 16)`.

A later solver can use declaration
`Contribution.Erdos1135CollatzDescent.erdos_1135_of_descent_mod_sixteen` to discharge
obligation `∀ (n : ℕ), n > 0 → ∃ m, CollatzConjecture.collatzStep^[m] n = 1` in target
`Erdos1135.erdos_1135`, reducing it to exhibiting, for every `n` with `n % 16 ∈ {7, 11, 15}`,
a positive `m` with `collatzStep^[m] n < n`. The final section contains worked use sites, stated
against the reward theorem's own type via `type_of%`.

*References:*
- [erdosproblems.com/1135](https://www.erdosproblems.com/1135)
- [Wikipedia, Collatz conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture)
- Terras, R., *A stopping time problem on the positive integers*, Acta Arith. 30 (1976), 241-252,
  <https://doi.org/10.4064/aa-30-3-241-252>
- Lagarias, J. C., *The 3x+1 problem and its generalizations*, Amer. Math. Monthly 92 (1985),
  3-23, <https://doi.org/10.1080/00029890.1985.11971528>
-/

namespace Contribution.Erdos1135CollatzDescent

open CollatzConjecture

/- ## A `simp` set for the two branches

`collatzStep` branches on `Even n`, which no tactic can take apart directly. Tagging both
branches `@[local simp]` in the shape produced by `Nat.even_or_odd'` means that
`rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩ <;> simp` computes a step, and every residue
computation below is `simp`-driven rather than hand-rolled. The attributes are `local`, so
importing this file does not silently change the ambient `simp` set; a downstream file that
wants the same convenience can re-declare them with `attribute [local simp]`. -/

/-- The even branch of `collatzStep`, in `rcases`-ready form. -/
@[local simp] theorem collatzStep_two_mul (k : ℕ) : collatzStep (2 * k) = k := by
  rw [collatzStep, if_pos ⟨k, (two_mul k)⟩]
  omega

/-- The odd branch of `collatzStep`, in `rcases`-ready form. The result is presented as
`6 * k + 4`, i.e. already visibly even, which is what the next step needs. -/
@[local simp] theorem collatzStep_two_mul_add_one (k : ℕ) :
    collatzStep (2 * k + 1) = 6 * k + 4 := by
  rw [collatzStep, if_neg]
  · ring
  · simp

/-- `collatzStep` preserves positivity; this is what keeps a descent induction inside the
positive integers. -/
theorem collatzStep_pos (n : ℕ) (hn : 0 < n) : 0 < collatzStep n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp only [collatzStep_two_mul]; omega
  · simp only [collatzStep_two_mul_add_one]; omega

/- ## The conclusion of the target, and moving it along the orbit -/

/-- `Reaches1 n` is exactly the conclusion of `Erdos1135.erdos_1135` for `n`. -/
def Reaches1 (n : ℕ) : Prop := ∃ m, collatzStep^[m] n = 1

/-- One step of the orbit may be taken (or untaken) without changing the goal. The `←` direction
is the useful one and is *not* formal: it relies on the cycle `1 → 4 → 2 → 1`. -/
theorem reaches1_step_iff (n : ℕ) : Reaches1 (collatzStep n) ↔ Reaches1 n := by
  have h1 : collatzStep 1 = 4 := by decide
  have h4 : collatzStep 4 = 2 := by decide
  have h2 : collatzStep 2 = 1 := by decide
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩
  · rintro ⟨m, hm⟩
    match m, hm with
    | 0, hm =>
      have hn1 : n = 1 := by simpa using hm
      subst hn1
      exact ⟨2, by rw [h1]; simp [Function.iterate_succ_apply, h4, h2]⟩
    | (j + 1), hm => exact ⟨j, by rw [← Function.iterate_succ_apply]; exact hm⟩

/-- The goal may be transported to **any** point of the orbit of any goal-preserving map, in
either direction. This is the lemma that lets a solver replace `n` by a smaller number it
reaches. -/
theorem reaches1_iterate_iff {f : ℕ → ℕ} (hstep : ∀ n, Reaches1 (f n) ↔ Reaches1 n) (m n : ℕ) :
    Reaches1 (f^[m] n) ↔ Reaches1 n := by
  induction m generalizing n with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, ih, hstep]

/- ## The descent principle

This is the reduction the classical attacks on the problem use: check a finite initial segment,
then show that every larger number eventually dips below itself. It is stated for an arbitrary map that
preserves `Reaches1` and positivity, so that it serves both `collatzStep` and the shortcut map. -/

/-- **Descent engine.** If every `n` below `B` is already known to reach `1`, and every `n` at
least `B` has *some* strictly smaller `f`-iterate, then every positive `n` reaches `1`. The
number of steps needs no positivity hypothesis: `f^[0] n = n` is never `< n`, so any witness is
automatically positive. -/
theorem reaches1_of_descent_above {f : ℕ → ℕ} (hstep : ∀ n, Reaches1 (f n) ↔ Reaches1 n)
    (hf : ∀ n, 0 < n → 0 < f n) (B : ℕ)
    (hlow : ∀ n, 0 < n → n < B → Reaches1 n)
    (hhigh : ∀ n, B ≤ n → ∃ m, f^[m] n < n) :
    ∀ n, 0 < n → Reaches1 n := by
  have hmaps : Set.MapsTo f {x : ℕ | 0 < x} {x : ℕ | 0 < x} := fun x hx => hf x hx
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases lt_or_ge n B with hb | hb
    · exact hlow n hn hb
    · obtain ⟨m, hmlt⟩ := hhigh n hb
      exact (reaches1_iterate_iff hstep m n).mp (ih _ hmlt (hmaps.iterate m hn))

/-- The descent reduction is lossless: the target is *equivalent* to the descent statement. -/
theorem forall_reaches1_iff_descent :
    (∀ n, 0 < n → Reaches1 n) ↔ ∀ n, 1 < n → ∃ m, 0 < m ∧ collatzStep^[m] n < n := by
  constructor
  · intro H n hn
    obtain ⟨m, hm⟩ := H n (by omega)
    refine ⟨m, ?_, by omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp at hm; omega
    · exact hm0
  · intro h
    refine reaches1_of_descent_above reaches1_step_iff collatzStep_pos 2 (fun n hn h2 => ?_)
      (fun n hn => (h n (by omega)).imp fun m hm => hm.2)
    exact ⟨0, by simpa using (by omega : n = 1)⟩

/- ## The Terras shortcut map

Terras and Lagarias work with `n ↦ (3 * n + 1) / 2` on odd `n`, which is the map with the affine
structure proved in the next section. -/

/-- The shortcut (Terras) map: one step on even numbers, two collapsed steps on odd numbers. -/
def collatzShortcut (n : ℕ) : ℕ := if Even n then n / 2 else (3 * n + 1) / 2

@[local simp] theorem collatzShortcut_two_mul (k : ℕ) : collatzShortcut (2 * k) = k := by
  rw [collatzShortcut, if_pos ⟨k, (two_mul k)⟩]
  omega

@[local simp] theorem collatzShortcut_two_mul_add_one (k : ℕ) :
    collatzShortcut (2 * k + 1) = 3 * k + 2 := by
  rw [collatzShortcut, if_neg]
  · omega
  · simp

theorem collatzShortcut_pos (n : ℕ) (hn : 0 < n) : 0 < collatzShortcut n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · simp only [collatzShortcut_two_mul]; omega
  · simp only [collatzShortcut_two_mul_add_one]; omega

/-- Every shortcut step is one or two `collatzStep` steps. -/
theorem exists_iterate_collatzStep_eq_collatzShortcut (n : ℕ) :
    ∃ j, 0 < j ∧ collatzStep^[j] n = collatzShortcut n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · exact ⟨1, one_pos, by simp⟩
  · refine ⟨2, by norm_num, ?_⟩
    show collatzStep (collatzStep (2 * k + 1)) = collatzShortcut (2 * k + 1)
    rw [collatzStep_two_mul_add_one, show 6 * k + 4 = 2 * (3 * k + 2) by ring,
      collatzStep_two_mul, collatzShortcut_two_mul_add_one]

/-- The shortcut map preserves the goal, so `reaches1_of_descent_above` applies to it too. -/
theorem reaches1_collatzShortcut_iff (n : ℕ) : Reaches1 (collatzShortcut n) ↔ Reaches1 n := by
  obtain ⟨j, -, hj⟩ := exists_iterate_collatzStep_eq_collatzShortcut n
  have h := reaches1_iterate_iff reaches1_step_iff j n
  rwa [hj] at h

/-- **Bridge.** `m` shortcut steps are `j ≥ m` `collatzStep` steps, on the nose. This is what
turns a shortcut descent into a `collatzStep` descent. -/
theorem exists_iterate_collatzStep_eq_iterate_collatzShortcut (m n : ℕ) :
    ∃ j, m ≤ j ∧ collatzStep^[j] n = collatzShortcut^[m] n := by
  induction m with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨j, hj, hje⟩ := ih
    obtain ⟨i, hi, hie⟩ :=
      exists_iterate_collatzStep_eq_collatzShortcut (collatzShortcut^[m] n)
    refine ⟨i + j, by omega, ?_⟩
    rw [Function.iterate_add_apply, hje, hie, Function.iterate_succ_apply']

/- ## The affine structure of the shortcut map (Terras)

This is the mathematical heart of the file. `T = collatzShortcut` restricted to a residue class
mod `2 ^ k` and iterated `k` times is an *affine* function of the class parameter, with slope
`3 ^ oddCount k r`. Consequently a single kernel computation on the representative `r` decides
the behaviour of the whole class. -/

/-- `oddCount k n` is the number of odd entries among the first `k` terms of the shortcut orbit
of `n`, i.e. the number of `3x+1` steps taken. -/
def oddCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (if Even n then 0 else 1) + oddCount k (collatzShortcut n)

/-- **Terras' affine structure theorem.** `collatzShortcut^[k]` is affine on each residue class
mod `2 ^ k`, with slope `3 ^ oddCount k n`. The whole class is therefore determined by its
representative. -/
theorem iterate_collatzShortcut_add_two_pow_mul (k n c : ℕ) :
    collatzShortcut^[k] (n + 2 ^ k * c) = collatzShortcut^[k] n + 3 ^ oddCount k n * c := by
  induction k generalizing n c with
  | zero => simp [oddCount]
  | succ k ih =>
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have hev : Even (2 * m) := ⟨m, by ring⟩
      have h1 : 2 * m + 2 ^ (k + 1) * c = 2 * (m + 2 ^ k * c) := by ring
      have hoc : oddCount (k + 1) (2 * m) = oddCount k m := by
        simp only [oddCount, if_pos hev, collatzShortcut_two_mul, Nat.zero_add]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1,
        collatzShortcut_two_mul, collatzShortcut_two_mul, ih, hoc]
    · have hev : ¬ Even (2 * m + 1) := by simp
      have h1 : 2 * m + 1 + 2 ^ (k + 1) * c = 2 * (m + 2 ^ k * c) + 1 := by ring
      have hoc : oddCount (k + 1) (2 * m + 1) = 1 + oddCount k (3 * m + 2) := by
        simp only [oddCount, if_neg hev, collatzShortcut_two_mul_add_one]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h1,
        collatzShortcut_two_mul_add_one, collatzShortcut_two_mul_add_one, hoc,
        show 3 * (m + 2 ^ k * c) + 2 = 3 * m + 2 + 2 ^ k * (3 * c) by ring, ih]
      rw [pow_add, pow_one]
      ring

/-- **Class descent criterion.** Two conditions on the representative `r = n % 2 ^ k` — the
slope `3 ^ oddCount k r` beats `2 ^ k`, and the representative itself already drops far enough —
force `n` to drop under `k` shortcut steps. -/
theorem iterate_collatzShortcut_lt_self (k n : ℕ)
    (hpow : 3 ^ oddCount k (n % 2 ^ k) < 2 ^ k)
    (hrep : collatzShortcut^[k] (n % 2 ^ k) < n % 2 ^ k + n / 2 ^ k) :
    collatzShortcut^[k] n < n := by
  have hn : n % 2 ^ k + 2 ^ k * (n / 2 ^ k) = n := Nat.mod_add_div n (2 ^ k)
  have key := iterate_collatzShortcut_add_two_pow_mul k (n % 2 ^ k) (n / 2 ^ k)
  rw [hn] at key
  have hpow' : 3 ^ oddCount k (n % 2 ^ k) + 1 ≤ 2 ^ k := hpow
  have hmul : (3 ^ oddCount k (n % 2 ^ k) + 1) * (n / 2 ^ k) ≤ 2 ^ k * (n / 2 ^ k) :=
    Nat.mul_le_mul_right _ hpow'
  rw [add_mul, one_mul] at hmul
  rw [key]
  calc collatzShortcut^[k] (n % 2 ^ k) + 3 ^ oddCount k (n % 2 ^ k) * (n / 2 ^ k)
      < (n % 2 ^ k + n / 2 ^ k) + 3 ^ oddCount k (n % 2 ^ k) * (n / 2 ^ k) :=
        Nat.add_lt_add_right hrep _
    _ = n % 2 ^ k + (3 ^ oddCount k (n % 2 ^ k) * (n / 2 ^ k) + n / 2 ^ k) := by ring
    _ ≤ n % 2 ^ k + 2 ^ k * (n / 2 ^ k) := Nat.add_le_add_left hmul _
    _ = n := hn

/-- **The user-facing tool.** For a concrete modulus `M = 2 ^ k` and residue `r`, `hpow` is a
closed numeric statement and `decide` settles it outright; `hrep` still mentions `n`, through
`n / M`, so `decide` does not apply to it — it is settled by a `decide` for the value
`collatzShortcut^[k] r` followed by `omega`. The conclusion is exactly the descent obligation on
the right of `forall_reaches1_iff_descent`, phrased back in terms of `collatzStep`, and it
implies the (slightly weaker) `hhigh` hypothesis of `reaches1_of_descent_above`. -/
theorem exists_descent_of_mod (k M r n : ℕ) (hk : 0 < k) (hM : M = 2 ^ k) (hr : n % M = r)
    (hpow : 3 ^ oddCount k r < M) (hrep : collatzShortcut^[k] r < r + n / M) :
    ∃ m, 0 < m ∧ collatzStep^[m] n < n := by
  subst hM
  subst hr
  have hlt : collatzShortcut^[k] n < n := iterate_collatzShortcut_lt_self k n hpow hrep
  obtain ⟨j, hj, hje⟩ := exists_iterate_collatzStep_eq_iterate_collatzShortcut k n
  exact ⟨j, by omega, by rw [hje]; exact hlt⟩

/- ## The two formulations of the conjecture agree -/

/-- The delicate direction: a `collatzStep` orbit reaching `1` can be replayed with the shortcut
map. The point is that the value an odd shortcut step jumps over is `3 * n + 1 ≥ 4`, never `1`. -/
theorem exists_iterate_collatzShortcut_eq_one :
    ∀ (m n : ℕ), collatzStep^[m] n = 1 → ∃ j, collatzShortcut^[j] n = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hn
    match m, hn with
    | 0, hn => exact ⟨0, by simpa using hn⟩
    | (m + 1), hn =>
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · rw [Function.iterate_succ_apply, collatzStep_two_mul] at hn
        obtain ⟨j, hj⟩ := ih m (by omega) k hn
        exact ⟨j + 1, by rw [Function.iterate_succ_apply, collatzShortcut_two_mul]; exact hj⟩
      · rw [Function.iterate_succ_apply, collatzStep_two_mul_add_one] at hn
        match m, hn with
        | 0, hn => simp at hn
        | (m' + 1), hn =>
          rw [Function.iterate_succ_apply, show 6 * k + 4 = 2 * (3 * k + 2) by ring,
            collatzStep_two_mul] at hn
          obtain ⟨j, hj⟩ := ih m' (by omega) (3 * k + 2) hn
          exact ⟨j + 1, by
            rw [Function.iterate_succ_apply, collatzShortcut_two_mul_add_one]; exact hj⟩

/-- The two formulations of the Collatz conjecture agree, pointwise. -/
theorem reaches1_iff_exists_iterate_collatzShortcut (n : ℕ) :
    Reaches1 n ↔ ∃ m, collatzShortcut^[m] n = 1 := by
  constructor
  · rintro ⟨m, hm⟩
    exact exists_iterate_collatzShortcut_eq_one m n hm
  · rintro ⟨m, hm⟩
    exact (reaches1_iterate_iff reaches1_collatzShortcut_iff m n).mp ⟨0, by simpa using hm⟩

/- ## A kernel-checked initial segment

`decide` — kernel evaluation only, with no compiled evaluation — discharges the `hlow`
hypothesis of `reaches1_of_descent_above` through this soundness lemma. -/

/-- `reachesOneIn f n` runs the orbit of `n` for `f` steps looking for `1`. -/
def reachesOneIn : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reachesOneIn f (collatzStep n)

/-- Soundness of the bounded search. -/
theorem reaches1_of_reachesOneIn : ∀ (f n : ℕ), reachesOneIn f n = true → Reaches1 n := by
  intro f
  induction f with
  | zero =>
    intro n h
    simp only [reachesOneIn, beq_iff_eq] at h
    subst h; exact ⟨0, rfl⟩
  | succ f ih =>
    intro n h
    simp only [reachesOneIn, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · subst h; exact ⟨0, rfl⟩
    · exact (reaches1_step_iff n).mp (ih _ h)

/-- The finite initial segment demanded by `reaches1_of_descent_above`, discharged in the
kernel. -/
theorem reaches1_of_lt_eight (n : ℕ) (h0 : 0 < n) (h8 : n < 8) : Reaches1 n := by
  interval_cases n <;> exact reaches1_of_reachesOneIn 20 _ (by decide)

/- ## Use sites

Everything below is stated against the reward theorem's own type, `type_of% Erdos1135.erdos_1135`. -/

/-- **Headline reduction.** Thirteen of the sixteen residue classes mod `16` are settled here by
three invocations of `exists_descent_of_mod`, each costing two `decide` calls and an `omega`, so
the target follows from a descent for the remaining three. -/
theorem erdos_1135_of_descent_mod_sixteen
    (h : ∀ n, n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 →
      ∃ m, 0 < m ∧ collatzStep^[m] n < n) :
    type_of% Erdos1135.erdos_1135 := by
  refine forall_reaches1_iff_descent.mpr (fun n hn => ?_)
  rcases (show n % 2 = 0 ∨ n % 4 = 1 ∨ n % 16 = 3 ∨ n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 by
    omega) with h2 | h4 | h3 | h7 | h11 | h15
  · refine exists_descent_of_mod 1 2 0 n one_pos (by norm_num) h2 (by decide) ?_
    have e : collatzShortcut^[1] 0 = 0 := by decide
    rw [e]; omega
  · refine exists_descent_of_mod 2 4 1 n (by norm_num) (by norm_num) h4 (by decide) ?_
    have e : collatzShortcut^[2] 1 = 1 := by decide
    rw [e]; omega
  · refine exists_descent_of_mod 4 16 3 n (by norm_num) (by norm_num) h3 (by decide) ?_
    have e : collatzShortcut^[4] 3 = 2 := by decide
    rw [e]; omega
  · exact h n (Or.inl h7)
  · exact h n (Or.inr (Or.inl h11))
  · exact h n (Or.inr (Or.inr h15))

/-- Working entirely with the Terras map also solves the target. -/
theorem erdos_1135_of_shortcut (h : ∀ n, 0 < n → ∃ m, collatzShortcut^[m] n = 1) :
    type_of% Erdos1135.erdos_1135 :=
  fun n hn => (reaches1_iff_exists_iterate_collatzShortcut n).mpr (h n hn)

/-- The machine keeps going. The residual class `7 mod 16` splits mod `128`, and `7 mod 128` is
already settled by the very same two `decide` calls and an `omega` — no new hand-written rewrite
chain. -/
example (n : ℕ) (hn : n % 128 = 7) : ∃ m, 0 < m ∧ collatzStep^[m] n < n := by
  refine exists_descent_of_mod 7 128 7 n (by norm_num) (by norm_num) hn (by decide) ?_
  have e : collatzShortcut^[7] 7 = 5 := by decide
  rw [e]; omega

/-- The famous long orbit of `27`, checked in the kernel through the search interface. -/
example : Reaches1 27 := reaches1_of_reachesOneIn 120 27 (by decide)

/-- A full worked assembly: descent above `8` plus the kernel-checked segment below `8` gives the
target. -/
example (h : ∀ n, 8 ≤ n → ∃ m, collatzStep^[m] n < n) :
    type_of% Erdos1135.erdos_1135 :=
  reaches1_of_descent_above reaches1_step_iff collatzStep_pos 8 reaches1_of_lt_eight h

/-- The same engine, driven by the shortcut map instead — this is the instantiation the Terras
literature works with. -/
example (h : ∀ n, 8 ≤ n → ∃ m, collatzShortcut^[m] n < n) :
    type_of% Erdos1135.erdos_1135 :=
  reaches1_of_descent_above reaches1_collatzShortcut_iff collatzShortcut_pos 8
    reaches1_of_lt_eight h

end Contribution.Erdos1135CollatzDescent
