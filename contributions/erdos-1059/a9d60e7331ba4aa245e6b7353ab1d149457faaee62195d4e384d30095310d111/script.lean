import Mathlib
import FormalConjectures.ErdosProblems.«1059»

/-!
# Erdős Problem 1059: a usable form of the target predicate, and the shifted-factorial obstruction

Target: `Erdos1059.erdos_1059` — are there infinitely many primes `p` such that `p - k!`
is composite for every `k` with `k ! < p`?

## The obstacle

The predicate on the right-hand side of the target is
`Erdos1059.AllFactorialSubtractionsComposite p`, unfolded as a bounded quantifier over the
*set* `Erdos1059.factorialsLessThanN p = {d | d < p ∧ d ∈ Set.range Nat.factorial}`.
Every argument about the problem — a construction, a search, or a covering-congruence
attempt — has to first turn a set membership plus an existential `∃ k, k ! = d` into a
statement indexed by `k`, and there is no `Decidable` instance for the predicate at all
(the pool file only supplies a separate, quadratic-cost `Prop` mirror plus a bridging
lemma). Worse, the natural first idea for producing infinitely many such `p` — pin `p`
down in a fixed residue class mod `M` so that each `p - k!` acquires a small prime factor —
is silently doomed, and nothing in the pool file records why.

## What is proved here

* `allFactorialSubtractionsComposite_iff` replaces the set-indexed predicate by the
  `rcases`-friendly form `∀ k, k ! < n → (n - k !).Composite`.
* `allFactorialSubtractionsComposite_iff_range` cuts that quantifier down to
  `Finset.range B` for any `B` with `n ≤ B !`. Taking `B` minimal (a bound of size
  `O(log n / log log n)`) makes this the cheap route to settling membership by `decide`.
* `decidableAllFactorialSubtractionsComposite` is the `Decidable` instance built from that
  lemma, so `decide` applies to the target's own predicate with no rewriting first — a
  capability the pool file does not provide. Its cost is *not* the `O(log n / log log n)`
  one: the instance instantiates `B := n` (via `Nat.self_le_factorial`), so it runs an
  `O(n)`-step check, and `decide` through it exceeds the default `maxRecDepth` already at
  `n = 211` (measured in this workspace: `n = 101` goes through at the default, while
  `n = 211` fails at the default and needs `maxRecDepth` around 20000; the demand grows
  with `n`).
  For anything beyond small `n`, rewrite with `allFactorialSubtractionsComposite_iff_range`
  at a minimal `B` instead of invoking the instance.
* `lt_of_prime_dvd_sub_factorial` is the arithmetic heart: if `p` is prime and `k ! < p`,
  then **every** prime divisor of `p - k !` is `> k` (a prime `q ≤ k` divides `k !`, so it
  would divide `p`). From it:
  * `not_dvd_sub_factorial_of_le` / `coprime_sub_factorial`: a modulus `M` all of whose
    prime factors are `≤ k` is coprime to `p - k !`; in particular `M ∤ (p - k !)` whenever
    `M ≤ k`. This is a checked impossibility result. Pinning `p` into a residue class modulo
    a modulus chosen once and for all — the standard Erdős covering-congruence device, and
    the first thing one reaches for here — provides *no* compositeness information about
    `p - k !` for any `k ≥ M`, so it can never cover the whole range `k ! < p`. Any
    construction must therefore supply certificate primes that grow with `k`; a solver
    should not spend time searching for a fixed covering system.
  * `sq_succ_le_sub_factorial`: for a prime `p` in the target set, `(k + 1) ^ 2 ≤ p - k !`
    for every `k` with `k ! < p`; equivalently `k ! + (k+1)^2 ≤ p`.
  * `not_allFactorialSubtractionsComposite_of_lt`: hence *no* prime in the window
    `(k !, k ! + (k+1)^2)` lies in the target set, for any `k`, and seeing this needs no
    primality or factorisation work on `p - k !`. The windows are thin — together they hold
    `O((log n / log log n)^3)` of the integers up to `n` — so this settles the primes
    sitting just above a factorial rather than materially shortening a search.

## Handoff (G1)

A later solver can use declaration
`Contribution.Erdos1059FactorialShifts.allFactorialSubtractionsComposite_iff` to discharge or
simplify obligation `Erdos1059.AllFactorialSubtractionsComposite p` (the membership condition
defining the set `{p | p.Prime ∧ Erdos1059.AllFactorialSubtractionsComposite p}` whose
infinitude is asserted) in target `Erdos1059.erdos_1059`.

The end of this file contains worked use sites: `infinite_setOf_of_certificates` turns
"unboundedly many primes `p`, each with a proper prime factor of every `p - k !`" into the
infinitude asserted by the target, `erdos_1059_answer_true_of_unbounded` produces the literal
statement `True ↔ Set.Infinite {p | p.Prime ∧ Erdos1059.AllFactorialSubtractionsComposite p}`
of the reward theorem from that input, and three `example`s check a positive instance through
`allFactorialSubtractionsComposite_iff_range`, the same positive instance through the
`Decidable` instance itself, and a negative instance through the window bound.

## Attribution

`Nat.Composite` is a *reducible* abbreviation in `FormalConjecturesForMathlib`
(`Nat.Composite n := 1 < n ∧ ¬ n.Prime`) with no lemmas of its own, but Mathlib's results
about `¬ n.Prime` apply through it unchanged. The one place below that has to *build* a
`Nat.Composite` — `allFactorialSubtractionsComposite_of_certificates` — therefore does so
with Mathlib's `Nat.not_prime_of_dvd_of_lt` (`Mathlib/Data/Nat/Prime/Basic.lean`); no local
introduction rule for `Nat.Composite` is stated here, since that would only repackage an
existing Mathlib lemma.
-/

open Nat

namespace Contribution.Erdos1059FactorialShifts

/- ### Reshaping the target predicate -/

/-- `Erdos1059.factorialsLessThanN n` is exactly the image under `Nat.factorial` of the
initial segment `{k | k ! < n}`. -/
theorem factorialsLessThanN_eq_image (n : ℕ) :
    Erdos1059.factorialsLessThanN n = Nat.factorial '' {k | k ! < n} := by
  ext d
  simp only [Erdos1059.factorialsLessThanN, Erdos1059.IsFactorial, Set.mem_setOf_eq,
    Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨hd, k, rfl⟩
    exact ⟨k, hd, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨hk, k, rfl⟩

/-- The workhorse reformulation: the set-indexed bounded quantifier in
`Erdos1059.AllFactorialSubtractionsComposite` becomes a plain quantifier over `k : ℕ`. -/
theorem allFactorialSubtractionsComposite_iff (n : ℕ) :
    Erdos1059.AllFactorialSubtractionsComposite n ↔
      ∀ k : ℕ, k ! < n → (n - k !).Composite := by
  simp only [Erdos1059.AllFactorialSubtractionsComposite, factorialsLessThanN_eq_image,
    Set.mem_image, Set.mem_setOf_eq, forall_exists_index]
  constructor
  · intro h k hk
    exact h (k !) k ⟨hk, rfl⟩
  · rintro h d k ⟨hk, rfl⟩
    exact h k hk

/-- Factorials are monotone, so `k ! < n` bounds `k` by any `B` with `n ≤ B !`. -/
theorem lt_of_factorial_lt {k n B : ℕ} (hk : k ! < n) (hB : n ≤ B !) : k < B := by
  by_contra h
  push_neg at h
  have : B ! ≤ k ! := Nat.factorial_le h
  omega

/-- A finite, decidable form of the target predicate: only `k < B` matter, for any `B`
with `n ≤ B !`. Taking `B` minimal makes this an `O(log n / log log n)`-step check, versus
the `O(n²)` mirror predicate in the pool file. -/
theorem allFactorialSubtractionsComposite_iff_range {n B : ℕ} (hB : n ≤ B !) :
    Erdos1059.AllFactorialSubtractionsComposite n ↔
      ∀ k ∈ Finset.range B, k ! < n → (n - k !).Composite := by
  rw [allFactorialSubtractionsComposite_iff]
  refine ⟨fun h k _ hk => h k hk, fun h k hk => h k ?_ hk⟩
  exact Finset.mem_range.mpr (lt_of_factorial_lt hk hB)

/-- `Erdos1059.AllFactorialSubtractionsComposite` is decidable, so `decide` applies directly
to the predicate appearing in the target statement, with no rewriting first.

Cost, stated honestly: this instance instantiates `allFactorialSubtractionsComposite_iff_range`
at `B := n`, so it is an `O(n)`-step check and **not** the `O(log n / log log n)` check that a
minimal `B` gives. Measured in this workspace, `decide` through the instance succeeds at
`n = 101` with the default `maxRecDepth` but already exceeds that default at `n = 211`,
where `maxRecDepth` around 20000 suffices; the demand grows with `n`. Rewriting with
`allFactorialSubtractionsComposite_iff_range` at a minimal `B` is the route to use beyond
small `n`. -/
instance decidableAllFactorialSubtractionsComposite (n : ℕ) :
    Decidable (Erdos1059.AllFactorialSubtractionsComposite n) :=
  decidable_of_iff _ (allFactorialSubtractionsComposite_iff_range
    (B := n) (Nat.self_le_factorial n)).symm

/- ### The shifted-factorial obstruction -/

/-- **Every prime divisor of `p - k !` exceeds `k`**, for `p` prime with `k ! < p`.
Indeed a prime `q ≤ k` divides `k !`, hence would divide `p = (p - k !) + k !`. -/
theorem lt_of_prime_dvd_sub_factorial {p k q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hk : k ! < p) (hdvd : q ∣ p - k !) : k < q := by
  by_contra hqk
  push_neg at hqk
  have hqf : q ∣ k ! := Nat.dvd_factorial hq.pos hqk
  have hqp : q ∣ p := by
    have h := dvd_add hdvd hqf
    rwa [Nat.sub_add_cancel hk.le] at h
  have hqe : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
  have h1 : k ≤ k ! := Nat.self_le_factorial k
  omega

/-- Any modulus built from primes `≤ k` is coprime to `p - k !`. -/
theorem coprime_sub_factorial {p k M : ℕ} (hp : p.Prime) (hk : k ! < p)
    (hM : ∀ q : ℕ, q.Prime → q ∣ M → q ≤ k) : Nat.Coprime M (p - k !) := by
  by_contra hco
  simp only [Nat.Coprime] at hco
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hco
  have h1 : q ∣ M := hqd.trans (Nat.gcd_dvd_left _ _)
  have h2 : q ∣ p - k ! := hqd.trans (Nat.gcd_dvd_right _ _)
  have := lt_of_prime_dvd_sub_factorial hp hq hk h2
  have := hM q hq h1
  omega

/-- **A fixed modulus certifies nothing once `k ≥ M`.** For a prime `p` and any `k ≥ M`, the
modulus `M` does not divide `p - k !`: forcing `p` into a residue class modulo a fixed `M`
gives no information about the compositeness of `p - k !` once `k ≥ M`. Hence no prime factor
of a fixed modulus `M` can certify compositeness of `p - k !` for `k ≥ M`, so a covering
system with a fixed modulus cannot cover the whole range `k ! < p`. (It says nothing about
whether such primes exist — they are plentiful — only that this device cannot exhibit
them by itself.) -/
theorem not_dvd_sub_factorial_of_le {p k M : ℕ} (hp : p.Prime) (hM : 1 < M) (hMk : M ≤ k)
    (hk : k ! < p) : ¬ M ∣ (p - k !) := by
  intro hdvd
  have hco : Nat.Coprime M (p - k !) :=
    coprime_sub_factorial hp hk fun q _ hqM => le_trans (Nat.le_of_dvd (by omega) hqM) hMk
  have := Nat.eq_one_of_dvd_coprimes hco dvd_rfl hdvd
  omega

/-- Quantitative necessary condition: if `p` is a prime of the kind asked for in
Erdős 1059, then `p - k !` is not merely composite, it is at least `(k+1)^2`, because all
of its prime factors exceed `k`. -/
theorem sq_succ_le_sub_factorial {p k : ℕ} (hp : p.Prime)
    (h : Erdos1059.AllFactorialSubtractionsComposite p) (hk : k ! < p) :
    (k + 1) ^ 2 ≤ p - k ! := by
  obtain ⟨h1, h2⟩ := (allFactorialSubtractionsComposite_iff p).mp h k hk
  have hm1 : p - k ! ≠ 1 := by omega
  have hpf : (Nat.minFac (p - k !)).Prime := Nat.minFac_prime hm1
  have hd : Nat.minFac (p - k !) ∣ p - k ! := Nat.minFac_dvd _
  have hlt : k < Nat.minFac (p - k !) := lt_of_prime_dvd_sub_factorial hp hpf hk hd
  calc (k + 1) ^ 2 ≤ (Nat.minFac (p - k !)) ^ 2 := Nat.pow_le_pow_left hlt 2
    _ ≤ p - k ! := Nat.minFac_sq_le_self (by omega) h2

/-- For every `k`, no prime in the window `(k !, k ! + (k+1)^2)` belongs to the set of
Erdős 1059, and no primality test or factorisation of `p - k !` is needed to see it. The
windows are thin — together they cover `O((log n / log log n)^3)` of the integers below `n` —
so this disposes of the primes lying just above a factorial; it is not a material speedup for
a search over all primes. -/
theorem not_allFactorialSubtractionsComposite_of_lt {p k : ℕ} (hp : p.Prime)
    (hk : k ! < p) (hlt : p < k ! + (k + 1) ^ 2) :
    ¬ Erdos1059.AllFactorialSubtractionsComposite p := by
  intro h
  have h2 := sq_succ_le_sub_factorial hp h hk
  have h3 : k ! ≤ p := hk.le
  omega

/- ### Use sites -/

/-- Reduction of the right-hand side of `Erdos1059.erdos_1059` to an unbounded existence
statement phrased purely in terms of `k`. -/
theorem infinite_setOf_of_unbounded
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ∀ k : ℕ, k ! < p → (p - k !).Composite) :
    Set.Infinite {p : ℕ | p.Prime ∧ Erdos1059.AllFactorialSubtractionsComposite p} := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp, hcomp⟩ := h a
  exact ⟨p, ⟨hp, (allFactorialSubtractionsComposite_iff p).mpr hcomp⟩, hpa⟩

/-- Certificate form: to place `p` in the target set it is enough to exhibit, for every `k`
with `k ! < p`, one proper prime factor of `p - k !`. Compositeness of `p - k !` then comes
straight from Mathlib's `Nat.not_prime_of_dvd_of_lt`, which applies through the reducible
abbreviation `Nat.Composite`. By `lt_of_prime_dvd_sub_factorial` every such certificate prime
is necessarily `> k`. -/
theorem allFactorialSubtractionsComposite_of_certificates {p : ℕ}
    (h : ∀ k : ℕ, k ! < p → ∃ q : ℕ, q.Prime ∧ q ∣ p - k ! ∧ q < p - k !) :
    Erdos1059.AllFactorialSubtractionsComposite p := by
  refine (allFactorialSubtractionsComposite_iff p).mpr fun k hk => ?_
  obtain ⟨q, hq, hqd, hql⟩ := h k hk
  exact ⟨lt_of_le_of_lt hq.one_lt.le hql, Nat.not_prime_of_dvd_of_lt hqd hq.two_le hql⟩

/-- The whole chain, in the shape a construction actually produces: unboundedly many primes,
each carrying a proper prime factor of every shifted difference. -/
theorem infinite_setOf_of_certificates
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
      ∀ k : ℕ, k ! < p → ∃ q : ℕ, q.Prime ∧ q ∣ p - k ! ∧ q < p - k !) :
    Set.Infinite {p : ℕ | p.Prime ∧ Erdos1059.AllFactorialSubtractionsComposite p} := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp, hcert⟩ := h a
  exact ⟨p, ⟨hp, allFactorialSubtractionsComposite_of_certificates hcert⟩, hpa⟩

/-- The reward statement `Erdos1059.erdos_1059` with `answer := True`, reduced to the one
number-theoretic input a solver has to supply. -/
theorem erdos_1059_answer_true_of_unbounded
    (h : ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ ∀ k : ℕ, k ! < p → (p - k !).Composite) :
    True ↔ Set.Infinite {p : ℕ | p.Prime ∧ Erdos1059.AllFactorialSubtractionsComposite p} :=
  iff_of_true trivial (infinite_setOf_of_unbounded h)

/- Use site 1: `101` is in the set, checked with a five-element search instead of the
pool file's `Finset.range 101`-sized computation. This is the fast route. -/
example : Erdos1059.AllFactorialSubtractionsComposite 101 := by
  rw [allFactorialSubtractionsComposite_iff_range (B := 5) (by decide)]
  decide

/- Use site 2: the same membership with no rewriting at all, straight through
`decidableAllFactorialSubtractionsComposite`. This is the capability the pool file does not
provide: without the instance, `decide` fails here with "failed to synthesize Decidable".
It takes the `B := n` route, so it is markedly slower than use site 1 and, for larger `n`,
runs past the default `maxRecDepth`. -/
example : Erdos1059.AllFactorialSubtractionsComposite 101 := by decide

/- Use site 3: `127` is *not* in the set, by the window bound alone — `120 = 5! < 127 <
120 + 36`, so `127 - 120` has all prime factors `> 5` and is too small to be composite.
No factorisation of `127 - 120` is performed. -/
example : ¬ Erdos1059.AllFactorialSubtractionsComposite 127 :=
  not_allFactorialSubtractionsComposite_of_lt (k := 5) (by norm_num) (by decide) (by decide)

end Contribution.Erdos1059FactorialShifts
