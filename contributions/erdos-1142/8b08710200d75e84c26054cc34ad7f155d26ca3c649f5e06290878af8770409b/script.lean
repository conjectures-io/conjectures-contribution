import Mathlib
import FormalConjectures.ErdosProblems.«1142»

/-!
# Erdős Problem 1142: a congruence sieve for `Erdos1142Prop`

`Erdos1142.Erdos1142Prop n` asks that `n - 2 ^ k` be prime for *every* `k ≥ 1` with `2 ^ k < n`.
Both obligations left open in `FormalConjectures/ErdosProblems/1142.lean` — the search statement
`Erdos1142.erdos_1142.variants.mientka_weitzenkamp` (all `n ≤ 2 ^ 44` with the property are
`4, 7, 15, 21, 45, 75, 105`) and the infinitude question `Erdos1142.erdos_1142` — run into the
same concrete obstacle: the definition is a *universally quantified, unbounded* primality
condition, so it offers no leverage at all on a single `n`. Refuting one `n` needs a witness
`k`; refuting a whole residue class needs an argument that the pool file does not provide.

This file supplies that argument as a checked API.

The engine is `dvd_of_covering`: if the powers `2 ^ 1, …, 2 ^ K` cover every nonzero residue
mod a prime `p` (a decidable, `by decide`-checkable finite condition), then every `n` with
`Erdos1142Prop n` and `n > 2 ^ K + p` is divisible by `p`. Reason: otherwise some `2 ^ k` is
congruent to `n`, so `p ∣ n - 2 ^ k`, and the *prime* `n - 2 ^ k` must then equal `p`, forcing
`n = 2 ^ k + p ≤ 2 ^ K + p`. Taking `K = p - 1`, the hypothesis says exactly that `2` is a
primitive root mod `p`; we check it for `p = 3, 5, 11, 13, 19`. The first four give `dvd_2145`
(`n > 4109 → 2145 ∣ n`) and all five give `dvd_40755` (`n > 262163 → 40755 ∣ n`). The prime
`p = 2` is the one case the sieve cannot supply — `2 ^ k ≡ 0 [MOD 2]` for every `k ≥ 1`, so the
residue `1` is never covered — so parity is proved directly instead, as `odd_of_four_lt`; that
lemma together with the sieves at `3` and `5` gives `mod_thirty_eq_fifteen`
(`n > 21 → n ≡ 15 [MOD 30]`).

**G1.** A later solver can use declaration
`Contribution.Erdos1142Sieve.mientka_weitzenkamp_of_residual` to discharge or simplify obligation
`Erdos1142.erdos_1142.variants.mientka_weitzenkamp` in target `Erdos1142.erdos_1142`: it reduces
that unproved statement to the single residual check that no multiple of `2145` in
`(4109, 2 ^ 44]` has the property. That removes `2144` of every `2145` residues from the search
and settles the initial segment `n ≤ 4109` outright (`eq_of_le_4109`,
`mientka_weitzenkamp_le_4109`). A later solver can equally use
`Contribution.Erdos1142Sieve.mientka_weitzenkamp_of_residual_sharp` for the same obligation: it
adds the `19`-sieve, so the residual becomes the `121` multiples of `2145` in `(4109, 262163]`
together with the multiples of `40755` in `(262163, 2 ^ 44]` — a further `19`-fold cut of the
part that dominates. Likewise, a later solver can use
`Contribution.Erdos1142Sieve.infinite_iff_infinite_mod_thirty` to simplify the obligation
`Infinite { n | Erdos1142Prop n }`, the right-hand side of `Erdos1142.erdos_1142`, to the same
statement for the single residue class `15 mod 30`.

Contents:

* `eq_two_pow_add_of_prime_dvd_sub` — the sieve step: a prime dividing `n - 2 ^ k` *is* `n - 2 ^ k`.
* `not_prop_of_not_prime_sub` — an `rcases`-free refutation certificate: one bad `k` kills `n`.
* `dvd_of_covering` — the general covering-congruence sieve.
* `odd_of_four_lt` — the parity case, which `dvd_of_covering` cannot supply: at `p = 2` its
  covering hypothesis is unsatisfiable, so this one is proved directly from
  `eq_two_pow_add_of_prime_dvd_sub`.
* `three_dvd`, `five_dvd`, `eleven_dvd`, `thirteen_dvd`, `nineteen_dvd` — the instances of
  `dvd_of_covering`.
* `mod_thirty_eq_fifteen`, `dvd_2145`, `dvd_40755` — the packaged congruence restrictions.
* `prop_iff_forall_mem_Icc`, `decidableErdos1142Prop`, `prop_of_forall_mem_Icc` — the unbounded
  `∀ k` turned into a finite `Finset.Icc` check, hence a `DecidablePred` instance and a
  `norm_num`-friendly way to certify a candidate far beyond the reach of `decide`. The reach is
  finite, not unlimited: in this workspace `norm_num` settles a ten-digit primality goal but
  overflows the elaborator's stack on a twelve-digit one, so certification stops well below the
  fourteen digits of `2 ^ 44`.
* `eq_of_le_4109`, `mientka_weitzenkamp_le_4109` — Mientka–Weitzenkamp verified up to `4109`
  (their range is `2 ^ 44`; `4109` is nearly `40` times the largest known solution `105`).
* `infinite_iff_infinite_mod_thirty`, `mientka_weitzenkamp_of_residual`,
  `mientka_weitzenkamp_of_residual_sharp` — the use sites.

*References:*
- [erdosproblems.com/1142](https://www.erdosproblems.com/1142)
- [A039669](https://oeis.org/A039669)
-/

open Nat Set

namespace Contribution.Erdos1142Sieve

open Erdos1142

/- ### The sieve step -/

/--
The key arithmetic fact behind every congruence restriction on `Erdos1142Prop`: for `0 < k` and
`2 ^ k < n` the number `n - 2 ^ k` is *prime*, so any prime `p` dividing it is equal to it and
`n` is pinned down completely as `2 ^ k + p`.
-/
theorem eq_two_pow_add_of_prime_dvd_sub {n k p : ℕ} (hn : Erdos1142Prop n)
    (hk : 0 < k) (hlt : 2 ^ k < n) (hp : p.Prime) (hdvd : p ∣ n - 2 ^ k) :
    n = 2 ^ k + p := by
  have hq : (n - 2 ^ k).Prime := hn.2 k hk hlt
  have h1 : p = n - 2 ^ k := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd
  rw [h1]
  exact (Nat.add_sub_cancel' hlt.le).symm

/--
A refutation certificate: a single exponent `k` with `n - 2 ^ k` composite refutes
`Erdos1142Prop n`. This is the shape in which concrete counterexamples are cheapest to check
(`norm_num` proves `¬ Nat.Prime m` from a factorisation), and it is what drives the search
bound below.
-/
theorem not_prop_of_not_prime_sub {n k : ℕ} (hk : 0 < k) (hlt : 2 ^ k < n)
    (h : ¬ (n - 2 ^ k).Prime) : ¬ Erdos1142Prop n := fun hn => h (hn.2 k hk hlt)

/--
**Covering-congruence sieve.** Let `p` be a prime whose nonzero residues are all of the form
`2 ^ k mod p` with `1 ≤ k ≤ K` (equivalently, `2` generates `(ZMod p)ˣ`; the hypothesis is a
finite decidable check). Then every `n > 2 ^ K + p` with `Erdos1142Prop n` is divisible by `p`.

This converts the unbounded primality condition into a divisibility constraint, which is what
makes a finite search feasible.
-/
theorem dvd_of_covering {p K n : ℕ} (hp : p.Prime)
    (hcov : ∀ r < p, r ≠ 0 → ∃ k ∈ Finset.Icc 1 K, 2 ^ k % p = r)
    (hn : Erdos1142Prop n) (hbig : 2 ^ K + p < n) : p ∣ n := by
  by_contra hpn
  obtain ⟨k, hk, hk2⟩ :=
    hcov (n % p) (Nat.mod_lt _ hp.pos) (fun h => hpn (Nat.dvd_of_mod_eq_zero h))
  rw [Finset.mem_Icc] at hk
  have hkle : (2 : ℕ) ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hk.2
  have hlt : (2 : ℕ) ^ k < n := by omega
  have hmod : (2 : ℕ) ^ k ≡ n [MOD p] := hk2
  have hdvd : p ∣ n - 2 ^ k := (Nat.modEq_iff_dvd' hlt.le).mp hmod
  have := eq_two_pow_add_of_prime_dvd_sub hn hk.1 hlt hp hdvd
  omega

/- ### The congruence restrictions -/

/-- Apart from `n = 4`, every `n` with `Erdos1142Prop n` is odd: otherwise `2 ∣ n - 2`. -/
theorem odd_of_four_lt {n : ℕ} (hn : Erdos1142Prop n) (h : 4 < n) : Odd n := by
  rcases Nat.even_or_odd n with he | ho
  · exfalso
    have hlt : (2 : ℕ) ^ 1 < n := by norm_num; omega
    have h2n : 2 ∣ n := he.two_dvd
    have hdvd : 2 ∣ n - 2 ^ 1 := by rw [pow_one]; omega
    have := eq_two_pow_add_of_prime_dvd_sub hn one_pos hlt Nat.prime_two hdvd
    norm_num at this
    omega
  · exact ho

/-- `2` is a primitive root mod `3`, so every solution `n > 7` is divisible by `3`. -/
theorem three_dvd {n : ℕ} (hn : Erdos1142Prop n) (h : 7 < n) : 3 ∣ n :=
  dvd_of_covering (p := 3) (K := 2) Nat.prime_three (by decide) hn (by simpa using h)

/-- `2` is a primitive root mod `5`, so every solution `n > 21` is divisible by `5`. -/
theorem five_dvd {n : ℕ} (hn : Erdos1142Prop n) (h : 21 < n) : 5 ∣ n :=
  dvd_of_covering (p := 5) (K := 4) Nat.prime_five (by decide) hn (by simpa using h)

/-- `2` is a primitive root mod `11`, so every solution `n > 1035` is divisible by `11`. -/
theorem eleven_dvd {n : ℕ} (hn : Erdos1142Prop n) (h : 1035 < n) : 11 ∣ n :=
  dvd_of_covering (p := 11) (K := 10) Nat.prime_eleven (by decide) hn (by simpa using h)

/-- `2` is a primitive root mod `13`, so every solution `n > 4109` is divisible by `13`. -/
theorem thirteen_dvd {n : ℕ} (hn : Erdos1142Prop n) (h : 4109 < n) : 13 ∣ n :=
  dvd_of_covering (p := 13) (K := 12) (by norm_num) (by decide) hn (by simpa using h)

/-- `2` is a primitive root mod `19`, so every solution `n > 262163 = 2 ^ 18 + 19` is divisible
by `19`. -/
theorem nineteen_dvd {n : ℕ} (hn : Erdos1142Prop n) (h : 262163 < n) : 19 ∣ n :=
  dvd_of_covering (p := 19) (K := 18) (by norm_num) (by decide) hn (by norm_num; omega)

/--
Every solution beyond the largest known one lies in a single residue class mod `30`:
`n ≡ 15 [MOD 30]`. (The seven known solutions `4, 7, 15, 21, 45, 75, 105` are consistent with
this: `45, 75, 105` are `≡ 15 [MOD 30]`.)
-/
theorem mod_thirty_eq_fifteen {n : ℕ} (hn : Erdos1142Prop n) (h : 21 < n) : n % 30 = 15 := by
  have h3 := three_dvd hn (by omega)
  have h5 := five_dvd hn h
  obtain ⟨m, hm⟩ := odd_of_four_lt hn (by omega)
  omega

/-- Beyond `4109` every solution is a multiple of `2145 = 3 * 5 * 11 * 13`. -/
theorem dvd_2145 {n : ℕ} (hn : Erdos1142Prop n) (h : 4109 < n) : 2145 ∣ n := by
  have h3 := three_dvd hn (by omega)
  have h5 := five_dvd hn (by omega)
  have h11 := eleven_dvd hn (by omega)
  have h13 := thirteen_dvd hn h
  have h15 : (15 : ℕ) ∣ n := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5
  have h165 : (165 : ℕ) ∣ n := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h15 h11
  simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 165 13 by norm_num) h165 h13

/-- Beyond `262163` every solution is a multiple of `40755 = 3 * 5 * 11 * 13 * 19`. -/
theorem dvd_40755 {n : ℕ} (hn : Erdos1142Prop n) (h : 262163 < n) : 40755 ∣ n := by
  have h2145 := dvd_2145 hn (by omega)
  have h19 := nineteen_dvd hn h
  simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2145 19 by norm_num) h2145 h19

/- ### A finite reformulation and decidability -/

/--
The unbounded quantifier `∀ k, 0 < k → 2 ^ k < n → …` in `Erdos1142Prop` is equivalent to a
quantifier over the explicit finite set `Finset.Icc 1 (Nat.log 2 n)`. This is the form a prover
actually wants: it is a finite check, and it yields the `Decidable` instance below.
-/
theorem prop_iff_forall_mem_Icc (n : ℕ) :
    Erdos1142Prop n ↔
      2 < n ∧ ∀ k ∈ Finset.Icc 1 (Nat.log 2 n), 2 ^ k < n → (n - 2 ^ k).Prime := by
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun k hk hlt => h k (Finset.mem_Icc.mp hk).1 hlt⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun k hk hlt => h k (Finset.mem_Icc.mpr ⟨hk, ?_⟩) hlt⟩
    exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr hlt.le

/--
`Erdos1142Prop` is decidable, so it can be `decide`d and used as a `DecidablePred` (to filter a
`Finset`, say). Only genuinely small instances are within reach of `decide`: `¬ Erdos1142Prop 9`
below goes through, while `¬ Erdos1142Prop 4095` already exceeds the default recursion depth.
For larger `n` the certificate lemma `not_prop_of_not_prime_sub` together with `norm_num` is far
cheaper, and that is what the search bound below uses.
-/
instance decidableErdos1142Prop (n : ℕ) : Decidable (Erdos1142Prop n) :=
  decidable_of_iff _ (prop_iff_forall_mem_Icc n).symm

/--
The converse direction of `prop_iff_forall_mem_Icc` with an explicit exponent bound: to certify
a candidate `n` it is enough to know `n ≤ 2 ^ (K + 1)` and to check the `K` primalities
`n - 2 ^ 1, …, n - 2 ^ K`. Unlike a `decide` on the whole predicate, every check here can be
discharged by `norm_num`, which reaches candidates far beyond the kernel evaluator — the latter
already exceeds its recursion limit on `¬ Erdos1142Prop 4095`. The gain is real but bounded:
measured in this workspace, a ten-digit primality goal (`Nat.Prime 1000000007`) compiles in about
`32` seconds including Mathlib's imports, while a twelve-digit one (`Nat.Prime 100000000003`)
aborts with a stack overflow — so this route too stops far short of `2 ^ 44`.
-/
theorem prop_of_forall_mem_Icc {n K : ℕ} (h2 : 2 < n) (hK : n ≤ 2 ^ (K + 1))
    (h : ∀ k ∈ Finset.Icc 1 K, 2 ^ k < n → (n - 2 ^ k).Prime) : Erdos1142Prop n := by
  refine ⟨h2, fun k hk hlt => h k (Finset.mem_Icc.mpr ⟨hk, ?_⟩) hlt⟩
  have : (2 : ℕ) ^ k < 2 ^ (K + 1) := lt_of_lt_of_le hlt hK
  have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp this
  omega

/-- `prop_of_forall_mem_Icc` in action on the largest known solution. -/
example : Erdos1142Prop 105 := by
  refine prop_of_forall_mem_Icc (K := 6) (by norm_num) (by norm_num) ?_
  intro k hk
  rw [Finset.mem_Icc] at hk
  obtain ⟨hk1, hk2⟩ := hk
  interval_cases k <;> intro _ <;> norm_num

/--
The instance in action. In the range `(7, 21]` the parity and mod `3` sieves leave only
`9, 15, 21`, of which `15` and `21` are solutions, so `9` is the single value left to refute and
`decide` disposes of it (`9 - 8 = 1` is not prime).
-/
theorem not_prop_nine : ¬ Erdos1142Prop 9 := by decide

/- ### A checked search bound -/

/--
No `n ≡ 15 [MOD 30]` with `135 ≤ n ≤ 1035` has the property. Each case is refuted by exhibiting
one exponent `k` for which `n - 2 ^ k` is composite.
-/
theorem not_prop_thirty_mul_add (m : ℕ) (hm : m ∈ Finset.Icc 4 34) :
    ¬ Erdos1142Prop (30 * m + 15) := by
  rw [Finset.mem_Icc] at hm
  obtain ⟨hm1, hm2⟩ := hm
  interval_cases m
  -- `135`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `165`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `195`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `225`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `255`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `285`
  · exact not_prop_of_not_prime_sub (k := 5) (by norm_num) (by norm_num) (by norm_num)
  -- `315`
  · exact not_prop_of_not_prime_sub (k := 4) (by norm_num) (by norm_num) (by norm_num)
  -- `345`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `375`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `405`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `435`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `465`
  · exact not_prop_of_not_prime_sub (k := 8) (by norm_num) (by norm_num) (by norm_num)
  -- `495`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `525`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `555`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `585`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `615`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `645`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `675`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `705`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `735`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `765`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `795`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `825`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `855`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `885`
  · exact not_prop_of_not_prime_sub (k := 4) (by norm_num) (by norm_num) (by norm_num)
  -- `915`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `945`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `975`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `1005`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `1035`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)

/--
No `n ≡ 165 [MOD 330]` with `1155 ≤ n ≤ 3795` has the property. Above `1035` the `11`-sieve
applies as well, so only these nine candidates survive in `(1035, 4109]`.
-/
theorem not_prop_threeHundredThirty_mul_add (j : ℕ) (hj : j ∈ Finset.Icc 3 11) :
    ¬ Erdos1142Prop (330 * j + 165) := by
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  interval_cases j
  -- `1155`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `1485`
  · exact not_prop_of_not_prime_sub (k := 3) (by norm_num) (by norm_num) (by norm_num)
  -- `1815`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `2145`
  · exact not_prop_of_not_prime_sub (k := 9) (by norm_num) (by norm_num) (by norm_num)
  -- `2475`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)
  -- `2805`
  · exact not_prop_of_not_prime_sub (k := 5) (by norm_num) (by norm_num) (by norm_num)
  -- `3135`
  · exact not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num)
  -- `3465`
  · exact not_prop_of_not_prime_sub (k := 6) (by norm_num) (by norm_num) (by norm_num)
  -- `3795`
  · exact not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num)

/--
**Mientka–Weitzenkamp, verified up to `4109`.** Every `n ≤ 4109` with `Erdos1142Prop n` is one
of the seven known solutions. The sieve leaves only `44` values in `[3, 4109]` to refute — `4`
below `22`, `31` in `(21, 1035]` and `9` in `(1035, 4109]` — each by a single exponent `k`.
-/
theorem eq_of_le_4109 {n : ℕ} (hn : Erdos1142Prop n) (h : n ≤ 4109) :
    n = 4 ∨ n = 7 ∨ n = 15 ∨ n = 21 ∨ n = 45 ∨ n = 75 ∨ n = 105 := by
  have h2 : 2 < n := hn.1
  rcases le_or_gt n 21 with h21 | h21
  · rcases le_or_gt n 7 with h7 | h7
    · interval_cases n
      -- `3`
      · exact absurd hn
          (not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num))
      -- `4`
      · norm_num
      -- `5`
      · exact absurd hn
          (not_prop_of_not_prime_sub (k := 2) (by norm_num) (by norm_num) (by norm_num))
      -- `6`
      · exact absurd hn
          (not_prop_of_not_prime_sub (k := 1) (by norm_num) (by norm_num) (by norm_num))
      -- `7`
      · norm_num
    · have h3 := three_dvd hn h7
      obtain ⟨t, ht⟩ := odd_of_four_lt hn (by omega)
      have hcases : n = 9 ∨ n = 15 ∨ n = 21 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact absurd hn not_prop_nine
      · norm_num
      · norm_num
  · have h30 := mod_thirty_eq_fifteen hn h21
    obtain ⟨m, rfl⟩ : ∃ m, n = 30 * m + 15 := ⟨n / 30, by omega⟩
    rcases le_or_gt m 34 with hm34 | hm34
    · rcases lt_or_ge m 4 with hm4 | hm4
      · have hm1 : 1 ≤ m := by omega
        interval_cases m <;> norm_num
      · exact absurd hn (not_prop_thirty_mul_add m (Finset.mem_Icc.mpr ⟨hm4, hm34⟩))
    · have h11 := eleven_dvd hn (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, m = 11 * j + 5 := ⟨(m - 5) / 11, by omega⟩
      rw [show 30 * (11 * j + 5) + 15 = 330 * j + 165 by ring] at hn
      exact absurd hn
        (not_prop_threeHundredThirty_mul_add j (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

/--
The statement of `Erdos1142.erdos_1142.variants.mientka_weitzenkamp` with the bound `2 ^ 44`
replaced by `4109`, proved. The `⊇` inclusion reuses the target file's own `test_*` lemmas.
-/
theorem mientka_weitzenkamp_le_4109 :
    {n : ℕ | n ≤ 4109 ∧ Erdos1142Prop n} = {4, 7, 15, 21, 45, 75, 105} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hle, hn⟩
    exact eq_of_le_4109 hn hle
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨by norm_num, erdos_1142.test_4⟩, ⟨by norm_num, erdos_1142.test_7⟩,
      ⟨by norm_num, erdos_1142.test_15⟩, ⟨by norm_num, erdos_1142.test_21⟩,
      ⟨by norm_num, erdos_1142.test_45⟩, ⟨by norm_num, erdos_1142.test_75⟩,
      ⟨by norm_num, erdos_1142.test_105⟩]

/- ### Use sites -/

/--
**Use site for `Erdos1142.erdos_1142.variants.mientka_weitzenkamp`.** That whole unproved
statement of the target file follows from the residual check that no multiple of `2145` in
`(4109, 2 ^ 44]` has the property: the sieve has removed `2144` of every `2145` residues, and
the initial segment `n ≤ 4109` is already settled.
-/
theorem mientka_weitzenkamp_of_residual
    (hres : ∀ m : ℕ, 4109 < 2145 * m → 2145 * m ≤ 2 ^ 44 → ¬ Erdos1142Prop (2145 * m)) :
    {n : ℕ | n ≤ 2 ^ 44 ∧ Erdos1142Prop n} = {4, 7, 15, 21, 45, 75, 105} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hle, hn⟩
    rcases le_or_gt n 4109 with h1 | h1
    · exact eq_of_le_4109 hn h1
    · obtain ⟨m, rfl⟩ := dvd_2145 hn h1
      exact absurd hn (hres m h1 hle)
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨by norm_num, erdos_1142.test_4⟩, ⟨by norm_num, erdos_1142.test_7⟩,
      ⟨by norm_num, erdos_1142.test_15⟩, ⟨by norm_num, erdos_1142.test_21⟩,
      ⟨by norm_num, erdos_1142.test_45⟩, ⟨by norm_num, erdos_1142.test_75⟩,
      ⟨by norm_num, erdos_1142.test_105⟩]

/--
**The same use site, sharpened by the `19`-sieve.** Above `262163` a solution must be a multiple
of `40755`, not merely of `2145`, so the residual splits into the `121` multiples of `2145` in
`(4109, 262163]` and the multiples of `40755` in `(262163, 2 ^ 44]`. The second range is the one
that dominates, and this cuts it by a further factor of `19`. Neither range is small enough to
be checked in the kernel today; the point is the size of the reduction, not its completion.
-/
theorem mientka_weitzenkamp_of_residual_sharp
    (h1 : ∀ m : ℕ, 4109 < 2145 * m → 2145 * m ≤ 262163 → ¬ Erdos1142Prop (2145 * m))
    (h2 : ∀ m : ℕ, 262163 < 40755 * m → 40755 * m ≤ 2 ^ 44 → ¬ Erdos1142Prop (40755 * m)) :
    {n : ℕ | n ≤ 2 ^ 44 ∧ Erdos1142Prop n} = {4, 7, 15, 21, 45, 75, 105} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hle, hn⟩
    rcases le_or_gt n 4109 with hlow | hlow
    · exact eq_of_le_4109 hn hlow
    · rcases le_or_gt n 262163 with hmid | hmid
      · obtain ⟨m, rfl⟩ := dvd_2145 hn hlow
        exact absurd hn (h1 m hlow hmid)
      · obtain ⟨m, rfl⟩ := dvd_40755 hn hmid
        exact absurd hn (h2 m hmid hle)
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨by norm_num, erdos_1142.test_4⟩, ⟨by norm_num, erdos_1142.test_7⟩,
      ⟨by norm_num, erdos_1142.test_15⟩, ⟨by norm_num, erdos_1142.test_21⟩,
      ⟨by norm_num, erdos_1142.test_45⟩, ⟨by norm_num, erdos_1142.test_75⟩,
      ⟨by norm_num, erdos_1142.test_105⟩]

/--
**Use site for `Erdos1142.erdos_1142` itself.** The right-hand side of the target biconditional
may be replaced by infinitude of the solutions in the single residue class `15 mod 30`: only
finitely many solutions can lie outside it. A solver constructing infinitely many solutions is
therefore free to assume the extra congruence, and one refuting them only has to handle it.
-/
theorem infinite_iff_infinite_mod_thirty :
    Infinite {n | Erdos1142Prop n} ↔ Infinite {n | Erdos1142Prop n ∧ n % 30 = 15} := by
  rw [Set.infinite_coe_iff, Set.infinite_coe_iff]
  constructor
  · intro h
    by_contra hfin
    rw [Set.not_infinite] at hfin
    refine h (Set.Finite.subset (hfin.union (Set.finite_Iic 21)) ?_)
    intro n hn
    rcases le_or_gt n 21 with h1 | h1
    · exact Or.inr h1
    · exact Or.inl ⟨hn, mod_thirty_eq_fifteen hn h1⟩
  · exact fun h => Set.Infinite.mono (fun n hn => hn.1) h

end Contribution.Erdos1142Sieve
#print axioms Contribution.Erdos1142Sieve.eq_two_pow_add_of_prime_dvd_sub
#print axioms Contribution.Erdos1142Sieve.not_prop_of_not_prime_sub
#print axioms Contribution.Erdos1142Sieve.dvd_of_covering
#print axioms Contribution.Erdos1142Sieve.odd_of_four_lt
#print axioms Contribution.Erdos1142Sieve.three_dvd
#print axioms Contribution.Erdos1142Sieve.five_dvd
#print axioms Contribution.Erdos1142Sieve.eleven_dvd
#print axioms Contribution.Erdos1142Sieve.thirteen_dvd
#print axioms Contribution.Erdos1142Sieve.nineteen_dvd
#print axioms Contribution.Erdos1142Sieve.mod_thirty_eq_fifteen
#print axioms Contribution.Erdos1142Sieve.dvd_2145
#print axioms Contribution.Erdos1142Sieve.dvd_40755
#print axioms Contribution.Erdos1142Sieve.prop_iff_forall_mem_Icc
#print axioms Contribution.Erdos1142Sieve.decidableErdos1142Prop
#print axioms Contribution.Erdos1142Sieve.prop_of_forall_mem_Icc
#print axioms Contribution.Erdos1142Sieve.not_prop_nine
#print axioms Contribution.Erdos1142Sieve.not_prop_thirty_mul_add
#print axioms Contribution.Erdos1142Sieve.not_prop_threeHundredThirty_mul_add
#print axioms Contribution.Erdos1142Sieve.eq_of_le_4109
#print axioms Contribution.Erdos1142Sieve.mientka_weitzenkamp_le_4109
#print axioms Contribution.Erdos1142Sieve.mientka_weitzenkamp_of_residual
#print axioms Contribution.Erdos1142Sieve.mientka_weitzenkamp_of_residual_sharp
#print axioms Contribution.Erdos1142Sieve.infinite_iff_infinite_mod_thirty
