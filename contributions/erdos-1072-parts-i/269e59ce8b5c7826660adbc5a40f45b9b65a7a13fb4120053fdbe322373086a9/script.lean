import Mathlib
import FormalConjectures.ErdosProblems.«1072»

/-!
# Erdős Problem 1072 (i): a dual-index, `sInf`-free API for `Erdos1072.f`

`Erdos1072.f p = sInf {n | n ! + 1 ≡ 0 [MOD p]}` is the least `n` with `n ! ≡ -1 (mod p)`,
and `erdos_1072.parts.i` asks whether `{p | p.Prime ∧ f p = p - 1}` is infinite.

Three concrete obstacles stand between that set and any usable statement about it. None of
them is deep; each of them costs a solver time.

* `f` is an `sInf` of a set of naturals, and each `sInf` fact needs its own input before it
  says anything: `Nat.sInf_mem` (used by `factorial_f_eq_neg_one`) needs the defining set to be
  nonempty, which here is Wilson's theorem, and `Nat.sInf_le` (used by `f_le_sub_one`) needs an
  explicit member; only the minimality direction `Nat.notMem_of_lt_sInf` (used by
  `factorial_ne_neg_one_of_lt_f`) needs neither. The predicate is also phrased with `Nat.ModEq`
  on `n ! + 1`, while the usable Mathlib facts about factorials mod `p` (`ZMod.wilsons_lemma`,
  `ZMod.cast_descFactorial`) are stated in `ZMod p`.
* The condition `f p = p - 1` is a statement about the factorials of the *large* indices
  `n ≤ p - 1`, i.e. about numbers of size `p!`. The dual form replaces one index by its
  complement: `p - 1 - a` solves `n ! ≡ -1` iff `a ! ≡ (-1) ^ a`, so a solution at a large index
  is certified by the single factorial `a !`, which is small exactly when `p - 1 - a` is large.
  This is the reflection `a ! · b ! ≡ (-1) ^ (a + 1)` for `a + b = p - 1`, which is not in
  Mathlib (Mathlib has only the one-sided `ZMod.cast_descFactorial`).
* The formalisation is `0`-indexed and `0! = 1`, so `f 2 = 0 ≠ 1 = 2 - 1`: the prime `2` is
  *not* a member of the target set even though Wilson's theorem holds for it. This is easy to
  miss and breaks any argument that starts its induction at `2`.

This file addresses all three. `factorial_add_one_modEq_zero_iff` moves the defining predicate
into `ZMod p`; `f_le_sub_one`, `factorial_f_eq_neg_one` and `factorial_ne_neg_one_of_lt_f` are the
`sInf` interface; `f_eq_sub_one_iff` turns the equation `f p = p - 1` into a bounded `∀`;
`factorial_mul_factorial_of_add_eq` is the reflection identity; `factorial_eq_neg_one_iff` is the
resulting duality, and `f_eq_sub_one_iff_forall_small` and `setOf_prime_and_f_eq_sub_one` package
it as a rewrite of the target set itself. `notMem_of_small_witness` is the cheap certificate for
excluding a prime, and `mem_iff_ball` makes membership `decide`-able.

One caveat, stated up front because the names invite the opposite reading: the set rewrite
`setOf_prime_and_f_eq_sub_one` is the bijective relabelling `a ↔ p - 1 - a` of the *same* index
range `1 ≤ a ≤ p - 1`, so it removes the `sInf` but does not shrink the factorials involved (it
still reaches `(p - 1)!`). The genuine small-index payoff is the one-witness certificate
`f_lt_sub_one_of_small_witness` / `notMem_of_small_witness`, which excludes a prime from a single
small `a !`; and the `decide`-able interface actually used by the examples below is
`mem_iff_ball`, which comes from `f_eq_sub_one_iff` and does not use the reflection at all.

A later solver can use `Contribution.Erdos1072Pillai.setOf_prime_and_f_eq_sub_one` to discharge or
simplify obligation `Set.Infinite {p | p.Prime ∧ Erdos1072.f p = p - 1}` in target
`Erdos1072.erdos_1072.parts.i`.

*Reference:* [erdosproblems.com/1072](https://www.erdosproblems.com/1072)
-/

open Nat

namespace Contribution.Erdos1072Pillai

open Erdos1072

variable {p a b n : ℕ}

/- ### From `Nat.ModEq` to `ZMod p` -/

/-- The defining predicate of `Erdos1072.f`, transported into `ZMod p`. Valid for every `p`
(including `p = 0`, where both sides are false). -/
theorem factorial_add_one_modEq_zero_iff (p n : ℕ) :
    n ! + 1 ≡ 0 [MOD p] ↔ (n ! : ZMod p) = -1 := by
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [add_eq_zero_iff_eq_neg]

/-- The same predicate as a decidable statement about natural numbers, ready for `decide`. -/
theorem factorial_add_one_mod_eq_zero_iff (p n : ℕ) :
    (n ! + 1) % p = 0 ↔ (n ! : ZMod p) = -1 := by
  rw [← factorial_add_one_modEq_zero_iff]
  simp [Nat.ModEq]

/- ### The `sInf` interface -/

/-- Wilson's theorem, in the shape needed to feed the `sInf` in `Erdos1072.f`. -/
theorem factorial_sub_one_modEq (hp : p.Prime) : (p - 1)! + 1 ≡ 0 [MOD p] := by
  haveI := Fact.mk hp
  rw [factorial_add_one_modEq_zero_iff]
  exact ZMod.wilsons_lemma p

/-- The defining set of `Erdos1072.f p` is nonempty at a prime, so the `sInf` is meaningful. -/
theorem nonempty_of_prime (hp : p.Prime) : {n | n ! + 1 ≡ 0 [MOD p]}.Nonempty :=
  ⟨p - 1, factorial_sub_one_modEq hp⟩

/-- `f p ≤ p - 1` for every prime `p`: the target set is exactly the set of primes at which this
bound is attained. -/
theorem f_le_sub_one (hp : p.Prime) : f p ≤ p - 1 :=
  Nat.sInf_le (factorial_sub_one_modEq hp)

/-- The value `f p` really is a solution (`Nat.sInf_mem` plus nonemptiness). -/
theorem factorial_f_eq_neg_one (hp : p.Prime) : ((f p)! : ZMod p) = -1 := by
  rw [← factorial_add_one_modEq_zero_iff]
  exact Nat.sInf_mem (nonempty_of_prime hp)

/-- Minimality of `f p`, in `ZMod p` form. -/
theorem factorial_ne_neg_one_of_lt_f (h : n < f p) : (n ! : ZMod p) ≠ -1 := fun hcon =>
  Nat.notMem_of_lt_sInf (s := {m | m ! + 1 ≡ 0 [MOD p]}) h
    ((factorial_add_one_modEq_zero_iff p n).2 hcon)

/-- The equation `f p = p - 1` as a bounded universal statement: no `sInf` left. -/
theorem f_eq_sub_one_iff (hp : p.Prime) :
    f p = p - 1 ↔ ∀ n < p - 1, (n ! : ZMod p) ≠ -1 := by
  constructor
  · intro h n hn
    exact factorial_ne_neg_one_of_lt_f (h ▸ hn)
  · intro h
    refine le_antisymm (f_le_sub_one hp) ?_
    rcases Nat.lt_or_ge (f p) (p - 1) with hlt | hge
    · exact absurd (factorial_f_eq_neg_one hp) (h _ hlt)
    · exact hge

/- ### The reflection `a ! · b ! ≡ (-1) ^ (a + 1)` and the resulting duality -/

private theorem neg_one_pow_mul_self (R : Type*) [Monoid R] [HasDistribNeg R] (a : ℕ) :
    ((-1 : R) ^ a) * ((-1 : R) ^ a) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- **Reflection identity.** If `a + b = p - 1` with `p` prime, then `a ! * b ! = (-1) ^ (a + 1)`
in `ZMod p`. Wilson's theorem is the case `a = 0`. -/
theorem factorial_mul_factorial_of_add_eq (hp : p.Prime) (hab : a + b = p - 1) :
    (a ! : ZMod p) * (b ! : ZMod p) = (-1) ^ (a + 1) := by
  haveI := Fact.mk hp
  have hp2 := hp.two_le
  have hb : p - 1 - a = b := by omega
  have hkey : ((b ! : ℕ) : ZMod p) * (((p - 1).descFactorial a : ℕ) : ZMod p) = -1 := by
    rw [← Nat.cast_mul, ← hb, Nat.factorial_mul_descFactorial (by omega), ZMod.wilsons_lemma]
  rw [ZMod.cast_descFactorial (by omega : a ≤ p)] at hkey
  calc (a ! : ZMod p) * (b ! : ZMod p)
      = (((-1 : ZMod p) ^ a) * ((-1 : ZMod p) ^ a)) * ((a ! : ZMod p) * (b ! : ZMod p)) := by
        rw [neg_one_pow_mul_self, one_mul]
    _ = ((-1 : ZMod p) ^ a) * ((b ! : ZMod p) * ((-1 : ZMod p) ^ a * (a ! : ZMod p))) := by ring
    _ = ((-1 : ZMod p) ^ a) * (-1) := by rw [hkey]
    _ = (-1) ^ (a + 1) := by rw [pow_succ]

/-- **Duality.** For `a + b = p - 1`, the index `b` solves `n ! ≡ -1 (mod p)` if and only if the
complementary index `a` satisfies `a ! ≡ (-1) ^ a (mod p)`. Applied with `b` large and
`a = p - 1 - b` small, it trades one large factorial for one small one. -/
theorem factorial_eq_neg_one_iff (hp : p.Prime) (hab : a + b = p - 1) :
    (b ! : ZMod p) = -1 ↔ (a ! : ZMod p) = (-1) ^ a := by
  have hpair := factorial_mul_factorial_of_add_eq hp hab
  constructor
  · intro hb
    rw [hb, pow_succ] at hpair
    simpa using hpair
  · intro ha
    calc (b ! : ZMod p)
        = (((-1 : ZMod p) ^ a) * ((-1 : ZMod p) ^ a)) * (b ! : ZMod p) := by
          rw [neg_one_pow_mul_self, one_mul]
      _ = ((-1 : ZMod p) ^ a) * (((-1 : ZMod p) ^ a) * (b ! : ZMod p)) := by ring
      _ = ((-1 : ZMod p) ^ a) * ((a ! : ZMod p) * (b ! : ZMod p)) := by rw [ha]
      _ = ((-1 : ZMod p) ^ a) * ((-1 : ZMod p) ^ (a + 1)) := by rw [hpair]
      _ = (((-1 : ZMod p) ^ a) * ((-1 : ZMod p) ^ a)) * (-1) := by rw [pow_succ]; ring
      _ = -1 := by rw [neg_one_pow_mul_self, one_mul]

/- ### The target set, rewritten in dual indices -/

/-- **Main reformulation.** For a prime `p`, the extremal condition `f p = p - 1` is equivalent to
a bounded check on the dually-indexed factorials `a !` for `1 ≤ a ≤ p - 1`, obtained from
`f_eq_sub_one_iff` by the relabelling `a ↔ p - 1 - a`. The relabelling keeps the index range the
same size -- the check still reaches `(p - 1)!`, whereas `f_eq_sub_one_iff` reaches only
`(p - 2)!` -- so this is a change of form, not a reduction in factorial size. The genuine
small-index payoff is the one-witness certificate `f_lt_sub_one_of_small_witness` below. -/
theorem f_eq_sub_one_iff_forall_small (hp : p.Prime) :
    f p = p - 1 ↔ ∀ a, 1 ≤ a → a ≤ p - 1 → (a ! : ZMod p) ≠ (-1) ^ a := by
  have hp2 := hp.two_le
  rw [f_eq_sub_one_iff hp]
  constructor
  · intro h a ha1 ha2 heq
    exact h (p - 1 - a) (by omega)
      ((factorial_eq_neg_one_iff hp (a := a) (b := p - 1 - a) (by omega)).2 heq)
  · intro h n hn heq
    exact h (p - 1 - n) (by omega) (by omega)
      ((factorial_eq_neg_one_iff hp (a := p - 1 - n) (b := n) (by omega)).1 heq)

/-- The target set of `Erdos1072.erdos_1072.parts.i`, rewritten so that the awkward `sInf` is
replaced by a bounded check on the dually-indexed factorials `a !` for `1 ≤ a ≤ p - 1`
(the relabelling `a ↔ p - 1 - a`). The range is the full one, so what this buys is the
disappearance of the `sInf`, not smaller factorials; for an executable membership test use
`mem_iff_ball`, and for cheap exclusion use `notMem_of_small_witness`. -/
theorem setOf_prime_and_f_eq_sub_one :
    {p | p.Prime ∧ f p = p - 1}
      = {p | p.Prime ∧ ∀ a ∈ Finset.Icc 1 (p - 1), (a ! : ZMod p) ≠ (-1) ^ a} := by
  ext p
  simp only [Set.mem_setOf_eq, Finset.mem_Icc, and_congr_right_iff]
  intro hp
  rw [f_eq_sub_one_iff_forall_small hp]
  exact ⟨fun h a ha => h a ha.1 ha.2, fun h a h1 h2 => h a ⟨h1, h2⟩⟩

/-- **Cheap exclusion certificate.** A single small `a` with `a ! ≡ (-1) ^ a (mod p)` proves
`f p < p - 1`, i.e. that `p` is *not* a member of the target set. -/
theorem f_lt_sub_one_of_small_witness (hp : p.Prime) (ha1 : 1 ≤ a) (ha2 : a ≤ p - 1)
    (h : (a ! : ZMod p) = (-1) ^ a) : f p < p - 1 :=
  lt_of_le_of_ne (f_le_sub_one hp)
    fun heq => (f_eq_sub_one_iff_forall_small hp).1 heq a ha1 ha2 h

/-- The exclusion certificate, phrased for the target set. -/
theorem notMem_of_small_witness (hp : p.Prime) (ha1 : 1 ≤ a) (ha2 : a ≤ p - 1)
    (h : (a ! : ZMod p) = (-1) ^ a) : p ∉ {q | q.Prime ∧ f q = q - 1} := by
  rintro ⟨-, heq⟩
  exact absurd heq (Nat.ne_of_lt (f_lt_sub_one_of_small_witness hp ha1 ha2 h))

/-- Membership in the target set is a decidable bounded check on natural numbers. -/
theorem mem_iff_ball (hp : p.Prime) :
    p ∈ {q | q.Prime ∧ f q = q - 1} ↔ ∀ n < p - 1, (n ! + 1) % p ≠ 0 := by
  simp only [Set.mem_setOf_eq, hp, true_and, f_eq_sub_one_iff hp,
    ne_eq, factorial_add_one_mod_eq_zero_iff]

/- ### Degenerate case: the prime `2` is not a member

`Erdos1072.f` is `0`-indexed and `0! = 1`, so `0! + 1 = 2 ≡ 0 [MOD 2]` and `f 2 = 0`, whereas
`2 - 1 = 1`. Any attempt to show the target set contains all primes of some shape must exclude
`2`. -/

/-- `f 2 = 0`, not `1`. The proof is not the point: `simp [Erdos1072.f]` closes this goal in
one call. The lemma is kept because the fact itself is a trap, and `two_notMem` needs it. -/
theorem f_two : f 2 = 0 :=
  Nat.le_zero.1 (Nat.sInf_le (show (0 : ℕ) ∈ {n | n ! + 1 ≡ 0 [MOD 2]} by decide))

/-- The prime `2` is not in the target set. -/
theorem two_notMem : (2 : ℕ) ∉ {q | q.Prime ∧ f q = q - 1} := by
  rintro ⟨-, heq⟩
  rw [f_two] at heq
  exact absurd heq (by decide)

/- ### Worked use sites -/

/-- **Use site for `erdos_1072.parts.i`.** The statement of the target is
`answer(..) ↔ Set.Infinite {p | p.Prime ∧ f p = p - 1}`; with `Answer` standing for whatever
answer is filled in, `setOf_prime_and_f_eq_sub_one` rewrites it into the dual-index form. -/
example (Answer : Prop)
    (h : Answer ↔
      Set.Infinite {p | p.Prime ∧ ∀ a ∈ Finset.Icc 1 (p - 1), (a ! : ZMod p) ≠ (-1) ^ a}) :
    Answer ↔ Set.Infinite {p | p.Prime ∧ f p = p - 1} := by
  rw [setOf_prime_and_f_eq_sub_one]
  exact h

/-- The target set is nonempty, and in particular not vacuous: `3, 5, 13, 17, 31` all lie in it.
This is checked by `decide` through `mem_iff_ball`. -/
example : ({3, 5, 13, 17, 31} : Set ℕ) ⊆ {q | q.Prime ∧ f q = q - 1} := by
  rintro q (rfl | rfl | rfl | rfl | rfl)
  · exact (mem_iff_ball (by norm_num)).2 (by decide)
  · exact (mem_iff_ball (by norm_num)).2 (by decide)
  · exact (mem_iff_ball (by norm_num)).2 (by decide)
  · exact (mem_iff_ball (by norm_num)).2 (by decide)
  · exact (mem_iff_ball (by norm_num)).2 (by decide)

/-- Exclusion by a small witness: `3! = 6 ≡ -1 = (-1) ^ 3 (mod 7)`, so the index `7 - 1 - 3 = 3`
already solves `n ! ≡ -1 (mod 7)` and `f 7 < 6`. -/
example : (7 : ℕ) ∉ {q | q.Prime ∧ f q = q - 1} :=
  notMem_of_small_witness (a := 3) (by norm_num) (by norm_num) (by norm_num) (by decide)

/-- The same certificate at `p = 23`: `4! = 24 ≡ 1 = (-1) ^ 4 (mod 23)` shows that `23 - 1 - 4 = 18`
solves `n ! ≡ -1 (mod 23)`, so `f 23 < 22` -- and `18 !` is never computed. -/
example : (23 : ℕ) ∉ {q | q.Prime ∧ f q = q - 1} :=
  notMem_of_small_witness (a := 4) (by norm_num) (by norm_num) (by norm_num) (by decide)

end Contribution.Erdos1072Pillai
