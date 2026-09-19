/-
Copyright (c) 2026 the contribution authors.
SPDX-License-Identifier: Apache-2.0
https://www.apache.org/licenses/LICENSE-2.0
-/

import Mathlib
import FormalConjectures.ErdosProblems.«835»

/-!
# Local incidence counts and the prime-parameter reduction for Erdős 835

A rainbow coloring of the `k`-subsets of a `2*k`-element set forces every
`r` in `1, ..., k` to divide `Nat.choose (k+r) (r-1)`. These arithmetic
conditions, for `k > 0`, hold exactly when `k+1` is prime. Thus all composite-successor
parameters are excluded from the official `Erdos835.Property`.

The central identity counts each color class inside an arbitrary ground
subset. The final equivalence restricts the original existence question to
prime parameters; it does not establish existence or nonexistence there.

The arithmetic obstruction is due to Jie Ma and Quanyu Tang, Proposition 2.1,
Theorem 2.2 and Lemma 2.3 of *A note on Erdős Problem #835*. The direct local
incidence proof generalizes the previously contributed `k=9` parity count.
Full provenance and the parent contribution identifier are in `sources.md`.
-/

open Finset

namespace Contribution.Erdos835Divisibility

variable {V : Type*} [DecidableEq V] {k : ℕ}

omit [DecidableEq V] in
/-- Each color occurs exactly once on the facets of a rainbow simplex. -/
theorem color_fiber_card (c : Finset V → Fin (k + 1))
    (A : Finset V) (hA : A.card = k + 1)
    (h : (A.powersetCard k).image c = univ) (a : Fin (k + 1)) :
    ((A.powersetCard k).filter (fun S => c S = a)).card = 1 := by
  classical
  have hinj : Set.InjOn c (A.powersetCard k) := by
    apply injOn_of_card_image_eq
    rw [h, card_univ, Fintype.card_fin, card_powersetCard, hA,
      Nat.choose_succ_self_right]
  have ha : a ∈ (A.powersetCard k).image c := by rw [h]; exact mem_univ _
  obtain ⟨S, hS, hcS⟩ := mem_image.mp ha
  apply card_eq_one.mpr
  refine ⟨S, ?_⟩
  ext T
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hT, hcT⟩
    exact hinj hT hS (hcT.trans hcS.symm)
  · rintro rfl
    exact ⟨hS, hcS⟩

/-- Exact local incidence identity for a coloring rainbow on every `(k+1)`-subset. -/
theorem local_color_count (E : Finset V) (c : Finset V → Fin (k + 1))
    (h : ∀ A ∈ E.powersetCard (k + 1), (A.powersetCard k).image c = univ)
    (a : Fin (k + 1)) :
    (E.card - k) * ((E.powersetCard k).filter (fun S => c S = a)).card =
      E.card.choose (k + 1) := by
  let T := (E.powersetCard k).filter (fun S => c S = a)
  have hleft : ∀ A ∈ E.powersetCard (k + 1),
      (T.bipartiteAbove (fun A S : Finset V => S ⊆ A) A).card = 1 := by
    intro A hA
    have hAE := (mem_powersetCard.mp hA).1
    have heq : T.bipartiteAbove (fun A S : Finset V => S ⊆ A) A =
        (A.powersetCard k).filter (fun S => c S = a) := by
      ext S
      simp only [T, bipartiteAbove, mem_filter, mem_powersetCard]
      constructor
      · rintro ⟨⟨⟨_, hSk⟩, hc⟩, hSA⟩
        exact ⟨⟨hSA, hSk⟩, hc⟩
      · rintro ⟨⟨hSA, hSk⟩, hc⟩
        exact ⟨⟨⟨hSA.trans hAE, hSk⟩, hc⟩, hSA⟩
    rw [heq]
    exact color_fiber_card c A (mem_powersetCard.mp hA).2 (h A hA) a
  have hright : ∀ S ∈ T,
      ((E.powersetCard (k + 1)).bipartiteBelow
        (fun A S : Finset V => S ⊆ A) S).card = E.card - k := by
    intro S hS
    obtain ⟨⟨hSE, hSk⟩, _⟩ := (mem_filter.mp hS).imp_left mem_powersetCard.mp
    change ((E.powersetCard (k + 1)).filter (S ⊆ ·)).card = _
    rw [card_filter_powersetCard_subset S E (k + 1) hSE (by omega), hSk]
    simp
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun A S : Finset V => S ⊆ A) (s := E.powersetCard (k + 1)) (t := T)
  rw [sum_congr rfl hleft, sum_congr rfl hright] at hdc
  simpa [T, card_powersetCard, Nat.mul_comm] using hdc.symm

/-- A rainbow coloring forces every local binomial divisibility condition. -/
theorem rainbow_divisibility (X : Finset V) (hX : X.card = 2 * k)
    (c : Finset V → Fin (k + 1))
    (h : ∀ A ∈ X.powersetCard (k + 1), (A.powersetCard k).image c = univ)
    {r : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) : r ∣ (k + r).choose (r - 1) := by
  obtain ⟨E, hEX, hE⟩ := exists_subset_card_eq (s := X) (n := k + r) (by omega)
  have hlocal := local_color_count E c (fun A hA => h A
    (mem_powersetCard.mpr ⟨(mem_powersetCard.mp hA).1.trans hEX,
      (mem_powersetCard.mp hA).2⟩)) 0
  rw [hE, Nat.add_sub_cancel_left] at hlocal
  have hsymm : (k + r).choose (r - 1) = (k + r).choose (k + 1) :=
    Nat.choose_symm_of_eq_add (by omega)
  exact ⟨_, hsymm.trans hlocal.symm⟩

/-- Lucas' congruence makes the local divisibility conditions impossible at
any proper prime divisor of `k+1`. -/
theorem prime_of_divisibility (hk : 0 < k)
    (h : ∀ r, 1 ≤ r → r ≤ k → r ∣ (k + r).choose (r - 1)) :
    (k + 1).Prime := by
  by_contra hn
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (n := k + 1) (by omega)
  have hp_le : p ≤ k + 1 := Nat.le_of_dvd (by omega) hpk
  have hp_ne : p ≠ k + 1 := fun he => hn (he ▸ hp)
  have hp_k : p ≤ k := by omega
  have hsmall := Nat.mod_lt k hp.pos
  have hz : (k % p + 1) % p = 0 := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt hp.one_lt] using Nat.mod_eq_zero_of_dvd hpk
  have hp_small : p ≤ k % p + 1 :=
    Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hz)
  have hkm : k % p = p - 1 := by omega
  have htop : (k + p) % p = p - 1 := by simpa using hkm
  let : Fact p.Prime := ⟨hp⟩
  have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := k + p) (k := p - 1) (p := p)
  have hbottom : p - 1 < p := by omega
  simp only [htop, Nat.mod_eq_of_lt hbottom, Nat.div_eq_of_lt hbottom,
    Nat.choose_self, Nat.choose_zero_right, mul_one] at hLucas
  have hzero := Nat.mod_eq_zero_of_dvd (h p hp.one_le hp_k)
  have hmod : (k + p).choose (p - 1) % p = 1 % p := hLucas
  rw [hzero, Nat.mod_eq_of_lt hp.one_lt] at hmod
  omega

/-- Prime successors satisfy all scalar incidence divisibilities, so these
conditions alone cannot settle the remaining prime parameters. -/
theorem divisibility_of_prime (hp : (k + 1).Prime) {r : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k) : r ∣ (k + r).choose (r - 1) := by
  have hd : k + 1 ∣ (k + r).choose r := by
    simpa [Nat.add_comm] using hp.dvd_choose_add
      (a := r) (b := k) (by omega) (by omega) (by omega)
  obtain ⟨m, hm⟩ := hd
  have he := Nat.choose_succ_right_eq (k + r) (r - 1)
  have hr1 : r - 1 + 1 = r := by omega
  have hsub : k + r - (r - 1) = k + 1 := by omega
  rw [hr1, hsub] at he
  refine ⟨m, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos k)
  calc
    (k + r).choose (r - 1) * (k + 1) = (k + r).choose r * r := he.symm
    _ = (r * m) * (k + 1) := by rw [hm]; ring

/-- Exact arithmetic boundary of the local incidence obstruction. -/
theorem divisibility_iff_prime (hk : 0 < k) :
    (∀ r, 1 ≤ r → r ≤ k → r ∣ (k + r).choose (r - 1)) ↔ (k + 1).Prime :=
  ⟨prime_of_divisibility hk, fun hp _ hr hrk => divisibility_of_prime hp hr hrk⟩

/-- The exact official rainbow property supplies the local divisibility constraints. -/
theorem property_divisibility (h : Erdos835.Property k) {r : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k) : r ∣ (k + r).choose (r - 1) := by
  classical
  obtain ⟨c, hc⟩ := h
  let c' : Finset (Fin (2 * k)) → Fin (k + 1) :=
    fun S => if hS : S.card = k then c ⟨S, hS⟩ else 0
  apply rainbow_divisibility (univ : Finset (Fin (2 * k))) (by simp) c' ?_ hr hrk
  intro A hA
  have hAk := (mem_powersetCard.mp hA).2
  apply eq_univ_iff_forall.mpr
  intro a
  have ha : a ∈ image c {s : {s : Finset (Fin (2 * k)) // s.card = k} | s.val ⊂ A} := by
    rw [hc A hAk]
    exact mem_univ _
  obtain ⟨S, hS, hcS⟩ := mem_image.mp ha
  have hSA : S.val ⊂ A := by simpa using hS
  apply mem_image.mpr
  refine ⟨S.val, mem_powersetCard.mpr ⟨hSA.subset, S.prop⟩, ?_⟩
  simpa [c', S.prop] using hcS

/-- Any admissible parameter for Erdős 835 has prime successor. -/
theorem prime_succ_of_property (hk : 0 < k) (h : Erdos835.Property k) :
    (k + 1).Prime :=
  prime_of_divisibility hk (fun _ hr hrk => property_divisibility h hr hrk)

/-- The rainbow coloring in the official statement is impossible at composite successors. -/
theorem not_property_of_not_prime (hk : 0 < k) (hp : ¬ (k + 1).Prime) :
    ¬ Erdos835.Property k := fun h => hp (prime_succ_of_property hk h)

/-- Exact restriction of the existential question to prime-successor parameters.
This does not assert that a coloring exists at any of the remaining primes. -/
theorem exists_property_iff_prime_parameter :
    (∃ k > 2, Erdos835.Property k) ↔
      ∃ p, p.Prime ∧ 3 < p ∧ Erdos835.Property (p - 1) := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k + 1, prime_succ_of_property (by omega) h, by omega, by simpa using h⟩
  · rintro ⟨p, _, hp, h⟩
    exact ⟨p - 1, by omega, h⟩

end Contribution.Erdos835Divisibility
