import Mathlib
import FormalConjectures.ErdosProblems.«364»

/-!
# Erdős 364: five exact source-bound candidate exclusions

For each of five fixed candidate starts, the middle term has a prime divisor whose square does
not divide it. Therefore the middle term is not `Nat.Powerful`, so that fixed start cannot begin
a consecutive powerful triple.

This file makes no claim that Erdős 364 is solved and no claim about a contiguous search frontier.
-/

namespace Contribution.Erdos364FiveCandidates

/-- Source index 19: the fixed candidate cannot begin a consecutive powerful triple. -/
theorem candidate19_not_powerful_triple :
    ¬ (Nat.Powerful 10598392015632694490959995932061887475123 ∧
       Nat.Powerful (10598392015632694490959995932061887475123 + 1) ∧
       Nat.Powerful (10598392015632694490959995932061887475123 + 2)) := by
  rintro ⟨_, hmid, _⟩
  have hp : Nat.Prime 19 := by norm_num
  have hdiv : 19 ∣ 10598392015632694490959995932061887475123 + 1 := by
    refine ⟨557810106085931288997894522740099340796, ?_⟩
    norm_num
  have hn0 : 10598392015632694490959995932061887475123 + 1 ≠ 0 := by norm_num
  have hsq : ¬ 19 ^ 2 ∣ 10598392015632694490959995932061887475123 + 1 := by
    intro hp2
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hp2
    norm_num at hzero
  exact hsq (hmid 19 (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn0⟩))

/-- Source index 20: the fixed candidate cannot begin a consecutive powerful triple. -/
theorem candidate20_not_powerful_triple :
    ¬ (Nat.Powerful 607354480741807640456097195891125640480487 ∧
       Nat.Powerful (607354480741807640456097195891125640480487 + 1) ∧
       Nat.Powerful (607354480741807640456097195891125640480487 + 2)) := by
  rintro ⟨_, hmid, _⟩
  have hp : Nat.Prime 29 := by norm_num
  have hdiv : 29 ∣ 607354480741807640456097195891125640480487 + 1 := by
    refine ⟨20943257956614056567451627444521573809672, ?_⟩
    norm_num
  have hn0 : 607354480741807640456097195891125640480487 + 1 ≠ 0 := by norm_num
  have hsq : ¬ 29 ^ 2 ∣ 607354480741807640456097195891125640480487 + 1 := by
    intro hp2
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hp2
    norm_num at hzero
  exact hsq (hmid 29 (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn0⟩))

/-- Source index 26: the fixed candidate cannot begin a consecutive powerful triple. -/
theorem candidate26_not_powerful_triple :
    ¬ (Nat.Powerful 246833868143510841778190301996679579985410604470827 ∧
       Nat.Powerful (246833868143510841778190301996679579985410604470827 + 1) ∧
       Nat.Powerful (246833868143510841778190301996679579985410604470827 + 2)) := by
  rintro ⟨_, hmid, _⟩
  have hp : Nat.Prime 7 := by norm_num
  have hdiv : 7 ∣ 246833868143510841778190301996679579985410604470827 + 1 := by
    refine ⟨35261981163358691682598614570954225712201514924404, ?_⟩
    norm_num
  have hn0 : 246833868143510841778190301996679579985410604470827 + 1 ≠ 0 := by norm_num
  have hsq : ¬ 7 ^ 2 ∣ 246833868143510841778190301996679579985410604470827 + 1 := by
    intro hp2
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hp2
    norm_num at hzero
  exact hsq (hmid 7 (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn0⟩))

/-- Source index 29: the fixed candidate cannot begin a consecutive powerful triple. -/
theorem candidate29_not_powerful_triple :
    ¬ (Nat.Powerful 41422006647842553948901599356619504905181932650376191205767 ∧
       Nat.Powerful (41422006647842553948901599356619504905181932650376191205767 + 1) ∧
       Nat.Powerful (41422006647842553948901599356619504905181932650376191205767 + 2)) := by
  rintro ⟨_, hmid, _⟩
  have hp : Nat.Prime 29 := by norm_num
  have hdiv : 29 ∣ 41422006647842553948901599356619504905181932650376191205767 + 1 := by
    refine ⟨1428345056822157032720744805400672582937308022426765213992, ?_⟩
    norm_num
  have hn0 : 41422006647842553948901599356619504905181932650376191205767 + 1 ≠ 0 := by norm_num
  have hsq : ¬ 29 ^ 2 ∣ 41422006647842553948901599356619504905181932650376191205767 + 1 := by
    intro hp2
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hp2
    norm_num at hzero
  exact hsq (hmid 29 (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn0⟩))

/-- Source index 33: the fixed candidate cannot begin a consecutive powerful triple. -/
theorem candidate33_not_powerful_triple :
    ¬ (Nat.Powerful 8117456360479648640268425072000645231601604504575217328838840903123 ∧
       Nat.Powerful (8117456360479648640268425072000645231601604504575217328838840903123 + 1) ∧
       Nat.Powerful (8117456360479648640268425072000645231601604504575217328838840903123 + 2)) := by
  rintro ⟨_, hmid, _⟩
  have hp : Nat.Prime 19 := by norm_num
  have hdiv : 19 ∣ 8117456360479648640268425072000645231601604504575217328838840903123 + 1 := by
    refine ⟨427234545288402560014127635368455012189558131819748280465202152796, ?_⟩
    norm_num
  have hn0 : 8117456360479648640268425072000645231601604504575217328838840903123 + 1 ≠ 0 := by norm_num
  have hsq : ¬ 19 ^ 2 ∣ 8117456360479648640268425072000645231601604504575217328838840903123 + 1 := by
    intro hp2
    have hzero := Nat.dvd_iff_mod_eq_zero.mp hp2
    norm_num at hzero
  exact hsq (hmid 19 (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn0⟩))

end Contribution.Erdos364FiveCandidates
