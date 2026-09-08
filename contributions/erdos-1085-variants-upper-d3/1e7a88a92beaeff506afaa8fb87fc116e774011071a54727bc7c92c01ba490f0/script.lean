import Mathlib
import FormalConjectures.ErdosProblems.«1085»

/-!
# Erdős problem 1085: an API for `f d n`, the Lenz bound proved, and a `K₃,₃`-free benchmark

Target: `Erdos1085.erdos_1085.variants.upper_d3`, which asks whether
`(fun n ↦ (Erdos1085.f 3 n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n))`,
where `Erdos1085.f d n = ⨆ (s : Finset (ℝ^d)) (_ : s.card = n), unitDistNum s` is the maximal
number of unit distances spanned by `n` points of `ℝ^d`.

## The obstacle

`Erdos1085.f` is an iterated conditional supremum of a `ℕ`-valued function over *all* finite
subsets of `ℝ^d`. Neither the pool file nor `FormalConjecturesForMathlib.Geometry.Metric` (which
contains only the definition of `unitDistNum`) records that this supremum is over a bounded set,
that it is attained, or how it compares with a single configuration, so there is no way to pass
between "every `n`-point configuration spans few unit distances" and an upper bound on `f 3 n`,
in either direction, nor between "here is a good configuration" and a lower bound. Independently,
every known upper bound for `f_3` builds on one geometric fact: three distinct points of a space
of dimension `< 4` have at most two common unit-distance neighbours, i.e. the unit-distance graph
of a finite subset of `ℝ^3` is `K₃,₃`-free. Mathlib's `SimpleGraph.UnitDistEmbedding` defines what
a unit-distance embedding of a graph is and transfers one along graph maps, but proves nothing
about how many unit distances a finite set of points can span, and states no `K₃,₃`-freeness.

This file supplies the missing transfer interface and the geometric input, and then uses them for
two things:

* an **outright proof of the pool file's companion `erdos_1085.variants.lower_d4_lenz`**, which
  is left unproved there; `lower_d4_lenz` below carries literally that statement. The proof
  is a complete formal Lenz construction: `n` points dealt round-robin onto `p = ⌊d/2⌋` pairwise
  orthogonal circles of radius `√2 / 2` in `ℝ^d`, every cross pair at distance exactly `1`. The
  round-robin dealing is what makes the error term the constant `p` rather than `Θ(n)`.
* the Kővári–Sós–Turán benchmark `f d n ≤ n + n ^ (5/3)` for every `1 ≤ d ≤ 3` (`f_le_rpow`),
  whose dimension hypothesis is then shown to be necessary (`not_f_le_rpow_of_dim_four`).

The target itself is **not** resolved, and the gap is measured here rather than asserted:
`isLittleO_target_rpow` and `not_isBigO_rpow_five_thirds` prove that `n^{4/3} log log n` is
`o(n^{5/3})` and that no change of constants closes the gap. Closing it needs incidence geometry,
which in the literature has reached `O(n^{3/2})` (Kaplan–Matoušek–Safernová–Sharir) and slightly
below (Zahl), still short of the conjectured bound.

## Direct relevance

A later solver can use declaration `Contribution.Erdos1085UnitDistance.isBigO_f_iff` to discharge
or simplify obligation `(fun n ↦ (Erdos1085.f 3 n : ℝ)) =O[atTop]
(fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * Real.log (Real.log n))` in target
`Erdos1085.erdos_1085.variants.upper_d3`: it is an `Iff`, so it rewrites that obligation — and
equally its negation, which is what is needed if the answer to the problem turns out to be
`False` — into a statement about arbitrary point configurations of `ℝ^3`, the form in which
geometry applies. The instantiation at the target, with the norm removed, is
`upper_d3_isBigO_iff`. Nothing here is a one-way reduction whose hypothesis could fail for a
legal instance of the target's binders: `isBigO_f_iff` and `isBigO_iff_f` are equivalences,
resting on `exists_unitDistNum_eq_f`, which says that the defining supremum is attained.

The same API serves the other companions of the pool file: `unitDistNum_le_f` turns an explicit
configuration into a lower bound on `f d n` (it is what proves `.lower_d4_lenz` here, and it is
needed for the lower half of `.upper_lower_d5_odd`), `f_le_real` and `f_le_iff` turn a uniform
configuration bound into an upper bound on `f d n` (`.upper_d4_erdos`, the upper half of
`.upper_lower_d5_odd`), and `isBigO_iff_f`, `isBigO_f_iff` do the same for the asymptotic
companions `.lower_d2`, `.lower_d3` and `.upper_d2`.

## What is proved

* Exact combinatorics of `unitDistNum`: the ordered-pair count `card_ordered_unit_pairs`, the
  handshake identity `two_mul_unitDistNum`, `unitDistNum_le_choose`, `unitDistNum_mono`, and the
  invariance `unitDistNum_map` under distance-preserving maps.
* The `Erdos1085.f` API: `bddAbove_unitDistNum`, `unitDistNum_le_f`, `f_le_iff`,
  `exists_unitDistNum_eq_f` (the supremum is attained), `f_le_real`, `f_mono` (monotone in `n`),
  `f_le_f_of_le` (monotone in the dimension, via the isometric embedding `embedSucc`), and the
  two equivalences `isBigO_f_iff`, `isBigO_iff_f`.
* The Lenz construction: `lenzX`, `lenzY` — a rational parametrisation of the circle of radius
  `√2 / 2`, with `lenzX_sq_add_lenzY_sq` and `lenz_param_injective` — then `lenzPt`,
  `dist_lenzPt` (points on different coordinate circles are at distance exactly one), `lenzIdx`,
  `lenzIdx_injective`, `lenzSet`, `card_lenzSet`; the balanced round-robin count
  `sum_card_residue_class`, `card_residue_class_le`, `le_card_residue_class` and the
  second-moment bound `mul_sum_sq_card_residue_class_le`; and finally
  `sq_le_two_mul_unitDistNum_lenzSet`, `lenz_lower_bound` and `lower_d4_lenz`.
* `K₃,₃`-freeness in dimension `< 4`: `inner_sub_sub_eq_zero`,
  `not_three_common_unit_neighbours` and `card_le_two_of_forall_dist_eq_one`, from the
  perpendicular-bisector identity and the orthogonality of the two spanned planes; and
  `exists_card_three_forall_dist_eq_one`, a Lenz configuration in `ℝ^4` witnessing that their
  dimension hypothesis cannot be dropped.
* The Kővári–Sós–Turán double count `sum_choose_three_le`, the constant-free `ℕ` inequality
  `two_mul_unitDistNum_sub_pow_three_le`, and the real forms `unitDistNum_le_rpow`, `f_le_rpow`,
  `isBigO_f_three_rpow`; `not_f_le_rpow_of_dim_four` shows that the hypothesis `d ≤ 3` of
  `f_le_rpow` is necessary, by exhibiting `n = 512` at which the bound already fails in `ℝ^4`.
* `isLittleO_target_rpow`, `not_isBigO_rpow_five_thirds`: how far the benchmark is from the
  target.
* Use sites: `upper_d3_isBigO_iff` and `isBigO_f_two_of_upper_d3`.

*Reference:* [erdosproblems.com/1085](https://www.erdosproblems.com/1085)
-/

open Finset Filter Real
open scoped EuclideanGeometry Topology RealInnerProductSpace

namespace Contribution.Erdos1085UnitDistance

/- ## Exact combinatorics of `unitDistNum` -/

section Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- The two representatives chosen by `Sym2.out` for `s(a, b)` are at distance `dist a b`. -/
theorem dist_out_mk (a b : X) : dist (s(a, b) : Sym2 X).out.1 (s(a, b)).out.2 = dist a b := by
  have h : s((s(a, b) : Sym2 X).out.1, (s(a, b)).out.2) = s(a, b) := Quot.out_eq _
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, dist_comm]

/-- Membership in the set of unit pairs counted by `unitDistNum`. -/
theorem mk_mem_unitPairs_iff {s : Finset X} {a b : X} :
    s(a, b) ∈ {p ∈ s.sym2 | dist p.out.1 p.out.2 = 1} ↔ a ∈ s ∧ b ∈ s ∧ dist a b = 1 := by
  rw [Finset.mem_filter, Finset.mk_mem_sym2_iff, dist_out_mk, and_assoc]

/-- Every unordered unit pair of `s` is hit by exactly two ordered ones. -/
theorem card_ordered_unit_pairs (s : Finset X) :
    #{q ∈ s ×ˢ s | dist q.1 q.2 = 1} = 2 * unitDistNum s := by
  classical
  rw [unitDistNum, Finset.card_eq_sum_card_fiberwise
    (f := fun q : X × X => s(q.1, q.2)) (t := {p ∈ s.sym2 | dist p.out.1 p.out.2 = 1})
    (fun q hq => by
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
      exact Finset.mem_coe.mpr (mk_mem_unitPairs_iff.mpr ⟨hq.1.1, hq.1.2, hq.2⟩))]
  rw [Finset.card_eq_sum_ones {p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b, p = s(a, b) := ⟨p.out.1, p.out.2, (Quot.out_eq p).symm⟩
  obtain ⟨ha, hb, hab⟩ := mk_mem_unitPairs_iff.mp hp
  have hne : a ≠ b := by rintro rfl; simp at hab
  have hfib : ({q ∈ s ×ˢ s | dist q.1 q.2 = 1}.filter fun q : X × X => s(q.1, q.2) = s(a, b))
      = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Sym2.eq_iff]
    constructor
    · rintro ⟨-, h | h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨⟨ha, hb⟩, hab⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨⟨hb, ha⟩, by rwa [dist_comm]⟩, Or.inr ⟨rfl, rfl⟩⟩
  rw [hfib, Finset.card_pair (fun h => hne (Prod.mk.inj h).1), mul_one]

/-- **Handshake lemma for the unit-distance graph.** The number of unit distances spanned by `s`
is half the sum of the unit-distance degrees of its points. -/
theorem two_mul_unitDistNum (s : Finset X) :
    2 * unitDistNum s = ∑ x ∈ s, #{y ∈ s | dist x y = 1} := by
  classical
  rw [← card_ordered_unit_pairs, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm

/-- The crude bound making the supremum that defines `Erdos1085.f` a supremum of a bounded set. -/
theorem unitDistNum_le_choose (s : Finset X) : unitDistNum s ≤ (#s).choose 2 := by
  classical
  have h : 2 * unitDistNum s ≤ #s * (#s - 1) := by
    rw [two_mul_unitDistNum]
    calc ∑ x ∈ s, #{y ∈ s | dist x y = 1} ≤ ∑ _x ∈ s, (#s - 1) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hsub : {y ∈ s | dist x y = 1} ⊆ s.erase x := by
            intro y hy
            rw [Finset.mem_filter] at hy
            refine Finset.mem_erase.mpr ⟨fun h => ?_, hy.1⟩
            rw [h, dist_self] at hy
            exact zero_ne_one hy.2
          calc #{y ∈ s | dist x y = 1} ≤ #(s.erase x) := Finset.card_le_card hsub
            _ = #s - 1 := Finset.card_erase_of_mem hx
      _ = #s * (#s - 1) := by rw [Finset.sum_const, smul_eq_mul]
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le two_pos]
  omega

/-- Adding points cannot destroy unit distances. -/
theorem unitDistNum_mono {s t : Finset X} (h : s ⊆ t) : unitDistNum s ≤ unitDistNum t := by
  classical
  unfold unitDistNum
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sym2_mono h))

/-- **Unit-distance counts are invariant under distance-preserving maps**, in particular under
isometries of `ℝ^d` and under isometric embeddings into a larger space. -/
theorem unitDistNum_map (e : X ↪ Y) (he : ∀ a b, dist (e a) (e b) = dist a b) (s : Finset X) :
    unitDistNum (s.map e) = unitDistNum s := by
  have hcard : #{q ∈ (s.map e) ×ˢ (s.map e) | dist q.1 q.2 = 1}
      = #{q ∈ s ×ˢ s | dist q.1 q.2 = 1} := by
    refine (Finset.card_bij (fun q _ => (e q.1, e q.2)) ?_ ?_ ?_).symm
    · rintro ⟨a, b⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨Finset.mem_map_of_mem e hq.1.1, Finset.mem_map_of_mem e hq.1.2⟩,
        by rw [he]; exact hq.2⟩
    · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (e.injective h.1) (e.injective h.2)
    · rintro ⟨u, v⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hq.1.1
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hq.1.2
      refine ⟨(a, b), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, hb⟩, by rw [he] at hq; exact hq.2⟩
  have h2 : 2 * unitDistNum (s.map e) = 2 * unitDistNum s := by
    rw [← card_ordered_unit_pairs, ← card_ordered_unit_pairs, hcard]
  omega

end Metric

/- ## An API for the extremal function `Erdos1085.f` -/

section Sup

variable {d n m : ℕ}

/-- The family whose supremum defines `Erdos1085.f d n` is bounded above by `n.choose 2`. -/
theorem bddAbove_unitDistNum (d n : ℕ) :
    BddAbove (Set.range fun s : Finset (ℝ^ d) => ⨆ (_ : #s = n), unitDistNum s) := by
  refine ⟨n.choose 2, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact ciSup_le' fun hs => hs ▸ unitDistNum_le_choose s

/-- Every `n`-point configuration is dominated by `Erdos1085.f d n`. -/
theorem unitDistNum_le_f {s : Finset (ℝ^ d)} (hs : #s = n) :
    unitDistNum s ≤ Erdos1085.f d n := by
  refine le_ciSup_of_le (bddAbove_unitDistNum d n) s ?_
  exact le_of_eq (ciSup_pos (f := fun _ : #s = n => unitDistNum s) hs).symm

/-- `Erdos1085.f d n ≤ m` is exactly a bound valid for all `n`-point configurations. -/
theorem f_le_iff : Erdos1085.f d n ≤ m ↔ ∀ s : Finset (ℝ^ d), #s = n → unitDistNum s ≤ m := by
  refine ⟨fun h s hs => (unitDistNum_le_f hs).trans h, fun h => ?_⟩
  exact ciSup_le' fun s => ciSup_le' fun hs => h s hs

/-- The standard isometric embedding `ℝ^d → ℝ^(d+1)`, padding a vector with a zero. -/
noncomputable def embedSucc (d : ℕ) (x : ℝ^ d) : ℝ^ (d + 1) :=
  WithLp.toLp 2 fun i : Fin (d + 1) => if h : (i : ℕ) < d then x ⟨i, h⟩ else 0

theorem dist_embedSucc (d : ℕ) (x y : ℝ^ d) :
    dist (embedSucc d x) (embedSucc d y) = dist x y := by
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_castSucc]
  simp [embedSucc]

/-- `embedSucc` packaged as an embedding, so that it acts on `Finset`s. -/
noncomputable def embedSuccEmb (d : ℕ) : (ℝ^ d) ↪ (ℝ^ (d + 1)) :=
  ⟨embedSucc d, fun a b hab => dist_eq_zero.mp (by rw [← dist_embedSucc d a b, hab, dist_self])⟩

/-- **`Erdos1085.f` is monotone in the dimension**: more room cannot decrease the number of unit
distances. -/
theorem f_le_f_of_le {d d' : ℕ} (h : d ≤ d') (n : ℕ) : Erdos1085.f d n ≤ Erdos1085.f d' n := by
  induction d', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    refine le_trans ih (f_le_iff.mpr fun s hs => ?_)
    have hcard : #(s.map (embedSuccEmb k)) = n := by rw [Finset.card_map, hs]
    calc unitDistNum s = unitDistNum (s.map (embedSuccEmb k)) :=
          (unitDistNum_map _ (dist_embedSucc k) s).symm
      _ ≤ Erdos1085.f (k + 1) n := unitDistNum_le_f hcard

/-- **The supremum defining `Erdos1085.f d n` is attained** (for `d ≥ 1`): there is an extremal
`n`-point configuration. This is what makes the interface below an equivalence rather than a
one-way reduction. -/
theorem exists_unitDistNum_eq_f (hd : 1 ≤ d) (n : ℕ) :
    ∃ s : Finset (ℝ^ d), #s = n ∧ unitDistNum s = Erdos1085.f d n := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨s₀, hs₀⟩ := Infinite.exists_subset_card_eq (ℝ^ d) n
  obtain ⟨s, hs⟩ : Erdos1085.f d n ∈
      Set.range fun s : Finset (ℝ^ d) => ⨆ (_ : #s = n), unitDistNum s :=
    Nat.sSup_mem ⟨_, ⟨s₀, rfl⟩⟩ (bddAbove_unitDistNum d n)
  have hs' : (⨆ (_ : #s = n), unitDistNum s) = Erdos1085.f d n := hs
  by_cases h : #s = n
  · exact ⟨s, h, by rw [← hs', ciSup_pos (f := fun _ : #s = n => unitDistNum s) h]⟩
  · haveI : IsEmpty (#s = n) := ⟨h⟩
    have hzero : Erdos1085.f d n = 0 := by
      rw [← hs', ciSup_of_empty]
      rfl
    refine ⟨s₀, hs₀, ?_⟩
    have hle := unitDistNum_le_f (d := d) (n := n) hs₀
    omega

/-- Real-valued transfer: a bound valid for all `n`-point configurations bounds `Erdos1085.f d n`
itself, with no positivity assumption on the bound. -/
theorem f_le_real (hd : 1 ≤ d) {M : ℝ}
    (h : ∀ s : Finset (ℝ^ d), #s = n → (unitDistNum s : ℝ) ≤ M) :
    (Erdos1085.f d n : ℝ) ≤ M := by
  obtain ⟨s, hs, hsf⟩ := exists_unitDistNum_eq_f hd n
  rw [← hsf]
  exact h s hs

/-- `Erdos1085.f d` is monotone: extremal configurations can always be padded with a far away
point. -/
theorem f_mono (hd : 1 ≤ d) : Monotone (Erdos1085.f d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine monotone_nat_of_le_succ fun n => ?_
  obtain ⟨s, hs, hsf⟩ := exists_unitDistNum_eq_f hd n
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset s
  have hcard : #(insert x s) = n + 1 := by rw [Finset.card_insert_of_notMem hx, hs]
  calc Erdos1085.f d n = unitDistNum s := hsf.symm
    _ ≤ unitDistNum (insert x s) := unitDistNum_mono (Finset.subset_insert _ _)
    _ ≤ Erdos1085.f d (n + 1) := unitDistNum_le_f hcard

/-- **The upper-bound interface.** An `IsBigO` upper bound on `Erdos1085.f d` is *equivalent* to an
eventual bound on every `n`-point configuration. -/
theorem isBigO_f_iff (hd : 1 ≤ d) (g : ℕ → ℝ) :
    (fun n ↦ (Erdos1085.f d n : ℝ)) =O[atTop] g ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : Finset (ℝ^ d), #s = n →
        (unitDistNum s : ℝ) ≤ C * ‖g n‖ := by
  rw [Asymptotics.isBigO_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨|C|, abs_nonneg C, ?_⟩
    filter_upwards [hC] with n hn s hs
    calc (unitDistNum s : ℝ) ≤ (Erdos1085.f d n : ℝ) := by exact_mod_cast unitDistNum_le_f hs
      _ ≤ ‖(Erdos1085.f d n : ℝ)‖ := le_norm_self _
      _ ≤ C * ‖g n‖ := hn
      _ ≤ |C| * ‖g n‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg (g n))
  · rintro ⟨C, -, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [hC] with n hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact f_le_real hd hn

/-- **The lower-bound interface.** An `IsBigO` lower bound on `Erdos1085.f d` is *equivalent* to
the eventual existence of good `n`-point configurations. -/
theorem isBigO_iff_f (hd : 1 ≤ d) (g : ℕ → ℝ) :
    g =O[atTop] (fun n ↦ (Erdos1085.f d n : ℝ)) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∃ s : Finset (ℝ^ d), #s = n ∧
        ‖g n‖ ≤ C * unitDistNum s := by
  rw [Asymptotics.isBigO_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨|C|, abs_nonneg C, ?_⟩
    filter_upwards [hC] with n hn
    obtain ⟨s, hs, hsf⟩ := exists_unitDistNum_eq_f hd n
    refine ⟨s, hs, ?_⟩
    rw [hsf]
    calc ‖g n‖ ≤ C * ‖(Erdos1085.f d n : ℝ)‖ := hn
      _ ≤ |C| * ‖(Erdos1085.f d n : ℝ)‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ = |C| * (Erdos1085.f d n : ℝ) := by rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, ?_⟩
    filter_upwards [hC] with n hn
    obtain ⟨s, hs, hle⟩ := hn
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    refine hle.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact_mod_cast unitDistNum_le_f hs

end Sup

/- ## The Lenz construction, and an outright proof of the companion `.lower_d4_lenz` -/

section Lenz

/-- First coordinate of a rational parametrisation of the circle of radius `√2 / 2` about the
origin of a plane. Rational rather than trigonometric, so that injectivity is an algebraic
identity rather than a statement about periods. -/
noncomputable def lenzX (t : ℝ) : ℝ := (1 - t ^ 2) / (√2 * (1 + t ^ 2))

/-- Second coordinate of the rational parametrisation of the circle of radius `√2 / 2`. -/
noncomputable def lenzY (t : ℝ) : ℝ := (2 * t) / (√2 * (1 + t ^ 2))

/-- The parametrisation really lands on the circle of radius `√2 / 2`. Two points on two
*orthogonal* such circles are therefore at distance `√(1/2 + 1/2) = 1`, which is the whole point
of the Lenz construction. -/
theorem lenzX_sq_add_lenzY_sq (t : ℝ) : lenzX t ^ 2 + lenzY t ^ 2 = 1 / 2 := by
  have h2 : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [lenzX, lenzY, div_pow, div_pow, mul_pow, h2, ← add_div,
    div_eq_div_iff (by positivity) (by norm_num)]
  ring

/-- The parametrisation is injective, so each circle carries arbitrarily many distinct points. -/
theorem lenz_param_injective {t u : ℝ} (hx : lenzX t = lenzX u) (hy : lenzY t = lenzY u) :
    t = u := by
  have hs : (0 : ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num)
  have ht : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hu : (0 : ℝ) < 1 + u ^ 2 := by positivity
  rw [lenzX, lenzX, div_eq_div_iff (by positivity) (by positivity)] at hx
  rw [lenzY, lenzY, div_eq_div_iff (by positivity) (by positivity)] at hy
  have hx' : (1 - t ^ 2) * (1 + u ^ 2) = (1 - u ^ 2) * (1 + t ^ 2) :=
    mul_left_cancel₀ hs.ne' (by linear_combination hx)
  have hy' : 2 * t * (1 + u ^ 2) = 2 * u * (1 + t ^ 2) :=
    mul_left_cancel₀ hs.ne' (by linear_combination hy)
  have hsq : t ^ 2 = u ^ 2 := by linarith [hx']
  have hzero : (t - u) * (1 + t ^ 2) = 0 := by linear_combination hy' / 2 + t * hsq
  have := (mul_eq_zero.mp hzero).resolve_right ht.ne'
  linarith

/-- The point of `ℝ^d` lying on the `j`-th coordinate circle — the circle of radius `√2 / 2` in
the plane spanned by the basis vectors number `2 * j` and `2 * j + 1` — with parameter `t`. -/
noncomputable def lenzPt (d j : ℕ) (t : ℝ) : ℝ^ d :=
  WithLp.toLp 2 (fun i : Fin d =>
    if (i : ℕ) = 2 * j then lenzX t else if (i : ℕ) = 2 * j + 1 then lenzY t else 0)

theorem lenzPt_apply (d j : ℕ) (t : ℝ) (i : Fin d) :
    lenzPt d j t i =
      if (i : ℕ) = 2 * j then lenzX t else if (i : ℕ) = 2 * j + 1 then lenzY t else 0 := rfl

/-- **Two points on different coordinate circles are at distance exactly one.** This is the
geometric heart of the Lenz construction: the two circles are orthogonal, so the squared distance
splits as `1/2 + 1/2`. -/
theorem dist_lenzPt {d j k : ℕ} (hj : 2 * j + 1 < d) (hk : 2 * k + 1 < d) (hjk : j ≠ k)
    (t u : ℝ) : dist (lenzPt d j t) (lenzPt d k u) = 1 := by
  have step1 : ∑ i : Fin d, dist (lenzPt d j t i) (lenzPt d k u i) ^ 2
      = ∑ a ∈ range d,
        ((if a = 2 * j then lenzX t else if a = 2 * j + 1 then lenzY t else 0) -
          (if a = 2 * k then lenzX u else if a = 2 * k + 1 then lenzY u else 0)) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun a =>
      ((if a = 2 * j then lenzX t else if a = 2 * j + 1 then lenzY t else 0) -
        (if a = 2 * k then lenzX u else if a = 2 * k + 1 then lenzY u else 0)) ^ 2) d]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Real.dist_eq, sq_abs, lenzPt_apply, lenzPt_apply]
  have hsub : ({2 * j, 2 * j + 1, 2 * k, 2 * k + 1} : Finset ℕ) ⊆ range d := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_range]
    omega
  have hzero : ∀ a ∈ range d, a ∉ ({2 * j, 2 * j + 1, 2 * k, 2 * k + 1} : Finset ℕ) →
      ((if a = 2 * j then lenzX t else if a = 2 * j + 1 then lenzY t else 0) -
        (if a = 2 * k then lenzX u else if a = 2 * k + 1 then lenzY u else 0)) ^ 2 = 0 := by
    intro a _ ha
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    obtain ⟨h1, h2, h3, h4⟩ := ha
    simp [h1, h2, h3, h4]
  have hx : ¬ (2 * j = 2 * k) := by omega
  have hx2 : ¬ (2 * j = 2 * k + 1) := by omega
  have hy1 : ¬ (2 * j + 1 = 2 * j) := by omega
  have hy2 : ¬ (2 * j + 1 = 2 * k) := by omega
  have hy3 : ¬ (2 * j + 1 = 2 * k + 1) := by omega
  have hz1 : ¬ (2 * k = 2 * j) := by omega
  have hz2 : ¬ (2 * k = 2 * j + 1) := by omega
  have hw1 : ¬ (2 * k + 1 = 2 * j) := by omega
  have hw2 : ¬ (2 * k + 1 = 2 * j + 1) := by omega
  have hw3 : ¬ (2 * k + 1 = 2 * k) := by omega
  have key : ∑ i : Fin d, dist (lenzPt d j t i) (lenzPt d k u i) ^ 2 = 1 := by
    rw [step1, ← Finset.sum_subset hsub hzero,
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton]
    simp only [if_neg hx, if_neg hx2, if_neg hy1, if_neg hy2, if_neg hy3,
      if_neg hz1, if_neg hz2, if_neg hw1, if_neg hw2, if_neg hw3, if_true,
      sub_zero, zero_sub, neg_sq]
    have h1 := lenzX_sq_add_lenzY_sq t
    have h2 := lenzX_sq_add_lenzY_sq u
    linarith
  rw [EuclideanSpace.dist_eq, key, Real.sqrt_one]

/-- The `i`-th point of the Lenz configuration on `p` coordinate circles of `ℝ^d`: the points are
dealt out to the circles round-robin, so the circles receive as equal numbers of points as
possible — which is what makes the error term in `lenz_lower_bound` a constant and not `O(n)`. -/
noncomputable def lenzIdx (d p i : ℕ) : ℝ^ d := lenzPt d (i % p) ((i / p : ℕ) : ℝ)

theorem lenzIdx_injective {d p : ℕ} (hp : 0 < p) (hpd : 2 * p ≤ d) :
    Function.Injective (lenzIdx d p) := by
  intro i i' h
  have hb : 2 * (i % p) + 1 < d := by have := Nat.mod_lt i hp; omega
  have hb' : 2 * (i' % p) + 1 < d := by have := Nat.mod_lt i' hp; omega
  by_cases hmod : i % p = i' % p
  · simp only [lenzIdx] at h
    rw [hmod] at h
    have hx : lenzX ((i / p : ℕ) : ℝ) = lenzX ((i' / p : ℕ) : ℝ) := by
      have hc := congrArg (fun v : ℝ^ d => v ⟨2 * (i' % p), by omega⟩) h
      simpa [lenzPt_apply] using hc
    have hy : lenzY ((i / p : ℕ) : ℝ) = lenzY ((i' / p : ℕ) : ℝ) := by
      have hc := congrArg (fun v : ℝ^ d => v ⟨2 * (i' % p) + 1, hb'⟩) h
      simpa [lenzPt_apply] using hc
    have hdiv : i / p = i' / p := by
      exact_mod_cast lenz_param_injective hx hy
    have e1 : p * (i / p) + i % p = i := Nat.div_add_mod i p
    have e2 : p * (i' / p) + i' % p = i' := Nat.div_add_mod i' p
    rw [← e1, ← e2, hdiv, hmod]
  · exfalso
    have hd1 : dist (lenzIdx d p i) (lenzIdx d p i') = 1 :=
      dist_lenzPt (d := d) hb hb' hmod ((i / p : ℕ) : ℝ) ((i' / p : ℕ) : ℝ)
    rw [h, dist_self] at hd1
    exact zero_ne_one hd1

/-- The Lenz configuration: `n` points distributed round-robin over `p` orthogonal circles of
radius `√2 / 2` inside `ℝ^d`. -/
noncomputable def lenzSet (d p n : ℕ) : Finset (ℝ^ d) := (range n).image (lenzIdx d p)

theorem card_lenzSet {d p : ℕ} (hp : 0 < p) (hpd : 2 * p ≤ d) (n : ℕ) :
    #(lenzSet d p n) = n := by
  rw [lenzSet, Finset.card_image_of_injective _ (lenzIdx_injective hp hpd), Finset.card_range]

/- The round-robin dealing is analysed by three lemmas on the sizes of the residue classes of
`range n` modulo `p`, which together pin those sizes down to `⌊n/p⌋` or `⌊n/p⌋ + 1`. -/

/-- The residue classes modulo `p` partition `range n`. -/
theorem sum_card_residue_class {p : ℕ} (hp : 0 < p) (n : ℕ) :
    ∑ j ∈ range p, #{i ∈ range n | i % p = j} = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := fun i => i % p) (s := range n) (t := range p)
    (fun i _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt i hp)))
  rw [Finset.card_range] at h
  exact h.symm

/-- Each residue class of `range n` modulo `p` has at most `⌊n/p⌋ + 1` elements. -/
theorem card_residue_class_le (p n j : ℕ) : #{i ∈ range n | i % p = j} ≤ n / p + 1 := by
  classical
  rw [← Finset.card_range (n / p + 1)]
  refine Finset.card_le_card_of_injOn (fun i => i / p) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    have h : i / p ≤ n / p := Nat.div_le_div_right hi.1.le
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have hab' : a / p = b / p := hab
    have h1 : p * (a / p) + a % p = a := Nat.div_add_mod a p
    have h2 : p * (b / p) + b % p = b := Nat.div_add_mod b p
    rw [← h1, ← h2, hab', ha.2, hb.2]

/-- Each residue class of `range n` modulo `p` has at least `⌊n/p⌋` elements. -/
theorem le_card_residue_class {p j : ℕ} (hp : 0 < p) (hj : j < p) (n : ℕ) :
    n / p ≤ #{i ∈ range n | i % p = j} := by
  classical
  rw [← Finset.card_range (n / p)]
  refine Finset.card_le_card_of_injOn (fun k => j + p * k) ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · have h1 : p * k + p ≤ p * (n / p) := by
        have h := Nat.mul_le_mul_left p (show k + 1 ≤ n / p from hk)
        rwa [Nat.mul_succ] at h
      have h2 : p * (n / p) ≤ n := Nat.mul_div_le n p
      exact lt_of_lt_of_le (Nat.add_lt_add_right hj (p * k)) (by omega)
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  · intro a _ b _ hab
    have hab' : j + p * a = j + p * b := hab
    exact Nat.eq_of_mul_eq_mul_left hp (by omega)

/-- **The second moment of a balanced partition.** Because the residue classes of `range n`
modulo `p` differ in size by at most one, the sum of the squares of their sizes exceeds the
convexity minimum `n ^ 2 / p` by at most the constant `p`. This is exactly the step that keeps
the error term of `lenz_lower_bound` bounded rather than linear in `n`. -/
theorem mul_sum_sq_card_residue_class_le {p : ℕ} (hp : 0 < p) (n : ℕ) :
    p * ∑ j ∈ range p, (#{i ∈ range n | i % p = j}) ^ 2 ≤ n ^ 2 + p ^ 2 := by
  classical
  set c : ℕ → ℕ := fun j => #{i ∈ range n | i % p = j} with hc
  set q := n / p with hq
  set r := n % p with hr
  have hrp : r < p := Nat.mod_lt n hp
  have hn : n = p * q + r := (Nat.div_add_mod n p).symm
  have hsum : ∑ j ∈ range p, c j = n := sum_card_residue_class hp n
  have hkey : ∀ j ∈ range p, (c j) ^ 2 + q * (q + 1) ≤ (2 * q + 1) * c j := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 : q ≤ c j := le_card_residue_class hp hj n
    have h2 : c j ≤ q + 1 := card_residue_class_le p n j
    rcases (show c j = q ∨ c j = q + 1 by omega) with h | h <;> rw [h] <;> nlinarith
  have hSum : (∑ j ∈ range p, (c j) ^ 2) + p * (q * (q + 1)) ≤ (2 * q + 1) * n := by
    calc (∑ j ∈ range p, (c j) ^ 2) + p * (q * (q + 1))
        = ∑ j ∈ range p, ((c j) ^ 2 + q * (q + 1)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ ∑ j ∈ range p, ((2 * q + 1) * c j) := Finset.sum_le_sum hkey
      _ = (2 * q + 1) * n := by rw [← Finset.mul_sum, hsum]
  have h' : p * (∑ j ∈ range p, (c j) ^ 2) + p * (p * (q * (q + 1)))
      ≤ p * ((2 * q + 1) * n) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left p hSum
  have hY : p * ((2 * q + 1) * n) ≤ (n ^ 2 + p ^ 2) + p * (p * (q * (q + 1))) := by
    have hle : r * p ≤ p * p := Nat.mul_le_mul_right p hrp.le
    rw [hn]
    nlinarith [hle]
  exact Nat.le_of_add_le_add_right (h'.trans hY)

/-- **Every ordered pair of Lenz points on different circles is a unit pair.** Hence `n ^ 2` is at
most twice the number of unit distances plus the number of ordered pairs sharing a circle. -/
theorem sq_le_two_mul_unitDistNum_lenzSet {d p : ℕ} (hp : 0 < p) (hpd : 2 * p ≤ d) (n : ℕ) :
    n ^ 2 ≤ 2 * unitDistNum (lenzSet d p n)
      + ∑ j ∈ range p, (#{i ∈ range n | i % p = j}) ^ 2 := by
  classical
  have hbnd : ∀ i : ℕ, 2 * (i % p) + 1 < d := fun i => by have := Nat.mod_lt i hp; omega
  have hsplit : #{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p}
      + #{z ∈ (range n) ×ˢ (range n) | ¬ (z.1 % p = z.2 % p)} = n ^ 2 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_product, Finset.card_range, sq]
  have hsame : #{z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p}
      = ∑ j ∈ range p, (#{i ∈ range n | i % p = j}) ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1 % p) (t := range p)
      (fun z _ => Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hp)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hset : {z ∈ {z ∈ (range n) ×ˢ (range n) | z.1 % p = z.2 % p} | z.1 % p = j}
        = ({i ∈ range n | i % p = j}) ×ˢ ({i ∈ range n | i % p = j}) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, hab⟩, hja⟩
        exact ⟨⟨ha, hja⟩, hb, by rw [← hab]; exact hja⟩
      · rintro ⟨⟨ha, hja⟩, hb, hjb⟩
        exact ⟨⟨⟨ha, hb⟩, by rw [hja, hjb]⟩, hja⟩
    rw [hset, Finset.card_product, sq]
  have hcross : #{z ∈ (range n) ×ˢ (range n) | ¬ (z.1 % p = z.2 % p)}
      ≤ 2 * unitDistNum (lenzSet d p n) := by
    rw [← card_ordered_unit_pairs (lenzSet d p n)]
    refine Finset.card_le_card_of_injOn (fun z => (lenzIdx d p z.1, lenzIdx d p z.2)) ?_ ?_
    · rintro ⟨a, b⟩ hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hz
      obtain ⟨⟨ha, hb⟩, hab⟩ := hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, lenzSet,
        Finset.mem_image, Finset.mem_range]
      exact ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, dist_lenzPt (hbnd a) (hbnd b) hab _ _⟩
    · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ heq
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext (lenzIdx_injective hp hpd heq.1) (lenzIdx_injective hp hpd heq.2)
  omega

/-- **The Lenz lower bound.** For `1 ≤ p` with `2 * p ≤ d`, the extremal function of Erdős 1085
satisfies `f d n ≥ (p - 1) / (2 p) * n ^ 2 - p` for *every* `n`, with a genuinely constant error
term. -/
theorem lenz_lower_bound {d p : ℕ} (hp : 0 < p) (hpd : 2 * p ≤ d) (n : ℕ) :
    ((p : ℝ) - 1) / (2 * p) * n ^ 2 - p ≤ Erdos1085.f d n := by
  classical
  have h1 := sq_le_two_mul_unitDistNum_lenzSet hp hpd n
  have h2 := mul_sum_sq_card_residue_class_le (p := p) hp n
  have hUf : (unitDistNum (lenzSet d p n) : ℝ) ≤ (Erdos1085.f d n : ℝ) := by
    exact_mod_cast unitDistNum_le_f (card_lenzSet hp hpd n)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have c1 : (n : ℝ) ^ 2 ≤ 2 * (unitDistNum (lenzSet d p n) : ℝ)
      + ((∑ j ∈ range p, (#{i ∈ range n | i % p = j}) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
  have c2 : (p : ℝ) * ((∑ j ∈ range p, (#{i ∈ range n | i % p = j}) ^ 2 : ℕ) : ℝ)
      ≤ (n : ℝ) ^ 2 + (p : ℝ) ^ 2 := by exact_mod_cast h2
  have key : ((p : ℝ) - 1) * n ^ 2 - p ^ 2 ≤ 2 * p * (unitDistNum (lenzSet d p n) : ℝ) := by
    nlinarith [c1, c2, hp0]
  rw [div_mul_eq_mul_div, sub_le_iff_le_add, div_le_iff₀ (by positivity)]
  nlinarith [key, hUf, hp0]

/-- **The companion `Erdos1085.erdos_1085.variants.lower_d4_lenz`, proved outright.** The pool
file states this Lenz bound but leaves it unproved; here is that statement, proved. For `d ≥ 4`,
writing `p = ⌊d/2⌋`, one has `f d n ≥ (p - 1) / (2 p) * n ^ 2 - C` for a constant `C`
(here `C = p`) independent of `n`. -/
theorem lower_d4_lenz {d : ℕ} (hd : 4 ≤ d) :
    ∃ C : ℝ, ∀ n : ℕ, ↑(d / 2 - 1) / (2 * ↑(d / 2)) * n ^ 2 - C ≤ Erdos1085.f d n := by
  have hp : 0 < d / 2 := by omega
  have hpd : 2 * (d / 2) ≤ d := by omega
  have hcast : ((d / 2 - 1 : ℕ) : ℝ) = ((d / 2 : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub hp, Nat.cast_one]
  refine ⟨((d / 2 : ℕ) : ℝ), fun n => ?_⟩
  rw [hcast]
  exact lenz_lower_bound hp hpd n

end Lenz

/- ## The geometric input: the unit-distance graph is `K₃,₃`-free in dimension `< 4` -/

section Geometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- If `p` and `q` are both equidistant from `e` and `f`, then `p - q ⊥ e - f`. -/
theorem inner_sub_sub_eq_zero {p q e f : V} (hp : dist p e = dist p f) (hq : dist q e = dist q f) :
    ⟪p - q, e - f⟫ = 0 := by
  have hp' : ‖p - e‖ ^ 2 = ‖p - f‖ ^ 2 := by rw [← dist_eq_norm, ← dist_eq_norm, hp]
  have hq' : ‖q - e‖ ^ 2 = ‖q - f‖ ^ 2 := by rw [← dist_eq_norm, ← dist_eq_norm, hq]
  rw [norm_sub_sq_real, norm_sub_sq_real] at hp' hq'
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

/-- Three distinct points at distance `1` from a common point are affinely independent. -/
theorem affineIndependent_of_dist_eq_one {a x y z : V} (hx : dist x a = 1) (hy : dist y a = 1)
    (hz : dist z a = 1) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    AffineIndependent ℝ ![x, y, z] := by
  have hc : EuclideanGeometry.Cospherical ({x, y, z} : Set V) := by
    refine ⟨a, 1, ?_⟩
    rintro p (rfl | rfl | rfl) <;> assumption
  exact hc.affineIndependent_of_ne hxy hxz hyz

/-- An affinely independent triple spans a plane. -/
theorem finrank_vectorSpan_eq_two [FiniteDimensional ℝ V] {x y z : V}
    (h : AffineIndependent ℝ ![x, y, z]) :
    Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set V)) = 2 := by
  have h2 := h.finrank_vectorSpan (n := 2) (by simp)
  have hr : Set.range ![x, y, z] = ({x, y, z} : Set V) := by ext w; simp; tauto
  rwa [hr] at h2

/-- **No `K₃,₃` in dimension at most three.** In a real inner product space of dimension `< 4`
there are no three distinct points `x, y, z` all at distance `1` from three distinct points
`a, b, c`: the two triangles would span orthogonal planes. -/
theorem not_three_common_unit_neighbours [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V < 4)
    {a b c x y z : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ∀ p ∈ ({x, y, z} : Set V), ∀ q ∈ ({a, b, c} : Set V), dist p q = 1) : False := by
  have hx : ∀ q ∈ ({a, b, c} : Set V), dist x q = 1 := h x (by simp)
  have hmem : ∀ p ∈ ({x, y, z} : Set V), dist p a = 1 := fun p hp => h p hp a (by simp)
  have hU : Module.finrank ℝ (vectorSpan ℝ ({a, b, c} : Set V)) = 2 :=
    finrank_vectorSpan_eq_two (affineIndependent_of_dist_eq_one
      (a := x) (by rw [dist_comm]; exact hx a (by simp))
      (by rw [dist_comm]; exact hx b (by simp)) (by rw [dist_comm]; exact hx c (by simp))
      hab hac hbc)
  have hW : Module.finrank ℝ (vectorSpan ℝ ({x, y, z} : Set V)) = 2 :=
    finrank_vectorSpan_eq_two (affineIndependent_of_dist_eq_one
      (a := a) (hmem x (by simp)) (hmem y (by simp)) (hmem z (by simp)) hxy hxz hyz)
  have hortho : vectorSpan ℝ ({x, y, z} : Set V) ⟂ vectorSpan ℝ ({a, b, c} : Set V) := by
    rw [vectorSpan_def, vectorSpan_def, Submodule.isOrtho_span]
    rintro u hu v hv
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.mp hu
    obtain ⟨e, he, f, hf, rfl⟩ := Set.mem_vsub.mp hv
    rw [vsub_eq_sub, vsub_eq_sub]
    exact inner_sub_sub_eq_zero (by rw [h p hp e he, h p hp f hf])
      (by rw [h q hq e he, h q hq f hf])
  have hle := Submodule.finrank_mono hortho.le
  have hsum := Submodule.finrank_add_finrank_orthogonal (K := vectorSpan ℝ ({a, b, c} : Set V))
  omega

/-- **`K₃,₃`-freeness in `Finset` form**: at most two points of a space of dimension `< 4` are at
distance `1` from each of three fixed distinct points. -/
theorem card_le_two_of_forall_dist_eq_one [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V < 4)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {t : Finset V}
    (ht : ∀ x ∈ t, dist x a = 1 ∧ dist x b = 1 ∧ dist x c = 1) : #t ≤ 2 := by
  by_contra hcon
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < #t by omega)
  refine not_three_common_unit_neighbours hV hab hac hbc hxy hxz hyz ?_
  rintro p (rfl | rfl | rfl) q (rfl | rfl | rfl)
  exacts [(ht _ hx).1, (ht _ hx).2.1, (ht _ hx).2.2, (ht _ hy).1, (ht _ hy).2.1, (ht _ hy).2.2,
    (ht _ hz).1, (ht _ hz).2.1, (ht _ hz).2.2]

end Geometry

/- ## Sharpness: the dimension hypothesis cannot be dropped -/

section Sharpness

/-- **The hypothesis `finrank ℝ V < 4` of `not_three_common_unit_neighbours` and
`card_le_two_of_forall_dist_eq_one` is necessary.** In `ℝ^4` the Lenz configuration on two
orthogonal circles realises `K₃,₃` in the unit-distance graph: three distinct points there do have
three common unit-distance neighbours. So the Kővári–Sós–Turán argument below stops at `d = 3`,
as the quadratic growth of `lenz_lower_bound` demands. -/
theorem exists_card_three_forall_dist_eq_one :
    ∃ (a b c : ℝ^ 4) (t : Finset (ℝ^ 4)), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ 2 < #t ∧
      ∀ x ∈ t, dist x a = 1 ∧ dist x b = 1 ∧ dist x c = 1 := by
  have hinj : Function.Injective (lenzIdx 4 2) :=
    lenzIdx_injective (by norm_num) (by norm_num)
  have hne : ∀ i i' : ℕ, i ≠ i' → lenzIdx 4 2 i ≠ lenzIdx 4 2 i' := fun i i' h hc => h (hinj hc)
  have hdist : ∀ i i' : ℕ, i % 2 ≠ i' % 2 → dist (lenzIdx 4 2 i) (lenzIdx 4 2 i') = 1 := by
    intro i i' h
    exact dist_lenzPt (by have := Nat.mod_lt i (show 0 < 2 by norm_num); omega)
      (by have := Nat.mod_lt i' (show 0 < 2 by norm_num); omega) h _ _
  refine ⟨lenzIdx 4 2 1, lenzIdx 4 2 3, lenzIdx 4 2 5,
    {lenzIdx 4 2 0, lenzIdx 4 2 2, lenzIdx 4 2 4},
    hne 1 3 (by norm_num), hne 1 5 (by norm_num), hne 3 5 (by norm_num), ?_, ?_⟩
  · rw [Finset.card_eq_three.mpr ⟨_, _, _, hne 0 2 (by norm_num), hne 0 4 (by norm_num),
      hne 2 4 (by norm_num), rfl⟩]
    norm_num
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      exact ⟨hdist _ _ (by decide), hdist _ _ (by decide), hdist _ _ (by decide)⟩

end Sharpness

/- ## The Kővári–Sós–Turán count -/

section Counting

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `6 * C(m, 3)` as a falling product, valid for all `m` with truncated subtraction. -/
theorem six_mul_choose_three (m : ℕ) : 6 * m.choose 3 = (m - 2) * ((m - 1) * m) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  simp [Nat.descFactorial, Nat.factorial] at h
  omega

/-- **The double count.** `K₃,₃`-freeness bounds the number of "cherries": triples of points with
a common unit-distance neighbour are counted at most twice. -/
theorem sum_choose_three_le [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V < 4) (s : Finset V) :
    ∑ x ∈ s, (#{y ∈ s | dist x y = 1}).choose 3 ≤ 2 * (#s).choose 3 := by
  classical
  calc ∑ x ∈ s, (#{y ∈ s | dist x y = 1}).choose 3
      = ∑ x ∈ s, ∑ T ∈ s.powersetCard 3,
          (if T ⊆ {y ∈ s | dist x y = 1} then 1 else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hT : ({y ∈ s | dist x y = 1} : Finset V).powersetCard 3
            = {T ∈ s.powersetCard 3 | T ⊆ {y ∈ s | dist x y = 1}} := by
          ext T
          simp only [Finset.mem_powersetCard, Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1.trans (Finset.filter_subset _ _), h2⟩, h1⟩
          · rintro ⟨⟨_, h2⟩, h3⟩
            exact ⟨h3, h2⟩
        rw [← Finset.card_powersetCard, hT, Finset.card_filter]
    _ = ∑ T ∈ s.powersetCard 3, ∑ x ∈ s,
          (if T ⊆ {y ∈ s | dist x y = 1} then 1 else 0) := Finset.sum_comm
    _ ≤ ∑ _T ∈ s.powersetCard 3, 2 := by
        refine Finset.sum_le_sum fun T hT => ?_
        rw [← Finset.card_filter]
        rw [Finset.mem_powersetCard] at hT
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT.2
        refine card_le_two_of_forall_dist_eq_one hV hab hac hbc ?_
        intro x hx
        rw [Finset.mem_filter] at hx
        have hsub := hx.2
        exact ⟨(Finset.mem_filter.mp (hsub (by simp))).2,
          (Finset.mem_filter.mp (hsub (by simp))).2, (Finset.mem_filter.mp (hsub (by simp))).2⟩
    _ = 2 * (#s).choose 3 := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, mul_comm]

/-- **The Kővári–Sós–Turán bound, `ℕ`-level and constant-free.** In any real inner product space
of dimension `< 4`, the number of unit distances `e` spanned by a set of `n` points satisfies
`(2e - 2n) ^ 3 ≤ 2 n ^ 5`. -/
theorem two_mul_unitDistNum_sub_pow_three_le [FiniteDimensional ℝ V]
    (hV : Module.finrank ℝ V < 4) (s : Finset V) :
    (2 * unitDistNum s - 2 * #s) ^ 3 ≤ 2 * (#s) ^ 5 := by
  classical
  set D : V → ℕ := fun x => #{y ∈ s | dist x y = 1} with hD
  have hcube : ∀ m : ℕ, (m - 2) ^ 3 ≤ 6 * m.choose 3 := by
    intro m
    rw [six_mul_choose_three]
    calc (m - 2) ^ 3 = (m - 2) * ((m - 2) * (m - 2)) := by ring
      _ ≤ (m - 2) * ((m - 1) * m) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hsix : ∀ m : ℕ, 6 * m.choose 3 ≤ m ^ 3 := by
    intro m
    rw [six_mul_choose_three]
    calc (m - 2) * ((m - 1) * m) ≤ m * (m * m) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) le_rfl)
      _ = m ^ 3 := by ring
  have hmoment : ∑ x ∈ s, (D x - 2) ^ 3 ≤ 2 * (#s) ^ 3 := by
    calc ∑ x ∈ s, (D x - 2) ^ 3 ≤ ∑ x ∈ s, 6 * (D x).choose 3 :=
          Finset.sum_le_sum fun x _ => hcube _
      _ = 6 * ∑ x ∈ s, (D x).choose 3 := by rw [Finset.mul_sum]
      _ ≤ 6 * (2 * (#s).choose 3) := Nat.mul_le_mul_left _ (sum_choose_three_le hV s)
      _ = 2 * (6 * (#s).choose 3) := by ring
      _ ≤ 2 * (#s) ^ 3 := Nat.mul_le_mul_left _ (hsix _)
  have hjensen : (∑ x ∈ s, (D x - 2)) ^ 3 ≤ (#s) ^ 2 * ∑ x ∈ s, (D x - 2) ^ 3 :=
    pow_sum_le_card_mul_sum_pow (fun x _ => Nat.zero_le _) 2
  have hsplit : 2 * unitDistNum s - 2 * #s ≤ ∑ x ∈ s, (D x - 2) := by
    have h1 : 2 * unitDistNum s = ∑ x ∈ s, D x := two_mul_unitDistNum s
    have h2 : ∑ x ∈ s, D x ≤ (∑ x ∈ s, (D x - 2)) + 2 * #s := by
      calc ∑ x ∈ s, D x ≤ ∑ x ∈ s, ((D x - 2) + 2) := Finset.sum_le_sum fun x _ => by omega
        _ = (∑ x ∈ s, (D x - 2)) + 2 * #s := by
            rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  calc (2 * unitDistNum s - 2 * #s) ^ 3 ≤ (∑ x ∈ s, (D x - 2)) ^ 3 :=
        Nat.pow_le_pow_left hsplit 3
    _ ≤ (#s) ^ 2 * ∑ x ∈ s, (D x - 2) ^ 3 := hjensen
    _ ≤ (#s) ^ 2 * (2 * (#s) ^ 3) := Nat.mul_le_mul_left _ hmoment
    _ = 2 * (#s) ^ 5 := by ring

/-- Cube roots: from `a ^ 3 ≤ 2 * b ^ 5` to `a ≤ 2 * b ^ (5 / 3)`. -/
theorem le_two_mul_rpow {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 3 ≤ 2 * b ^ 5) :
    a ≤ 2 * b ^ (5 / 3 : ℝ) := by
  have hcube : (2 * b ^ (5 / 3 : ℝ)) ^ 3 = 8 * b ^ 5 := by
    rw [mul_pow, ← Real.rpow_natCast (b ^ (5 / 3 : ℝ)) 3, ← Real.rpow_mul hb]
    norm_num
  have hb5 : (0 : ℝ) ≤ b ^ 5 := by positivity
  by_contra hcon
  push_neg at hcon
  have hlt : (2 * b ^ (5 / 3 : ℝ)) ^ 3 < a ^ 3 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  rw [hcube] at hlt
  linarith

/-- **The upper bound for a single configuration**: `n` points in a real inner product space of
dimension `< 4` span at most `n + n^{5/3}` unit distances. -/
theorem unitDistNum_le_rpow [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V < 4) (s : Finset V) :
    (unitDistNum s : ℝ) ≤ #s + (#s : ℝ) ^ (5 / 3 : ℝ) := by
  have hnat := two_mul_unitDistNum_sub_pow_three_le hV s
  have hcast : ((2 * unitDistNum s - 2 * #s : ℕ) : ℝ) ^ 3 ≤ 2 * ((#s : ℝ)) ^ 5 := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  have hle := le_two_mul_rpow (Nat.cast_nonneg (#s)) hcast
  have hsplit : 2 * unitDistNum s ≤ (2 * unitDistNum s - 2 * #s) + 2 * #s := by omega
  have hsplit' : 2 * (unitDistNum s : ℝ) ≤ ((2 * unitDistNum s - 2 * #s : ℕ) : ℝ) + 2 * #s := by
    have := (Nat.cast_le (α := ℝ)).mpr hsplit
    push_cast at this
    exact this
  linarith

end Counting

/- ## The consequence for the target's function `Erdos1085.f 3` -/

section Main

/-- `f d n ≤ n + n^{5/3}` for every dimension `1 ≤ d ≤ 3`: a checked, explicit upper bound for
the function of Erdős 1085. -/
theorem f_le_rpow {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) (n : ℕ) :
    (Erdos1085.f d n : ℝ) ≤ n + (n : ℝ) ^ (5 / 3 : ℝ) := by
  refine f_le_real hd fun s hs => ?_
  have hfr : Module.finrank ℝ (ℝ^ d) < 4 := by
    rw [finrank_euclideanSpace_fin]
    omega
  have h := unitDistNum_le_rpow (V := ℝ^ d) hfr s
  rw [hs] at h
  exact h

/-- **`f 3 n = O(n^{5/3})`**, the Kővári–Sós–Turán benchmark for the target's function. -/
theorem isBigO_f_three_rpow :
    (fun n ↦ (Erdos1085.f 3 n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (5 / 3 : ℝ) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (n : ℝ) ^ (5 / 3 : ℝ) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (5 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have h2 := f_le_rpow (d := 3) (by norm_num) (by norm_num) n
  linarith

/-- **The hypothesis `d ≤ 3` of `f_le_rpow` is necessary**, and not merely because the proof
breaks: in dimension four the bound `f d n ≤ n + n ^ (5/3)` already fails at `n = 512`, since the
Lenz configuration forces `f 4 n ≥ n ^ 2 / 4 - 2`. -/
theorem not_f_le_rpow_of_dim_four :
    ∃ n : ℕ, ¬ ((Erdos1085.f 4 n : ℝ) ≤ n + (n : ℝ) ^ (5 / 3 : ℝ)) := by
  refine ⟨2 ^ 9, fun hcon => ?_⟩
  have hlow := lenz_lower_bound (d := 4) (p := 2) (by norm_num) (by norm_num) (2 ^ 9)
  have hcast : ((2 ^ 9 : ℕ) : ℝ) = 2 ^ (9 : ℕ) := by push_cast; ring
  rw [hcast] at hlow hcon
  have hrp : ((2 : ℝ) ^ (9 : ℕ)) ^ (5 / 3 : ℝ) = 2 ^ (15 : ℕ) := by
    rw [← Real.rpow_natCast (2 : ℝ) 9, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast (2 : ℝ) 15]
    norm_num
  rw [hrp] at hcon
  norm_num at hlow hcon
  linarith

end Main

/- ## How far the benchmark is from the target -/

section Gap

/-- The target's bounding function is `o(n^{5/3})`: the conjectured bound is strictly stronger
than the one proved here. -/
theorem isLittleO_target_rpow :
    (fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n)) =o[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (5 / 3 : ℝ) := by
  have hloglog : (fun n : ℕ ↦ log (log n)) =O[atTop] fun n : ℕ ↦ log n := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 1 ≤ log (n : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      calc Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
        _ ≤ (n : ℝ) := by linarith
    have hll : log (log (n : ℝ)) ≤ log (n : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < log n by linarith)
      linarith
    rw [Real.norm_of_nonneg (Real.log_nonneg hlog), Real.norm_of_nonneg (by linarith), one_mul]
    exact hll
  have hlog : (fun n : ℕ ↦ log n) =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) :=
    (isLittleO_log_rpow_atTop (by norm_num)).comp_tendsto tendsto_natCast_atTop_atTop
  have hmul := (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ)) atTop).mul_isLittleO
    (hloglog.trans_isLittleO hlog)
  refine hmul.congr' (EventuallyEq.refl _ _) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add h1]
  norm_num

/-- The benchmark `f 3 n = O(n^{5/3})` cannot be upgraded to the target's bound by a change of
constants: `n^{5/3}` is not `O(n^{4/3} log log n)`. Hence `isBigO_f_three_rpow` does **not**
settle `Erdos1085.erdos_1085.variants.upper_d3`. -/
theorem not_isBigO_rpow_five_thirds :
    ¬ ((fun n : ℕ ↦ (n : ℝ) ^ (5 / 3 : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n)) := by
  intro h
  refine Asymptotics.isLittleO_irrefl (f'' := fun n : ℕ ↦ (n : ℝ) ^ (5 / 3 : ℝ))
    (l := atTop) ?_ (h.trans_isLittleO isLittleO_target_rpow)
  refine Filter.Eventually.frequently ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have : (1 : ℝ) ≤ (n : ℝ) ^ (5 / 3 : ℝ) := Real.one_le_rpow h1 (by norm_num)
  linarith

end Gap

/- ## Worked use site: the obligation of `erdos_1085.variants.upper_d3` -/

section UseSite

/-- The `IsBigO` obligation of `Erdos1085.erdos_1085.variants.upper_d3`, rewritten by
`isBigO_f_iff` into an equivalent statement about arbitrary point configurations of `ℝ^3`, with
the norm eliminated. Being an `Iff`, it serves both a proof and a refutation of the target. -/
theorem upper_d3_isBigO_iff :
    ((fun n ↦ (Erdos1085.f 3 n : ℝ)) =O[atTop]
        fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n)) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : Finset (ℝ^ 3), #s = n →
        (unitDistNum s : ℝ) ≤ C * ((n : ℝ) ^ (4 / 3 : ℝ) * log (log n)) := by
  have hpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) ≤ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog : 1 ≤ log (n : ℝ) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      calc Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
        _ ≤ (n : ℝ) := by linarith
    have hll : 0 ≤ log (log (n : ℝ)) := Real.log_nonneg hlog
    positivity
  rw [isBigO_f_iff (by norm_num)]
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hC, hpos] with n h1 h2 s hs
    rw [← Real.norm_of_nonneg h2]
    exact h1 s hs
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, ?_⟩
    filter_upwards [hC, hpos] with n h1 h2 s hs
    rw [Real.norm_of_nonneg h2]
    exact h1 s hs

/-- A second worked use site, for the dimension API: an affirmative answer to
`erdos_1085.variants.upper_d3` transfers down to the plane, because `Erdos1085.f 2 n ≤
Erdos1085.f 3 n`. -/
theorem isBigO_f_two_of_upper_d3
    (h : (fun n ↦ (Erdos1085.f 3 n : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n)) :
    (fun n ↦ (Erdos1085.f 2 n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ) * log (log n) := by
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le atTop fun n => ?_) h
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast f_le_f_of_le (by norm_num) n

end UseSite

end Contribution.Erdos1085UnitDistance
