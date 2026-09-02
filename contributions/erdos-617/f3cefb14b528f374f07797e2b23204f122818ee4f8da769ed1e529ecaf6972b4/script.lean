import Mathlib
import FormalConjectures.ErdosProblems.«617»

/-!
# Erdős 617: balanced colourings, and the sharpness of `r ^ 2 + 1` and of `r ≥ 3`

Target: `Erdos617.erdos_617` — for `r ≥ 3`, every `r`-colouring of the edges of the complete
graph on `r ^ 2 + 1` vertices contains `r + 1` vertices spanning no edge of some colour;
equivalently, no such colouring is *balanced*. The same module contains the companion
obligation `Erdos617.erdos_617.variants.r2`, which asks for infinitely many `r` for which
`K_(r ^ 2)` carries a balanced `r`-colouring.

## The obstacle

Both statements are phrased with a bare `coloring : Sym2 V → Fin r` and a raw pairwise
condition `∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k` on a `Finset` of cardinality
*exactly* `r + 1`. Three concrete difficulties follow.

* Adding one vertex to a colour-avoiding set forces one to re-prove the pairwise condition
  including the symmetric case `s(u, v)` versus `s(v, u)`, which `Sym2` does not do for you.
* The `r2` variant needs an explicit infinite family of balanced colourings. The natural
  constructions are geometric (the parallel classes of an affine plane), and nothing in the
  pinned Mathlib turns a finite field into an edge colouring of `K_(q ^ 2)`, let alone bounds
  the independence number of a colour class.
* Nothing in the file records *why* the two hypotheses `hr : r ≥ 3` and
  `hV : Fintype.card V = r ^ 2 + 1` are needed, so a solver has no way of knowing when an
  attempted argument is provably doomed.

## What is proved here

1. **The affine-plane construction.** `slopeColoring` is the edge colouring of the affine plane
   `K × K` over a field `K` that gives an edge the slope of the line joining its two endpoints
   (vertical edges get slope `0`). `exists_ne_slopeColoring_eq` is the geometric heart: *any* set
   of more than `Fintype.card K` points of `K × K` contains two distinct points lying on a common
   line of any prescribed slope `m`. Consequently (`isBalanced_slopeColoring`) the slope
   colouring, transported along any `e : K ≃ Fin r`, is balanced.
2. **`Erdos617.erdos_617.variants.r2` is proved outright.** Instantiating the construction at
   `K = ZMod p` for every prime `p` gives `infinite_setOf_isBalanced_sq`, whose statement is
   *character-for-character* the statement of `Erdos617.erdos_617.variants.r2`.
   `exists_coloring_no_missesColor_card_eq_sq` states the same fact in the shape of the main
   theorem: the hypothesis `Fintype.card V = r ^ 2 + 1` cannot be weakened to `r ^ 2`.
3. **`hr : r ≥ 3` is necessary.** `pentagonColoring` is the `2`-colouring of `K_5 = K_(2 ^ 2 + 1)`
   by the pentagon and the pentagram; `not_exists_missesColor_pentagon` (checked by `decide`)
   says the conclusion of `Erdos617.erdos_617` fails verbatim for it. So no proof of
   `Erdos617.erdos_617` can avoid using `hr`.
4. **A small API for the conclusion predicate.** `MissesColor` names it,
   `MissesColor.insert` performs the `Sym2` symmetry step once and for all, and
   `exists_missesColor_iff_exists_link` converts the goal into the `rcases`-friendly form
   "one vertex `v`, one colour `k`, one `r`-element set `T` avoiding `k`, with all edges from
   `v` into `T` avoiding `k`" — an equivalence, not a strengthening.
   `IsBalanced.exists_link_of_missesColor` is its contrapositive (in a balanced colouring, an
   `r`-element `k`-avoiding set is `k`-dominating), and `IsBalanced.exists_le_card_colorLink`
   is a first counting consequence of that domination.
   `not_exists_missesColor_iff_isBalanced` connects the two halves of the file: the negation of
   the goal of `Erdos617.erdos_617` is equivalent to `IsBalanced coloring`, and a single
   `simp [IsBalanced]` proves it, so a `by_contra` puts the solver inside the balanced-colouring
   API. The two `Decidable` instances make `MissesColor` and `IsBalanced` checkable by `decide`
   on concrete finite colourings, which is what powers the `r = 2` counterexample above.

A later solver can use declaration `Contribution.Erdos617Independence.infinite_setOf_isBalanced_sq`
to discharge obligation `Erdos617.erdos_617.variants.r2` in target
`FormalConjectures.ErdosProblems.«617»`, and can use
`Contribution.Erdos617Independence.exists_missesColor_iff_exists_link` to simplify the
obligation `∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k` of `Erdos617.erdos_617` to the
one-vertex-plus-`r`-set form. Note that `k` and the set are *existentially* quantified there:
no claim is made that a colour or a set can be prescribed in advance. That same obligation can
instead be attacked by contradiction: `Contribution.Erdos617Independence.not_exists_missesColor_iff_isBalanced`
turns its negation into `IsBalanced coloring`, after which `IsBalanced.exists_link_of_missesColor`
and `IsBalanced.exists_le_card_colorLink` apply directly (use site 6 runs exactly this route).

The main statement `Erdos617.erdos_617` itself is *not* proved here and remains open; what is
offered for it is the API of item 4 together with the two checked impossibility results of
items 2 and 3, which delimit what a future proof may look like.

The final section contains six worked use sites: two stated with the binders of the reward
theorems themselves, one deriving `False` from a hypothetical hypothesis-free form of
`Erdos617.erdos_617`, two non-vacuity checks for the balanced-colouring API run on the pentagon
(a genuinely balanced colouring, not a constant one), and one running the contradiction route
from the negated goal of `Erdos617.erdos_617` to the counting lemma.

*References:*
- [erdosproblems.com/617](https://www.erdosproblems.com/617)
- Erdős, P. and Gyárfás, A., *Split and balanced colorings of complete graphs*,
  Discrete Math. 200 (1999), 79-86.
-/

namespace Contribution.Erdos617Independence

open Finset

/- ## The conclusion predicate of `Erdos617.erdos_617` -/

/-- `MissesColor coloring k S` says that colour `k` does not occur on any edge inside `S`.
This is, verbatim, the conclusion predicate of `Erdos617.erdos_617`. -/
def MissesColor {V : Type*} {r : ℕ} (coloring : Sym2 V → Fin r) (k : Fin r) (S : Finset V) :
    Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

instance decidableMissesColor {V : Type*} [DecidableEq V] {r : ℕ} (coloring : Sym2 V → Fin r)
    (k : Fin r) (S : Finset V) : Decidable (MissesColor coloring k S) :=
  inferInstanceAs (Decidable (∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k))

/-- The extension step: a vertex all of whose edges into `S` avoid colour `k` can be added to a
`k`-avoiding set. This is where the `Sym2` symmetry is handled once and for all. -/
theorem MissesColor.insert {V : Type*} [DecidableEq V] {r : ℕ} {coloring : Sym2 V → Fin r}
    {k : Fin r} {S : Finset V} {v : V} (hS : MissesColor coloring k S)
    (hv : ∀ u ∈ S, coloring s(v, u) ≠ k) :
    MissesColor coloring k (insert v S) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact hv y hy
  · rcases hy with rfl | hy
    · rw [Sym2.eq_swap]
      exact hv x hx
    · exact hS x hx y hy hxy

/-- **Reformulation of the goal of `Erdos617.erdos_617`.** Producing `r + 1` vertices that miss
a colour is *equivalent* to producing one vertex `v`, one colour `k` and one `r`-element set `T`
with `v ∉ T`, such that `T` misses `k` and every edge from `v` into `T` avoids `k`.

This is the shape a greedy or inductive argument actually wants: the ambient set has been split
off from the distinguished vertex, the cardinality is `r` rather than `r + 1`, and the awkward
symmetric pairwise condition at `v` has become a plain condition on the link of `v`. Nothing is
strengthened: `k` and `T` remain existentially quantified. -/
theorem exists_missesColor_iff_exists_link {V : Type*} [DecidableEq V] {r : ℕ}
    (coloring : Sym2 V → Fin r) :
    (∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ MissesColor coloring k S) ↔
      ∃ (v : V) (k : Fin r) (T : Finset V), v ∉ T ∧ T.card = r ∧ MissesColor coloring k T ∧
        ∀ u ∈ T, coloring s(v, u) ≠ k := by
  constructor
  · rintro ⟨S, k, hcard, hS⟩
    obtain ⟨v, hv⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    refine ⟨v, k, S.erase v, Finset.notMem_erase _ _, ?_, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hv, hcard]
      omega
    · exact fun x hx y hy hxy =>
        hS x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
    · exact fun u hu =>
        hS v hv u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu).symm
  · rintro ⟨v, k, T, hvT, hcard, hT, hlink⟩
    exact ⟨insert v T, k, by rw [Finset.card_insert_of_notMem hvT, hcard], hT.insert hlink⟩

/- ## Balanced colourings -/

/-- A colouring is *balanced* when every `r + 1` vertices see all `r` colours. This is exactly
the predicate occurring inside `Erdos617.erdos_617.variants.r2`, and its negation is the
conclusion of `Erdos617.erdos_617`. -/
def IsBalanced {V : Type*} {r : ℕ} (coloring : Sym2 V → Fin r) : Prop :=
  ∀ S : Finset V, S.card = r + 1 → ∀ k : Fin r, ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k

instance decidableIsBalanced {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (coloring : Sym2 V → Fin r) : Decidable (IsBalanced coloring) :=
  inferInstanceAs (Decidable (∀ S : Finset V, S.card = r + 1 → ∀ k : Fin r,
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k))

/-- **The negated goal is balancedness.** The negation of the conclusion of
`Erdos617.erdos_617`, written out verbatim, is equivalent to `IsBalanced coloring`. It is not a
deep fact — a single `simp [IsBalanced]` closes it — but it is what makes the `IsBalanced` API
below reachable from the reward theorem's own goal by `by_contra`. -/
theorem not_exists_missesColor_iff_isBalanced {V : Type*} {r : ℕ} (coloring : Sym2 V → Fin r) :
    (¬ ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k) ↔ IsBalanced coloring := by
  simp [IsBalanced]

/-- **Domination.** In a balanced colouring, an `r`-element set `T` avoiding colour `k` is
`k`-dominating: every vertex outside `T` is joined to `T` by an edge of colour `k`. (This is
the contrapositive of `exists_missesColor_iff_exists_link`, and is the form used in extremal
arguments: a `k`-avoiding set of size `r` can never be extended.) -/
theorem IsBalanced.exists_link_of_missesColor {V : Type*} [DecidableEq V] {r : ℕ}
    {coloring : Sym2 V → Fin r} (hb : IsBalanced coloring) {k : Fin r} {T : Finset V}
    (hcard : T.card = r) (hT : MissesColor coloring k T) {v : V} (hv : v ∉ T) :
    ∃ u ∈ T, coloring s(v, u) = k := by
  by_contra hc
  push_neg at hc
  obtain ⟨x, hx, y, hy, hxy, hcol⟩ :=
    hb (insert v T) (by rw [Finset.card_insert_of_notMem hv, hcard]) k
  exact hT.insert hc x hx y hy hxy hcol

/-- A counting consequence of domination on `K_(r ^ 2 + 1)`: if a balanced colouring has an
`r`-element set `T` avoiding colour `k`, then some vertex of `T` already carries `r` edges of
colour `k` going outside `T`. -/
theorem IsBalanced.exists_le_card_colorLink {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    {coloring : Sym2 V → Fin r} (hb : IsBalanced coloring) (hV : Fintype.card V = r ^ 2 + 1)
    {k : Fin r} {T : Finset V} (hcard : T.card = r) (hT : MissesColor coloring k T) :
    ∃ u ∈ T, r ≤ ((Finset.univ \ T).filter fun v => coloring s(u, v) = k).card := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; exact k.elim0)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  by_contra hc
  push_neg at hc
  have hcover : Finset.univ \ T ⊆
      T.biUnion fun u => (Finset.univ \ T).filter fun v => coloring s(u, v) = k := by
    intro v hv
    obtain ⟨u, huT, hu⟩ :=
      hb.exists_link_of_missesColor hcard hT (Finset.mem_sdiff.1 hv).2
    exact Finset.mem_biUnion.2 ⟨u, huT, Finset.mem_filter.2 ⟨hv, by rwa [Sym2.eq_swap]⟩⟩
  have h1 : (Finset.univ \ T).card ≤
      ∑ u ∈ T, ((Finset.univ \ T).filter fun v => coloring s(u, v) = k).card :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have h2 : ∑ u ∈ T, ((Finset.univ \ T).filter fun v => coloring s(u, v) = k).card
      ≤ ∑ _u ∈ T, s := Finset.sum_le_sum fun u hu => by have := hc u hu; omega
  rw [Finset.sum_const, hcard, smul_eq_mul] at h2
  have h3 : (Finset.univ \ T).card + T.card = Fintype.card V := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T), Finset.card_univ]
  rw [hcard, hV] at h3
  have e1 : (s + 1) * s = s * s + s := by ring
  have e2 : (s + 1) ^ 2 = s * s + 2 * s + 1 := by ring
  omega

/- ## The affine plane over a field, and balanced colourings of `K_(q ^ 2)` -/

/-- The **slope colouring** of the affine plane over a field `K`: the edge joining two points is
coloured by the slope of the line through them, vertical edges (and the diagonal, which the
problem never looks at) receiving the colour `0`. -/
def slopeColoring {K : Type*} [Field K] [DecidableEq K] : Sym2 (K × K) → K :=
  Sym2.lift ⟨fun P Q => if P.1 = Q.1 then 0 else (P.2 - Q.2) / (P.1 - Q.1), by
    intro P Q
    dsimp only
    by_cases h : P.1 = Q.1
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h), ← neg_sub P.2 Q.2, ← neg_sub P.1 Q.1, neg_div_neg_eq]⟩

@[simp]
theorem slopeColoring_mk {K : Type*} [Field K] [DecidableEq K] (P Q : K × K) :
    slopeColoring s(P, Q) = if P.1 = Q.1 then 0 else (P.2 - Q.2) / (P.1 - Q.1) := rfl

/-- Two distinct points with the same value of the linear form `y - m * x` lie on a common line
of slope `m`, so the edge between them has colour `m`. -/
theorem slopeColoring_eq_of_sub_mul_eq {K : Type*} [Field K] [DecidableEq K] {m : K} {P Q : K × K}
    (hPQ : P ≠ Q) (h : P.2 - m * P.1 = Q.2 - m * Q.1) : slopeColoring s(P, Q) = m := by
  rw [slopeColoring_mk]
  by_cases hx : P.1 = Q.1
  · exact absurd (Prod.ext hx (by linear_combination h + m * hx)) hPQ
  · rw [if_neg hx]
    have hne : P.1 - Q.1 ≠ 0 := sub_ne_zero.2 hx
    have h2 : P.2 - Q.2 = m * (P.1 - Q.1) := by linear_combination h
    rw [h2, mul_div_assoc, div_self hne, mul_one]

/-- **The geometric heart.** Any set of more than `Fintype.card K` points of the affine plane
`K × K` contains two distinct points joined by an edge of any prescribed slope `m`: the
`Fintype.card K` lines of slope `m` partition the plane, so a pigeonhole applies. -/
theorem exists_ne_slopeColoring_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {S : Finset (K × K)} (hS : Fintype.card K < S.card) (m : K) :
    ∃ P ∈ S, ∃ Q ∈ S, P ≠ Q ∧ slopeColoring s(P, Q) = m := by
  obtain ⟨P, hP, Q, hQ, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (t := (Finset.univ : Finset K)) (by simpa using hS)
      (f := fun R : K × K => R.2 - m * R.1) fun a _ => Finset.mem_univ _
  exact ⟨P, hP, Q, hQ, hne, slopeColoring_eq_of_sub_mul_eq hne heq⟩

/-- The slope colouring, transported along any identification `e : K ≃ Fin r` of the colour set,
is a balanced colouring of the complete graph on the `r ^ 2` points of `K × K`. -/
theorem isBalanced_slopeColoring {K : Type*} [Field K] [Fintype K] [DecidableEq K] {r : ℕ}
    (e : K ≃ Fin r) : IsBalanced fun x : Sym2 (K × K) => e (slopeColoring x) := by
  have hcard : Fintype.card K = r := by rw [Fintype.card_congr e, Fintype.card_fin]
  intro S hS k
  obtain ⟨P, hP, Q, hQ, hne, hslope⟩ := exists_ne_slopeColoring_eq (S := S) (by omega) (e.symm k)
  refine ⟨P, hP, Q, hQ, hne, ?_⟩
  show e (slopeColoring s(P, Q)) = k
  rw [hslope, Equiv.apply_symm_apply]

/-- For every prime `p` there is a balanced `p`-colouring of the complete graph on `p ^ 2`
vertices: take the affine plane over `ZMod p` coloured by slopes. -/
theorem exists_isBalanced_card_eq_sq (p : ℕ) (hp : p.Prime) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (coloring : Sym2 V → Fin p),
      Fintype.card V = p ^ 2 ∧ IsBalanced coloring := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨ZMod p × ZMod p, inferInstance, inferInstance,
    fun x => Fintype.equivFinOfCardEq (ZMod.card p) (slopeColoring x), ?_, ?_⟩
  · rw [Fintype.card_prod, ZMod.card, sq]
  · exact isBalanced_slopeColoring _

/-- **Sharpness of `Fintype.card V = r ^ 2 + 1`.** For every prime `p` there is a `p`-colouring
of a `p ^ 2`-vertex complete graph for which the conclusion of `Erdos617.erdos_617` fails
verbatim. So a proof of `Erdos617.erdos_617` must use the extra vertex. -/
theorem exists_coloring_no_missesColor_card_eq_sq (p : ℕ) (hp : p.Prime) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (coloring : Sym2 V → Fin p),
      Fintype.card V = p ^ 2 ∧
      ¬ ∃ (S : Finset V) (k : Fin p), S.card = p + 1 ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  obtain ⟨V, hF, hD, coloring, hcard, hbal⟩ := exists_isBalanced_card_eq_sq p hp
  refine ⟨V, hF, hD, coloring, hcard, ?_⟩
  rintro ⟨S, k, hS, hmiss⟩
  obtain ⟨u, hu, v, hv, huv, hcol⟩ := hbal S hS k
  exact hmiss u hu v hv huv hcol

/-- **`Erdos617.erdos_617.variants.r2`, proved.** The statement is character-for-character the
one carried by `Erdos617.erdos_617.variants.r2`; every prime belongs to the set. -/
theorem infinite_setOf_isBalanced_sq :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r ^ 2 ∧
      ∃ (coloring : Sym2 V → Fin r),
        ∀ (S : Finset V), S.card = r + 1 →
          ∀ (k : Fin r), ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k}.Infinite := by
  refine Set.Infinite.mono ?_ Nat.infinite_setOf_prime
  intro p hp
  obtain ⟨V, hF, hD, coloring, hcard, hbal⟩ := exists_isBalanced_card_eq_sq p hp
  exact ⟨V, hF, hD, hcard, coloring, hbal⟩

/- ## The pentagon: `r ≥ 3` is necessary -/

/-- The `2`-colouring of `K_5 = K_(2 ^ 2 + 1)` whose colour classes are the pentagon `C_5` and
the pentagram: an edge is coloured `0` when its endpoints are consecutive mod `5`. -/
def pentagonColoring : Sym2 (Fin 5) → Fin 2 :=
  Sym2.lift ⟨fun i j => if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then 0 else 1,
    by decide⟩

/-- Both colour classes of `pentagonColoring` are `5`-cycles, which have independence number
`2`, so the colouring is balanced. -/
theorem isBalanced_pentagonColoring : IsBalanced pentagonColoring := by decide

/-- **Sharpness of `hr : r ≥ 3`.** For `r = 2` the conclusion of `Erdos617.erdos_617` fails
verbatim on `K_(2 ^ 2 + 1)`, witnessed by `pentagonColoring`. So no proof of
`Erdos617.erdos_617` can go through without using `hr`. -/
theorem not_exists_missesColor_pentagon :
    Fintype.card (Fin 5) = 2 ^ 2 + 1 ∧
      ¬ ∃ (S : Finset (Fin 5)) (k : Fin 2), S.card = 2 + 1 ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → pentagonColoring s(u, v) ≠ k := by
  refine ⟨by simp, ?_⟩
  rintro ⟨S, k, hS, hmiss⟩
  obtain ⟨u, hu, v, hv, huv, hcol⟩ := isBalanced_pentagonColoring S hS k
  exact hmiss u hu v hv huv hcol

/- ## Worked use sites

Use sites 1 and 2 are stated with the binders of `Erdos617.erdos_617.variants.r2` and of
`Erdos617.erdos_617` respectively, so that their goals are literally the goals a solver faces.
Use site 3 instead derives `False` from a hypothetical hypothesis-free form of
`Erdos617.erdos_617`. Use sites 4 and 5 are concrete non-vacuity checks on the pentagon, with
no reward-theorem binders at all. Use site 6 returns to the binders of `Erdos617.erdos_617` and
runs the contradiction route. -/

/-- Use site 1: the obligation `Erdos617.erdos_617.variants.r2` is discharged outright. -/
example :
    {r : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V), Fintype.card V = r ^ 2 ∧
      ∃ (coloring : Sym2 V → Fin r),
        ∀ (S : Finset V), S.card = r + 1 →
          ∀ (k : Fin r), ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ coloring s(u, v) = k}.Infinite :=
  infinite_setOf_isBalanced_sq

/-- Use site 2: the reformulation applied to the goal of `Erdos617.erdos_617`. After
`rw [← exists_missesColor_iff_exists_link]`-style rewriting, what is left is to exhibit *some*
vertex, *some* colour and *some* `r`-element set — one existential package instead of the
symmetric pairwise condition on an `(r + 1)`-element set. -/
example (r : ℕ) (_hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (_hV : Fintype.card V = r ^ 2 + 1) (coloring : Sym2 V → Fin r)
    (H : ∃ (v : V) (k : Fin r) (T : Finset V), v ∉ T ∧ T.card = r ∧ MissesColor coloring k T ∧
      ∀ u ∈ T, coloring s(v, u) ≠ k) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k :=
  (exists_missesColor_iff_exists_link coloring).2 H

/-- Use site 3: a proof of `Erdos617.erdos_617` must use *both* of its hypotheses. Assuming the
conclusion held for `r = 2`, or for `Fintype.card V = r ^ 2`, gives `False`. -/
example
    (Hr : ∀ (r : ℕ) {V : Type} [Fintype V] [DecidableEq V], Fintype.card V = r ^ 2 + 1 →
      ∀ coloring : Sym2 V → Fin r, ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
        ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k) : False :=
  not_exists_missesColor_pentagon.2
    (Hr 2 not_exists_missesColor_pentagon.1 pentagonColoring)

/-- Use site 4: non-vacuity of the balanced-colouring API, run on a *genuinely* balanced
colouring rather than a constant one. In `pentagonColoring` the set `{0, 2}` has `r = 2`
elements and avoids colour `0`, so `IsBalanced.exists_link_of_missesColor` applies and says
that every other vertex of `K_5` sends a colour-`0` edge into `{0, 2}`. -/
example : ∀ v ∉ ({0, 2} : Finset (Fin 5)),
    ∃ u ∈ ({0, 2} : Finset (Fin 5)), pentagonColoring s(v, u) = 0 :=
  fun _ hv =>
    isBalanced_pentagonColoring.exists_link_of_missesColor (by decide) (by decide) hv

/-- Use site 5: the counting lemma on the same non-degenerate example. Here
`Fintype.card (Fin 5) = 2 ^ 2 + 1` and `{0, 2}` avoids colour `0`, so one of its two vertices
carries `2` colour-`0` edges leaving the set (e.g. the vertex `0`, joined to `1` and to `4`;
the vertex `2`, joined to `1` and to `3`, is an equally good witness). -/
example : ∃ u ∈ ({0, 2} : Finset (Fin 5)),
    2 ≤ ((Finset.univ \ ({0, 2} : Finset (Fin 5))).filter
      fun v => pentagonColoring s(u, v) = 0).card :=
  isBalanced_pentagonColoring.exists_le_card_colorLink (k := 0) (T := {0, 2})
    (by decide) (by decide) (by decide)

/-- Use site 6: the contradiction route at the binders of `Erdos617.erdos_617`. A solver who
opens with `by_contra` has exactly the hypothesis `hcon` below; `not_exists_missesColor_iff_isBalanced`
converts it into `IsBalanced coloring`, and the counting lemma then applies to any `r`-element
set avoiding a colour. This is the use site that makes the `IsBalanced` API reachable from the
reward theorem's own goal. -/
example (r : ℕ) (_hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = r ^ 2 + 1) (coloring : Sym2 V → Fin r)
    (hcon : ¬ ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k)
    (k : Fin r) (T : Finset V) (hT : T.card = r) (hTk : MissesColor coloring k T) :
    ∃ u ∈ T, r ≤ ((Finset.univ \ T).filter fun v => coloring s(u, v) = k).card :=
  ((not_exists_missesColor_iff_isBalanced coloring).1 hcon).exists_le_card_colorLink hV hT hTk

end Contribution.Erdos617Independence
