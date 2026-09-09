import FormalConjectures.GreensOpenProblems.«33»

/-!
# Green's Problem 33: the sharp `√2` bound, its equality cases, and the spike theorem

Green 33 asks whether the constant `√2` is *attained*: are there infinitely many `q` with a set
`A ⊆ ℤ/qℤ`, `A + A = ℤ/qℤ`, and `|A| = (√2 + o(1))√q`? The pinned file records only the trivial
`q ≤ |A|²` (constant `1`). This file proves three things, all unconditional.

* **Part I — the sharp lower bound.** Counting *unordered* sums gives `|A + A| ≤ |A|(|A|+1)/2`,
  hence `2q ≤ |A|(|A|+1)` and `|A| ≥ √(2q) - 1`. So `√2` is the true floor, and `green_33`
  reduces to the one-sided upper bound `|A|/√q < √2 + ε` (`abs_lt_iff_upper`).
* **Part II — equality is classified.** `2q = |A|(|A|+1)` forces `|A| ≤ 2`: a perfect basis is
  a Sidon set, so its `|A|(|A|-1)` nonzero differences are distinct. Hence `ℤ/qℤ` has a perfect
  basis iff `q ∈ {1, 3}` (`tight_iff`), and for `q ≥ 4` the bound improves to
  `2(q+1) ≤ |A|(|A|+1)` (`two_mul_succ_le_card_mul`).
* **Part III — the spike theorem.** With `r_A(x) = |A ∩ (x - A)|`, the energy identity
  `∑ r_A(x)² = ∑ d_A(y)²` and Cauchy–Schwarz over nonzero differences give, for some `x`,
  `(k+1)·r_A(x)·(k² + k - 2q) ≥ k(k-1)(k-3)` where `k = |A|` (`exists_spike`). A basis within
  `t` of `√(2q)` is therefore `≈ 1/(2t+1)`-symmetric about some point
  (`exists_spike_of_le_sqrt`). This is the shape of a symmetric `(q, k, 2)` difference set
  (a biplane), whose sumset is a `√2`-basis: the three known cyclic biplanes give the
  small cases, and "infinitely many biplanes" is itself open — which is why Green 33 is hard.
* **Part IV — the refined universal bound.** Pairs summing to the spike are wasted, which
  gives `2q + r_A(x) ≤ k² + k + 2`; played against the spike theorem this kills the linear
  term: **`2q ≤ |A|² + 2` for every basis** (`two_mul_le_sq_add_two`), i.e. `√(2q − 2) ≤ |A|`.
  The bound is attained at `q = 3, 9, 19` by symmetric perfect bases, and equality forces
  `|A ∩ (x − A)| ≥ |A| − 1` (`exists_rep_ge_of_eq`).
-/

open Finset
open scoped Pointwise

namespace Contribution.Green33LowerBound

variable {q : ℕ+} {A : Finset (ZMod q)}

/-- **Unordered-sum bound.** In any commutative additive group, `|A + A| ≤ |A|(|A|+1)/2`,
because the (symmetric) sum map factors through the `A.card(A.card+1)/2` unordered pairs. -/
theorem card_add_self_le_choose (A : Finset (ZMod q)) :
    (A + A).card ≤ Nat.choose (A.card + 1) 2 := by
  have hsub : A + A ⊆ A.sym2.image (Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩) := by
    intro x hx
    rw [Finset.mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine Finset.mem_image.mpr ⟨s(a, b), ?_, rfl⟩
    exact Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩
  calc (A + A).card
      ≤ (A.sym2.image _).card := Finset.card_le_card hsub
    _ ≤ A.sym2.card := Finset.card_image_le
    _ = Nat.choose (A.card + 1) 2 := Finset.card_sym2 A

/-- **The counting core.** If `A + A = ℤ/qℤ` then `2q ≤ |A|(|A|+1)`. -/
theorem two_mul_le_card_mul (hA : A + A = Finset.univ) :
    2 * (q : ℕ) ≤ A.card * (A.card + 1) := by
  have hq : (q : ℕ) ≤ Nat.choose (A.card + 1) 2 := by
    calc (q : ℕ) = Fintype.card (ZMod q) := (ZMod.card q).symm
      _ = (Finset.univ : Finset (ZMod q)).card := Finset.card_univ.symm
      _ = (A + A).card := by rw [hA]
      _ ≤ Nat.choose (A.card + 1) 2 := card_add_self_le_choose A
  rw [Nat.choose_two_right, Nat.add_sub_cancel] at hq
  have hdvd : 2 ∣ (A.card + 1) * A.card := by
    rw [mul_comm]; exact (Nat.even_mul_succ_self A.card).two_dvd
  calc 2 * (q : ℕ)
      ≤ 2 * ((A.card + 1) * A.card / 2) := by omega
    _ = (A.card + 1) * A.card := Nat.mul_div_cancel' hdvd
    _ = A.card * (A.card + 1) := by ring

/-- **The sharp lower bound.** If `A + A = ℤ/qℤ` then `√2 · √q ≤ |A| + 1`. Equivalently
`|A| ≥ √(2q) − 1`, so `|A|/√q ≥ √2 − 1/√q`: no basis beats the constant `√2`. -/
theorem sqrt_two_mul_sqrt_le (hA : A + A = Finset.univ) :
    Real.sqrt 2 * Real.sqrt q ≤ (A.card : ℝ) + 1 := by
  have hnat := two_mul_le_card_mul hA
  have hq2 : (2 * q : ℝ) ≤ ((A.card : ℝ) + 1) ^ 2 := by
    have : (2 * (q : ℕ) : ℝ) ≤ (A.card * (A.card + 1) : ℕ) := by exact_mod_cast hnat
    push_cast at this ⊢; nlinarith [this]
  have hpos : (0 : ℝ) ≤ (A.card : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt (2 * q) ≤ (A.card : ℝ) + 1 := by
    rw [show ((A.card : ℝ) + 1) = Real.sqrt (((A.card : ℝ) + 1) ^ 2) from
      (Real.sqrt_sq hpos).symm]
    exact Real.sqrt_le_sqrt hq2
  rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at hsqrt

/-- **Ratio form.** `|A|/√q ≥ √2 − 1/√q`. The `1/√q` slack vanishes as `q → ∞`, so
`liminf |A|/√q ≥ √2` over all bases: the `√2` in Green 33 is a genuine floor. -/
theorem sqrt_two_sub_le_ratio (hA : A + A = Finset.univ) :
    Real.sqrt 2 - 1 / Real.sqrt q ≤ (A.card : ℝ) / Real.sqrt q := by
  have hsq : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast q.pos)
  have h := sqrt_two_mul_sqrt_le hA
  rw [le_div_iff₀ hsq, sub_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
  linarith

/-- **Target simplification.** Since the lower bound is automatic, once `q` is large enough
(`1/√q < ε`) the two-sided closeness in `green_33` collapses to the *one-sided* upper bound
`|A|/√q < √2 + ε`. A solver need only build bases that are not too large. -/
theorem abs_lt_iff_upper (hA : A + A = Finset.univ) {ε : ℝ}
    (hε : 1 / Real.sqrt q < ε) :
    |(A.card : ℝ) / Real.sqrt q - Real.sqrt 2| < ε ↔
      (A.card : ℝ) / Real.sqrt q - Real.sqrt 2 < ε := by
  rw [abs_lt]
  constructor
  · exact fun h => h.2
  · refine fun h => ⟨?_, h⟩
    have := sqrt_two_sub_le_ratio hA
    linarith

/-- **Tightness: `√2` is not improvable.** The counting bound `2q ≤ |A|(|A|+1)` is *attained*,
so no larger constant than `√2` is a valid lower bound. Witness: `q = 3`, `A = {0, 1}`, a
perfect basis with `A + A = ℤ/3ℤ` and `2·3 = 2·3`. -/
theorem exists_tight :
    ∃ (q : ℕ+) (A : Finset (ZMod q)), A + A = Finset.univ ∧ 2 * (q : ℕ) = A.card * (A.card + 1) := by
  refine ⟨3, {0, 1}, ?_, ?_⟩
  · decide
  · decide


/- ## Part II: the sharp bound is attained only for `q ∈ {1, 3}`

A *perfect* basis (`2q = |A|(|A|+1)`) has every element of `ℤ/qℤ` as a sum in exactly one
unordered way, so it is a Sidon set; then its `|A|(|A|-1)` ordered nonzero differences are
distinct, forcing `|A|(|A|-1) ≤ q - 1`. Together with `2q = |A|(|A|+1)` this gives `|A| ≤ 2`. -/

/-- In a perfect basis the unordered sum map is injective on `A.sym2` (a Sidon set). -/
theorem sum_injOn_sym2_of_tight (hA : A + A = Finset.univ)
    (ht : 2 * (q : ℕ) = A.card * (A.card + 1)) :
    Set.InjOn (Sym2.lift ⟨fun a b : ZMod q => a + b, fun a b => add_comm a b⟩)
      (A.sym2 : Set (Sym2 (ZMod q))) := by
  have hsub : A + A ⊆ A.sym2.image
      (Sym2.lift ⟨fun a b : ZMod q => a + b, fun a b => add_comm a b⟩) := by
    intro x hx
    rw [Finset.mem_add] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact Finset.mem_image.mpr ⟨s(a, b), Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, rfl⟩
  have hchoose : Nat.choose (A.card + 1) 2 = (q : ℕ) := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have : (A.card + 1) * A.card = 2 * (q : ℕ) := by rw [ht]; ring
    omega
  apply Finset.card_image_iff.mp
  apply le_antisymm Finset.card_image_le
  calc A.sym2.card = Nat.choose (A.card + 1) 2 := Finset.card_sym2 A
    _ = (q : ℕ) := hchoose
    _ = Fintype.card (ZMod q) := (ZMod.card q).symm
    _ = (Finset.univ : Finset (ZMod q)).card := Finset.card_univ.symm
    _ = (A + A).card := by rw [hA]
    _ ≤ (A.sym2.image _).card := Finset.card_le_card hsub

/-- In a perfect basis all ordered differences `a - b` with `a ≠ b` are distinct. -/
theorem sub_injOn_offDiag_of_tight (hA : A + A = Finset.univ)
    (ht : 2 * (q : ℕ) = A.card * (A.card + 1)) :
    Set.InjOn (fun p : ZMod q × ZMod q => p.1 - p.2) (A.offDiag : Set (ZMod q × ZMod q)) := by
  have hinj := sum_injOn_sym2_of_tight hA ht
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  rw [Finset.mem_coe, Finset.mem_offDiag] at hab hcd
  simp only at h hab hcd
  have hsum : a + d = c + b := by linear_combination h
  have h1 : s(a, d) ∈ (A.sym2 : Set (Sym2 (ZMod q))) := by
    rw [Finset.mem_coe]; exact Finset.mk_mem_sym2_iff.mpr ⟨hab.1, hcd.2.1⟩
  have h2 : s(c, b) ∈ (A.sym2 : Set (Sym2 (ZMod q))) := by
    rw [Finset.mem_coe]; exact Finset.mk_mem_sym2_iff.mpr ⟨hcd.1, hab.2.1⟩
  have h3 := hinj h1 h2 (by simpa using hsum)
  rw [Sym2.eq_iff] at h3
  rcases h3 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd rfl hab.2.2

/-- **Equality is rare.** If `A + A = ℤ/qℤ` and `2q = |A|(|A|+1)` then `|A| ≤ 2`. -/
theorem card_le_two_of_tight (hA : A + A = Finset.univ)
    (ht : 2 * (q : ℕ) = A.card * (A.card + 1)) : A.card ≤ 2 := by
  have hinj := sub_injOn_offDiag_of_tight hA ht
  have himg : A.offDiag.image (fun p : ZMod q × ZMod q => p.1 - p.2) ⊆
      (Finset.univ : Finset (ZMod q)).erase 0 := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hy
    rw [Finset.mem_offDiag] at hab
    exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hab.2.2, Finset.mem_univ _⟩
  have hcard : A.offDiag.card ≤ (q : ℕ) - 1 := by
    calc A.offDiag.card
        = (A.offDiag.image (fun p : ZMod q × ZMod q => p.1 - p.2)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((Finset.univ : Finset (ZMod q)).erase 0).card := Finset.card_le_card himg
      _ = (q : ℕ) - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [Finset.offDiag_card] at hcard
  have hq : 1 ≤ (q : ℕ) := q.pos
  have ht' : 2 * (q : ℕ) = A.card * A.card + A.card := by rw [ht]; ring
  have h1 : A.card ≤ A.card * A.card := Nat.le_mul_self _
  by_contra hk
  push Not at hk
  have h3 : 3 * A.card ≤ A.card * A.card := Nat.mul_le_mul_right _ hk
  omega

/-- For `q ≥ 4` the sharp bound is strict; by parity of `|A|(|A|+1)` it improves to
`2(q+1) ≤ |A|(|A|+1)`. -/
theorem two_mul_succ_le_card_mul (hA : A + A = Finset.univ) (hq : 4 ≤ (q : ℕ)) :
    2 * ((q : ℕ) + 1) ≤ A.card * (A.card + 1) := by
  have h := two_mul_le_card_mul hA
  obtain ⟨m, hm⟩ := Nat.even_mul_succ_self A.card
  rcases h.lt_or_eq with hlt | heq
  · omega
  · have hk := card_le_two_of_tight hA heq
    have : A.card * (A.card + 1) ≤ 2 * (2 + 1) := Nat.mul_le_mul hk (by omega)
    omega

/-- **Complete classification of equality.** `ℤ/qℤ` has a perfect basis iff `q = 1` or `q = 3`. -/
theorem tight_iff :
    (∃ A : Finset (ZMod q), A + A = Finset.univ ∧ 2 * (q : ℕ) = A.card * (A.card + 1)) ↔
      (q : ℕ) = 1 ∨ (q : ℕ) = 3 := by
  constructor
  · rintro ⟨A, hA, ht⟩
    have hk := card_le_two_of_tight hA ht
    have hq := q.pos
    obtain ⟨k, hk'⟩ : ∃ k, A.card = k := ⟨_, rfl⟩
    rw [hk'] at hk ht
    interval_cases k <;> omega
  · rintro (h | h)
    · have : q = 1 := PNat.eq h
      subst this
      exact ⟨{0}, by decide, by decide⟩
    · have : q = 3 := PNat.eq h
      subst this
      exact ⟨{0, 1}, by decide, by decide⟩


/- ## Part III: additive energy and the spike theorem

Write `r_A(x) = #{(a,b) ∈ A² : a + b = x}` and `d_A(y) = #{(a,b) ∈ A² : a - b = y}`. The energy
identity `∑ r_A(x)² = ∑ d_A(y)²` (from `a + b = c + d ⟺ a - d = c - b`) and Cauchy–Schwarz over
the `q - 1` nonzero differences force `∑ r_A(x)² ≥ |A|² + |A|²(|A|-1)²/(q-1)`. A basis close to
the sharp bound has `r_A ≈ 2` on average, so this excess energy must sit on a *spike*: some `x`
with `r_A(x) = |A ∩ (x - A)|` large, i.e. `A` is approximately symmetric about `x/2`. -/

/-- Ordered representation count `r_A(x) = #{(a, b) ∈ A × A : a + b = x}`. -/
def rep (A : Finset (ZMod q)) (x : ZMod q) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 + p.2 = x)).card

/-- Ordered difference count `d_A(y) = #{(a, b) ∈ A × A : a - b = y}`. -/
def dif (A : Finset (ZMod q)) (y : ZMod q) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 - p.2 = y)).card

/-- `r_A(x)` is the size of `A ∩ (x - A)`: the symmetry defect of `A` about `x/2`. -/
theorem rep_eq_card_filter (A : Finset (ZMod q)) (x : ZMod q) :
    rep A x = (A.filter (fun a => x - a ∈ A)).card := by
  unfold rep
  apply Finset.card_nbij' (fun p => p.1) (fun a => (a, x - a))
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h ⊢
    refine ⟨h.1.1, ?_⟩
    rw [← h.2, add_sub_cancel_left]
    exact h.1.2
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at ha ⊢
    exact ⟨⟨ha.1, ha.2⟩, add_sub_cancel a x⟩
  · rintro ⟨a, b⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h
    simp only
    rw [← h.2, add_sub_cancel_left]
  · intro a _
    rfl

/-- Fibre-count identity: `∑_x #{p ∈ S : f p = x}² = #{(p, p') ∈ S² : f p = f p'}`. -/
theorem sum_sq_card_filter_eq {α β : Type*} [DecidableEq β] [Fintype β] (S : Finset α)
    (f : α → β) :
    ∑ x : β, (S.filter (fun p => f p = x)).card ^ 2
      = ((S ×ˢ S).filter (fun pp => f pp.1 = f pp.2)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun pp : α × α => f pp.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sq, ← Finset.card_product, Finset.filter_filter, ← Finset.filter_product]
  congr 1
  ext ⟨p, p'⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hp, hp'⟩, hx, hx'⟩
    exact ⟨⟨hp, hp'⟩, hx.trans hx'.symm, hx⟩
  · rintro ⟨⟨hp, hp'⟩, he, hx⟩
    exact ⟨⟨hp, hp'⟩, hx, he.symm.trans hx⟩

/-- **Energy identity.** `∑_x r_A(x)² = ∑_y d_A(y)²`, via `a + b = c + d ⟺ a - d = c - b`. -/
theorem sum_sq_rep_eq_sum_sq_dif (A : Finset (ZMod q)) :
    ∑ x : ZMod q, rep A x ^ 2 = ∑ y : ZMod q, dif A y ^ 2 := by
  unfold rep dif
  rw [show (∑ x : ZMod q, ((A ×ˢ A).filter (fun p => p.1 + p.2 = x)).card ^ 2) = _ from
      sum_sq_card_filter_eq (A ×ˢ A) (fun p => p.1 + p.2),
    show (∑ y : ZMod q, ((A ×ˢ A).filter (fun p => p.1 - p.2 = y)).card ^ 2) = _ from
      sum_sq_card_filter_eq (A ×ˢ A) (fun p => p.1 - p.2)]
  apply Finset.card_nbij' (fun pp => ((pp.1.1, pp.2.2), (pp.2.1, pp.1.2)))
    (fun pp => ((pp.1.1, pp.2.2), (pp.2.1, pp.1.2)))
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h ⊢
    obtain ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, he⟩ := h
    exact ⟨⟨⟨ha, hd⟩, ⟨hc, hb⟩⟩, by linear_combination he⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h ⊢
    obtain ⟨⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩, he⟩ := h
    exact ⟨⟨⟨ha, hd⟩, ⟨hc, hb⟩⟩, by linear_combination he⟩
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    rfl
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    rfl

/-- `∑_x r_A(x) = |A|²`. -/
theorem sum_rep (A : Finset (ZMod q)) : ∑ x : ZMod q, rep A x = A.card * A.card := by
  unfold rep
  rw [← Finset.card_product]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun p : ZMod q × ZMod q => p.1 + p.2)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

/-- `∑_y d_A(y) = |A|²`. -/
theorem sum_dif (A : Finset (ZMod q)) : ∑ y : ZMod q, dif A y = A.card * A.card := by
  unfold dif
  rw [← Finset.card_product]
  exact (Finset.card_eq_sum_card_fiberwise (f := fun p : ZMod q × ZMod q => p.1 - p.2)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)).symm

/-- `d_A(0) = |A|`. -/
theorem dif_zero (A : Finset (ZMod q)) : dif A 0 = A.card := by
  unfold dif
  rw [← Finset.diag_card A]
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag, sub_eq_zero]
  constructor
  · rintro ⟨⟨ha, _⟩, h⟩
    exact ⟨ha, h⟩
  · rintro ⟨ha, rfl⟩
    exact ⟨⟨ha, ha⟩, rfl⟩

/-- The nonzero differences: `∑_{y ≠ 0} d_A(y) = |A|² - |A|`. -/
theorem sum_dif_erase_zero (A : Finset (ZMod q)) :
    ∑ y ∈ (Finset.univ : Finset (ZMod q)).erase 0, dif A y = A.card * A.card - A.card := by
  have h := Finset.add_sum_erase (Finset.univ : Finset (ZMod q)) (dif A) (Finset.mem_univ 0)
  rw [sum_dif, dif_zero] at h
  omega

/-- Cauchy–Schwarz over the `q - 1` nonzero differences. -/
theorem sq_sum_dif_le (A : Finset (ZMod q)) :
    (A.card * A.card - A.card) ^ 2 ≤
      ((q : ℕ) - 1) * ∑ y ∈ (Finset.univ : Finset (ZMod q)).erase 0, dif A y ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod q)).erase 0) (f := dif A)
  rwa [sum_dif_erase_zero, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card] at h

/-- **Energy lower bound.** `(q-1) ∑_x r_A(x)² ≥ (|A|² - |A|)² + (q-1)|A|²`. -/
theorem energy_lower (A : Finset (ZMod q)) :
    (A.card * A.card - A.card) ^ 2 + ((q : ℕ) - 1) * A.card ^ 2
      ≤ ((q : ℕ) - 1) * ∑ x : ZMod q, rep A x ^ 2 := by
  rw [sum_sq_rep_eq_sum_sq_dif,
    ← Finset.add_sum_erase (Finset.univ : Finset (ZMod q)) (fun y => dif A y ^ 2)
      (Finset.mem_univ 0),
    dif_zero, mul_add]
  have := sq_sum_dif_le A
  omega

/-- Every element has a representation. -/
theorem one_le_rep (hA : A + A = Finset.univ) (x : ZMod q) : 1 ≤ rep A x := by
  have hx : x ∈ A + A := hA ▸ Finset.mem_univ x
  rw [Finset.mem_add] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact Finset.card_pos.mpr
    ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩

/-- An element that is not a double `a + a` has at least two ordered representations. -/
theorem two_le_rep_of_not_mem_double {x : ZMod q} (hx : x ∉ A.image (fun a => a + a))
    (h1 : 1 ≤ rep A x) : 2 ≤ rep A x := by
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp h1
  have hab' := hab
  rw [Finset.mem_filter, Finset.mem_product] at hab
  obtain ⟨⟨ha, hb⟩, hs⟩ := hab
  have hne : a ≠ b := by
    rintro rfl
    exact hx (Finset.mem_image.mpr ⟨a, ha, hs⟩)
  have hba : (b, a) ∈ (A ×ˢ A).filter (fun p => p.1 + p.2 = x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, by rw [← hs]; exact add_comm b a⟩
  exact Finset.one_lt_card.mpr ⟨(a, b), hab', (b, a), hba, fun h => hne (Prod.mk.inj h).1⟩

/-- **Spike theorem (exact form).** If `A + A = ℤ/qℤ`, `k = |A|`, and `M = max_x r_A(x)`, then
`k²(k-1)² ≤ (q-1)·(M·(k² + k - 2q) + k² - k)`. Here `k² + k - 2q ≥ 0` is the excess over the
sharp bound, so a basis close to the bound must have a large spike `M`. -/
theorem exists_rep_spike (hA : A + A = Finset.univ) :
    ∃ x : ZMod q,
      (A.card : ℤ) ^ 2 * ((A.card : ℤ) - 1) ^ 2 ≤
        ((q : ℤ) - 1) *
          ((rep A x : ℤ) * ((A.card : ℤ) ^ 2 + A.card - 2 * q) + A.card ^ 2 - A.card) := by
  obtain ⟨x₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (rep A) Finset.univ_nonempty
  refine ⟨x₀, ?_⟩
  -- pointwise: `r² + 2M ≤ M·r + 2r + (M-1)·[x is a double]`, using `1 ≤ r ≤ M`
  have hpt : ∀ x : ZMod q,
      rep A x ^ 2 + 2 * rep A x₀ ≤ rep A x₀ * rep A x + 2 * rep A x +
        (rep A x₀ - 1) * (if x ∈ A.image (fun a => a + a) then 1 else 0) := by
    intro x
    have h1 : 1 ≤ rep A x := one_le_rep hA x
    have hxM : rep A x ≤ rep A x₀ := hmax x (Finset.mem_univ _)
    split_ifs with hx
    · have h1M : 1 ≤ rep A x₀ := h1.trans hxM
      obtain ⟨t, ht⟩ : ∃ t, rep A x₀ = t + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1M).symm⟩
      rw [ht, Nat.add_sub_cancel]
      rw [ht] at hxM
      nlinarith [Nat.mul_le_mul_right (rep A x - 1) hxM, Nat.sub_add_cancel h1]
    · have h2 : 2 ≤ rep A x := two_le_rep_of_not_mem_double hx h1
      nlinarith [Nat.mul_le_mul_right (rep A x - 2) hxM, Nat.sub_add_cancel h2]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (ZMod q))) => hpt x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_rep,
    Finset.sum_const, Finset.card_univ, ZMod.card, Finset.sum_boole, smul_eq_mul] at hsum
  have hc : ((Finset.univ : Finset (ZMod q)).filter
      (fun x => x ∈ A.image (fun a => a + a))).card ≤ A.card :=
    (Finset.card_le_card (fun x hx => (Finset.mem_filter.mp hx).2)).trans Finset.card_image_le
  have hE := energy_lower A
  have hq : 1 ≤ (q : ℕ) := q.pos
  have hk1 : A.card ≤ A.card * A.card := Nat.le_mul_self _
  have hM1 : 1 ≤ rep A x₀ := one_le_rep hA x₀
  have hkq := two_mul_le_card_mul hA
  -- move to `ℤ`
  have hM1z : (1 : ℤ) ≤ rep A x₀ := by exact_mod_cast hM1
  have hsum' : (∑ x : ZMod q, (rep A x : ℤ) ^ 2) + 2 * (q : ℤ) * rep A x₀ ≤
      (rep A x₀ : ℤ) * (A.card * A.card) + 2 * (A.card * A.card) +
        ((rep A x₀ : ℤ) - 1) * A.card := by
    have := hsum
    zify [hM1] at this
    have hcz : (((Finset.univ : Finset (ZMod q)).filter
        (fun x => x ∈ A.image (fun a => a + a))).card : ℤ) ≤ A.card := by exact_mod_cast hc
    have := mul_le_mul_of_nonneg_left hcz (sub_nonneg.mpr hM1z)
    linarith
  have hE' : ((A.card : ℤ) * A.card - A.card) ^ 2 + ((q : ℤ) - 1) * (A.card : ℤ) ^ 2
      ≤ ((q : ℤ) - 1) * ∑ x : ZMod q, (rep A x : ℤ) ^ 2 := by
    have := hE
    zify [hq, hk1] at this
    exact this
  have hq' : (0 : ℤ) ≤ (q : ℤ) - 1 := by
    have : (1 : ℤ) ≤ q := by exact_mod_cast hq
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hsum' hq', hE']

/-- **Spike theorem (symmetry-defect form).** Let `k = |A|` and `D = k² + k - 2q ≥ 0` be the
excess of `A` over the sharp bound. Then some `x` has
`(k+1) · |A ∩ (x - A)| · D ≥ k(k-1)(k-3)`, i.e. `|A ∩ (x - A)| ≳ k²/D`. In particular a basis
with `D = O(k)` (within an additive constant of `√(2q)`) is symmetric about some `x/2` on a
positive proportion of its elements: this is exactly the shape of a symmetric biplane. -/
theorem exists_spike (hA : A + A = Finset.univ) :
    ∃ x : ZMod q,
      (A.card : ℤ) * ((A.card : ℤ) - 1) * ((A.card : ℤ) - 3) ≤
        ((A.card : ℤ) + 1) * (A.filter (fun a => x - a ∈ A)).card *
          ((A.card : ℤ) ^ 2 + A.card - 2 * q) := by
  obtain ⟨x, hx⟩ := exists_rep_spike hA
  refine ⟨x, ?_⟩
  rw [← rep_eq_card_filter]
  have hkq : ((2 * (q : ℕ) : ℕ) : ℤ) ≤ ((A.card * (A.card + 1) : ℕ) : ℤ) := by
    exact_mod_cast two_mul_le_card_mul hA
  push_cast at hkq
  have hq : (1 : ℤ) ≤ q := by exact_mod_cast q.pos
  have hM : (0 : ℤ) ≤ rep A x := by positivity
  have hk0 : (0 : ℤ) ≤ A.card := by positivity
  have hk1 : (1 : ℤ) ≤ A.card := by
    by_contra h
    have : (A.card : ℤ) = 0 := by omega
    rw [this] at hkq
    linarith
  have hD : (0 : ℤ) ≤ (A.card : ℤ) ^ 2 + A.card - 2 * q := by nlinarith
  have hX : (0 : ℤ) ≤ (rep A x : ℤ) * ((A.card : ℤ) ^ 2 + A.card - 2 * q) +
      (A.card : ℤ) ^ 2 - A.card := by nlinarith [mul_nonneg hM hD]
  have h2 : 2 * ((q : ℤ) - 1) ≤ (A.card : ℤ) ^ 2 + A.card - 2 := by linarith
  have h3 : 2 * ((A.card : ℤ) ^ 2 * ((A.card : ℤ) - 1) ^ 2) ≤
      ((A.card : ℤ) ^ 2 + A.card) *
        ((rep A x : ℤ) * ((A.card : ℤ) ^ 2 + A.card - 2 * q) + (A.card : ℤ) ^ 2 - A.card) := by
    nlinarith [mul_le_mul_of_nonneg_right h2 hX]
  by_contra hneg
  push Not at hneg
  have := mul_lt_mul_of_pos_left hneg (by linarith : (0 : ℤ) < A.card)
  nlinarith [h3, this]

/-- **Spike theorem, asymptotic form.** If `|A| ≤ √2·√q + t` with `t ≥ 0`, then some `x` has
`|A ∩ (x - A)| ≥ k(k-1)(k-3) / ((k+1)((2t+1)k + t² + 2t)) ≈ k/(2t+1)`, `k = |A|`. So any basis
within `t` of the sharp bound `√(2q)` is `1/(2t+1)`-symmetric about some point. -/
theorem exists_spike_of_le_sqrt (hA : A + A = Finset.univ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (A.card : ℝ) ≤ Real.sqrt 2 * Real.sqrt q + t) :
    ∃ x : ZMod q,
      (A.card : ℝ) * ((A.card : ℝ) - 1) * ((A.card : ℝ) - 3) ≤
        ((A.card : ℝ) + 1) * (A.filter (fun a => x - a ∈ A)).card *
          ((2 * t + 1) * A.card + t ^ 2 + 2 * t) := by
  obtain ⟨x, hx⟩ := exists_spike hA
  refine ⟨x, ?_⟩
  have hx' : (A.card : ℝ) * ((A.card : ℝ) - 1) * ((A.card : ℝ) - 3) ≤
      ((A.card : ℝ) + 1) * (A.filter (fun a => x - a ∈ A)).card *
        ((A.card : ℝ) ^ 2 + A.card - 2 * q) := by exact_mod_cast hx
  have hs : Real.sqrt 2 * Real.sqrt q ≤ (A.card : ℝ) + 1 := sqrt_two_mul_sqrt_le hA
  have hs2 : (Real.sqrt 2 * Real.sqrt q) ^ 2 = 2 * q := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  have hk0 : (0 : ℝ) ≤ A.card := by positivity
  have hD : (A.card : ℝ) ^ 2 + A.card - 2 * q ≤ (2 * t + 1) * A.card + t ^ 2 + 2 * t := by
    have h1 : ((A.card : ℝ)) ^ 2 ≤ (Real.sqrt 2 * Real.sqrt q + t) ^ 2 :=
      pow_le_pow_left₀ hk0 ht 2
    have h2 := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 2 * t)
    nlinarith [h1, h2, hs2]
  have hnn : (0 : ℝ) ≤ ((A.card : ℝ) + 1) * (A.filter (fun a => x - a ∈ A)).card := by
    positivity
  exact hx'.trans (mul_le_mul_of_nonneg_left hD hnn)


/- ## Part IV: the refined universal bound `2q ≤ |A|² + 2`

The spike theorem and a "wasted pairs" count pull in opposite directions: every unordered pair
summing to the spike `x` produces the *same* element, so `2q ≤ k² + k − r_A(x) + 2`; while the
spike theorem forces `r_A(x)` large when `k² + k − 2q` is small. Together they eliminate the
linear term of the sharp bound: `2q ≤ |A|² + 2` for **every** basis. This is the bound that
symmetric sets satisfy trivially, now proved universally. Equality forces `r_A(x) ≥ |A| − 1`. -/

/-- **Wasted pairs.** All unordered pairs summing to `x` collapse to the single element `x`, so
`2q + r_A(x) ≤ |A|(|A|+1) + 2`. -/
theorem two_mul_add_rep_le (hA : A + A = Finset.univ) (x : ZMod q) :
    2 * (q : ℕ) + rep A x ≤ A.card * (A.card + 1) + 2 := by
  set f : Sym2 (ZMod q) → ZMod q :=
    Sym2.lift ⟨fun a b : ZMod q => a + b, fun a b => add_comm a b⟩ with hf
  set P := A.sym2.filter (fun p => f p = x) with hP
  have hsub : A + A ⊆ (A.sym2 \ P).image f ∪ {x} := by
    intro y hy
    rw [Finset.mem_add] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    by_cases hx : a + b = x
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hx)
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s(a, b), ?_, rfl⟩)
      rw [Finset.mem_sdiff, hP, Finset.mem_filter]
      exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨ha, hb⟩, fun h => hx h.2⟩
  have hPsub : P ⊆ A.sym2 := Finset.filter_subset _ _
  have h1 : (q : ℕ) + P.card ≤ Nat.choose (A.card + 1) 2 + 1 := by
    have hq : (q : ℕ) ≤ (A.sym2 \ P).card + 1 := by
      calc (q : ℕ) = Fintype.card (ZMod q) := (ZMod.card q).symm
        _ = (Finset.univ : Finset (ZMod q)).card := Finset.card_univ.symm
        _ = (A + A).card := by rw [hA]
        _ ≤ ((A.sym2 \ P).image f ∪ {x}).card := Finset.card_le_card hsub
        _ ≤ ((A.sym2 \ P).image f).card + ({x} : Finset (ZMod q)).card :=
            Finset.card_union_le _ _
        _ ≤ (A.sym2 \ P).card + 1 := by
            rw [Finset.card_singleton]; exact Nat.add_le_add_right Finset.card_image_le _
    rw [Finset.card_sdiff_of_subset hPsub, Finset.card_sym2] at hq
    have hle := Finset.card_le_card hPsub
    rw [Finset.card_sym2] at hle
    omega
  have h2 : rep A x ≤ 2 * P.card := by
    unfold rep
    set R := (A ×ˢ A).filter (fun p : ZMod q × ZMod q => p.1 + p.2 = x) with hR
    have himg : R.image (fun p : ZMod q × ZMod q => s(p.1, p.2)) ⊆ P := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hy
      rw [hR, Finset.mem_filter, Finset.mem_product] at hab
      rw [hP, Finset.mem_filter]
      exact ⟨Finset.mk_mem_sym2_iff.mpr ⟨hab.1.1, hab.1.2⟩, hab.2⟩
    have hfib : ∀ y ∈ R.image (fun p : ZMod q × ZMod q => s(p.1, p.2)),
        (R.filter (fun p => s(p.1, p.2) = y)).card ≤ 2 := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨⟨a, b⟩, -, rfl⟩ := hy
      have hsub2 : R.filter (fun p : ZMod q × ZMod q => s(p.1, p.2) = s(a, b)) ⊆
          {(a, b), (b, a)} := by
        rintro ⟨c, d⟩ hcd
        rw [Finset.mem_filter] at hcd
        have h := hcd.2
        simp only at h
        rw [Sym2.eq_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.card_le_card hsub2).trans Finset.card_le_two
    calc R.card ≤ 2 * (R.image (fun p : ZMod q × ZMod q => s(p.1, p.2))).card :=
          Finset.card_le_mul_card_image R 2 hfib
      _ ≤ 2 * P.card := Nat.mul_le_mul_left _ (Finset.card_le_card himg)
  have hchoose : 2 * Nat.choose (A.card + 1) 2 = A.card * (A.card + 1) := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
    have hdvd : 2 ∣ (A.card + 1) * A.card := by
      rw [mul_comm]; exact (Nat.even_mul_succ_self A.card).two_dvd
    rw [Nat.mul_div_cancel' hdvd]; ring
  omega

/-- **The refined universal bound.** If `A + A = ℤ/qℤ` then `2q ≤ |A|² + 2`. The linear term of
`2q ≤ |A|(|A|+1)` is gone: no basis does better than a symmetric one. -/
theorem two_mul_le_sq_add_two (hA : A + A = Finset.univ) : 2 * (q : ℕ) ≤ A.card ^ 2 + 2 := by
  obtain ⟨x, hx⟩ := exists_rep_spike hA
  have hw := two_mul_add_rep_le hA x
  have hkq := two_mul_le_card_mul hA
  have hw' : (2 * (q : ℕ) : ℤ) + rep A x ≤ (A.card : ℤ) * (A.card + 1) + 2 := by
    exact_mod_cast hw
  have hkq' : (2 * (q : ℕ) : ℤ) ≤ (A.card : ℤ) * (A.card + 1) := by exact_mod_cast hkq
  by_contra hcon
  push Not at hcon
  have hcon' : (A.card : ℤ) ^ 2 + 3 ≤ 2 * (q : ℤ) := by
    have : A.card ^ 2 + 3 ≤ 2 * (q : ℕ) := hcon
    exact_mod_cast this
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (A.card : ℤ) ^ 2 + A.card - 2 * q = t := by
    refine Int.eq_ofNat_of_zero_le ?_
    linarith
  obtain ⟨e, he⟩ : ∃ e : ℕ, (A.card : ℤ) - 3 - t = e := by
    refine Int.eq_ofNat_of_zero_le ?_
    linarith
  have hk : (A.card : ℤ) = e + 3 + t := by linarith
  have hM : (rep A x : ℤ) ≤ t + 2 := by linarith
  have hq : 2 * ((q : ℤ) - 1) = (A.card : ℤ) ^ 2 + A.card - t - 2 := by linarith
  have hq1 : (0 : ℤ) ≤ (q : ℤ) - 1 := by
    have : (1 : ℤ) ≤ q := by exact_mod_cast q.pos
    linarith
  have hD0 : (0 : ℤ) ≤ (t : ℤ) := by positivity
  rw [ht] at hx
  have step1 : (A.card : ℤ) ^ 2 * ((A.card : ℤ) - 1) ^ 2 ≤
      ((q : ℤ) - 1) * (((t : ℤ) + 2) * t + (A.card : ℤ) ^ 2 - A.card) := by
    refine hx.trans (mul_le_mul_of_nonneg_left ?_ hq1)
    nlinarith [mul_le_mul_of_nonneg_right hM hD0]
  have step2 : 2 * ((A.card : ℤ) ^ 2 * ((A.card : ℤ) - 1) ^ 2) ≤
      ((A.card : ℤ) ^ 2 + A.card - t - 2) * (((t : ℤ) + 2) * t + (A.card : ℤ) ^ 2 - A.card) := by
    have h2 : 2 * (((q : ℤ) - 1) * (((t : ℤ) + 2) * t + (A.card : ℤ) ^ 2 - A.card)) =
        (2 * ((q : ℤ) - 1)) * (((t : ℤ) + 2) * t + (A.card : ℤ) ^ 2 - A.card) := by ring
    rw [hq] at h2
    linarith [mul_le_mul_of_nonneg_left step1 (by norm_num : (0 : ℤ) ≤ 2), h2]
  rw [hk] at step2
  have key : (((e : ℤ) + 3 + t) ^ 2 + ((e : ℤ) + 3 + t) - t - 2) *
      (((t : ℤ) + 2) * t + ((e : ℤ) + 3 + t) ^ 2 - ((e : ℤ) + 3 + t)) +
      (12 + 14 * (t : ℤ) + 6 * (t : ℤ) ^ 2 + (t : ℤ) ^ 3 + 28 * (e : ℤ) + 37 * (e : ℤ) * t +
        15 * (e : ℤ) * (t : ℤ) ^ 2 + 2 * (e : ℤ) * (t : ℤ) ^ 3 + 23 * (e : ℤ) ^ 2 +
        23 * (e : ℤ) ^ 2 * t + 5 * (e : ℤ) ^ 2 * (t : ℤ) ^ 2 + 8 * (e : ℤ) ^ 3 +
        4 * (e : ℤ) ^ 3 * t + (e : ℤ) ^ 4)
      = 2 * (((e : ℤ) + 3 + t) ^ 2 * (((e : ℤ) + 3 + t) - 1) ^ 2) := by ring
  have hpos : (0 : ℤ) < 12 + 14 * (t : ℤ) + 6 * (t : ℤ) ^ 2 + (t : ℤ) ^ 3 + 28 * (e : ℤ) +
      37 * (e : ℤ) * t + 15 * (e : ℤ) * (t : ℤ) ^ 2 + 2 * (e : ℤ) * (t : ℤ) ^ 3 +
      23 * (e : ℤ) ^ 2 + 23 * (e : ℤ) ^ 2 * t + 5 * (e : ℤ) ^ 2 * (t : ℤ) ^ 2 +
      8 * (e : ℤ) ^ 3 + 4 * (e : ℤ) ^ 3 * t + (e : ℤ) ^ 4 := by positivity
  linarith [step2, key, hpos]

/-- **Real form.** Every basis satisfies `√(2q − 2) ≤ |A|`, improving `√(2q) − 1 ≤ |A|`. -/
theorem sqrt_two_mul_sub_two_le (hA : A + A = Finset.univ) :
    Real.sqrt (2 * q - 2) ≤ A.card := by
  have h := two_mul_le_sq_add_two hA
  have h' : (2 * (q : ℝ) - 2) ≤ (A.card : ℝ) ^ 2 := by
    have : ((2 * (q : ℕ) : ℕ) : ℝ) ≤ ((A.card ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  calc Real.sqrt (2 * q - 2) ≤ Real.sqrt ((A.card : ℝ) ^ 2) := Real.sqrt_le_sqrt h'
    _ = A.card := Real.sqrt_sq (by positivity)

/-- **Equality forces near-total symmetry.** If `2q = |A|² + 2` and `|A| ≥ 3`, some `x` has
`|A ∩ (x − A)| ≥ |A| − 1`. (Known equality cases: `q = 3, 9, 19`, all symmetric perfect bases.) -/
theorem exists_rep_ge_of_eq (hA : A + A = Finset.univ) (heq : 2 * (q : ℕ) = A.card ^ 2 + 2)
    (hk : 3 ≤ A.card) : ∃ x : ZMod q, A.card - 1 ≤ (A.filter (fun a => x - a ∈ A)).card := by
  obtain ⟨x, hx⟩ := exists_rep_spike hA
  refine ⟨x, ?_⟩
  rw [← rep_eq_card_filter]
  have heq' : (2 * (q : ℕ) : ℤ) = (A.card : ℤ) ^ 2 + 2 := by exact_mod_cast heq
  have hk' : (3 : ℤ) ≤ A.card := by exact_mod_cast hk
  have hD : (A.card : ℤ) ^ 2 + A.card - 2 * q = A.card - 2 := by linarith
  have hq : 2 * ((q : ℤ) - 1) = (A.card : ℤ) ^ 2 := by linarith
  rw [hD] at hx
  have h2 : 2 * ((A.card : ℤ) ^ 2 * ((A.card : ℤ) - 1) ^ 2) ≤
      (A.card : ℤ) ^ 2 * ((rep A x : ℤ) * ((A.card : ℤ) - 2) + (A.card : ℤ) ^ 2 - A.card) := by
    have h5 : 2 * (((q : ℤ) - 1) * ((rep A x : ℤ) * ((A.card : ℤ) - 2) + (A.card : ℤ) ^ 2 - A.card))
        = (2 * ((q : ℤ) - 1)) * ((rep A x : ℤ) * ((A.card : ℤ) - 2) + (A.card : ℤ) ^ 2 - A.card) := by
      ring
    rw [hq] at h5
    linarith [mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℤ) ≤ 2), h5]
  -- h2 : 2 k²(k−1)² ≤ k² (M(k−2) + k² − k)  ⟹  2(k−1)² ≤ M(k−2) + k² − k
  have hkpos : (0 : ℤ) < (A.card : ℤ) ^ 2 := by positivity
  have h3 : 2 * ((A.card : ℤ) - 1) ^ 2 ≤
      (rep A x : ℤ) * ((A.card : ℤ) - 2) + (A.card : ℤ) ^ 2 - A.card := by
    by_contra hneg
    push Not at hneg
    have := mul_lt_mul_of_pos_left hneg hkpos
    nlinarith [h2, this]
  by_contra hneg
  push Not at hneg
  have hneg' : (rep A x : ℤ) ≤ A.card - 2 := by
    have : rep A x + 1 ≤ A.card - 1 := hneg
    have h4 : rep A x + 2 ≤ A.card := by omega
    have : ((rep A x + 2 : ℕ) : ℤ) ≤ A.card := by exact_mod_cast h4
    push_cast at this; linarith
  nlinarith [mul_le_mul_of_nonneg_right hneg' (by linarith : (0 : ℤ) ≤ (A.card : ℤ) - 2)]

end Contribution.Green33LowerBound
