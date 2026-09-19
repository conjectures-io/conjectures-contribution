import Mathlib
import FormalConjectures.ErdosProblems.«617»

/-!
# Erdős 617: partition stability, minimum-hole transfer, and surplus bounds

The primary results construct a labelled partition under an independence cap,
bound its missing internal edges by the exact edge surplus, and prove the
vertex-transfer inequalities for a single minimum-hole partition. Empty parts
are permitted. Ordered and unordered counts are related by an explicit
factor-of-two proof; surpluses in the colour-graph interface are signed integers.

Applications to the target include hereditary palette bounds, a local-degree
bound, the uniform bound t_j >= r-1, and the isolated-vertex bound.
The exact identity sum_j t_j = r*choose(r,2) is retained. No strict aggregate
inequality, unconditional per-colour target bound, or all-r solution is asserted.
-/

namespace Contribution.Erdos617Partitions
set_option linter.unusedSectionVars false
/- Bridge -/
section
set_option autoImplicit false

open Finset SimpleGraph

namespace ColourBounds

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}


abbrev Coloring (V : Type*) (r : ℕ) := Sym2 V → Fin r


def Independent (c : Coloring V r) (i : Fin r) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → c s(x, y) ≠ i


/-- Every colour class has independence number at most r. -/
def Caps (c : Coloring V r) : Prop :=
  ∀ (j : Fin r) (T : Finset V), Independent c j T → T.card ≤ r


/-- The simple graph formed by the unordered non-diagonal pairs of one colour. -/
def colourGraph (c : Coloring V r) (j : Fin r) : SimpleGraph V where
  Adj u v := u ≠ v ∧ c s(u, v) = j
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelColourGraph (c : Coloring V r) (j : Fin r) :
    DecidableRel (colourGraph c j).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ c s(u, v) = j))

@[simp] lemma colourGraph_adj {c : Coloring V r} {j : Fin r} {u v : V} :
    (colourGraph c j).Adj u v ↔ u ≠ v ∧ c s(u, v) = j := Iff.rfl


lemma isIndepSet_colourGraph_iff {c : Coloring V r} {j : Fin r} {S : Finset V} :
    (colourGraph c j).IsIndepSet (S : Set V) ↔ Independent c j S := by
  constructor
  · intro h x hx y hy hxy hc
    exact h (by simpa using hx) (by simpa using hy) hxy ⟨hxy, hc⟩
  · intro h x hx y hy hxy hadj
    exact h x (by simpa using hx) y (by simpa using hy) hxy hadj.2


lemma indepSetFree_of_caps {c : Coloring V r} (h : Caps c) (j : Fin r) :
    (colourGraph c j).IndepSetFree (r + 1) := by
  intro t ht
  have hind : Independent c j t := isIndepSet_colourGraph_iff.mp ht.isIndepSet
  have hcard := h j t hind
  have := ht.card_eq
  omega


theorem card_edgeFinset_add_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset + #Gᶜ.edgeFinset = (Fintype.card V).choose 2 := by
  classical
  have hdisj : Disjoint G.edgeFinset Gᶜ.edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he he'
    rw [mem_edgeFinset] at he he'
    induction e with
    | _ u v =>
      rw [mem_edgeSet] at he he'
      exact he'.2 he
  rw [← card_edgeFinset_top_eq_card_choose_two (V := V), ← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext e
  induction e with
  | _ u v =>
    simp only [Finset.mem_union, mem_edgeFinset, mem_edgeSet, compl_adj, top_adj]
    constructor
    · rintro (hadj | ⟨hne, -⟩)
      · exact hadj.ne
      · exact hne
    · intro hne
      by_cases hadj : G.Adj u v
      · exact Or.inl hadj
      · exact Or.inr ⟨hne, hadj⟩


private lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_div_cancel' (by simpa [Nat.mul_comm] using (Nat.even_mul_succ_self m).two_dvd)]


private lemma turan_bound_at (hr : 2 ≤ r) :
    ((r ^ 2 + 1) ^ 2 - ((r ^ 2 + 1) % r) ^ 2) * (r - 1) / (2 * r)
        + ((r ^ 2 + 1) % r).choose 2
      = r.choose 2 * (r ^ 2 + 2) := by
  have hmod : (r ^ 2 + 1) % r = 1 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.mod_self]
    simp [Nat.mod_eq_of_lt (show 1 < r by omega)]
  have hsq : (r ^ 2 + 1) ^ 2 - 1 ^ 2 = r ^ 2 * (r ^ 2 + 2) := by ring_nf; omega
  have hkey : ((r ^ 2 + 1) ^ 2 - 1 ^ 2) * (r - 1) = 2 * r * (r.choose 2 * (r ^ 2 + 2)) := by
    rw [hsq]
    have h2 := two_mul_choose_two r
    calc r ^ 2 * (r ^ 2 + 2) * (r - 1)
        = r * ((r * (r - 1)) * (r ^ 2 + 2)) := by ring
      _ = r * ((2 * r.choose 2) * (r ^ 2 + 2)) := by rw [h2]
      _ = 2 * r * (r.choose 2 * (r ^ 2 + 2)) := by ring
  rw [hmod, hkey, Nat.mul_div_cancel_left _ (by omega : 0 < 2 * r)]
  norm_num


def tau0 (r : ℕ) : ℕ := (r + 1).choose 2 + (r - 1) * r.choose 2

private lemma tau0_add_turan (hr : 2 ≤ r) :
    tau0 r + r.choose 2 * (r ^ 2 + 2) = (r ^ 2 + 1).choose 2 := by
  have h2 : ∀ n : ℕ, 2 * n.choose 2 = n * (n - 1) := two_mul_choose_two
  have e1 := h2 (r + 1)
  have e2 := h2 r
  have e3 := h2 (r ^ 2 + 1)
  simp only [Nat.add_sub_cancel] at e1 e3

  have hgoal : 2 * (tau0 r + r.choose 2 * (r ^ 2 + 2)) = 2 * (r ^ 2 + 1).choose 2 := by
    unfold tau0
    rw [Nat.mul_add, Nat.mul_add, e1, e3]
    have : 2 * ((r - 1) * r.choose 2) = (r - 1) * (r * (r - 1)) := by
      rw [← e2]; ring
    rw [this]
    have h2' : 2 * (r.choose 2 * (r ^ 2 + 2)) = (r * (r - 1)) * (r ^ 2 + 2) := by
      rw [← e2]; ring
    rw [h2']
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 from by omega]
    ring
  omega


theorem tau0_le_card_edgeFinset (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IndepSetFree (r + 1)) :
    tau0 r ≤ #G.edgeFinset := by
  classical
  have hcf : Gᶜ.CliqueFree (r + 1) := by rw [cliqueFree_compl]; exact h
  have hub := hcf.card_edgeFinset_le
  rw [hV] at hub
  simp only at hub
  rw [turan_bound_at hr] at hub
  have hsum := card_edgeFinset_add_compl G
  rw [hV] at hsum
  have := tau0_add_turan (r := r) hr
  omega


def tau (m k : ℕ) : ℕ := k * (m / k).choose 2 + (m % k) * (m / k)

variable {k : ℕ}

private lemma div_eq_of_lt (hk : 0 < k) (q s : ℕ) (hs : s < k) : (k * q + s) / k = q := by
  rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hs, Nat.add_zero]

private lemma mod_eq_of_lt (q s : ℕ) (hs : s < k) : (k * q + s) % k = s := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]


private lemma cast_choose_two (n : ℕ) : 2 * (n.choose 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n with
  | zero => simp
  | succ p =>
    have h := two_mul_choose_two (p + 1)
    rw [Nat.add_sub_cancel] at h
    have : ((2 * (p + 1).choose 2 : ℕ) : ℤ) = (((p + 1) * p : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at this ⊢
    linarith


private lemma turan_upper_eq (hk : 0 < k) (m : ℕ) :
    (m ^ 2 - (m % k) ^ 2) * (k - 1) / (2 * k)
      = (m / k) ^ 2 * k.choose 2 + (m % k) * (m / k) * (k - 1) := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < k ∧ m = k * q + s :=
    ⟨m / k, m % k, Nat.mod_lt _ hk, (Nat.div_add_mod m k).symm⟩
  rw [div_eq_of_lt hk q s hs, mod_eq_of_lt q s hs]
  have hch : 2 * k.choose 2 = k * (k - 1) := two_mul_choose_two k
  have hsub : (k * q + s) ^ 2 - s ^ 2 = k * q * (k * q + 2 * s) := by
    have h1 : (k * q + s) ^ 2 = k * q * (k * q + 2 * s) + s ^ 2 := by ring
    omega
  have hnum : ((k * q + s) ^ 2 - s ^ 2) * (k - 1)
      = 2 * k * (q ^ 2 * k.choose 2 + s * q * (k - 1)) := by
    rw [hsub]
    have h2 : 2 * k * (q ^ 2 * k.choose 2 + s * q * (k - 1))
        = q ^ 2 * (2 * k.choose 2) * k + 2 * k * s * q * (k - 1) := by ring
    rw [h2, hch]
    ring
  rw [hnum, Nat.mul_div_cancel_left _ (by omega : 0 < 2 * k)]


private lemma tau_add_upper (hk : 0 < k) (m : ℕ) :
    tau m k + ((m / k) ^ 2 * k.choose 2 + (m % k) * (m / k) * (k - 1)
      + (m % k).choose 2) = m.choose 2 := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < k ∧ m = k * q + s :=
    ⟨m / k, m % k, Nat.mod_lt _ hk, (Nat.div_add_mod m k).symm⟩
  unfold tau
  rw [div_eq_of_lt hk q s hs, mod_eq_of_lt q s hs]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have c1 := cast_choose_two q
  have c2 := cast_choose_two (k' + 1)
  have c3 := cast_choose_two s
  have c4 := cast_choose_two ((k' + 1) * q + s)
  have key : (((k' + 1) * q.choose 2 + s * q
        + ((q ^ 2 * (k' + 1).choose 2 + s * q * k') + s.choose 2) : ℕ) : ℤ)
      = ((((k' + 1) * q + s).choose 2 : ℕ) : ℤ) := by
    push_cast at c1 c2 c3 c4 ⊢
    linarith [mul_left_cancel₀ (show (2:ℤ) ≠ 0 by norm_num)
      (show (2:ℤ) * (((k' + 1) : ℤ) * (q.choose 2 : ℤ) + (s : ℤ) * q
          + ((q : ℤ) ^ 2 * ((k' + 1).choose 2 : ℤ) + (s : ℤ) * q * k')
          + (s.choose 2 : ℤ))
        = 2 * ((((k' + 1) * q + s).choose 2 : ℕ) : ℤ) by
        push_cast
        linear_combination ((k' : ℤ) + 1) * c1 + (q : ℤ) ^ 2 * c2 + c3 - c4)]
  exact_mod_cast key


theorem tau_le_card_edgeFinset (hk : 0 < k) (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IndepSetFree (k + 1)) : tau (Fintype.card V) k ≤ #G.edgeFinset := by
  classical
  have hcf : Gᶜ.CliqueFree (k + 1) := by rw [cliqueFree_compl]; exact h
  have hub := hcf.card_edgeFinset_le
  simp only at hub
  rw [turan_upper_eq hk] at hub
  have hsum := card_edgeFinset_add_compl G
  have := tau_add_upper (k := k) hk (Fintype.card V)
  omega


theorem tau0_eq_tau (hr : 2 ≤ r) : tau0 r = tau (r ^ 2 + 1) r := by
  have hq : (r ^ 2 + 1) / r = r := by
    rw [show r ^ 2 + 1 = r * r + 1 from by ring]
    exact div_eq_of_lt (by omega) r 1 (by omega)
  have hs : (r ^ 2 + 1) % r = 1 := by
    rw [show r ^ 2 + 1 = r * r + 1 from by ring]
    exact mod_eq_of_lt r 1 (by omega)
  unfold tau tau0
  rw [hq, hs, one_mul]
  have e1 := two_mul_choose_two (r + 1)
  have e2 := two_mul_choose_two r
  rw [Nat.add_sub_cancel] at e1
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  rw [Nat.mul_add, Nat.mul_add, e1]
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega] at e2 ⊢
  have hx : 2 * ((m + 1) * (m + 2).choose 2) = (m + 1) * (2 * (m + 2).choose 2) := by ring
  have hy : 2 * ((m + 2) * (m + 2).choose 2) = (m + 2) * (2 * (m + 2).choose 2) := by ring
  rw [hx, hy, e2]
  ring


theorem sum_card_edgeFinset (c : Coloring V r) :
    ∑ j : Fin r, #(colourGraph c j).edgeFinset = (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two (V := V)]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun e => c e) (s := (⊤ : SimpleGraph V).edgeFinset) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 1
  ext e
  induction e with
  | _ u v =>
    simp only [mem_edgeFinset, mem_edgeSet, colourGraph_adj, Finset.mem_filter, top_adj]


def surplus (c : Coloring V r) (j : Fin r) : ℤ :=
  (#(colourGraph c j).edgeFinset : ℤ) - (tau0 r : ℤ)


private lemma choose_eq_r_mul_tau0 (hr : 2 ≤ r) :
    (r ^ 2 + 1).choose 2 = r * tau0 r + r * r.choose 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have h2 : ∀ n : ℕ, 2 * n.choose 2 = n * (n - 1) := two_mul_choose_two
  have e1 := h2 (m + 3)
  have e2 := h2 (m + 2)
  have e3 := h2 ((m + 2) ^ 2 + 1)
  rw [show m + 3 - 1 = m + 2 from by omega] at e1
  rw [show m + 2 - 1 = m + 1 from by omega] at e2
  rw [Nat.add_sub_cancel] at e3
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  unfold tau0
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 + 1 = m + 3 from rfl]
  have expand : 2 * ((m + 2) * ((m + 3).choose 2 + (m + 1) * (m + 2).choose 2)
        + (m + 2) * (m + 2).choose 2)
      = (m + 2) * (2 * (m + 3).choose 2)
        + (m + 1) * (m + 2) * (2 * (m + 2).choose 2)
        + (m + 2) * (2 * (m + 2).choose 2) := by ring
  rw [expand, e1, e2, e3]
  ring


/-- Exact conservation of the signed colour surpluses on r²+1 vertices. -/
theorem sum_surplus (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1) (c : Coloring V r) :
    ∑ j : Fin r, surplus c j = (r : ℤ) * (r.choose 2 : ℤ) := by
  have hsum := sum_card_edgeFinset c
  rw [hV] at hsum
  have hbudget := choose_eq_r_mul_tau0 (r := r) hr
  have hnat : ∑ j : Fin r, #(colourGraph c j).edgeFinset = r * tau0 r + r * r.choose 2 := by
    rw [hsum, hbudget]
  have hcast : ((∑ j : Fin r, #(colourGraph c j).edgeFinset : ℕ) : ℤ)
      = ((r * tau0 r + r * r.choose 2 : ℕ) : ℤ) := by exact_mod_cast hnat
  push_cast at hcast
  simp only [surplus, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [hcast]
  ring


theorem not_caps_of_surplus_ge (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Coloring V r)
    (h : ∀ j : Fin r, (r.choose 2 : ℤ) + 1 ≤ surplus c j) : False := by
  have hsum := sum_surplus hr hV c
  have hlb : ∑ _j : Fin r, ((r.choose 2 : ℤ) + 1) ≤ ∑ j : Fin r, surplus c j :=
    Finset.sum_le_sum (fun j _ => h j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlb
  rw [hsum] at hlb
  have hrpos : (0 : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : 0 < r)
  nlinarith

private lemma independent_mono {c : Coloring V r} {j : Fin r} {S T : Finset V}
    (hST : S ⊆ T) (h : Independent c j T) : Independent c j S :=
  fun x hx y hy hxy => h x (hST hx) y (hST hy) hxy


theorem exists_indep_of_TB (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Coloring V r)
    (ColourBounds : Caps c → ∀ j : Fin r, (r.choose 2 : ℤ) + 1 ≤ surplus c j) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ Independent c k S := by
  by_contra hn
  push Not at hn
  have hcaps : Caps c := by
    intro j T hT
    by_contra hcard
    obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq (show r + 1 ≤ T.card by omega)
    exact hn S j hScard (independent_mono hST hT)
  exact not_caps_of_surplus_ge hr hV c (ColourBounds hcaps)


example : tau0 5 = 55 ∧ Nat.choose 5 2 + 1 = 11 := by decide


section Partition

variable {p : ℕ}


def part (f : V → Fin p) (i : Fin p) : Finset V := univ.filter (fun v => f v = i)

@[simp] lemma mem_part {f : V → Fin p} {i : Fin p} {v : V} : v ∈ part f i ↔ f v = i := by
  simp [part]

lemma sum_card_part (f : V → Fin p) : ∑ i, #(part f i) = Fintype.card V :=
  (Finset.card_eq_sum_card_fiberwise (f := f) (s := (univ : Finset V)) (t := univ)
    (fun x _ => Finset.mem_univ (f x))).symm


def classCount (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p)
    (c : Sym2 (Fin p)) : ℕ :=
  #(G.edgeFinset.filter (fun e => Sym2.map f e = c))


def internalCount (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) (i : Fin p) : ℕ :=
  classCount G f s(i, i)


def crossCount (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) (i k : Fin p) : ℕ :=
  classCount G f s(i, k)


lemma map_eq_diag_iff {f : V → Fin p} {i : Fin p} {u v : V} :
    Sym2.map f s(u, v) = s(i, i) ↔ u ∈ part f i ∧ v ∈ part f i := by
  simp


lemma map_eq_pair_iff {f : V → Fin p} {i k : Fin p} {u v : V} :
    Sym2.map f s(u, v) = s(i, k) ↔
      (u ∈ part f i ∧ v ∈ part f k) ∨ (u ∈ part f k ∧ v ∈ part f i) := by
  simp


lemma internalCount_fin_one (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin 1) :
    internalCount G f 0 = #G.edgeFinset := by
  unfold internalCount classCount
  congr 1
  refine Finset.filter_true_of_mem (fun e _ => ?_)
  induction e with
  | _ u v => simp [Subsingleton.elim (f u) 0, Subsingleton.elim (f v) 0]


private def key (f : V → Fin p) (e : Sym2 V) : Fin p × Fin p :=
  ((Sym2.map f e).inf, (Sym2.map f e).sup)

private lemma key_fst_le_snd (f : V → Fin p) (e : Sym2 V) : (key f e).1 ≤ (key f e).2 :=
  Sym2.inf_le_sup _

private lemma key_eq_iff {f : V → Fin p} {i k : Fin p} (hik : i ≤ k) {e : Sym2 V} :
    key f e = (i, k) ↔ Sym2.map f e = s(i, k) := by
  rw [← Sym2.inf_eq_inf_and_sup_eq_sup]
  simp [key, Prod.ext_iff, inf_of_le_left hik, sup_of_le_right hik]

private lemma count_key (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p)
    {i k : Fin p} (hik : i ≤ k) :
    #(G.edgeFinset.filter (fun e => key f e = (i, k))) = classCount G f s(i, k) := by
  unfold classCount
  congr 1
  exact Finset.filter_congr (fun e _ => by simp [key_eq_iff hik])

private lemma count_key_zero (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p)
    {i k : Fin p} (hik : ¬ i ≤ k) :
    #(G.edgeFinset.filter (fun e => key f e = (i, k))) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _ he
  have hle := key_fst_le_snd f e
  rw [he] at hle
  exact hik hle

private lemma Ici_eq_insert_Ioi (i : Fin p) : Finset.Ici i = insert i (Finset.Ioi i) := by
  ext k
  simp only [Finset.mem_Ici, Finset.mem_insert, Finset.mem_Ioi]
  constructor
  · intro h; rcases eq_or_lt_of_le h with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'
  · rintro (rfl | h); · exact le_rfl
    · exact h.le


theorem card_edgeFinset_eq_internal_add_cross (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin p) :
    #G.edgeFinset
      = ∑ i, internalCount G f i + ∑ i, ∑ k ∈ Finset.Ioi i, crossCount G f i k := by
  classical
  have h1 : #G.edgeFinset
      = ∑ q : Fin p × Fin p, #(G.edgeFinset.filter (fun e => key f e = q)) :=
    Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ _)
  rw [h1, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hsub : ∑ k : Fin p, #(G.edgeFinset.filter (fun e => key f e = (i, k)))
      = ∑ k ∈ Finset.Ici i, #(G.edgeFinset.filter (fun e => key f e = (i, k))) := by
    refine (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => ?_)).symm
    exact count_key_zero G f (by simpa using hk)
  rw [hsub, Ici_eq_insert_Ioi, Finset.sum_insert (by simp)]
  rw [count_key G f (le_refl i)]
  refine congrArg _ (Finset.sum_congr rfl (fun k hk => ?_))
  exact count_key G f (Finset.mem_Ioi.mp hk).le


def binom2 (x : ℤ) : ℤ := x * (x - 1) / 2

lemma two_mul_binom2 (x : ℤ) : 2 * binom2 x = x * (x - 1) := by
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ x * (x - 1) := by
    rcases Int.even_or_odd x with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (x - 1), by rw [hm]; ring⟩
    · exact ⟨x * m, by rw [hm]; ring⟩
  unfold binom2
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

lemma binom2_nonneg (x : ℤ) : 0 ≤ binom2 x := by
  have h := two_mul_binom2 x
  rcases le_or_gt x 0 with hx | hx
  · nlinarith
  · have hx1 : 1 ≤ x := by omega
    nlinarith

lemma binom2_natCast (m : ℕ) : binom2 (m : ℤ) = (m.choose 2 : ℤ) := by
  have h1 := two_mul_binom2 (m : ℤ)
  have h2 := cast_choose_two m
  linarith


def partSizeExcess (f : V → Fin p) (r : ℕ) (i : Fin p) : ℤ := (#(part f i) : ℤ) - (r : ℤ)


def partImbalance (f : V → Fin p) (r : ℕ) : ℤ := ∑ i, binom2 (partSizeExcess f r i)


theorem partImbalance_nonneg (f : V → Fin p) (r : ℕ) : 0 ≤ partImbalance f r :=
  Finset.sum_nonneg (fun i _ => binom2_nonneg _)

lemma sum_partSizeExcess (f : V → Fin p) (r : ℕ) (hV : Fintype.card V = p * r + 1) :
    ∑ i, partSizeExcess f r i = 1 := by
  unfold partSizeExcess
  rw [Finset.sum_sub_distrib]
  have hs : ((∑ i, #(part f i) : ℕ) : ℤ) = ((p * r + 1 : ℕ) : ℤ) := by
    rw [sum_card_part, hV]
  push_cast at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [hs]
  ring

private lemma tau_partition (hp : 1 ≤ p) (r : ℕ) : tau (p * r + 1) p = p * r.choose 2 + r := by
  rcases eq_or_lt_of_le hp with h1 | h2
  · subst h1
    simp only [tau, one_mul, Nat.div_one, Nat.mod_one, Nat.zero_mul, Nat.add_zero]
    have h1 := two_mul_choose_two (r + 1)
    have h2 := two_mul_choose_two r
    rw [Nat.add_sub_cancel] at h1
    have h3 : (r + 1) * r = r * (r - 1) + 2 * r := by
      cases r with
      | zero => simp
      | succ m => rw [Nat.add_sub_cancel]; ring
    omega
  · have hq : (p * r + 1) / p = r := div_eq_of_lt (by omega) r 1 (by omega)
    have hs : (p * r + 1) % p = 1 := mod_eq_of_lt r 1 (by omega)
    simp [tau, hq, hs]


def partSurplus (G : SimpleGraph V) [DecidableRel G.Adj] (p r : ℕ) : ℤ :=
  (#G.edgeFinset : ℤ) - (tau (p * r + 1) p : ℤ)


def partHoles (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) : ℤ :=
  ∑ i, (((#(part f i)).choose 2 : ℤ) - (internalCount G f i : ℤ))


def partCross (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) : ℤ :=
  ∑ i, ∑ k ∈ Finset.Ioi i, (crossCount G f i k : ℤ)

private lemma sum_choose_part (f : V → Fin p) (r : ℕ) (hV : Fintype.card V = p * r + 1) :
    ∑ i, ((#(part f i)).choose 2 : ℤ)
      = (p : ℤ) * (r.choose 2 : ℤ) + (r : ℤ) + partImbalance f r := by
  have key : ∀ i : Fin p, ((#(part f i)).choose 2 : ℤ)
      = (r.choose 2 : ℤ) + (r : ℤ) * partSizeExcess f r i + binom2 (partSizeExcess f r i) := by
    intro i
    have e1 := cast_choose_two (#(part f i))
    have e2 := cast_choose_two r
    have e3 := two_mul_binom2 (partSizeExcess f r i)
    have hm : ((#(part f i)) : ℤ) = (r : ℤ) + partSizeExcess f r i := by
      unfold partSizeExcess; ring
    rw [hm] at e1
    refine mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) ?_
    linear_combination e1 - e2 - e3
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_partSizeExcess f r hV]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, partImbalance]
  ring


/-- Exact partition accounting: surplus equals crossing edges minus holes plus imbalance. -/
theorem partSurplus_eq (hp : 1 ≤ p) (r : ℕ) (hV : Fintype.card V = p * r + 1)
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) :
    partSurplus G p r = partCross G f - partHoles G f + partImbalance f r := by
  have hdec := card_edgeFinset_eq_internal_add_cross G f
  have hdecZ : (#G.edgeFinset : ℤ)
      = (∑ i, (internalCount G f i : ℤ)) + partCross G f := by
    have : ((#G.edgeFinset : ℕ) : ℤ)
        = ((∑ i, internalCount G f i + ∑ i, ∑ k ∈ Finset.Ioi i, crossCount G f i k : ℕ) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdec
    push_cast at this
    simpa [partCross] using this
  have hchoose := sum_choose_part (f := f) r hV
  have htau : (tau (p * r + 1) p : ℤ) = (p : ℤ) * (r.choose 2 : ℤ) + (r : ℤ) := by
    rw [tau_partition hp r]; push_cast; ring
  unfold partSurplus partHoles
  rw [hdecZ, htau, Finset.sum_sub_distrib, hchoose]
  ring

end Partition


theorem not_caps_of_sum_bound (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Coloring V r) (b : Fin r → ℤ)
    (hb : ∀ j : Fin r, b j ≤ surplus c j)
    (hbudget : (r : ℤ) * (r.choose 2 : ℤ) < ∑ j : Fin r, b j) : False := by
  have hsum := sum_surplus hr hV c
  have hle : ∑ j : Fin r, b j ≤ ∑ j : Fin r, surplus c j :=
    Finset.sum_le_sum (fun j _ => hb j)
  linarith


theorem exists_indep_of_sum_TB (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Coloring V r) (b : Fin r → ℤ)
    (ColourBounds : Caps c → ∀ j : Fin r, b j ≤ surplus c j)
    (hbudget : (r : ℤ) * (r.choose 2 : ℤ) < ∑ j : Fin r, b j) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ Independent c k S := by
  by_contra hn
  push Not at hn
  have hcaps : Caps c := by
    intro j T hT
    by_contra hcard
    obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq (show r + 1 ≤ T.card by omega)
    exact hn S j hScard (independent_mono hST hT)
  exact not_caps_of_sum_bound hr hV c b (ColourBounds hcaps) hbudget


theorem exists_indep_of_one_special (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Coloring V r) (j₀ : Fin r) (L m : ℤ)
    (hL : Caps c → L ≤ surplus c j₀)
    (hm : Caps c → ∀ j : Fin r, j ≠ j₀ → m ≤ surplus c j)
    (hbudget : (r : ℤ) * (r.choose 2 : ℤ) < L + ((r : ℤ) - 1) * m) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ Independent c k S := by
  have hs : ∑ j : Fin r, (if j = j₀ then L else m) = L + ((r : ℤ) - 1) * m := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
    rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.mem_erase.mp hj).1)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, if_pos rfl, Nat.cast_sub (by omega : 1 ≤ r)]
    push_cast
    ring
  refine exists_indep_of_sum_TB hr hV c (fun j => if j = j₀ then L else m) ?_ (by rw [hs]; exact hbudget)
  intro hcaps j
  by_cases h : j = j₀
  · subst h
    simpa using hL hcaps
  · simpa [h] using hm hcaps j h


def Lpacked (x : ℤ) : ℤ := (x - 2) * binom2 (x - 1) + 3 * x - 6


theorem Lpacked_add_rest (x : ℤ) :
    Lpacked x + (x - 1) * (2 * x - 4) = x * binom2 x + x - 4 := by
  have h1 := two_mul_binom2 (x - 1)
  have h2 := two_mul_binom2 x
  refine mul_left_cancel₀ (show (2 : ℤ) ≠ 0 by norm_num) ?_
  unfold Lpacked
  linear_combination (x - 2) * h1 - x * h2


theorem exists_indep_of_packed (hr : 5 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Coloring V r) (j₀ : Fin r)
    (hL : Caps c → Lpacked (r : ℤ) ≤ surplus c j₀)
    (hm : Caps c → ∀ j : Fin r, j ≠ j₀ → (2 * (r : ℤ) - 4) ≤ surplus c j) :
    ∃ (S : Finset V) (k : Fin r), S.card = r + 1 ∧ Independent c k S := by
  refine exists_indep_of_one_special (by omega) hV c j₀ (Lpacked (r : ℤ)) (2 * (r : ℤ) - 4)
    hL hm ?_
  have hid := Lpacked_add_rest (r : ℤ)
  have hb : binom2 (r : ℤ) = (r.choose 2 : ℤ) := binom2_natCast r
  have hr5 : (5 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  rw [hb] at hid
  linarith


example : Lpacked 5 = 27 ∧ Lpacked 5 + 4 * 6 = 5 * binom2 5 + 1 := by decide

end ColourBounds
end


/- Palette -/
section
set_option autoImplicit false

open Finset SimpleGraph

namespace ColourBounds

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}


/-- The colouring induced on a finite subset of the original carrier. -/
def restrictColouring (c : Coloring V r) (U : Finset V) : Coloring {v // v ∈ U} r :=
  fun e => c (Sym2.map Subtype.val e)

@[simp] lemma restrictColouring_apply (c : Coloring V r) (U : Finset V)
    (a b : {v // v ∈ U}) :
    restrictColouring c U s(a, b) = c s((a : V), (b : V)) := rfl


lemma caps_restrictColouring {c : Coloring V r} (h : Caps c) (U : Finset V) :
    Caps (restrictColouring c U) := by
  intro j T hT
  have himg : Independent c j (T.image Subtype.val) := by
    intro x hx y hy hxy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun hEq => hxy (by rw [hEq])
    simpa using hT a ha b hb hab
  have hcard : (T.image Subtype.val).card = T.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have := h j (T.image Subtype.val) himg
  omega


/-- The signed count of pairs in U that avoid the selected colour. -/
def holesIn (c : Coloring V r) (j : Fin r) (U : Finset V) : ℤ :=
  ((U.card).choose 2 : ℤ) - (#(colourGraph (restrictColouring c U) j).edgeFinset : ℤ)


/-- Pairs avoiding one colour are exactly the disjoint union of the other colour classes. -/
lemma holesIn_eq_sum (c : Coloring V r) (j : Fin r) (U : Finset V) :
    holesIn c j U
      = ((∑ k ∈ univ.erase j, #(colourGraph (restrictColouring c U) k).edgeFinset : ℕ) : ℤ) := by
  classical
  have hsum := sum_card_edgeFinset (restrictColouring c U)
  rw [Fintype.card_coe] at hsum
  have hsplit : ∑ k ∈ univ.erase j, #(colourGraph (restrictColouring c U) k).edgeFinset
      + #(colourGraph (restrictColouring c U) j).edgeFinset = (U.card).choose 2 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    exact hsum
  have hcast := congrArg (Nat.cast : ℕ → ℤ) hsplit
  push_cast at hcast
  unfold holesIn
  push_cast
  linarith


/-- Sum the extremal lower bounds for the other colours on the same vertex subset. -/
theorem holesIn_ge_palette (hr : 0 < r) {c : Coloring V r} (h : Caps c)
    (j : Fin r) (U : Finset V) :
    ((r : ℤ) - 1) * (tau U.card r : ℤ) ≤ holesIn c j U := by
  classical
  have hcaps := caps_restrictColouring h U
  have hlow : ∀ k : Fin r, tau U.card r ≤ #(colourGraph (restrictColouring c U) k).edgeFinset := by
    intro k
    have hk := tau_le_card_edgeFinset (k := r) hr (colourGraph (restrictColouring c U) k)
      (indepSetFree_of_caps hcaps k)
    rwa [Fintype.card_coe] at hk
  have hbound : (r - 1) * tau U.card r
      ≤ ∑ k ∈ univ.erase j, #(colourGraph (restrictColouring c U) k).edgeFinset := by
    calc (r - 1) * tau U.card r
        = ∑ _k ∈ univ.erase j, tau U.card r := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun k _ => hlow k)
  have hcast : (((r - 1) * tau U.card r : ℕ) : ℤ) = ((r : ℤ) - 1) * (tau U.card r : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_sub hr]
    norm_num
  rw [holesIn_eq_sum]
  calc ((r : ℤ) - 1) * (tau U.card r : ℤ)
      = (((r - 1) * tau U.card r : ℕ) : ℤ) := hcast.symm
    _ ≤ _ := Int.ofNat_le.mpr hbound


private lemma tau_key (r s : ℕ) (hs : s < r) : ∀ q : ℕ,
    (r : ℤ) * (q : ℤ) + (s : ℤ) - (r : ℤ) ≤ (r : ℤ) * (q.choose 2 : ℤ) + (s : ℤ) * (q : ℤ)
  | 0 => by
      rw [Nat.choose_eq_zero_of_lt (by norm_num)]
      have hsr : (s : ℤ) < (r : ℤ) := by exact_mod_cast hs
      push_cast
      linarith
  | 1 => by
      rw [Nat.choose_eq_zero_of_lt (by norm_num)]
      push_cast
      linarith
  | (n + 2) => by
      have hch : 2 * ((n + 2).choose 2 : ℤ) = ((n : ℤ) + 2) * ((n : ℤ) + 1) := by
        have h1 := binom2_natCast (n + 2)
        have h2 := two_mul_binom2 ((n : ℤ) + 2)
        push_cast at h1 h2 ⊢
        linarith
      have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
      have hs0 : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
      have hr0 : (0 : ℤ) ≤ (r : ℤ) := Int.natCast_nonneg r
      push_cast
      nlinarith [hch, mul_nonneg hr0 (mul_nonneg hn (by linarith : (0:ℤ) ≤ (n:ℤ) + 1)),
        mul_nonneg hs0 (by linarith : (0:ℤ) ≤ (n:ℤ) + 1)]


/-- The integral balanced-partition threshold is at least m-r. -/
theorem sub_le_tau (hr : 0 < r) (m : ℕ) : (m : ℤ) - (r : ℤ) ≤ (tau m r : ℤ) := by
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < r ∧ m = r * q + s :=
    ⟨m / r, m % r, Nat.mod_lt _ hr, (Nat.div_add_mod m r).symm⟩
  have hq : (r * q + s) / r = q := by
    rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hs, Nat.add_zero]
  have hmod : (r * q + s) % r = s := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  have htau : (tau (r * q + s) r : ℤ)
      = (r : ℤ) * (q.choose 2 : ℤ) + (s : ℤ) * (q : ℤ) := by
    unfold tau
    rw [hq, hmod]
    push_cast
    ring
  rw [htau]
  have := tau_key r s hs q
  push_cast at this ⊢
  linarith


theorem holesIn_ge_linear (hr : 0 < r) {c : Coloring V r} (h : Caps c)
    (j : Fin r) (U : Finset V) :
    ((r : ℤ) - 1) * ((U.card : ℤ) - (r : ℤ)) ≤ holesIn c j U := by
  have h1 := holesIn_ge_palette hr h j U
  have h2 := sub_le_tau (r := r) hr U.card
  have hR : (0 : ℤ) ≤ (r : ℤ) - 1 := by
    have : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
    linarith
  nlinarith

end ColourBounds
end


/- Stability -/
section
/-
# Elementary partition stability for the partition-stability development

This file proves the partition lemma by induction on the independence bound,
using a vertex of minimum degree.  No extremal graph theorem is invoked.
All counts in the construction are ordered; the final bridge divides by two
only after proving the exact counting identities.
-/

set_option autoImplicit false

namespace Stability

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

def degree (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (x : V) : ℕ :=
  #(W.filter (G.Adj x))

def arcs (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : ℕ :=
  ∑ x ∈ W, degree G W x

def holes (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : ℕ :=
  arcs Gᶜ W

def cost (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : ℕ :=
  #W * (#W - 1) + holes G W

def IndependenceBound (G : SimpleGraph V) (W : Finset V) (p : ℕ) : Prop :=
  ∀ S ⊆ W, G.IsIndepSet (S : Set V) → #S ≤ p

def cell (W : Finset V) (f : V → ℕ) (i : ℕ) : Finset V :=
  W.filter (fun x => f x = i)

lemma degree_split (G : SimpleGraph V) [DecidableRel G.Adj]
    {W A : Finset V} (hA : A ⊆ W) (x : V) :
    degree G W x = degree G A x + degree G (W \ A) x := by
  unfold degree
  rw [← card_union_of_disjoint]
  · rw [← filter_union, union_sdiff_of_subset hA]
  · exact disjoint_filter_filter disjoint_sdiff

omit [DecidableEq V] in
lemma cut_swap (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, degree G B a) = ∑ b ∈ B, degree G A b := by
  simp only [degree, card_filter]
  rw [sum_comm]
  exact sum_congr rfl (fun b _ => sum_congr rfl (fun a _ => by simp only [G.adj_comm]))

lemma deletion_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    {W A : Finset V} (hA : A ⊆ W) :
    arcs G W + arcs G A = arcs G (W \ A) + 2 * ∑ x ∈ A, degree G W x := by
  have h1 : arcs G W = (∑ x ∈ A, degree G W x) +
      ∑ x ∈ W \ A, degree G W x := by
    rw [← sum_union disjoint_sdiff, union_sdiff_of_subset hA]
    rfl
  have h2 : (∑ x ∈ A, degree G W x) =
      arcs G A + ∑ x ∈ A, degree G (W \ A) x := by
    unfold arcs
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun x _ => degree_split G hA x)
  have h3 : (∑ x ∈ W \ A, degree G W x) =
      (∑ x ∈ W \ A, degree G A x) + arcs G (W \ A) := by
    unfold arcs
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun x _ => degree_split G hA x)
  rw [cut_swap G (W \ A) A] at h3
  omega

lemma degree_add_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {W : Finset V} {x : V} (hx : x ∈ W) :
    degree G W x + degree Gᶜ W x = #W - 1 := by
  have hd : Disjoint (W.filter (G.Adj x)) (W.filter (Gᶜ.Adj x)) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    exact (mem_filter.mp hz).2.2 (mem_filter.mp hy).2
  have hu : W.filter (G.Adj x) ∪ W.filter (Gᶜ.Adj x) = W.erase x := by
    ext y
    simp only [mem_union, mem_filter, compl_adj, mem_erase]
    constructor
    · rintro (⟨hy, hxy⟩ | ⟨hy, hxy, _⟩)
      · exact ⟨hxy.ne.symm, hy⟩
      · exact ⟨hxy.symm, hy⟩
    · rintro ⟨hyx, hy⟩
      by_cases hxy : G.Adj x y
      · exact Or.inl ⟨hy, hxy⟩
      · exact Or.inr ⟨hy, hyx.symm, hxy⟩
  unfold degree
  rw [← card_union_of_disjoint hd, hu, card_erase_of_mem hx]

lemma arcs_add_holes (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    arcs G W + holes G W = #W * (#W - 1) := by
  unfold holes arcs
  rw [← sum_add_distrib]
  rw [sum_congr rfl (fun x hx => degree_add_compl G hx)]
  simp

def closed (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (x : V) : Finset V :=
  insert x (W.filter (G.Adj x))

lemma closed_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    {W : Finset V} {x : V} (hx : x ∈ W) : closed G W x ⊆ W :=
  insert_subset hx (filter_subset _ _)

lemma closed_card (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (x : V) :
    #(closed G W x) = degree G W x + 1 := by
  simp [closed, degree]

lemma independence_delete_closed (G : SimpleGraph V) [DecidableRel G.Adj]
    {W : Finset V} {x : V} {p : ℕ} (hx : x ∈ W)
    (h : IndependenceBound G W (p + 1)) :
    IndependenceBound G (W \ closed G W x) p := by
  intro S hS hI
  have hxS : x ∉ S := by
    intro hxS
    exact (mem_sdiff.mp (hS hxS)).2 (mem_insert_self _ _)
  have hIS : G.IsIndepSet (insert x S : Finset V) := by
    intro a ha b hb hab hadj
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at ha hb
    rcases ha with rfl | ha
    · have hbS : b ∈ S := hb.resolve_left hab.symm
      exact (mem_sdiff.mp (hS hbS)).2
        (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp (hS hbS)).1, hadj⟩))
    · rcases hb with rfl | hb
      · exact (mem_sdiff.mp (hS ha)).2
          (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp (hS ha)).1, hadj.symm⟩))
      · exact hI ha hb hab hadj
  have hb := h (insert x S) (insert_subset hx (hS.trans sdiff_subset)) hIS
  rw [card_insert_of_notMem hxS] at hb
  omega

lemma minimum_degree_step (G : SimpleGraph V) [DecidableRel G.Adj]
    {W : Finset V} {x : V} (hx : x ∈ W)
    (hmin : ∀ v ∈ W, degree G W x ≤ degree G W v) :
    arcs G (W \ closed G W x) + cost G (closed G W x) ≤ arcs G W := by
  have hi := deletion_identity G (closed_subset G hx)
  have hc := closed_card G W x
  have hh := arcs_add_holes G (closed G W x)
  have hl : #(closed G W x) * degree G W x ≤
      ∑ v ∈ closed G W x, degree G W v := by
    calc _ = ∑ _v ∈ closed G W x, degree G W x := by simp
         _ ≤ _ := sum_le_sum (fun v hv => hmin v (closed_subset G hx hv))
  unfold cost
  rw [hc] at hh hl ⊢
  simp only [Nat.add_sub_cancel] at hh ⊢
  nlinarith

/-- A stronger form of the partition step: its actual part sizes, not an
extremal comparison graph, pay for all holes in the partition. -/
theorem exists_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (W : Finset V) (h : IndependenceBound G W p) :
    ∃ f : V → ℕ, (∀ x ∈ W, f x < p) ∧
      (∑ i ∈ range p, cost G (cell W f i)) ≤ arcs G W := by
  induction p generalizing W with
  | zero =>
    have he : W = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hs : G.IsIndepSet ({x} : Finset V) := by
        intro a ha b hb hab
        have ha' : a = x := mem_singleton.mp ha
        have hb' : b = x := mem_singleton.mp hb
        exact (hab (ha'.trans hb'.symm)).elim
      have := h {x} (singleton_subset_iff.mpr hx) hs
      simp at this
    subst W
    exact ⟨fun _ => 0, by simp, by simp [arcs]⟩
  | succ p ih =>
    by_cases he : W = ∅
    · subst W
      exact ⟨fun _ => 0, by simp, by simp [cell, cost, holes, arcs]⟩
    obtain ⟨x, hx, hmin⟩ := exists_min_image W (degree G W) (nonempty_iff_ne_empty.mpr he)
    let B := closed G W x
    let A := W \ B
    obtain ⟨f, hf, hcost⟩ := ih A (independence_delete_closed G hx h)
    let g : V → ℕ := fun y => if y ∈ B then p else f y
    have hg : ∀ y ∈ W, g y < p + 1 := by
      intro y hy
      by_cases hyB : y ∈ B
      · simp [g, hyB]
      · have hf' := hf y (mem_sdiff.mpr ⟨hy, hyB⟩)
        simpa [g, hyB] using Nat.lt_succ_of_lt hf'
    have hcell : ∀ i < p, cell W g i = cell A f i := by
      intro i hi
      ext y
      simp only [cell, mem_filter, A, mem_sdiff]
      by_cases hyB : y ∈ B <;> simp [g, hyB, (Nat.ne_of_lt hi).symm]
    have hlast : cell W g p = B := by
      ext y
      simp only [cell, mem_filter]
      constructor
      · rintro ⟨hy, hgy⟩
        by_contra hyB
        have hf' := hf y (mem_sdiff.mpr ⟨hy, hyB⟩)
        simp only [g, if_neg hyB] at hgy
        omega
      · intro hyB
        exact ⟨closed_subset G hx hyB, by simp [g, hyB]⟩
    refine ⟨g, hg, ?_⟩
    rw [sum_range_succ, hlast]
    have hsum : (∑ i ∈ range p, cost G (cell W g i)) =
        ∑ i ∈ range p, cost G (cell A f i) :=
      sum_congr rfl (fun i hi => by rw [hcell i (mem_range.mp hi)])
    rw [hsum]
    exact (Nat.add_le_add_right hcost _).trans (minimum_degree_step G hx hmin)

/- ## Exact arithmetic for arbitrary labelled parts -/

omit [DecidableEq V] in
lemma sum_card_cell {W : Finset V} {f : V → ℕ} {p : ℕ}
    (hf : ∀ x ∈ W, f x < p) : (∑ i ∈ range p, #(cell W f i)) = #W := by
  exact (card_eq_sum_card_fiberwise (fun x hx => mem_range.mpr (hf x hx))).symm

lemma int_mul_pred_nonneg (x : ℤ) : 0 ≤ x * (x - 1) := by
  rcases le_or_gt x 0 with hx | hx
  · nlinarith
  · have : 1 ≤ x := by omega
    nlinarith

lemma cast_mul_pred (n : ℕ) : ((n * (n - 1) : ℕ) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; ring

lemma two_choose (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.choose_two_right]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_div_cancel' (by simpa [Nat.mul_comm] using (Nat.even_mul_succ_self n).two_dvd)]

/-- The tangent bound is integer-exact: its error is `(m-q)(m-q-1)`. -/
lemma part_size_tangent (m q : ℕ) :
    2 * (q : ℤ) * m - (q : ℤ) * (q + 1) ≤ (m * (m - 1) : ℕ) := by
  have h := int_mul_pred_nonneg ((m : ℤ) - q)
  rw [cast_mul_pred]
  nlinarith

omit [DecidableEq V] in
/-- No invocation of Turán: sum the preceding elementary integer inequality. -/
theorem size_budget {W : Finset V} {f : V → ℕ} {p : ℕ}
    (hf : ∀ x ∈ W, f x < p) :
    2 * (p * (#W / p).choose 2 + (#W % p) * (#W / p)) ≤
      ∑ i ∈ range p, #(cell W f i) * (#(cell W f i) - 1) := by
  let q := #W / p
  have hs := sum_card_cell hf
  have ht := sum_le_sum (s := range p) (fun i _ => part_size_tangent (#(cell W f i)) q)
  have hsZ : (∑ i ∈ range p, (#(cell W f i) : ℤ)) = (#W : ℤ) := by
    exact_mod_cast hs
  simp only [sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at ht
  rw [hsZ] at ht
  have hq : p * q + #W % p = #W := Nat.div_add_mod #W p
  have hqZ : (p : ℤ) * q + (#W % p : ℕ) = (#W : ℤ) := by exact_mod_cast hq
  have hc : 2 * ((q.choose 2 : ℕ) : ℤ) = (q : ℤ) * (q - 1) := by
    have hh := congrArg (Nat.cast : ℕ → ℤ) (two_choose q)
    rw [cast_mul_pred] at hh
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hresult :
      (2 : ℤ) * ((p : ℤ) * (q.choose 2 : ℕ) + (#W % p : ℕ) * (q : ℤ)) ≤
      ∑ i ∈ range p, ((#(cell W f i) * (#(cell W f i) - 1) : ℕ) : ℤ) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ p by positivity) (show (0 : ℤ) ≤ q by positivity)]
  exact_mod_cast hresult

/- ## Ordered counts really count each unordered edge twice -/

def edges (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) : Finset (Sym2 V) :=
  W.sym2.filter (fun e => e ∈ G.edgeSet)

omit [DecidableEq V] in
@[simp] lemma mem_edges_mk (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (x y : V) :
    s(x, y) ∈ edges G W ↔ x ∈ W ∧ y ∈ W ∧ G.Adj x y := by
  simp [edges, and_assoc]

omit [DecidableEq V] in
lemma arcs_eq_ordered (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    arcs G W = #((W ×ˢ W).filter (fun xy => G.Adj xy.1 xy.2)) := by
  simp only [arcs, degree, card_filter, sum_product]

lemma edge_fiber_two (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V)
    (e : Sym2 V) (he : e ∈ edges G W) :
    #(((W ×ˢ W).filter (fun xy => G.Adj xy.1 xy.2)).filter
      (fun xy => s(xy.1, xy.2) = e)) = 2 := by
  induction e with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := (mem_edges_mk G W a b).mp he
    have hset : ((W ×ˢ W).filter (fun xy => G.Adj xy.1 xy.2)).filter
        (fun xy => s(xy.1, xy.2) = s(a, b)) = {(a, b), (b, a)} := by
      ext xy
      rcases xy with ⟨x, y⟩
      simp only [mem_filter, mem_product, mem_insert, mem_singleton, Prod.mk.injEq,
        Sym2.eq_iff]
      constructor
      · exact fun h => h.2
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨⟨ha, hb⟩, hab⟩, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨⟨hb, ha⟩, hab.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
    rw [hset, card_insert_of_notMem, card_singleton]
    simp only [mem_singleton, Prod.mk.injEq, not_and]
    intro heq
    exact (hab.ne heq).elim

theorem arcs_eq_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    arcs G W = 2 * #(edges G W) := by
  rw [arcs_eq_ordered]
  have hmap : ∀ xy ∈ (W ×ˢ W).filter (fun xy => G.Adj xy.1 xy.2),
      s(xy.1, xy.2) ∈ edges G W := by
    intro xy hxy
    have h := mem_filter.mp hxy
    exact (mem_edges_mk G W xy.1 xy.2).mpr ⟨(mem_product.mp h.1).1,
      (mem_product.mp h.1).2, h.2⟩
  rw [card_eq_sum_card_fiberwise hmap]
  rw [sum_congr rfl (fun e he => edge_fiber_two G W e he)]
  simp [Nat.mul_comm]

omit [DecidableEq V] in
lemma edges_univ [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    edges G univ = G.edgeFinset := by
  ext e
  induction e with
  | _ a b => simp

lemma choose_eq_edges_add_compl (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) :
    (#W).choose 2 = #(edges G W) + #(edges Gᶜ W) := by
  have h := arcs_add_holes G W
  unfold holes at h
  rw [arcs_eq_twice_edges, arcs_eq_twice_edges, ← two_choose] at h
  omega

/-- The unsigned, unordered form of the stronger partition inequality. -/
theorem exists_partition_unordered (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (W : Finset V) (h : IndependenceBound G W p) :
    ∃ f : V → ℕ, (∀ x ∈ W, f x < p) ∧
      (∑ i ∈ range p, ((#(cell W f i)).choose 2 + #(edges Gᶜ (cell W f i)))) ≤
        #(edges G W) := by
  obtain ⟨f, hf, hh⟩ := exists_partition G p W h
  refine ⟨f, hf, ?_⟩
  have hc : ∀ S : Finset V,
      cost G S = 2 * ((#S).choose 2 + #(edges Gᶜ S)) := by
    intro S
    rw [cost, holes, arcs_eq_twice_edges, ← two_choose]
    ring
  simp_rw [hc] at hh
  rw [← mul_sum, arcs_eq_twice_edges] at hh
  omega

/-- **partition stability**, with an explicit partition: holes are bounded by the exact
edge surplus. The expression for the threshold is the exact `tau(n,p)`. -/
theorem partition_stability (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (W : Finset V) (h : IndependenceBound G W p) :
    ∃ f : V → ℕ, (∀ x ∈ W, f x < p) ∧
      (∑ i ∈ range p, #(edges Gᶜ (cell W f i))) +
        (p * (#W / p).choose 2 + (#W % p) * (#W / p)) ≤ #(edges G W) := by
  obtain ⟨f, hf, hh⟩ := exists_partition_unordered G p W h
  refine ⟨f, hf, ?_⟩
  have hs := size_budget hf
  simp_rw [← two_choose] at hs
  rw [← mul_sum] at hs
  rw [sum_add_distrib] at hh
  omega

/-- The exact extremal lower bound, derived here from the minimum-degree
induction rather than imported from an external graph theorem. -/
theorem edge_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : ℕ) (W : Finset V) (h : IndependenceBound G W p) :
    p * (#W / p).choose 2 + (#W % p) * (#W / p) ≤ #(edges G W) := by
  obtain ⟨f, _, hh⟩ := partition_stability G p W h
  omega

omit [DecidableEq V] in
lemma edges_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A W : Finset V} (hAW : A ⊆ W) : edges G A ⊆ edges G W := by
  intro e he
  induction e with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := (mem_edges_mk G A x y).mp he
    exact (mem_edges_mk G W x y).mpr ⟨hAW hx, hAW hy, hxy⟩

/-- Delete a vertex and its neighbours, retaining the disjoint incident edges.
This is the graph-theoretic part of the exact local-degree bound the local-degree bound. -/
theorem local_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {W : Finset V} {x : V} (hx : x ∈ W)
    (h : IndependenceBound G W (p + 1)) :
    degree G W x +
      (p * ((#W - (degree G W x + 1)) / p).choose 2 +
        ((#W - (degree G W x + 1)) % p) * ((#W - (degree G W x + 1)) / p)) ≤
      #(edges G W) := by
  have hlow := edge_lower_bound G p (W \ closed G W x)
    (independence_delete_closed G hx h)
  have hcard : #(W \ closed G W x) = #W - (degree G W x + 1) := by
    rw [card_sdiff_of_subset (closed_subset G hx), closed_card]
  rw [hcard] at hlow
  have hsub : W \ closed G W x ⊆ W \ {x} := by
    intro y hy
    obtain ⟨hyW, hyB⟩ := mem_sdiff.mp hy
    refine mem_sdiff.mpr ⟨hyW, ?_⟩
    intro hyx
    exact hyB (mem_insert.mpr (Or.inl (mem_singleton.mp hyx)))
  have he := card_le_card (edges_mono G hsub)
  have hi := deletion_identity G (singleton_subset_iff.mpr hx)
  have hz : arcs G {x} = 0 := by simp [arcs, degree]
  rw [hz, add_zero, sum_singleton, arcs_eq_twice_edges, arcs_eq_twice_edges] at hi
  omega

end Stability
end


/- Consequences -/
section
/-
# Connections of the elementary partition proof to the ColourBounds vocabulary

The proofs below use the new minimum-degree induction for every extremal
inequality. Only definitions, arithmetic and elementary counting are reused
from TBBridge and TBPalette. The full target remains a separate open statement.
-/

set_option autoImplicit false

namespace Consequences

open Finset SimpleGraph Stability

variable {V : Type*} [Fintype V] [DecidableEq V] {r p : ℕ}

theorem independenceBound_of_caps {c : ColourBounds.Coloring V r} (hc : ColourBounds.Caps c)
    (j : Fin r) (W : Finset V) : IndependenceBound (ColourBounds.colourGraph c j) W r := by
  intro S _ hS
  exact hc j S (ColourBounds.isIndepSet_colourGraph_iff.mp hS)

omit [Fintype V] in
/-- The earlier library-dependent lower bound, now with an internal proof. -/
theorem tau_le_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (h : IndependenceBound G W p) :
    ColourBounds.tau #W p ≤ #(edges G W) := edge_lower_bound G p W h

theorem tau_le_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IndependenceBound G univ p) :
    ColourBounds.tau (Fintype.card V) p ≤ #G.edgeFinset := by
  simpa only [card_univ, edges_univ] using tau_le_edges G univ h

lemma internalCount_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin p) (i : Fin p) :
    ColourBounds.internalCount G f i = #(edges G (ColourBounds.part f i)) := by
  unfold ColourBounds.internalCount ColourBounds.classCount
  congr 1
  ext e
  induction e with
  | _ x y => simp [edges, and_assoc, and_comm]

lemma partHoles_eq (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) :
    ColourBounds.partHoles G f = ∑ i : Fin p, (#(edges Gᶜ (ColourBounds.part f i)) : ℤ) := by
  unfold ColourBounds.partHoles
  apply sum_congr rfl
  intro i _
  rw [internalCount_eq]
  have h := choose_eq_edges_add_compl G (ColourBounds.part f i)
  have hz := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at hz
  omega

/-- **partition stability in the existing `ColourBounds.partHoles` and `ColourBounds.tau` definitions.**
All p labelled parts are present and empty parts are allowed. -/
theorem exists_partHoles_le_surplus (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IndependenceBound G univ p) :
    ∃ f : V → Fin p,
      ColourBounds.partHoles G f ≤ (#G.edgeFinset : ℤ) - (ColourBounds.tau (Fintype.card V) p : ℤ) := by
  obtain ⟨f, hf, hh⟩ := partition_stability G p univ h
  let g : V → Fin p := fun x => ⟨f x, hf x (mem_univ x)⟩
  have hcell : ∀ i : Fin p, cell univ f (i : ℕ) = ColourBounds.part g i := by
    intro i
    ext x
    simp [cell, ColourBounds.part, g, Fin.ext_iff]
  have hsum : (∑ i ∈ range p, #(edges Gᶜ (cell univ f i))) =
      ∑ i : Fin p, #(edges Gᶜ (ColourBounds.part g i)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl (fun i _ => by rw [hcell])
  rw [hsum, card_univ, edges_univ] at hh
  refine ⟨g, ?_⟩
  rw [partHoles_eq]
  have hz : (∑ i : Fin p, (#(edges Gᶜ (ColourBounds.part g i)) : ℤ)) +
      (ColourBounds.tau (Fintype.card V) p : ℤ) ≤ (#G.edgeFinset : ℤ) := by exact_mod_cast hh
  linarith

/-- **the palette bound**, using only the internal extremal bound proved above. -/
theorem palette (hr : 0 < r) {c : ColourBounds.Coloring V r} (hc : ColourBounds.Caps c)
    (j : Fin r) (W : Finset V) :
    ((r : ℤ) - 1) * (ColourBounds.tau #W r : ℤ) ≤ ColourBounds.holesIn c j W := by
  classical
  have hcW := ColourBounds.caps_restrictColouring hc W
  have hlow : ∀ k : Fin r,
      ColourBounds.tau #W r ≤ #(ColourBounds.colourGraph (ColourBounds.restrictColouring c W) k).edgeFinset := by
    intro k
    simpa only [Fintype.card_coe] using tau_le_edgeFinset
      (ColourBounds.colourGraph (ColourBounds.restrictColouring c W) k)
      (independenceBound_of_caps hcW k univ)
  have hbound : (r - 1) * ColourBounds.tau #W r ≤
      ∑ k ∈ univ.erase j, #(ColourBounds.colourGraph (ColourBounds.restrictColouring c W) k).edgeFinset := by
    calc _ = ∑ _k ∈ univ.erase j, ColourBounds.tau #W r := by simp
         _ ≤ _ := sum_le_sum (fun k _ => hlow k)
  rw [ColourBounds.holesIn_eq_sum]
  have hz := (Int.ofNat_le.mpr hbound)
  rw [Nat.cast_mul, Nat.cast_sub hr] at hz
  norm_num at hz ⊢
  exact hz

lemma partHoles_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → Fin p) :
    0 ≤ ColourBounds.partHoles G f := by
  rw [partHoles_eq]
  exact sum_nonneg (fun _ _ => Int.natCast_nonneg _)

/-- The minimum-hole partition exists, and its H and X satisfy the exact
minimum-hole optimality bounds. This is finite minimization, with no balance assumption. -/
theorem exists_minimum_partition (hp : 1 ≤ p)
    (hV : Fintype.card V = p * r + 1)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IndependenceBound G univ p) :
    ∃ f : V → Fin p,
      (∀ g : V → Fin p, ColourBounds.partHoles G f ≤ ColourBounds.partHoles G g) ∧
      0 ≤ ColourBounds.partHoles G f ∧
      ColourBounds.partHoles G f ≤ ColourBounds.partSurplus G p r ∧
      ColourBounds.partCross G f ≤ 2 * ColourBounds.partSurplus G p r := by
  classical
  obtain ⟨g, hg⟩ := exists_partHoles_le_surplus G h
  obtain ⟨f, _, hmin⟩ := exists_min_image (univ : Finset (V → Fin p))
    (ColourBounds.partHoles G) ⟨g, mem_univ g⟩
  have hfg := hmin g (mem_univ g)
  have hH : ColourBounds.partHoles G f ≤ ColourBounds.partSurplus G p r := by
    unfold ColourBounds.partSurplus
    rw [hV] at hg
    exact hfg.trans hg
  have heq := ColourBounds.partSurplus_eq hp r hV G f
  have hI := ColourBounds.partImbalance_nonneg f r
  exact ⟨f, fun g => hmin g (mem_univ g), partHoles_nonneg G f, hH, by linarith⟩

/-- **the local-degree bound** in the signed-surplus vocabulary, for every vertex.
No assumption that a vertex of a particular degree exists is made. -/
theorem local_surplus_bound (hr : 1 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    {c : ColourBounds.Coloring V r} (hc : ColourBounds.Caps c) (j : Fin r) (x : V) :
    (degree (ColourBounds.colourGraph c j) univ x : ℤ) +
      (ColourBounds.tau (r ^ 2 - degree (ColourBounds.colourGraph c j) univ x) (r - 1) : ℤ) -
      (ColourBounds.tau0 r : ℤ) ≤ ColourBounds.surplus c j := by
  have hb : IndependenceBound (ColourBounds.colourGraph c j) univ ((r - 1) + 1) := by
    rw [Nat.sub_add_cancel hr]
    exact independenceBound_of_caps hc j univ
  have hl := local_degree_bound (ColourBounds.colourGraph c j) (mem_univ x) hb
  have hd : #((univ : Finset V)) - (degree (ColourBounds.colourGraph c j) univ x + 1) =
      r ^ 2 - degree (ColourBounds.colourGraph c j) univ x := by
    rw [card_univ, hV]
    omega
  rw [hd, edges_univ] at hl
  change degree (ColourBounds.colourGraph c j) univ x +
    ColourBounds.tau (r ^ 2 - degree (ColourBounds.colourGraph c j) univ x) (r - 1) ≤
    #(ColourBounds.colourGraph c j).edgeFinset at hl
  have hz := (Int.ofNat_le.mpr hl)
  push_cast at hz
  unfold ColourBounds.surplus
  omega

lemma sum_coloured_edges (c : ColourBounds.Coloring V r) (W : Finset V) :
    (∑ j : Fin r, #(edges (ColourBounds.colourGraph c j) W)) = (#W).choose 2 := by
  have htop : #(edges (⊤ : SimpleGraph V) W) = (#W).choose 2 := by
    have h := choose_eq_edges_add_compl (⊤ : SimpleGraph V) W
    simpa [edges] using h.symm
  rw [← htop, card_eq_sum_card_fiberwise
    (f := c) (s := edges (⊤ : SimpleGraph V) W) (t := univ) (fun _ _ => mem_univ _)]
  apply sum_congr rfl
  intro j _
  congr 1
  ext e
  induction e with
  | _ x y => simp [edges, ColourBounds.colourGraph_adj, and_assoc]

/-- Palette in raw unordered counts on the original carrier. -/
theorem palette_edges {c : ColourBounds.Coloring V r} (hc : ColourBounds.Caps c)
    (j : Fin r) (W : Finset V) :
    (r - 1) * ColourBounds.tau #W r ≤ #(edges (ColourBounds.colourGraph c j)ᶜ W) := by
  have hlow : ∀ k : Fin r, ColourBounds.tau #W r ≤ #(edges (ColourBounds.colourGraph c k) W) := by
    intro k
    exact tau_le_edges _ _ (independenceBound_of_caps hc k W)
  have hle := sum_le_sum (s := univ.erase j) (fun k _ => hlow k)
  have hsum := sum_coloured_edges c W
  have hsplit := sum_erase_add (univ : Finset (Fin r))
    (fun k => #(edges (ColourBounds.colourGraph c k) W)) (mem_univ j)
  have hpairs := choose_eq_edges_add_compl (ColourBounds.colourGraph c j) W
  simp only [sum_const, card_erase_of_mem (mem_univ j), card_univ,
    Fintype.card_fin, smul_eq_mul] at hle
  omega

/-- A direct, uniform consequence of the newly proved stability and palette
lemmas. Its bound `r-1` is strictly below the per-colour target bound's target when r>=5. -/
theorem surplus_ge_pred (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    {c : ColourBounds.Coloring V r} (hc : ColourBounds.Caps c) (j : Fin r) :
    (r : ℤ) - 1 ≤ ColourBounds.surplus c j := by
  classical
  obtain ⟨f, hf⟩ := exists_partHoles_le_surplus (ColourBounds.colourGraph c j)
    (independenceBound_of_caps hc j univ)
  rw [hV, ← ColourBounds.tau0_eq_tau hr] at hf
  have hlarge : ∃ i : Fin r, r + 1 ≤ #(ColourBounds.part f i) := by
    by_contra hn
    have hsize : ∀ i : Fin r, #(ColourBounds.part f i) ≤ r := by
      intro i
      by_contra hi
      exact hn ⟨i, by omega⟩
    have hs := sum_le_sum (s := univ) (fun i _ => hsize i)
    rw [ColourBounds.sum_card_part, hV] at hs
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hs
    nlinarith
  obtain ⟨i, hi⟩ := hlarge
  have ht := ColourBounds.sub_le_tau (by omega : 0 < r) (#(ColourBounds.part f i))
  have htz : (1 : ℤ) ≤ (ColourBounds.tau #(ColourBounds.part f i) r : ℤ) := by
    have hiz : (r : ℤ) + 1 ≤ (#(ColourBounds.part f i) : ℤ) := by exact_mod_cast hi
    omega
  have htN : 1 ≤ ColourBounds.tau #(ColourBounds.part f i) r := by exact_mod_cast htz
  have hp := palette_edges hc j (ColourBounds.part f i)
  have hmul : r - 1 ≤ (r - 1) * ColourBounds.tau #(ColourBounds.part f i) r := by
    simpa using Nat.mul_le_mul_left (r - 1) htN
  have hh : r - 1 ≤ #(edges (ColourBounds.colourGraph c j)ᶜ (ColourBounds.part f i)) := hmul.trans hp
  have hs : (#(edges (ColourBounds.colourGraph c j)ᶜ (ColourBounds.part f i)) : ℤ) ≤
      ColourBounds.partHoles (ColourBounds.colourGraph c j) f := by
    rw [partHoles_eq]
    exact single_le_sum (fun _ _ => Int.natCast_nonneg _) (mem_univ i)
  have hhZ : (r : ℤ) - 1 ≤ (#(edges (ColourBounds.colourGraph c j)ᶜ (ColourBounds.part f i)) : ℤ) := by
    have hz := Int.ofNat_le.mpr hh
    rw [Nat.cast_sub (by omega : 1 ≤ r)] at hz
    simpa using hz
  exact hhZ.trans (hs.trans hf)

lemma tau_isolated_identity (hr : 3 ≤ r) :
    ColourBounds.tau (r ^ 2) (r - 1) = ColourBounds.tau0 r + r.choose 2 + 1 := by
  have hr1 : 1 ≤ r := by omega
  have hd : (r - 1) * (r + 1) + 1 = r ^ 2 := by
    have h := Nat.sub_add_cancel hr1
    nlinarith
  have hq : r ^ 2 / (r - 1) = r + 1 := by
    rw [← hd, Nat.mul_add_div (by omega : 0 < r - 1),
      Nat.div_eq_of_lt (by omega : 1 < r - 1), Nat.add_zero]
  have hm : r ^ 2 % (r - 1) = 1 := by
    rw [← hd, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 1 < r - 1)]
  unfold ColourBounds.tau ColourBounds.tau0
  rw [hq, hm, one_mul]
  have h1 := two_choose (r + 1)
  have h2 := two_choose r
  rw [Nat.add_sub_cancel] at h1
  have hd' := Nat.sub_add_cancel hr1
  have h1' := congrArg (fun x : ℕ => (r - 1) * x) h1
  have h2' := congrArg (fun x : ℕ => (r - 1) * x) h2
  nlinarith

/-- The local bound reaches precisely the per-colour target bound at an isolated vertex. The
existence of such a vertex is not inferred or assumed in the main target. -/
theorem surplus_of_isolated (hr : 3 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    {c : ColourBounds.Coloring V r} (hc : ColourBounds.Caps c) (j : Fin r) (x : V)
    (hx : degree (ColourBounds.colourGraph c j) univ x = 0) :
    (r.choose 2 : ℤ) + 1 ≤ ColourBounds.surplus c j := by
  have h := local_surplus_bound (by omega : 1 ≤ r) hV hc j x
  rw [hx, Nat.sub_zero, tau_isolated_identity hr] at h
  push_cast at h
  linarith

end Consequences
end


/- Optimality -/
section
/- The vertex-transfer part of minimum-hole optimality. All changes of the partition and
all changes of the unordered edge counts are proved explicitly. -/

set_option autoImplicit false

namespace Optimality

open Finset Stability Consequences

variable {V : Type*} [Fintype V] [DecidableEq V] {p r : ℕ}

omit [Fintype V] in
lemma edges_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {x : V} (hx : x ∉ S) :
    #(edges G (insert x S)) = #(edges G S) + degree G S x := by
  have hi := deletion_identity G
    (singleton_subset_iff.mpr (mem_insert_self x S))
  have hs : insert x S \ {x} = S := by ext y; simp; aesop
  have hz : arcs G {x} = 0 := by simp [arcs, degree]
  have hd : degree G (insert x S) x = degree G S x := by simp [degree, filter_insert]
  rw [hz, add_zero, hs, sum_singleton, hd, arcs_eq_twice_edges, arcs_eq_twice_edges] at hi
  omega

omit [Fintype V] in
lemma edges_erase (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {x : V} (hx : x ∈ S) :
    #(edges G S) = #(edges G (S.erase x)) + degree G S x := by
  have h := edges_insert G (notMem_erase x S)
  have hd : degree G (S.erase x) x = degree G S x := by
    simp [degree, filter_erase, erase_eq_of_notMem]
  rw [insert_erase hx, hd] at h
  exact h

omit [Fintype V] in
lemma degree_add_compl_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {x : V} (hx : x ∉ S) :
    degree G S x + degree Gᶜ S x = #S := by
  have h := degree_add_compl G (mem_insert_self x S)
  simpa [degree, hx, filter_insert] using h

def move (f : V → Fin p) (x : V) (k : Fin p) : V → Fin p := Function.update f x k

lemma move_source (f : V → Fin p) (x : V) (k : Fin p) (hk : k ≠ f x) :
    ColourBounds.part (move f x k) (f x) = (ColourBounds.part f (f x)).erase x := by
  ext y
  by_cases hy : y = x
  · subst y
    simp [ColourBounds.part, move, Function.update, hk]
  · simp [ColourBounds.part, move, Function.update, hy]

lemma move_destination (f : V → Fin p) (x : V) (k : Fin p) :
    ColourBounds.part (move f x k) k = insert x (ColourBounds.part f k) := by
  ext y
  by_cases hy : y = x
  · subst y
    simp [ColourBounds.part, move, Function.update]
  · simp [ColourBounds.part, move, Function.update, hy]

lemma move_other (f : V → Fin p) (x : V) (k i : Fin p)
    (hix : i ≠ f x) (hik : i ≠ k) : ColourBounds.part (move f x k) i = ColourBounds.part f i := by
  ext y
  by_cases hy : y = x
  · subst y
    simp [ColourBounds.part, move, Function.update, Ne.symm hix, Ne.symm hik]
  · simp [ColourBounds.part, move, Function.update, hy]

/-- Moving one vertex changes the hole count by the difference of its
complement-degrees into the receiving and donating parts. -/
theorem move_holes_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin p) (x : V) (k : Fin p) (hk : k ≠ f x) :
    ColourBounds.partHoles G (move f x k) = ColourBounds.partHoles G f -
      (degree Gᶜ (ColourBounds.part f (f x)) x : ℤ) + (degree Gᶜ (ColourBounds.part f k) x : ℤ) := by
  have hx : x ∈ ColourBounds.part f (f x) := by simp
  have hxk : x ∉ ColourBounds.part f k := by simp [Ne.symm hk]
  have hterm : ∀ i : Fin p,
      (#(edges Gᶜ (ColourBounds.part (move f x k) i)) : ℤ) =
        (#(edges Gᶜ (ColourBounds.part f i)) : ℤ) +
          (if i = f x then -(degree Gᶜ (ColourBounds.part f (f x)) x : ℤ) else 0) +
          (if i = k then (degree Gᶜ (ColourBounds.part f k) x : ℤ) else 0) := by
    intro i
    by_cases hix : i = f x
    · subst i
      rw [move_source f x k hk]
      have h := congrArg (Nat.cast : ℕ → ℤ) (edges_erase Gᶜ hx)
      push_cast at h
      simp only [ite_true, if_neg (Ne.symm hk), add_zero]
      linarith
    · by_cases hik : i = k
      · subst i
        rw [move_destination f x k, edges_insert Gᶜ hxk]
        simp [hk]
      · rw [move_other f x k i hix hik]
        simp [hix, hik]
  rw [partHoles_eq, partHoles_eq, sum_congr rfl (fun i _ => hterm i),
    sum_add_distrib, sum_add_distrib]
  simp [sub_eq_add_neg]

/-- **minimum-hole optimality, vertex transfer.** For a minimum-hole partition, a vertex has
at most as many internal non-neighbours as non-neighbours in any other part. -/
theorem minimum_holes_transfer (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → Fin p)
    (hmin : ∀ g : V → Fin p, ColourBounds.partHoles G f ≤ ColourBounds.partHoles G g)
    (x : V) (k : Fin p) (hk : k ≠ f x) :
    degree Gᶜ (ColourBounds.part f (f x)) x ≤ #(ColourBounds.part f k) - degree G (ColourBounds.part f k) x := by
  have h := hmin (move f x k)
  rw [move_holes_identity G f x k hk] at h
  have hle : degree Gᶜ (ColourBounds.part f (f x)) x ≤ degree Gᶜ (ColourBounds.part f k) x := by
    exact_mod_cast (show (degree Gᶜ (ColourBounds.part f (f x)) x : ℤ) ≤
      (degree Gᶜ (ColourBounds.part f k) x : ℤ) by linarith)
  have hd := degree_add_compl_outside G (show x ∉ ColourBounds.part f k by simp [Ne.symm hk])
  omega

/-- All clauses of minimum-hole optimality, including the transfer inequality, on the same
single minimum-hole partition. -/
theorem minimum_partition_package (hp : 1 ≤ p)
    (hV : Fintype.card V = p * r + 1)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IndependenceBound G univ p) :
    ∃ f : V → Fin p,
      (∀ g : V → Fin p, ColourBounds.partHoles G f ≤ ColourBounds.partHoles G g) ∧
      0 ≤ ColourBounds.partHoles G f ∧
      ColourBounds.partHoles G f ≤ ColourBounds.partSurplus G p r ∧
      ColourBounds.partCross G f ≤ 2 * ColourBounds.partSurplus G p r ∧
      ∀ (x : V) (k : Fin p), k ≠ f x →
        degree Gᶜ (ColourBounds.part f (f x)) x ≤ #(ColourBounds.part f k) - degree G (ColourBounds.part f k) x := by
  obtain ⟨f, hf, h0, hH, hX⟩ := exists_minimum_partition hp hV G h
  exact ⟨f, hf, h0, hH, hX, fun x k hk => minimum_holes_transfer G f hf x k hk⟩

end Optimality
end


/- Target -/
section
/- Exact sufficient bounds and their equivalence to the literal target.
These are equivalences only; no proof of the full target is asserted. -/

set_option autoImplicit false

namespace Target

open Finset

variable {r : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- the aggregate target bound for one colouring. Subtraction is already in Int in `ColourBounds.surplus`. -/
def AggregateBound (c : ColourBounds.Coloring V r) : Prop :=
  ColourBounds.Caps c → (r : ℤ) * (r.choose 2 : ℤ) + 1 ≤ ∑ j : Fin r, ColourBounds.surplus c j

/-- the per-colour target bound for one colouring, retained to check the potentially ambiguous name. -/
def PerColourBound (c : ColourBounds.Coloring V r) : Prop :=
  ColourBounds.Caps c → ∀ j : Fin r, (r.choose 2 : ℤ) + 1 ≤ ColourBounds.surplus c j

/-- The full quantified target, without a supplied proof or assumed bound. -/
def Statement : Prop :=
  ∀ r : ℕ, 5 ≤ r → ∀ {V : Type} [Fintype V] [DecidableEq V],
    Fintype.card V = r ^ 2 + 1 → ∀ c : ColourBounds.Coloring V r, AggregateBound c


theorem aggregate_iff_not_caps (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : ColourBounds.Coloring V r) : AggregateBound c ↔ ¬ ColourBounds.Caps c := by
  constructor
  · intro hb hc
    have h := hb hc
    rw [ColourBounds.sum_surplus hr hV c] at h
    omega
  · intro hn hc
    exact (hn hc).elim

theorem perColour_iff_not_caps (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : ColourBounds.Coloring V r) : PerColourBound c ↔ ¬ ColourBounds.Caps c := by
  constructor
  · intro hb hc
    exact ColourBounds.not_caps_of_surplus_ge hr hV c (hb hc)
  · intro hn hc
    exact (hn hc).elim

theorem aggregate_iff_perColour (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : ColourBounds.Coloring V r) : AggregateBound c ↔ PerColourBound c :=
  (aggregate_iff_not_caps hr hV c).trans (perColour_iff_not_caps hr hV c).symm

omit [DecidableEq V] in
theorem not_caps_iff_literal (c : ColourBounds.Coloring V r) :
    (¬ ColourBounds.Caps c) ↔ ∃ (S : Finset V) (j : Fin r), #S = r + 1 ∧ ColourBounds.Independent c j S := by
  classical
  constructor
  · intro hn
    by_contra he
    apply hn
    intro j T hT
    by_contra hcard
    obtain ⟨S, hST, hScard⟩ := exists_subset_card_eq (show r + 1 ≤ #T by omega)
    apply he
    exact ⟨S, j, hScard, fun x hx y hy hxy => hT x (hST hx) y (hST hy) hxy⟩
  · rintro ⟨S, j, hS, hI⟩ hc
    have := hc j S hI
    omega

theorem aggregate_iff_literal (hr : 2 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : ColourBounds.Coloring V r) :
    AggregateBound c ↔ ∃ (S : Finset V) (j : Fin r), #S = r + 1 ∧ ColourBounds.Independent c j S :=
  (aggregate_iff_not_caps hr hV c).trans (not_caps_iff_literal c)

/-- Full statement match, including the lower parameter bound and all carriers. -/
theorem statement_iff_literal : Statement ↔
    ∀ r : ℕ, 5 ≤ r → ∀ {V : Type} [Fintype V] [DecidableEq V],
      Fintype.card V = r ^ 2 + 1 → ∀ c : Sym2 V → Fin r,
        ∃ (S : Finset V) (j : Fin r), #S = r + 1 ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ j := by
  constructor
  · intro h r hr V _ _ hV c
    exact (aggregate_iff_literal (by omega) hV c).mp (h r hr hV c)
  · intro h r hr V _ _ hV c
    exact (aggregate_iff_literal (by omega) hV c).mpr (h r hr hV c)


end Target
end


/-- Apply the partition theorem to an actual colour graph under the target's
independence caps. All inequalities refer to the same chosen partition. -/
example {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}
    (hr : 1 ≤ r) (hV : Fintype.card V = r ^ 2 + 1)
    (c : Sym2 V → Fin r) (hc : ColourBounds.Caps c) (j : Fin r) :
    ∃ f : V → Fin r,
      (∀ g : V → Fin r, ColourBounds.partHoles (ColourBounds.colourGraph c j) f ≤
        ColourBounds.partHoles (ColourBounds.colourGraph c j) g) ∧
      0 ≤ ColourBounds.partHoles (ColourBounds.colourGraph c j) f ∧
      ColourBounds.partHoles (ColourBounds.colourGraph c j) f ≤
        ColourBounds.partSurplus (ColourBounds.colourGraph c j) r r ∧
      ColourBounds.partCross (ColourBounds.colourGraph c j) f ≤
        2 * ColourBounds.partSurplus (ColourBounds.colourGraph c j) r r ∧
      ∀ (x : V) (k : Fin r), k ≠ f x →
        Stability.degree (ColourBounds.colourGraph c j)ᶜ (ColourBounds.part f (f x)) x ≤
          (ColourBounds.part f k).card -
            Stability.degree (ColourBounds.colourGraph c j) (ColourBounds.part f k) x := by
  apply Optimality.minimum_partition_package hr (by simpa [pow_two] using hV)
  exact Consequences.independenceBound_of_caps hc j Finset.univ

end Contribution.Erdos617Partitions
