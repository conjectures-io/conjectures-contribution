import FormalConjectures.GreensOpenProblems.«12»

/-!
# Two universal families of Green 12 tuples

This file isolates the elementary counting engine used for sparse subsets: tuples with a
constant right row and tuples with a constant left row.  The two parametrizations are injective,
and their only overlap comes from constant `A`-valued words.
-/

open Finset

namespace Contribution.Green12ConstantFamilies

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The tuple predicate appearing on the right side of `Green12.green_12`. -/
def Valid (A : Finset G) (t : (Fin 5 → G) × (Fin 5 → G)) : Prop :=
  ∀ i : Fin 5, ∀ j ∈ ({i, i + 1, i + 2} : Finset (Fin 5)), t.1 i + t.2 j ∈ A

/-- The finite set counted on the right side of `Green12.green_12`. -/
noncomputable def validTuples (A : Finset G) : Finset ((Fin 5 → G) × (Fin 5 → G)) :=
  by
    classical
    exact Finset.univ.filter (Valid A)

@[simp] lemma mem_validTuples {A : Finset G} {t : (Fin 5 → G) × (Fin 5 → G)} :
    t ∈ validTuples A ↔ Valid A t := by
  classical
  simp [validTuples]

/-- A word in `A`, viewed as a `G`-valued word. -/
def wordValue {A : Finset G} (u : Fin 5 → A) : Fin 5 → G := fun i ↦ u i

/-- The Green tuple obtained by making every right coordinate equal to `g`. -/
def constantRightTuple {A : Finset G} (u : Fin 5 → A) (g : G) :
    (Fin 5 → G) × (Fin 5 → G) :=
  (fun i ↦ wordValue u i - g, fun _ ↦ g)

/-- The Green tuple obtained by making every left coordinate equal to `g`. -/
def constantLeftTuple {A : Finset G} (u : Fin 5 → A) (g : G) :
    (Fin 5 → G) × (Fin 5 → G) :=
  (fun _ ↦ g, fun j ↦ wordValue u j - g)

/-- Every constant-right tuple is valid (indeed, every one of its five relevant sums is in `A`). -/
lemma constantRightTuple_valid {A : Finset G} (u : Fin 5 → A) (g : G) :
    Valid A (constantRightTuple u g) := by
  intro i j hj
  simpa [constantRightTuple, wordValue] using (u i).property

/-- Every constant-left tuple is valid (in fact all twenty-five sums lie in `A`). -/
lemma constantLeftTuple_valid {A : Finset G} (u : Fin 5 → A) (g : G) :
    Valid A (constantLeftTuple u g) := by
  intro i j hj
  simpa [constantLeftTuple, wordValue, add_comm] using (u j).property

/-- The constant-right parametrization loses no information. -/
lemma constantRightTuple_injective {A : Finset G} :
    Function.Injective (fun p : (Fin 5 → A) × G ↦ constantRightTuple p.1 p.2) := by
  rintro ⟨u, g⟩ ⟨v, h⟩ hp
  have hgh : g = h := by
    have hfun := congrArg Prod.snd hp
    exact congrFun hfun 0
  subst h
  have huv : u = v := by
    funext i
    apply Subtype.ext
    have hi := congrFun (congrArg Prod.fst hp) i
    simpa [constantRightTuple, wordValue] using hi
  subst v
  rfl

/-- The constant-left parametrization loses no information. -/
lemma constantLeftTuple_injective {A : Finset G} :
    Function.Injective (fun p : (Fin 5 → A) × G ↦ constantLeftTuple p.1 p.2) := by
  rintro ⟨u, g⟩ ⟨v, h⟩ hp
  have hgh : g = h := by
    have hfun := congrArg Prod.fst hp
    exact congrFun hfun 0
  subst h
  have huv : u = v := by
    funext i
    apply Subtype.ext
    have hi := congrFun (congrArg Prod.snd hp) i
    simpa [constantLeftTuple, wordValue] using hi
  subst v
  rfl

/-- An `A`-valued word is constant when all five coordinates have one common value. -/
def IsConstant {A : Finset G} (u : Fin 5 → A) : Prop :=
  ∃ a : A, u = fun _ ↦ a

/-- A constant-right tuple can equal a constant-left tuple only when both words are constant. -/
lemma constantRight_eq_constantLeft_imp_constant {A : Finset G}
    (u v : Fin 5 → A) (g h : G)
    (heq : constantRightTuple u g = constantLeftTuple v h) :
    IsConstant u ∧ IsConstant v := by
  have hx : ∀ i, (u i : G) - g = h := by
    intro i
    exact congrFun (congrArg Prod.fst heq) i
  have hy : ∀ j, g = (v j : G) - h := by
    intro j
    exact congrFun (congrArg Prod.snd heq) j
  constructor
  · refine ⟨u 0, ?_⟩
    funext i
    apply Subtype.ext
    exact sub_left_injective (hx i |>.trans (hx 0).symm)
  · refine ⟨v 0, ?_⟩
    funext j
    apply Subtype.ext
    exact sub_left_injective ((hy j).symm.trans (hy 0))

/-- Constant words are in bijection with the elements of `A`. -/
def constantWordEquiv (A : Finset G) : A ≃ {u : Fin 5 → A // IsConstant u} where
  toFun a := ⟨fun _ ↦ a, ⟨a, rfl⟩⟩
  invFun u := u.1 0
  left_inv a := rfl
  right_inv := by
    rintro ⟨u, a, rfl⟩
    rfl

/-- The finite set of nonconstant `A`-valued words of length five. -/
noncomputable def nonconstantWords (A : Finset G) : Finset (Fin 5 → A) := by
  classical
  exact Finset.univ.filter fun u ↦ ¬ IsConstant u

/-- There are exactly `|A|⁵ - |A|` nonconstant `A`-valued words of length five. -/
lemma card_nonconstant_words (A : Finset G) :
    (nonconstantWords A).card = A.card ^ 5 - A.card := by
  classical
  have hmem (u : Fin 5 → A) : u ∈ nonconstantWords A ↔ ¬ IsConstant u := by
    simp [nonconstantWords]
  calc
    (nonconstantWords A).card = Fintype.card {u : Fin 5 → A // u ∈ nonconstantWords A} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {u : Fin 5 → A // ¬ IsConstant u} :=
      Fintype.card_congr (Equiv.subtypeEquivProp (funext fun u ↦ propext (hmem u)))
    _ = Fintype.card (Fin 5 → A) - Fintype.card {u : Fin 5 → A // IsConstant u} :=
      Fintype.card_subtype_compl _
    _ = A.card ^ 5 - A.card := by
      have hfun : Fintype.card (Fin 5 → A) = A.card ^ 5 := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      have hconst : Fintype.card {u : Fin 5 → A // IsConstant u} = A.card :=
        (Fintype.card_congr (constantWordEquiv A).symm).trans (Fintype.card_coe A)
      rw [hfun, hconst]

/-- The two universal families inject disjointly after constant left words are omitted. -/
def twoFamilyEmbedding (A : Finset G) :
    (((Fin 5 → A) × G) ⊕ ({u : Fin 5 → A // u ∈ nonconstantWords A} × G)) ↪
      {t : (Fin 5 → G) × (Fin 5 → G) // t ∈ validTuples A} where
  toFun
    | Sum.inl p => ⟨constantRightTuple p.1 p.2,
        mem_validTuples.mpr (constantRightTuple_valid p.1 p.2)⟩
    | Sum.inr p => ⟨constantLeftTuple p.1.1 p.2,
        mem_validTuples.mpr (constantLeftTuple_valid p.1.1 p.2)⟩
  inj' := by
    classical
    intro p q hpq
    cases p with
    | inl p =>
      cases q with
      | inl q =>
        have hp : p = q := constantRightTuple_injective (congrArg Subtype.val hpq)
        subst q
        rfl
      | inr q =>
        exfalso
        have hc := (constantRight_eq_constantLeft_imp_constant p.1 q.1.1 p.2 q.2
          (congrArg Subtype.val hpq)).2
        exact (Finset.mem_filter.mp q.1.2).2 hc
    | inr p =>
      cases q with
      | inl q =>
        exfalso
        have hc := (constantRight_eq_constantLeft_imp_constant q.1 p.1.1 q.2 p.2
          (congrArg Subtype.val hpq).symm).2
        exact (Finset.mem_filter.mp p.1.2).2 hc
      | inr q =>
        have hraw : constantLeftTuple p.1.1 p.2 = constantLeftTuple q.1.1 q.2 :=
          congrArg Subtype.val hpq
        have hpair : (p.1.1, p.2) = (q.1.1, q.2) :=
          constantLeftTuple_injective hraw
        simp only [Prod.mk.injEq] at hpair
        have hp : p = q := by
          apply Prod.ext
          · apply Subtype.ext
            exact hpair.1
          · exact hpair.2
        subst q
        rfl

/-- Universal cardinal lower bound furnished by the constant-left and constant-right families. -/
theorem card_validTuples_lower_bound (A : Finset G) :
    A.card ^ 5 * Fintype.card G + (A.card ^ 5 - A.card) * Fintype.card G ≤
      (validTuples A).card := by
  classical
  let E := twoFamilyEmbedding A
  have hcard := Fintype.card_le_of_injective E E.injective
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin] at hcard
  have hn := Fintype.card_coe (nonconstantWords A)
  have hv := Fintype.card_coe (validTuples A)
  have ha := Fintype.card_coe A
  rw [ha, hn, card_nonconstant_words, hv] at hcard
  exact hcard

/-- Symmetric form of `card_validTuples_lower_bound`: the two families have total size
`|G| (2 |A|⁵ - |A|)`. -/
theorem card_validTuples_ge_card_mul (A : Finset G) :
    Fintype.card G * (2 * A.card ^ 5 - A.card) ≤ (validTuples A).card := by
  have ha : A.card ≤ A.card ^ 5 := Nat.le_pow (by omega)
  calc
    Fintype.card G * (2 * A.card ^ 5 - A.card) =
        A.card ^ 5 * Fintype.card G + (A.card ^ 5 - A.card) * Fintype.card G := by
      rw [show 2 * A.card ^ 5 - A.card =
        A.card ^ 5 + (A.card ^ 5 - A.card) by omega]
      simp [Nat.mul_add, Nat.mul_comm]
    _ ≤ (validTuples A).card := card_validTuples_lower_bound A

/-- The universal constant-coordinate families prove the exact Green 12 inequality whenever
`|G|⁶ (2 |A|⁵ - |A|) ≥ |A|¹⁵`.  This is an unbounded sparse-set regime, not the unrestricted
conjecture. -/
theorem green12_of_card_condition (A : Finset G)
    (hcard : A.card ^ 15 ≤ Fintype.card G ^ 6 * (2 * A.card ^ 5 - A.card)) :
    ((validTuples A).card : ℝ) ≥
      ((A.card : ℝ) / Fintype.card G) ^ 15 * (Fintype.card G : ℝ) ^ 10 := by
  let N := Fintype.card G
  let a := A.card
  let d := 2 * a ^ 5 - a
  have hNnat : 0 < N := Fintype.card_pos
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hfamilyNat : N * d ≤ (validTuples A).card := card_validTuples_ge_card_mul A
  have hfamily : (N : ℝ) * d ≤ ((validTuples A).card : ℝ) := by exact_mod_cast hfamilyNat
  have hcondition : (a : ℝ) ^ 15 ≤ (N : ℝ) ^ 6 * d := by exact_mod_cast hcard
  have hscaled : (a : ℝ) ^ 15 / (N : ℝ) ^ 5 ≤ (N : ℝ) * d := by
    rw [div_le_iff₀ (pow_pos hN 5)]
    nlinarith [hcondition]
  calc
    ((A.card : ℝ) / Fintype.card G) ^ 15 * (Fintype.card G : ℝ) ^ 10 =
        (a : ℝ) ^ 15 / (N : ℝ) ^ 5 := by
      dsimp [a, N]
      field_simp
    _ ≤ (N : ℝ) * d := hscaled
    _ ≤ ((validTuples A).card : ℝ) := hfamily

end Contribution.Green12ConstantFamilies
